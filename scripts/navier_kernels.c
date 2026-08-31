/* Fused pointwise kernels for the pseudo-spectral Navier--Stokes core.
 *
 * WHY THIS EXISTS (measured, 2026-08-31, macbook-satellite):
 * at the grid sizes this benchmark runs (N = 16, 32, 48) a single spectral
 * component is 2.3k-56k complex numbers -- tens of kilobytes.  Every numpy
 * expression on an array that small is dominated by interpreter and ufunc
 * dispatch, not arithmetic.  One IFRK4 step at N=16 issued ~150 separate
 * numpy calls and cost 1184 us, of which only 440 us was FFT.  Profiled
 * breakdown of one RHS evaluation (best-of-200, in-process perf_counter):
 *
 *     irfftn (6 comp)  75 us      curl_hat        40 us
 *     rfftn  (3 comp)  35 us      leray           36 us
 *                                 cross product  ~30 us
 *                                 dealias mults  ~15 us
 *
 * The 120 us of pointwise work is ~50k flops over ~110 KB.  That is
 * memory-bandwidth trivial; it was purely dispatch.  Fusing it into four C
 * loops removes ~40 numpy dispatches per RHS evaluation.
 *
 * Every routine here is a bit-for-bit reformulation of the numpy expression
 * it replaces: same operation order per element, same IEEE-754 double
 * arithmetic, no reassociation, no fast-math.  ``navier_spectral_core``
 * verifies this at import time against the numpy path and falls back
 * silently if the two ever disagree.
 *
 * Complex numbers are handled as interleaved (re, im) doubles rather than
 * C99 _Complex so the file compiles identically under any C11 toolchain and
 * so the multiply-by-i in the curl is written as the exact swap-and-negate
 * numpy performs, not as a general complex multiply.
 */

#include <stddef.h>

/* ------------------------------------------------------------------ *
 * 1. pre_transform: dealias the velocity and build its curl, packing  *
 *    both into one 6-component spectral buffer for a single batched   *
 *    inverse transform.                                               *
 *                                                                     *
 *    numpy equivalent:                                                *
 *        work = vhat * dealias                                        *
 *        curl[0] = 1j*(ky*work[2] - kz*work[1])   (and cyclic)        *
 *                                                                     *
 *    ``m`` is the number of complex entries in ONE component,         *
 *    n*n*(n/2+1).  ``out`` is 6*m complex entries.                    *
 * ------------------------------------------------------------------ */
void navier_pre_transform(const double *vhat,   /* 3*m complex, interleaved */
                          const double *kx,
                          const double *ky,
                          const double *kz,
                          const double *dealias,
                          double *out,          /* 6*m complex, interleaved */
                          size_t m)
{
    const double *v0 = vhat;
    const double *v1 = vhat + 2 * m;
    const double *v2 = vhat + 4 * m;
    double *w0 = out;
    double *w1 = out + 2 * m;
    double *w2 = out + 4 * m;
    double *c0 = out + 6 * m;
    double *c1 = out + 8 * m;
    double *c2 = out + 10 * m;

    for (size_t i = 0; i < m; ++i) {
        const size_t j = 2 * i;
        const double d = dealias[i];
        const double a = kx[i], b = ky[i], c = kz[i];

        const double w0r = v0[j] * d, w0i = v0[j + 1] * d;
        const double w1r = v1[j] * d, w1i = v1[j + 1] * d;
        const double w2r = v2[j] * d, w2i = v2[j + 1] * d;

        w0[j] = w0r; w0[j + 1] = w0i;
        w1[j] = w1r; w1[j + 1] = w1i;
        w2[j] = w2r; w2[j + 1] = w2i;

        /* curl = i * (k x w).  Multiplying by i sends (re, im) -> (-im, re). */
        const double t0r = b * w2r - c * w1r;
        const double t0i = b * w2i - c * w1i;
        const double t1r = c * w0r - a * w2r;
        const double t1i = c * w0i - a * w2i;
        const double t2r = a * w1r - b * w0r;
        const double t2i = a * w1i - b * w0i;

        c0[j] = -t0i; c0[j + 1] = t0r;
        c1[j] = -t1i; c1[j + 1] = t1r;
        c2[j] = -t2i; c2[j + 1] = t2r;
    }
}

/* ------------------------------------------------------------------ *
 * 2. cross: the physical-space rotational term omega x u, reading the *
 *    packed (u, omega) buffer the batched inverse transform produced. *
 *    ``p`` = n^3 real entries per component.                          *
 * ------------------------------------------------------------------ */
void navier_cross(const double *uw,   /* 6*p real: u in 0..2, omega in 3..5 */
                  double *out,        /* 3*p real */
                  size_t p)
{
    const double *u0 = uw, *u1 = uw + p, *u2 = uw + 2 * p;
    const double *g0 = uw + 3 * p, *g1 = uw + 4 * p, *g2 = uw + 5 * p;
    double *o0 = out, *o1 = out + p, *o2 = out + 2 * p;

    for (size_t i = 0; i < p; ++i) {
        const double a0 = u0[i], a1 = u1[i], a2 = u2[i];
        const double b0 = g0[i], b1 = g1[i], b2 = g2[i];
        o0[i] = b1 * a2 - b2 * a1;
        o1[i] = b2 * a0 - b0 * a2;
        o2[i] = b0 * a1 - b1 * a0;
    }
}

/* ------------------------------------------------------------------ *
 * 3. post_leray: dealias the transformed product, apply the           *
 *    Helmholtz--Leray projector, and scale -- all in one pass,        *
 *    writing into ``out`` (which may alias ``chat``).                 *
 *                                                                     *
 *    numpy equivalent:                                                *
 *        c *= dealias                                                 *
 *        s = (kx*c0 + ky*c1 + kz*c2) * inv_k2                         *
 *        c0 -= kx*s ;  c1 -= ky*s ;  c2 -= kz*s                       *
 *        out = scale * c                                              *
 *                                                                     *
 *    ``scale`` folds in both the sign of the rotational term and the  *
 *    IFRK4 step size, removing two more full-array numpy passes.      *
 * ------------------------------------------------------------------ */
void navier_post_leray(const double *chat,     /* 3*m complex */
                       const double *kx,
                       const double *ky,
                       const double *kz,
                       const double *inv_k2,
                       const double *dealias,
                       double scale,
                       int apply_dealias,
                       double *out,            /* 3*m complex */
                       size_t m)
{
    const double *c0 = chat, *c1 = chat + 2 * m, *c2 = chat + 4 * m;
    double *o0 = out, *o1 = out + 2 * m, *o2 = out + 4 * m;

    for (size_t i = 0; i < m; ++i) {
        const size_t j = 2 * i;
        const double d = apply_dealias ? dealias[i] : 1.0;
        const double a = kx[i], b = ky[i], c = kz[i];

        const double x0r = c0[j] * d, x0i = c0[j + 1] * d;
        const double x1r = c1[j] * d, x1i = c1[j + 1] * d;
        const double x2r = c2[j] * d, x2i = c2[j + 1] * d;

        const double sr = (a * x0r + b * x1r + c * x2r) * inv_k2[i];
        const double si = (a * x0i + b * x1i + c * x2i) * inv_k2[i];

        o0[j]     = scale * (x0r - a * sr);
        o0[j + 1] = scale * (x0i - a * si);
        o1[j]     = scale * (x1r - b * sr);
        o1[j + 1] = scale * (x1i - b * si);
        o2[j]     = scale * (x2r - c * sr);
        o2[j + 1] = scale * (x2i - c * si);
    }
}

/* ------------------------------------------------------------------ *
 * 4. IFRK4 stage assembly.  ``e_full`` and ``e_half`` are REAL        *
 *    (n, n, n/2+1) integrating factors broadcast over the three       *
 *    velocity components, so each is indexed by i while the state is  *
 *    indexed by component.  ``m`` is entries per component.           *
 * ------------------------------------------------------------------ */

/* out = e_half * (v + 0.5 * a)          -- stage-2 input */
void navier_stage2(const double *v, const double *a, const double *eh,
                   double *out, size_t m)
{
    for (size_t comp = 0; comp < 3; ++comp) {
        const double *vc = v + 2 * m * comp, *ac = a + 2 * m * comp;
        double *oc = out + 2 * m * comp;
        for (size_t i = 0; i < m; ++i) {
            const double e = eh[i];
            oc[2 * i]     = e * (vc[2 * i]     + 0.5 * ac[2 * i]);
            oc[2 * i + 1] = e * (vc[2 * i + 1] + 0.5 * ac[2 * i + 1]);
        }
    }
}

/* out = e_half * v + 0.5 * b            -- stage-3 input */
void navier_stage3(const double *v, const double *b, const double *eh,
                   double *out, size_t m)
{
    for (size_t comp = 0; comp < 3; ++comp) {
        const double *vc = v + 2 * m * comp, *bc = b + 2 * m * comp;
        double *oc = out + 2 * m * comp;
        for (size_t i = 0; i < m; ++i) {
            const double e = eh[i];
            oc[2 * i]     = e * vc[2 * i]     + 0.5 * bc[2 * i];
            oc[2 * i + 1] = e * vc[2 * i + 1] + 0.5 * bc[2 * i + 1];
        }
    }
}

/* out = e_full * v + e_half * c         -- stage-4 input */
void navier_stage4(const double *v, const double *c, const double *ef,
                   const double *eh, double *out, size_t m)
{
    for (size_t comp = 0; comp < 3; ++comp) {
        const double *vc = v + 2 * m * comp, *cc = c + 2 * m * comp;
        double *oc = out + 2 * m * comp;
        for (size_t i = 0; i < m; ++i) {
            const double f = ef[i], h = eh[i];
            oc[2 * i]     = f * vc[2 * i]     + h * cc[2 * i];
            oc[2 * i + 1] = f * vc[2 * i + 1] + h * cc[2 * i + 1];
        }
    }
}

/* out = e_full*v + (e_full*a + 2*e_half*(b + c) + d) / 6   -- final combine
 *
 * NOTE ON THE 1/6.  numpy does NOT divide a complex array by a real scalar
 * componentwise: it strength-reduces ``w / 6.0`` to ``w * (1.0 / 6.0)``,
 * and 1/6 is not representable, so the two differ by one ULP.  Measured
 * 2026-08-31: writing ``/ 6.0`` here made the self-check fail at 4.97e-16.
 * Multiplying by the reciprocal reproduces numpy bit-for-bit.
 */
void navier_combine(const double *v, const double *a, const double *b,
                    const double *c, const double *d, const double *ef,
                    const double *eh, double *out, size_t m)
{
    const double sixth = 1.0 / 6.0;
    for (size_t comp = 0; comp < 3; ++comp) {
        const size_t o = 2 * m * comp;
        const double *vc = v + o, *ac = a + o, *bc = b + o;
        const double *cc = c + o, *dc = d + o;
        double *oc = out + o;
        for (size_t i = 0; i < m; ++i) {
            const double f = ef[i], h = eh[i];
            const size_t j = 2 * i;
            oc[j] = f * vc[j]
                  + (f * ac[j] + 2.0 * h * (bc[j] + cc[j]) + dc[j]) * sixth;
            oc[j + 1] = f * vc[j + 1]
                  + (f * ac[j + 1] + 2.0 * h * (bc[j + 1] + cc[j + 1])
                     + dc[j + 1]) * sixth;
        }
    }
}

/* out = base + dt * forcing_projected   -- MMS forcing accumulation */
void navier_axpy(const double *base, const double *add, double dt,
                 double *out, size_t n)
{
    for (size_t i = 0; i < n; ++i)
        out[i] = base[i] + dt * add[i];
}
