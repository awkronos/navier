"""STEP 0 for `exists_subseq_windowCauchy`: truth-check the dyadic-average route
to Riesz-Frechet-Kolmogorov BEFORE any Lean.

(J)  pointwise Jensen : ||avg_S f - c||^2 <= avg_S ||f(y) - c||^2
(C)  cell bound       : int_W |E_h f - f|^2 <= 2^d * sup_{|k|_inf <= h} ||tau_k f - f||^2
(B)  Bolzano-Weierstrass: E_h f lives in a finite-dim space, so bounded => precompact
(E)  end to end       : (C)+(B) => totally bounded => Cauchy subsequence
"""
import numpy as np
rng = np.random.default_rng(7)

print("== (J) pointwise Jensen, vector-valued, 20000 random trials ==")
worst = -1e9
for _ in range(20000):
    m = rng.integers(1, 12); d = rng.integers(1, 4)
    f = rng.normal(size=(m, d)) * rng.uniform(0.1, 5.0)
    c = rng.normal(size=d) * rng.uniform(0.1, 5.0)
    lhs = np.sum((f.mean(axis=0) - c)**2)
    rhs = np.mean(np.sum((f - c)**2, axis=1))
    worst = max(worst, lhs - rhs)
print(f"  max(lhs - rhs) = {worst:.3e}   (must be <= 0)  -> {'HOLDS' if worst <= 1e-12 else 'FAILS'}")

def cell_test(d, N, h_cells, trials=60):
    """|E_h f - f|^2 vs 2^d sup_{|k|_inf <= h} ||tau_k f - f||^2 on the torus grid."""
    worst_ratio = 0.0
    for _ in range(trials):
        shape = (N,) * d
        # rough random field: white noise + a smooth part, so the modulus is nontrivial
        f = rng.normal(size=shape) + 3*np.sin(2*np.pi*np.add.outer(*[np.arange(N)/N]*d)
                                              if d == 2 else 2*np.pi*np.arange(N)/N)
        b = N // h_cells                       # cells are b x b ... blocks, side h = b/N
        blocks = f.reshape(*sum([[h_cells, b] for _ in range(d)], []))
        axes = tuple(range(1, 2*d, 2))
        Ef = np.repeat(blocks.mean(axis=axes, keepdims=True), b, axis=1)
        if d == 2:
            Ef = np.repeat(Ef, b, axis=3)
        Ef = Ef.reshape(shape)
        lhs = np.mean((Ef - f)**2)
        sup = 0.0
        rng_k = range(-(b-1), b)
        for k0 in rng_k:
            if d == 1:
                sup = max(sup, np.mean((np.roll(f, -k0) - f)**2))
            else:
                for k1 in rng_k:
                    sup = max(sup, np.mean((np.roll(np.roll(f, -k0, 0), -k1, 1) - f)**2))
        worst_ratio = max(worst_ratio, lhs / max(sup, 1e-30))
    return worst_ratio

print("\n== (C) cell bound: ratio  int|E_h f - f|^2 / sup_{|k|_inf<=h} ||tau_k f - f||^2 ==")
for d, N, hc in ((1, 512, 32), (1, 512, 8), (2, 64, 16), (2, 64, 8)):
    r = cell_test(d, N, hc)
    print(f"  d={d}  N={N}  cells={hc}  worst ratio = {r:.4f}   bound 2^d = {2**d}"
          f"   -> {'HOLDS' if r <= 2**d else 'FAILS'}")

print("\n== (E) end to end: equicontinuous + bounded => Cauchy subsequence exists ==")
N = 2048; x = np.arange(N)/N
def modulus(fam, hs):
    return [max(np.mean((np.roll(f, -int(h*N)) - f)**2) for f in fam) for h in hs]
equi = [np.exp(-((x-0.5)**2)*20) * (1 + 0.3*np.sin(2*np.pi*x*(1+j/50))) for j in range(40)]
bad  = [np.exp(-((x-0.5)**2)*20) * np.sin(2*np.pi*x*2**j) for j in range(1, 9)]
hs = [1/8, 1/32, 1/128, 1/512]
print(f"  equicontinuous family: sup_m ||tau_h f_m - f_m||^2 at h={hs} -> "
      + ", ".join(f"{v:.2e}" for v in modulus(equi, hs)))
print(f"  oscillating  family  : sup_m ||tau_h f_m - f_m||^2 at h={hs} -> "
      + ", ".join(f"{v:.2e}" for v in modulus(bad, hs)))
def min_pair_dist(fam):
    return min(np.mean((fam[i]-fam[j])**2) for i in range(len(fam)) for j in range(i+1, len(fam)))
print(f"  min pairwise L2^2 distance: equicontinuous {min_pair_dist(equi):.3e}"
      f"  (small => Cauchy subseq), oscillating {min_pair_dist(bad):.3e}  (bounded away => none)")
