"""Truth-check for the dyadic cell-oscillation summation inequality used by
`Navier.Analysis.LerayWeak.sum_cellError_le_modulus_of_memL2`.

Checks, in d = 1 on an off-grid step function (so the cell error is genuinely
nonzero), at four dyadic scales and two grid resolutions:

  (1)  sum_j int_{C_j} |f - avg_{C_j} f|^2  <=  h^{-d} int_{|k|<=h} ||tau_k f - f||_2^2 dk
  (2)  h^{-d} int_{|k|<=h} ||tau_k f - f||_2^2 dk  <=  2^d * sup_{|k|<=h} ||tau_k f - f||_2^2

(2) is the `volume.real (closedBall 0 h) / h^d = 2^d` step, whose h-independence
is what lets h -> 0 drive the cell error to zero uniformly over an
equicontinuous family.  Run: python3 experiments/riesz_kolmogorov_cell_sum_toy.py
"""

import numpy as np


def f(x):
    return np.where((x >= 0.07) & (x < 0.43), 1.0,
                    np.where((x >= 0.43) & (x < 0.91), -1.0, 0.0))


def run(exp_n):
    L, N = 4.0, 2 ** exp_n
    xs = -2.0 + L * np.arange(N) / N
    dx = L / N

    def cell_error(h):
        idx = np.floor(xs / h).astype(np.int64)
        tot = 0.0
        for j in np.unique(idx):
            v = f(xs[idx == j])
            tot += ((v - v.mean()) ** 2).sum() * dx
        return tot

    def modint(h, nk=801):
        ks = np.linspace(-h, h, nk)
        out = np.array([((f(xs + k) - f(xs)) ** 2).sum() * dx for k in ks])
        return np.trapezoid(out, ks), out.max()

    print(f"grid 2^{exp_n}")
    for h in [0.25, 0.125, 0.0625, 0.03125]:
        lhs = cell_error(h)
        I, M = modint(h)
        ok1 = lhs <= I / h + 1e-9
        ok2 = I / h <= 2 * M + 1e-9
        print(f"  h={h:8.5f} LHS={lhs:.6f} h^-1*int={I / h:.6f} 2*Mmod={2 * M:.6f} "
              f"(1)={ok1} (2)={ok2}")
        assert ok1 and ok2


if __name__ == "__main__":
    run(19)
    run(22)
