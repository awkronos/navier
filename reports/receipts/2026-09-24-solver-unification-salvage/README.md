# Solver-lane salvage banking (W19 fold, 2026-09-24)

Unique payloads of `solver-rsi/navier-spectral-smoke-algorithm`,
`salvage/navier-wt-20260910-1`, `-2`, `-3` materialized here before remote-ref
pruning. The Python performance work (runtime FFT backend ladder
pyFFTW > scipy.fft > numpy.fft, redundant forcing-projection skip) landed in
the canonical unified solver home `~/reality/solvers/navier/navier_spectral_core.py`
(Tim directive 2026-09-01; `scripts/` in this repository are re-export shims).
`.txt` suffixes keep the banking out of the Lean build surface; bytes are
unmodified from the branch blobs (git show).
