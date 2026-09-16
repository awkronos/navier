# interval_cert — float64 rounding-envelope certificates

Lane NS5-SOLVER (2026-09-16). **OBSERVATION SURFACE, NOT PROOF**
(`docs/FALSIFICATION_LEDGER.md` F-012: numerics are observation-only; the
permitted successor is interval certificates, which this is).

| file | role |
| --- | --- |
| `float64_cert.py` | outward-rounded float64 interval arithmetic (1 ulp widening, `nextafter`-based) enclosing the periodic solver's energy-budget diagnostic score: defect `E + ∫D dt − E₀` and its relative form, with an optional caller-declared input radius for upstream (FFT/backend) uncertainty |
| `test_float64_cert.py` | enclosure verified two ways: mpmath exact re-evaluation (50 dps) of the same expression on the same float64 operands, and the fixed-order float64 evaluation itself; adversarial cancellation, non-finite refusal (`finite_certification` requires finite endpoints), and a different-order (`np.trapezoid`) caveat test |
| `energy_budget_demo.py` | live demo: Taylor–Green IFRK4 evolution through the `scripts/` unification shim into `~/reality/solvers/navier/navier_spectral_core.py` (canonical body), emitting a machine-readable certificate record |
| `conditioning_probe.py` | measured `exp` crossover thresholds for the mild multiplier `exp(ν‖ξ‖²t)` truncation — a falsifiable inequality proposed to the formal side |

Scope guard (module docstring): the envelope bounds round-off of the declared
expression in the fixed evaluation order; it does not enclose FFT internals
that produced the operands (declare an input radius for that), other summation
orders (needs a separate order-aware `gamma_n` bound — the test demonstrates
this distinction), or any continuum residual. The soundness argument is the
monotone-rounding induction in `float64_cert.py`.

Run: `python3 -m pytest solver/interval_cert/test_float64_cert.py -q` ·
`python3 solver/interval_cert/energy_budget_demo.py` ·
`python3 solver/interval_cert/conditioning_probe.py`

Note: placement is `navier/solver/` by dispatch fence; under the 2026-09-01
unification directive the natural long-term home is
`reality/solvers/navier/` with a shim — proposed in
`docs/NS5-SOLVER-FINDINGS.md`, not acted (single-writer/consolidation call
deferred to the root fold).
