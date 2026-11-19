# Critical mild mean-drift removal receipt

- Base commit: `1bd8c4f63d89045d783563b279ea4ee99d59a43b`
- Source: `Navier/Analysis/CriticalMildMeanDriftRemoval.lean`
- SHA-256: `cbd082de5f1a75317361c55e8ac01f4d28df56a9635544ad59e79219f95e68ec`
- Source compiler: `lake env lean Navier/Analysis/CriticalMildMeanDriftRemoval.lean`, exit 0.
- LSP diagnostics: `[]`.
- Same-source axiom probe: exit 0; every audited endpoint uses exactly
  `propext`, `Classical.choice`, and `Quot.sound`.

The source proves the period-one phase convention, its exact isometry on the
completed weighted carrier, the faithful raw normalization
`A_k = -2π i û_k`, literal summand-to-`tsum` phase covariance, the unique
constant-mean cross term, and its exact cancellation with the phase derivative.
The mean-removed carrier preserves `amplitudeOffZero`, its squared sum, and
`heatHalfGeneratorMoment`, so the existing nonzero-mode terminal estimates do
not charge the arbitrary constant mean.

Scientific residual: this module proves the coefficientwise and semigroup
algebra needed for the change of frame.  A downstream module must still carry
the time-dependent phase through the complete Bochner/Volterra fixed-point
identity before claiming that an entire `CriticalMildPathBall` is transported
to another mild solution.  Arbitrary-data global control of the remaining
nonzero modes is also open.

## Duplicate-group pointer (added 2026-11-19)

`source-snapshot.lean.txt` in this directory is byte-identical (blob
`0415973b968e5d0540ac540ff8461d352128c32d`) to the live module
`Navier/Analysis/CriticalMildMeanDriftRemoval.lean` at current main. That
identity is a dispositioned `duplicate_group` row, not redundancy: this
snapshot is the frozen capture pinned by the SHA-256 above, while the live
module is the carrier of all later edits. See
`reports/receipts/DUPLICATE_GROUP_MEAN_DRIFT_SNAPSHOT_2026-11-19.md` for the
measured member table and the refused collapse alternatives. (Lane
`RST-NAVCMD-1116`, RSI generation `93fa7be454194153a23d95d38f5a69cf`.)
