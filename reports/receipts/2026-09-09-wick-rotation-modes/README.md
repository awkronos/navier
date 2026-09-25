# Wick rotation modes receipt

- Baseline HEAD: `36c5955819dd382773e7cde33df319db04add007`
- Source: `Navier/Analysis/WickRotationModes.lean`
- Source SHA-256: `70f249398876a88355353e5b6f5dff2813d465aa6483ad0c805421e1dc830d76`
- Source compile: `timeout 1800 lake env lean Navier/Analysis/WickRotationModes.lean`, exit 0.
- CLI LSP diagnostics: `[]`.
- Same-source audit: `timeout 1800 lake env lean /tmp/WickRotationModes.audit.lean`, exit 0.
- Every audited public declaration has exactly `[propext, Classical.choice, Quot.sound]`.

The exact entire multiplier `exp(-a z)` restricts to the repository heat multiplier at `a = ν |k|²`, has real-time generator `-a`, and has Wick-rotated generator `-i a`. Positive real time strictly damps every nonzero lattice mode at positive viscosity. Imaginary time has norm one, and cannot satisfy any positive exponential damping estimate.

Scope: one linear Fourier multiplier. No theorem identifies the full nonlinear real Navier--Stokes flow with a quantum or Gross--Pitaevskii flow; winding and vortex regularity require separate carriers and dynamics.
