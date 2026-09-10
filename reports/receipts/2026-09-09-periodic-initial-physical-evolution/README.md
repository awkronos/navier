# Periodic initial physical evolution receipt

- Baseline HEAD: `358324ee16a63a7a2f8403f34ab4188bf972f0ac`
- Source: `Navier/Analysis/PeriodicInitialPhysicalEvolution.lean`
- Source SHA-256: `77c8684b1ddaab3a1764e9adc69d6d719c6a0fe3ca9ae97404f92cc65818f8cf`
- Exact imported polynomial-moment object SHA-256: `2b1a15c1e4755f200f254b76d71092165a46c96f1b0c0d3d734bba11abd6e053`
- Source compile: `timeout 1800 lake env lean Navier/Analysis/PeriodicInitialPhysicalEvolution.lean`, exit 0; see `source-compile.log`.
- Same-source audit: `timeout 1800 lake env lean /tmp/PeriodicInitialPhysicalEvolution.audit.lean`, exit 0; see `raw-axioms.log`.
- Every audited public declaration has exactly `[propext, Classical.choice, Quot.sound]`.
- CLI LSP could not open the isolated snapshot because the canonical polynomial-moment dependency source was introduced after the worktree baseline; it refused to use the available canonical object in no-build mode. This is recorded in `lsp-diag.log`; the project single-file compiler and same-source audit both succeeded.

The endpoint consumes `PhysicalLocalEvolution.exists_physical_local_evolution` for the exact raw initializer `-2πi · nativeInitialCarrier`. It retains the actual local bound, positive-time mode derivative, summability, normalized pressure equation, exact reconstruction at time zero, divergence freedom, anti-Hermitian reality, and every natural-order initial polynomial moment.

Residual: this is local existence plus smooth initial extraction. A horizon-uniform critical estimate/global continuation is still required for periodic global regularity.
