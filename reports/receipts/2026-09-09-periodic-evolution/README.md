# Periodic evolution providers — independent source audit

The modules listed in `verification.json` passed the project single-file compiler
on 2026-09-09. Each exact source copy appended the diagnostic commands retained
in its `.audit.lean.txt` file; the production proof terms were unchanged. The
verification JSON binds each result to its current source SHA-256. Two compiler
processes ran at most concurrently. Exact dependency modules were materialized
before auditing consumers; no umbrella build was used.

All raw transitive axiom lists in the accompanying `.txt` outputs contain only
`propext`, `Classical.choice`, and `Quot.sound`. `PeriodicGalileanReduction`
also received fresh LSP diagnostics with no errors or warnings.

Read the printed theorem type together with its axiom list. The native energy
identity assumes a classical solution. Pressure recovery assumes the projected
mode equation. The Dini estimate assumes the displayed integrability. The
interior modulus derives terminal-window Dini control from actual bounded mild
dynamics, but its constants depend on local time and radius. These are proved
providers, not unconditional proofs of B.

The exact initial reconstruction theorem has no reconstruction premise:
`nativeInitialReconstruction u₀ hu₀ = u₀` for every native `PeriodicInitialDatum`.
The moving-frame theorem transports all fields of the actual native periodic
classical contract, including the one-sided initial-time equation. Neither
constructs arbitrary-data global evolution.

See [the result map](../../../docs/RESULT_MAP.md) for original consumers,
remaining quantified inputs and the distinction between periodic and whole-space
regularity. Further active-lane files are not included in this receipt.

The full positive-time module now consumes the local Dini window and frozen-source estimate, proving actual raw mild half-generator membership with explicit local bounds. Physical identification still requires the phase/scaling decoder described in the result map. This audit does not discharge that decoder or the global bound.
