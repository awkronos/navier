# Constructed alternative-C baseline audit

This receipt freezes the exact public result at Git revision
`e7aba55ff119deb7de47819ca4b33e4d1c7b5d5c` before subsequent research work.
It is a named-endpoint audit, not a project-wide proof census.

## Environment and fingerprints

- Compiler: `Lean 4.31.0`, commit
  `68218e876d2a38b1985b8590fff244a83c321783`, arm64 macOS release build.
- Root module: `Navier.Breakdown.ConstructedBreakdown`.
- Local source closure: 613 modules.
- Environment fingerprint:
  `1dc7a917a47a421e2b8ae3f40375f0e4cf196f4ea189a15b8e3bfd2d368c086c`.
- Root source SHA-256:
  `ce664913ff732d47004ed46669664b8065a67b031914f1998ba30797494b00c9`.
- Root dependency fingerprint:
  `5f65d687596593a9655958f2a9010d4f64af1c15c013f40d05edcffeed995c27`.

Direct dependency fingerprints:

| Module | Source SHA-256 | Transitive dependency fingerprint |
| --- | --- | --- |
| `NativeConstructionEndpoint` | `b6580620b13894411cab3f952cb9bb888edfd0c9be9a671bde007f6cf057faed` | `304249beae1ee0ea8050e75e069e655a809a21fe42f52f67b13589518491bed4` |
| `R3ActualCandidate` | `9f2ee0f2e1346f773ee491b2c0889ed9f65b539540d310679d27d5f04fb5f450` | `7971001bf4b9276293bd131e8346ddc8fef9131a1308646eeb89a062e7001b73` |
| `ForceRecursivePartials` | `84b723b6f40c910fd22d1683ab9d6a8223127b57f8e4d98d901383d62d22ac57` | `9335a9a688f609d859802b388a95fa037dfa90298fb4a878447b40182f1d9bd6` |
| `ConstructedForceExtension` | `bce09def7ca162d2bda791632d7fb669581c107010add66ba6772797207b0859` | `cdff6293e98d97db7e4a650b74da909f581b1be8fe09e534e9b10f298157acb3` |
| `SelectedCandidateEnergy` | `9ff80470aec544a93e7918dd360f968b94ba4b67727a424094384c4d3f732201` | `ae22116d7616dfb2f707b9e22bc428b26ce5ed88a92a56e4b4bbdb7cddc7faba` |

## Commands and results

```text
lake env lean Navier/Breakdown/ConstructedBreakdown.lean
exit_code=0

lake env lean Navier/ConditionalAudit.lean
exit_code=0
```

The second command printed the exact public types. The original consumer was:

```text
Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown :
  Navier.ProblemStatements.WholeSpaceBreakdown
```

The strengthened finite-energy endpoint was:

```text
Navier.Breakdown.ConstructedBreakdown.selectedFiniteEnergyCandidate :
  exists u p f,
    R3CompactCandidate.Properties u p f and
    ContDiff Real infinity f and
    UniformFiniteEnergy (Set.Ico 0 1) u
```

Raw transitive axiom output for the original C consumer, the globally smooth
force theorem, the successive-partials strengthening, and the selected
finite-energy candidate was exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The audit source is stored as text evidence outside the Lake module tree. The compiler checked it as `Audit.lean` before packaging. It contains the faithful carrier witness in [`Audit.lean.txt`](Audit.lean.txt):

```lean
example : Navier.ProblemStatements.WholeSpaceBreakdown :=
  Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown
```

No theorem in this receipt inhabits
`Navier.ProblemStatements.WholeSpaceGlobalRegularity`. The latter is the
unforced all-data statement A and remains a separate open endpoint.
