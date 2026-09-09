# Force and regularity proof receipt

This receipt records the source-fresh check of the sharper unit-viscosity,
deadline-one comparison consequences and the unchanged original forced
breakdown consumer. It makes no unforced Navier–Stokes claim.

## Sources

```text
9f87a6ab36e9fe62a86af24c89d957aa86703ff31f4d894a99c89663b2e3e847  Navier/Analysis/ConstructedFiniteTimeObstruction.lean
4405a3be79cf234ef6f1ada20baabaa7800e55ef0955ab9ce256904b432b40b4  docs/EXACT_FORCE_AND_REGULARITY.md
523efc908f78916425f5b184f81c2ea7de2a6b151b7fc061229562906615a9d7  Navier/Breakdown/ConstructedBreakdown.lean
```

## Commands

All commands ran from the repository root on 2026-09-09.

```text
lake env lean Navier/Analysis/ConstructedFiniteTimeObstruction.lean
exit 0

lake build Navier.Analysis.ConstructedFiniteTimeObstruction
exit 0; target built successfully

lake env lean Navier/Breakdown/ConstructedBreakdown.lean
exit 0

cp reports/receipts/2026-09-09-force-regularity/Audit.lean.txt /tmp/navier-force-regularity-audit.lean
lake env lean /tmp/navier-force-regularity-audit.lean
exit 0

git diff --check -- Navier/Analysis/ConstructedFiniteTimeObstruction.lean docs/EXACT_FORCE_AND_REGULARITY.md
exit 0
```

`source-compile.log` contains the source-fresh theorem types and raw axiom
prints. `consumer-audit.log` contains the exact original-consumer and new
endpoint types plus their raw axiom prints. Every printed declaration depends
on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The new exact output covers:

- compact physical support of the selected force on `t ≥ 0`, with a finite
  future cutoff;
- transfer of `SpeedUnboundedAtOne` to every presingular-smooth, same-force,
  zero-data competitor with finite energy separately on each `[0,T]`, `T<1`;
- existence of `0<t<1` and `x` where the selected force is nonzero;
- exclusion of a competitor in that local class which is also continuous
  through `t=1` on the selected velocity's compact support.

The original checked consumer remains
`Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown :
Navier.ProblemStatements.WholeSpaceBreakdown`.
