# Final constructed-C verification receipt

This receipt binds the final research-polish source snapshot to its compiled
Lean objects and raw public theorem audits. The snapshot is based on Git
revision `e7aba55ff119deb7de47819ca4b33e4d1c7b5d5c`; the changed source bytes are
identified independently in [`module-manifest.json`](module-manifest.json).

## Source rebuild

```text
python3 -u scripts/verify_construction.py --jobs 8
exit_code=0
root=Navier.Breakdown.ConstructedBreakdown
local_closure=615
```

The first pass rebuilt all 615 local modules. After the final obstruction
corollary was added, the closing pass reported `fresh=613 rebuild=2`, rebuilt
`ConstructedFiniteTimeObstruction` and `ConstructedBreakdown`, and exited zero.
Every one of the 615 reusable receipts records a successful compiler exit and
the SHA-256 of its produced `.olean`; the verifier also checks source,
environment and transitive local dependency fingerprints before reuse.

[`full-rebuild.txt`](full-rebuild.txt) preserves the complete source-rebuild
output. [`verifier.txt`](verifier.txt) is the complete closing verifier output.
[`axioms.txt`](axioms.txt) is the verifier's raw exact-type, proof-term and
transitive-axiom audit for these eleven declarations:

1. `ConstructedBreakdown.wholeSpaceBreakdown`
2. `ConstructedForceExtension.constructedWholeSpaceBreakdownWithGloballySmoothForce`
3. `ForceRecursivePartials.forcedDataRapidDecay_bounds_successivePartials`
4. `ConstructedBreakdown.wholeSpaceBreakdown_with_successivePartials`
5. `ConstructedBreakdown.selectedFiniteEnergyCandidate`
6. `ForceCoordinateEquivalence.forcedDataRapidDecay_iff_successivePartials`
7. `ForceCoordinateEquivalence.periodicForcedDataRapidDecay_iff_successivePartials`
8. `ComparatorBridge.compact_candidate_unique_on_Icc`
9. `ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile`
10. `ConstructedFiniteTimeObstruction.selected_candidate_no_continuous_extension`
11. `ConstructedFiniteTimeObstruction.selected_candidate_excludes_locally_finite_energy_continuation`

Every declaration's raw transitive axiom list is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The independent selected-frontier source check

```text
lake env lean Navier/ConditionalAudit.lean
exit_code=0
```

is preserved verbatim in [`conditional-audit.txt`](conditional-audit.txt). It
includes the exact conditional inputs for unforced global regularity as well as
the completed forced construction.

The smaller faithful endpoint witness in the earlier baseline receipt was also
recompiled after the final imports changed; its exit-zero raw output is
preserved in [`baseline-audit-recheck.txt`](baseline-audit-recheck.txt).

## Verified boundary

The original proof-bearing consumer is still exactly:

```text
Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown :
  Navier.ProblemStatements.WholeSpaceBreakdown
```

The strengthened results show, on one selected witness, a globally smooth
force, uniform finite energy before time one, uniqueness against smooth
finite-energy competitors on every closed pre-singular slab, and no continuous
terminal extension on the fixed compact region occupied by the flow. The
strongest corollary lets a competitor's finite-energy bound depend on the slab
and deteriorate as its endpoint tends to one.

No declaration in this receipt proves
`Navier.ProblemStatements.WholeSpaceGlobalRegularity`. That unforced all-data
statement A remains open. The periodic alternative D also remains open here.
