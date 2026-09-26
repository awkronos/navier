# Bridge obligations matrix — NSQM-0926 lane R-B (2026-09-26)

Machine-checked companion to `docs/MADELUNG_CORRESPONDENCE.md:121-127`, `docs/OPEN_FRONTIER_MAP.md:39`, `docs/RESULT_MAP.md:348-359`.

Every compiler-backed cell names a declaration probed by `proof-loop.py census` (runtime collectAxioms over the loaded aggregate) at navier head `2fe9a639483f` on MacBook (/tmp/nsqm-rb); raw receipt `/tmp/rb_navier_census.json`, digest `/tmp/rb_navier_census_receipt.json`.

Status vocabulary: `theorem | counterexample | open | unformalized`. An unmeasured cell renders as `unformalized` (or `unknown` for reality cells pending the Studio census), never as a verdict.


| obligation | hopf-cole | wick | madelung | warp |
|---|---|---|---|---|
| PDE | unformalized (no surface) | open — `module boundary` | open — `docs/MADELUNG_CORRESPONDENCE.md` | open — `grails/Warp/Shift.lean warpShift_staticDivergence, warpShiftEvol` |
| forcing | unformalized (no surface) | unformalized (no surface) | open — `Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candida` | unformalized (no surface) |
| energy class | unformalized (no surface) | counterexample — `Navier.Analysis.WickRotationModes.nonzero_lattice_mode_strictly_` | open — `partial structure` | unformalized (no surface) |
| phase topology | unformalized (no surface) | unformalized (no surface) | counterexample — `Navier.Analysis.MadelungDecoderCurlObstruction.no_scalar_madelun` | unformalized (no surface) |
| zeros | unformalized (no surface) | unformalized (no surface) | counterexample — `no_scalar_madelung_initial_lift_of_rotational_data` | unformalized (no surface) |

## Notes per non-unformalized cell

- **wick × PDE** — open. Linear one-mode multiplier only; no PDE transport theorem exists on this bridge. (probe host `macbook`, ts 2026-09-26T08:45:53). Backing: module boundary: Navier/Analysis/WickRotationModes.lean header ('does not identify the nonlinear real Navier--Stokes equation with a quantum or Gross-Pitaevskii evolution')
- **wick × energy class** — counterexample. Scoped: strict parabolic damping is NOT retained by the Wick continuation at the linear multiplier level (unit modulus on imaginary time). Not a nonlinear-energy counterexample; carrier bound stated in the module header. (probe host `macbook`, ts 2026-09-26T08:45:53). Backing: Navier.Analysis.WickRotationModes.nonzero_lattice_mode_strictly_damped_but_wick_mode_not (strict; census 15/15)
- **madelung × PDE** — open. Source result agrees with doc. (probe host `macbook`, ts 2026-09-26T08:45:53). Backing: docs/MADELUNG_CORRESPONDENCE.md:125-128 (obligation moved to WholeSpaceScaledCutoff family WholeSpaceSolenoidalHeatApproximation/ConvectionLimit/FullViscousLimit); no lift-side decl discharges it
- **madelung × forcing** — open.  (probe host `macbook`, ts 2026-09-26T08:45:53). Backing: Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_madelung_amplitude_or_derivative_degenerates enters via the forced dichotomy; forcing obligation itself unproven for the lift (docs MADELUNG_CORRESPONDENCE.md:125)
- **madelung × energy class** — open. First transport/energy-identity structure built (module header cites docs requirement); does not yet discharge the NS energy-class obligation. (probe host `macbook`, ts 2026-09-26T08:45:53). Backing: partial structure: Navier.Analysis.MadelungTransportIdentity.psiFamily_transport_excludes_amplitude_floor, uniformDensity_transport_rigidity, cpsi_transport_along_flow (all strict, census 43/43)
- **madelung × phase topology** — counterexample. Scalar route transports irrotational data only. (probe host `macbook`, ts 2026-09-26T08:45:53). Backing: Navier.Analysis.MadelungDecoderCurlObstruction.no_scalar_madelung_initial_lift_of_rotational_data (datum rotationalDatum : SchwartzVelocity; strict, census 35/35) + QuantumVortexWinding.vortex_phase_circulation_quantized, no_differentiable_periodic_phaseLift_of_nonzero (strict, 30/30)
- **madelung × zeros** — counterexample.  (probe host `macbook`, ts 2026-09-26T08:45:53). Backing: no_scalar_madelung_initial_lift_of_rotational_data (discharges {phase topology, zeros} jointly per docs/MADELUNG_CORRESPONDENCE.md:121-122) + QuantumVortexRegularity.unitVortex_velocity_unbounded_at_core, smooth_wavefunction_does_not_bound_decoded_velocity (strict, 48/48)
- **warp × PDE** — open. Zero-expansion (Natario) class; NS evolution not claimed. Grails decls NOT axiom-probed this lane (no census receipt) - see residual. (probe host `macbook`, ts 2026-09-26T08:45:53). Backing: grails/Warp/Shift.lean warpShift_staticDivergence, warpShiftEvol_incompressible, warpShift_convection_zero (incompressible slice + rigid self-advection only; no momentum-equation theorem)

## Doc cross-check (source is authority; prose repair owned by R-A)

- `MADELUNG_CORRESPONDENCE.md:121-127` — AGREES with source: decl exists, joint {phase topology, zeros} discharge claim matches statement form (psi 0 = 0 excluded); 'All three public results are strict' confirmed (foundational_only all, 0 sorry).
- `OPEN_FRONTIER_MAP.md:39` — AGREES: 'FALSIFIED (kernel, decoder level)' row names the same decl and the same obligation split.
- `RESULT_MAP.md:348-359` — AGREES: 'on the crown SchwartzVelocity carrier and under strict axioms' verified - rotationalDatum : SchwartzVelocity (MadelungDecoderCurlObstruction.lean:199); census strict 35/35.

## Navier census receipts — 9 bridge modules, all strict

| module | decls | strict | sorry-tainted | native-tainted | crown-reachable |
|---|---|---|---|---|---|
| Analysis.BKMForcedBreakdownNecessity | 14 | 14 | 0 | 0 | 0 |
| Analysis.ConstructedFiniteTimeObstruction | 22 | 22 | 0 | 0 | 0 |
| Analysis.MadelungDecoderCurlObstruction | 35 | 35 | 0 | 0 | 0 |
| Analysis.MadelungDegeneracySharpness | 41 | 41 | 0 | 0 | 0 |
| Analysis.MadelungTransportIdentity | 43 | 43 | 0 | 0 | 0 |
| Analysis.QuantumVortexRegularity | 48 | 48 | 0 | 0 | 0 |
| Analysis.QuantumVortexWinding | 30 | 30 | 0 | 0 | 0 |
| Analysis.WickRotationModes | 15 | 15 | 0 | 0 | 0 |
| Breakdown.DeadlineParameterizedWholeSpaceBreakdown | 37 | 37 | 0 | 0 | 0 |

Total 285 decls, 0 sorry-tainted, 0 native-tainted, transitive axioms ⊂ `{propext, Classical.choice, Quot.sound}` for every declaration (per-decl `foundational_only` flag in `/tmp/rb_navier_census.json`).

## Reality modules (Studio census in flight at head ba5458f1)

`Reality.Physics.{MadelungHolonomy 9/9, MadelungEuclideanVelocityBound 34/34,
ResonanceCorrespondence 524/524 strict}`, `Reality.Cosmology.{SingularityBounce
44/44, NavierBlowupIntegration 10/10 strict}` — 621 decls, 0 sorry-tainted,
0 native-tainted (Studio census at head 8723f545; the umbrella `Reality.olean`
was NOT materialized before this lane — 13302-job build run under
`flock /tmp/nsqm-lean-slot.lock` — which is itself why the carried proof-report
row could never certify reality). Receipt
`/tmp/rb_reality_census_receipt.json` (Studio). MadelungHolonomy's gauge side imports
`Navier.Analysis.QuantumVortexWinding` (census: 30/30 strict on MacBook), so the
phase-topology counterexample is compiler-backed on the navier side regardless.

## Mission 3 — open-math routing failure: root cause (measured this lane)

`/tmp/open_math.json` (MacBook, 08:13) = pull of Studio's sidecar via
`com.kagami.proof-report-pull` (`proof-report-pull.py`; the MacBook checkout's
`native_declaration_inventory.py` last change Sep 18 cannot emit the reason
string — emitter is Studio's Sep 25 build). Two independent causes, both
measured:

1. **Sweep budget kills the heavy-row force-builds (navier/reality/grails
   specifically).** `/tmp/proof-report-refresh.log` (Studio): every 39 unknown
   row carries `declaration_inventory.partial_reasons =
   [native_inventory:compiler_exit=None, native_inventory:markers_absent]` —
   carried facts, no compiler run this sweep. Rows: navier 66.5 h @ b51e44f
   (current 2fe9a639), reality 204 h @ 16eca58 (current ba5458f1), grails 23 h.
   The sweep logs `ERROR: proof-report sweep exceeded 21900s runtime budget` →
   `rc=124` + `reaped_process_groups: 2`, and a `STARVATION OVERRIDE` shows the
   single active build slot occupied by a reimann aggregate while
   `reporter_build_slots=2`. `force-building through decline path` appears 45×
   in the log: stale-facts escape (threshold 47400 s) re-arms each pass, the
   14400 s reality / 3600 s default budgets never finish inside the remaining
   sweep window, the reaper kills them, rows never converge.
2. **The 2026-09-25 compact-projection gate UNKNOWNs 30 of 39 projects**
   (`native_declaration_inventory.py:1172 _compact_consumer_projection_reason`
   on Studio, mirrored in `~/Projects/kagami/.worktrees/*-0925` on MacBook):
   when a non-compacted declaration list contains direct consumers of an
   open/unknown obligation, the open-math reverse-consumer index cannot type the
   projection, and `load_overflow_declarations` returns the advisory reason →
   `open_math.build` keeps the tasklist row UNKNOWN even though the kernel plane
   certifies (this is the documented two-valued contract, dario-floors w21
   fix). 22 of 39 MacBook rows are unknown on this reason ALONE.

**Minimal fix (for root; this lane ran no producer)**: (a) let the stale heavy
rows finish — bound the sweep so the force-build path (reality 14400 s) fits
remaining `max_sweep_s`, or give the stale-facts escape its own reserved build
slot; re-provision via the canonical producer on Studio. (b) The projection
gate is producer-intended; if targets must flow for fully-certified projects,
the fix lives in `_compact_consumer_projection_reason` resolving consumers via
`load_overflow_record` from the overflow sidecar before declaring untypability.
Absent either, `status=partial, targets=[]` is the *correct* rendering of a
stale-and-gated report plane — not a consumer bug.

## Coverage

20 cells. 11 cells backed by named declarations or module headers (9 via
census-strict navier decls, 1 via grails source read without an axiom receipt,
1 doc-cited); 6 unformalized with recorded absence greps (hopf-cole probed
across navier/reality/grails — zero Cole–Hopf surface); 0 theorem cells.

