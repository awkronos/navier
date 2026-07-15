# Twelve-lane scientific-frontier attack

Starting point: `dbb8e6111684d276c60dad1d630ce07d56b0bc90` on
`codex/navier-six-lane-20260714`.

This campaign attacks every producer class in the canonical registry.  Its
global status is `SCIENTIFIC_FRONTIER`: neither an official positive endpoint
nor an official breakdown endpoint has an inhabitant.  A compiled surface,
conditional consumer, experiment, or representation bridge is not an endpoint
proof.

The runtime permits three workers plus the integrating agent.  The twelve
logical lanes therefore execute in four fold-and-refill waves.  Each lane must
return one of:

- a checked nontrivial Lean theorem with an allowed raw axiom audit;
- a checked counterexample or exact replayable falsification witness; or
- a strictly smaller reference-grounded residual with an exact declaration
  signature and consumer.

## Lane matrix

| Lane | Pattern family | Canonical obligations | Required artifact | Residual guarded against |
|---|---|---|---|---|
| L01 | representation transport | `semantics.encoding_bridges`, `semantics.exact_a_surface` | A/B datum, norm, smoothness, PDE, energy, or periodic bridge | treating the current Lean encoding as definitionally identical to Fefferman's coordinates |
| L02 | representation transport | `breakdown.c_encoding_bridges`, `breakdown.exact_c_surface` | C/D force, derivative, point-norm, PDE, energy, or quotient bridge | importing periodic semantics into C or weakening force admissibility |
| L03 | data contract | `scaling.algebraic_critical_line` | faithful `MemLp`/norm and mixed-norm infrastructure with genuine measure semantics | raw integrals that silently become zero on nonintegrable functions |
| L04 | payload realization | `local.mild_solution` | heat/Leray/Duhamel infrastructure and a datum-dependent contraction leaf | assuming local existence or using the wrong projected operator |
| L05 | bridge contract | `local.continuation_alternative` | restriction, restart-compatible uniqueness, maximal gluing, or critical blowup alternative | assuming global smoothness in a continuation proof |
| L06 | kernel certificate | `energy.smooth_identity` | compact-support pressure/convection cancellation and a justified decay limit | discarding a boundary, pressure, or integrability term |
| L07 | data contract + bridge | `energy.global_weak_solution`, `epsilon.local_regular_criterion` | weak/suitable solution, local energy, pressure, and cylinder interface | calling a distributional solution suitable without the local energy inequality |
| L08 | bridge contract | `critical.global_regularity_bridge` | conditional endpoint regularity theorem with exact solution and pressure hypotheses | hiding the unconditional critical bound inside the conditional theorem |
| L09 | decomposition tree + payload | `compact.profile_decomposition`, `compact.rigidity_exclusion` | orthogonality/remainder leaf or a precise ancient-profile rigidity statement | an untracked translation, scale, or frequency defect |
| L10 | bridge contract + payload | `vorticity.alignment_criterion`, `vorticity.unconditional_depletion` | curl/Biot--Savart/direction infrastructure and one checked stretching estimate | defining direction at zero vorticity or dropping nonlocal recovery |
| L11 | falsification ledger + payload | `frequency.cascade_exclusion`, `critical.unconditional_bound` | complete generated convolution network, exact shell balance, and predeclared collective weight | promoting one selected output or a finite table to a PDE shell estimate |
| L12 | payload realization + verifier interface | `breakdown.forced_c_payload`, `breakdown.zero_force_blowup_payload`, `breakdown.any_exact_realization` | an admissible partial solution plus agreement and blowup, or a checked obstruction that lowers the construction target | averaged operators, weak nonuniqueness, rough force, or consumer-only witnesses |

## Consumer graph

The positive endpoint requires all of the following layers:

1. official representation bridges;
2. a local solution with restart-compatible uniqueness;
3. a conditional continuation theorem;
4. at least one unconditional analytic producer;
5. the smooth energy clause and final viscosity-one composition.

The critical route must keep `critical.unconditional_bound` independent from
`critical.global_regularity_bridge`.  A separate `ALL` composition joins the
payload and conditional theorem before `regularity.any_positive_route`.

The negative endpoint requires:

1. exact force/datum representation bridges;
2. an admissible viscosity-one datum and force;
3. an exact classical solution on a genuine half-open interval;
4. local uniqueness or agreement with every official global pair;
5. point-norm blowup or another exact nonextension mechanism;
6. the already checked conditional nonextension consumer.

## Verification gates

- Lean LSP diagnostics and exact declaration signatures are the preflight
  evidence for each new file.
- A targeted `lake env lean <file>` is required before folding a Lean file.
- Public lower-theorem claims require raw `#print axioms` contained in
  `{propext, Classical.choice, Quot.sound}`, with `native_decide` explicitly
  identified if used.
- Experiments retain `closes_clay_endpoint=false` and never provide realization
  evidence.
- One serialized aggregate verifier runs only after all writers have folded.
- `StatementA`, `StatementB`, `StatementC`, or `StatementD` may be called proved
  only if an actual native inhabitant passes the same axiom audit.

## Current verifier caveat

The Kimina configuration file contains a `navier` project entry, but the live
Kimina server's project map did not expose it at campaign start.  Local Lean
LSP remains available.  This is recorded as stale live verifier state; it is
not permission to restart a service or modify shared verifier infrastructure.
