# W20 NS-1 notes — explicit nondegenerate control, BKM budget, horizon-free restart

Lane NS-1, wave 20. Module: `Navier/Analysis/HorizonFreeBudgetRestart.lean`
(imported from `Navier.lean` between `WienerRestartLeaf` and `WienerHigherEnergy`).
Everything below compiles with zero `sorry` and raw transitive axioms
`[propext, Classical.choice, Quot.sound]` (verified by the footer probes;
fresh compile 2026-09-25 in the warm lane worktree).

## Item 1 — the explicit control `N`

`h3EnvelopeBudget v := if (∃ a, Rep v a) then ⨆ (a) (_ : Rep v a), ⨆ i, h3F (a·i) else ⊤`
and `h3EnvelopeControl T u := ⨆ t ∈ Ico 0 T, h3EnvelopeBudget (u t)`.
This is a genuine control on the repo's carrier: it dominates the H³-type
Wiener seminorm of *every* `Rep` representer of every time-slice
(`h3F_component_le_budget`), is equivalent to that domination
(`h3EnvelopeBudget_le_iff`), and any `< ⊤` value forces a representer to
exist (`exists_rep_of_budget_lt_top`). No degenerate substitution: `⊤`
outside the representer class is the maximal honest value.

## Item 2 — BKM budget on each `SolvesBefore` member

`wienerH3Apriori_h3EnvelopeControl : WienerH3Apriori h3EnvelopeControl` —
the repo's per-member budget predicate (ν, u₀, M, T, u, p, `SolvesBefore ν T u p`,
`RegularOnCompacts`, `N T u ≤ M ⊢ ∀ τ < T, ∀ a, Rep (u τ) a → ∀ i,
h3F (a·i) ≤ ofReal K`) holds UNCONDITIONALLY with budget `K = M.toReal`.
(For the energy route, `budgetPropagationDatumFree_preterminalEnergy` is the
analogous datum-free propagation for `preterminalEnergyControl`.)

## Item 3 — `h = h(ν, M)`, horizon-free

- `HorizonIndependentRestartR N` — F-025's strengthening of the repo's
  `DatumHorizonIndependentRestartR`: `∀ ν ∀ M ∃ h` *before* the datum,
  with the full R-conclusion (`SolvesFrom` + `RegularOnCompactsFrom` +
  normalization) on `[T₀, T+h)`.
- `horizonIndependentRestartR_h3EnvelopeControl : HorizonIndependentRestartR
  h3EnvelopeControl` — PROVED from the branch engines (`rep_all`, `piece_at`,
  `strip_of_piece`): `h = 4π²ν / (3·10⁶·(CW.toReal·M.toReal + 1))`, a term
  that depends only on `(ν, M)`; the horizon `T` never enters `h`.
  `datumRestartR_of_horizonIndependentRestartR` weakens it to the repo's
  post-datum R-order, feeding `wholeSpaceGlobalRegularity_of_R_restart_apriori`.
- `restart_of_budget` — the mission's named reduction theorem for the PLAIN
  `Navier.Analysis.RestartPaste.HorizonIndependentRestart` (pre-datum form,
  no `RegularOnCompacts` fields): budget local existence + pre-datum budget
  propagation + class restart uniqueness (instantiated at `trivialClass`,
  class premises `True`) compose to the restart, step `h/2`,
  `T₀ = max 0 (T − h/2)`. Pressure agreement on the CLOSED window `[T₀, T)`
  is new here: interior by `pressure_eq_of_velocity_eq_interior`, at `T₀` by
  `pressure_eq_at_left` (both pressures are the limit along `𝓝[>] T₀` of the
  same evaluation map into their strips, `tendsto_nhds_unique`).

### Exact remaining estimates (named, per the attack plan)

1. Plain-order energy route: `BudgetLocalExistenceIn trivialClass
   sliceEnergyBudget` (a `SolvesFrom` local piece with a kinetic-energy
   budget — the classical-energy local-existence estimate on this carrier)
   and `RestartUniquenessIn trivialClass` (weak–strong uniqueness on the
   trivial class). `wholeSpaceGlobalRegularity_of_energyBudgetRestart` is
   the crown consumer awaiting them; `localClassicalExistence`
   (WienerLocalClassical) is already unconditional.
2. Envelope crown route: `APrioriIn RegularOnCompacts h3EnvelopeControl` —
   feeding `crown_from_envelopeApriori`. And a `< ⊤` exhibit for
   `h3EnvelopeBudget` needs a.e.-uniqueness of the Wiener profile under the
   repo's pointwise `fourierInv` (recorded in the module header; precedent
   `bkmVorticityControl_nondegenerate`).

## Non-degeneracy exhibits for the energy control (both poles)

- `exists_preterminalEnergyControl_pos` — `0 < preterminalEnergyControl 1 u`
  for the constant slice of the shift bump `shiftSchwartz 0` (compact
  support + nonzero → positive kinetic energy, peer idiom from
  `shiftSchwartz_self_pos`).
- `exists_preterminalEnergyControl_lt_top` — `preterminalEnergyControl 1 0 = 0
  < ⊤` (zero evolution): `N` is neither identically 0 nor identically ⊤.

## Parallel item — physical-carrier transport: assessed, not landed (RED-by-blocker)

The four pieces each already have a transported layer on main:
smoothing moments (`ContinuousLeiLinPhysicalSmoothing`), frequency
derivative (`ContinuousLeiLinFrequencyODE` consumed at the datum via
`ContinuousLeiLinODEDominationSupply.hasDerivAt_physicalVelocity_continuousMildImage_fourierDatum`),
pressure (`ContinuousLeiLinPressurePhysical` + transported budgets in
`ContinuousLeiLinMildFixedPointPressure`), admissible-ball integrability
(`ContinuousLeiLinPhysicalIntegrability.integrable_of_integrable_Xm1_X1`
→ `physicalCoord_im_eq_zero_of_Xm1_X1`).
The remaining hop at each named consumer is gated by exactly one of three
premises that the estate names as unproduced: the 12-field
`MildAssemblyLeaves` record (produced nowhere for general box elements;
nonvacuous only at the zero datum —
`ContinuousLeiLinMildFixedPointPressure.existsUnique_mildFixedPoint_zeroBox`),
the degree-2 recent moment ("beyond the box slots",
`ContinuousLeiLinODEDominationSupply` producer table), and the pointwise-in-ξ
`hsrc` envelope ("measured impossibility from moment estimates", same table —
NOT re-attacked here per that file's own directive). No hop among the four
is cheap; the transport needs its own lane with the `ActualLinkedBox` /
`RepresentativeGoodAt` carrier tutorial, not an opportunistic slice.

## What this lane does NOT claim

Global regularity does not follow: both crown routes above keep their named
premise. The endpoint stays the conditional composition
(`wholeSpaceGlobalRegularity_of_local_horizonIndependentEnergyRestart`,
`wholeSpaceGlobalRegularity_of_R_restart_apriori`); this output is the
producer side of the restart premise.
