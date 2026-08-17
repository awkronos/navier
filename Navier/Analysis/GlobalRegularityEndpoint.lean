import Navier.Breakdown.MaximalNonextension
import Navier.Frontier

/-!
# A typed conditional inhabitant of the whole-space endpoint

Before this module the repository had **no** declaration whose conclusion is
`Navier.ProblemStatements.WholeSpaceGlobalRegularity`; the residual lived only
in prose and in the `Frontier.FrontierNode` planning enum.  This module gives
the endpoint a named conditional inhabitant, so that the residual is a *type*
and is diffable across waves.

`wholeSpaceGlobalRegularity_of_halfLineExistence_and_energyClause` is
**CONDITIONAL**, never closed.  It takes exactly two hypotheses:

* `HalfLineClassicalExistence` -- the `Frontier.globalContinuation` node.  For
  every `ν > 0` and every divergence-free Schwartz datum there is a
  velocity/pressure pair attaining the datum which, for **every** finite
  horizon `T > 0`, is smooth, incompressible and solves the equation on
  `[0,T) × ℝ³`.  This hypothesis carries the analytic weight of the problem;
  it is stated plainly rather than hidden behind a payload.
* `WholeSpaceEnergyClause` -- the `Frontier.wholeSpaceEnergyBridge` node.  Every
  globally smooth incompressible solution of the unforced equation has
  integrable kinetic-energy density and a uniform strict energy bound
  (Fefferman's clause (7)).

The metamathematical `Frontier` representation bridges
(`schwartzConventionBridge`, `halfSpaceSmoothnessBridge`,
`frechetCoordinatePDEBridge`) are not hypotheses of the Lean proposition, and
correctly do not appear here; the fourth remaining bridge,
`wholeSpaceEnergyBridge`, is the second hypothesis above.

## The three gates

**NON-CIRCULARITY.**  Neither hypothesis is the conclusion.
`WholeSpaceEnergyClause` is an implication whose hypothesis is a solution it
does not produce; it constructs nothing and is strictly weaker.
`HalfLineClassicalExistence` is stated honestly: it is the endpoint with the
two energy fields deleted and with joint smoothness demanded only on the
half-open regions `[0,T) × ℝ³` rather than on `[0,∞) × ℝ³`.  It is therefore
strictly weaker than the conclusion, but it is *not* a soft hypothesis -- it is
the hard analytic half of the problem, and this module claims no reduction of
its difficulty.  The mathematical content proved here is exactly the passage
from the half-open family to the closed half-space
(`contDiffOn_ici_of_forall_before`) plus the assembly.

**SATISFIABILITY.**  Both hypothesis shapes are checked at a genuine point of
their own quantifier range, against the repository's history of vacuity
defects.  `zero_is_solution_before` inhabits every clause of the body of
`HalfLineClassicalExistence` with the zero pair, and
`zero_satisfies_energyClause` inhabits the conclusion of
`WholeSpaceEnergyClause`, including the `Integrable` conjunct whose omission
elsewhere in this repository produced a vacuous energy bracket.  Neither
hypothesis is refutable by the pressure gauge freedom: no hypothesis here
asserts uniqueness of the pressure, which is only determined up to an additive
function of time and would have made an agreement-style hypothesis FALSE and
the endpoint vacuous.

**NON-VACUITY.**  Neither hypothesis follows from the ambient typeclasses:
`Space`, `VelocityEvolution` and `PressureEvolution` are plain function types
carrying no PDE content, and both hypotheses quantify over the Schwartz data of
the actual problem.

Scope: this is a conditional reduction of Fefferman statement A to two named
analytic residuals.  It is NOT a solution, NOT a global-regularity theorem, and
it does not shrink the frontier by itself.
-/

set_option autoImplicit false

open scoped ContDiff

namespace Navier.Analysis.GlobalRegularityEndpoint

open MeasureTheory Navier Navier.Breakdown

/-! ## The local-to-global smoothness passage -/

/-- **From every half-open horizon to the closed half-space.**

If `F` is `C^∞` on `[0,T) × ℝ³` for every `T > 0`, then it is `C^∞` on
`[0,∞) × ℝ³`.  Each point `(t,x)` with `t ≥ 0` lies in the relatively open
subset cut out by `s < t + 1`, so the horizon-`(t+1)` region is a neighbourhood
of `(t,x)` within `[0,∞) × ℝ³`.

This is the only analytic step of the assembly below; it is what makes the
half-open hypothesis `HalfLineClassicalExistence` sufficient for the closed
half-space smoothness demanded by `IsClassicalSolution`. -/
theorem contDiffOn_ici_of_forall_before {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ × Space → E}
    (h : ∀ T : ℝ, 0 < T → ContDiffOn ℝ ∞ F (Set.Ico 0 T ×ˢ (Set.univ : Set Space))) :
    ContDiffOn ℝ ∞ F (Set.Ici 0 ×ˢ (Set.univ : Set Space)) := by
  intro z hz
  have hz0 : (0:ℝ) ≤ z.1 := hz.1
  have hT : (0:ℝ) < z.1 + 1 := by linarith
  have hzmem : z ∈ Set.Ico 0 (z.1 + 1) ×ˢ (Set.univ : Set Space) :=
    ⟨⟨hz0, by linarith⟩, Set.mem_univ _⟩
  have hbase := h (z.1 + 1) hT z hzmem
  refine hbase.mono_of_mem_nhdsWithin ?_
  refine mem_nhdsWithin.mpr
    ⟨Set.Iio (z.1 + 1) ×ˢ (Set.univ : Set Space), isOpen_Iio.prod isOpen_univ,
      Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_add_one z.1), Set.mem_univ _⟩, ?_⟩
  rintro w ⟨hw1, hw2⟩
  exact ⟨⟨hw2.1, hw1.1⟩, Set.mem_univ _⟩

/-! ## The two hypotheses -/

/-- **Residual 1 (`Frontier.globalContinuation`).**  Existence, for every
viscosity and every divergence-free Schwartz datum, of a velocity/pressure pair
attaining the datum and solving the unforced equation classically on every
finite horizon `[0,T)`.

This is the hard analytic residual.  It is strictly weaker than the endpoint:
it demands no energy integrability, no uniform energy bound, and joint
smoothness only on the half-open regions. -/
def HalfLineClassicalExistence : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ u : VelocityEvolution, ∃ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) ∧
      ∀ T : ℝ, 0 < T →
        SmoothVelocityBefore T u ∧ SmoothPressureBefore T p ∧
          IncompressibleBefore T u ∧
          SatisfiesNavierStokesBefore ν zeroForce T u p

/-- **Residual 2 (`Frontier.wholeSpaceEnergyBridge`).**  Every globally smooth
incompressible classical solution of the unforced equation issuing from
Schwartz data has integrable kinetic-energy density at each time and a uniform
strict energy bound.

This constructs no solution: it is an implication whose hypothesis is supplied
by residual 1.  The `Integrable` conjunct is explicit, so the bracket cannot be
satisfied vacuously by Lean's junk value for integrals of nonintegrable
functions. -/
def WholeSpaceEnergyClause : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      SmoothVelocityOnNonnegativeTime u → SmoothPressureOnNonnegativeTime p →
      (∀ x : Space, u 0 x = u₀ x) → Incompressible u →
      SatisfiesNavierStokes ν zeroForce u p →
      (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)) ∧
        (∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E)

/-! ## The conditional endpoint -/

/-- **CONDITIONAL: Fefferman statement A from the two named residuals.**

`HalfLineClassicalExistence → WholeSpaceEnergyClause →
Navier.ProblemStatements.WholeSpaceGlobalRegularity`.

This is a reduction, not a solution.  Both hypotheses are open; nothing in this
repository proves either.  The theorem exists so that the endpoint has a typed
inhabitant whose hypothesis list is the current residual and can be diffed as
waves close pieces of it.

Scope: conditional.  No global-regularity claim is made, and neither hypothesis
is discharged here. -/
theorem wholeSpaceGlobalRegularity_of_halfLineExistence_and_energyClause
    (hexist : HalfLineClassicalExistence) (henergy : WholeSpaceEnergyClause) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  intro ν hν u₀ hdiv
  obtain ⟨u, p, hinit, hbefore⟩ := hexist ν hν u₀ hdiv
  have hus : SmoothVelocityOnNonnegativeTime u :=
    contDiffOn_ici_of_forall_before fun T hT => (hbefore T hT).1
  have hps : SmoothPressureOnNonnegativeTime p :=
    contDiffOn_ici_of_forall_before fun T hT => (hbefore T hT).2.1
  have hinc : Incompressible u := by
    intro t ht x
    exact (hbefore (t + 1) (by linarith)).2.2.1 t ht (by linarith) x
  have heq : SatisfiesNavierStokes ν zeroForce u p := by
    intro t ht x
    exact (hbefore (t + 1) (by linarith)).2.2.2 t ht (by linarith) x
  obtain ⟨hfin, hbnd⟩ := henergy ν hν u₀ hdiv u p hus hps hinit hinc heq
  refine ⟨u, p, ?_⟩
  exact
    { velocity_smooth := hus
      pressure_smooth := hps
      initial_condition := hinit
      incompressible := hinc
      equation := heq
      finite_energy := hfin
      uniformly_bounded_energy := hbnd }

/-! ## Satisfiability smoke tests

Both hypothesis bodies are inhabited at a real point of their quantifier
range.  These are guards against the vacuity failures recorded for this
repository, not evidence for the hypotheses themselves. -/

/-- The zero pair satisfies every PDE clause in the body of
`HalfLineClassicalExistence`, for every viscosity and every horizon.  The
hypothesis shape is therefore inhabitable: it is not unsatisfiable, and the
conditional endpoint is not vacuously true for that reason. -/
theorem zero_is_solution_before (ν T : ℝ) :
    SmoothVelocityBefore T (fun _ _ => 0) ∧
      SmoothPressureBefore T (fun _ _ => 0) ∧
      IncompressibleBefore T (fun _ _ => 0) ∧
      SatisfiesNavierStokesBefore ν zeroForce T (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨contDiffOn_const, contDiffOn_const, ?_, ?_⟩
  · intro t _ _ x
    simp [divergence, spatialDerivative]
  · intro t _ _ x
    have hpg : pressureGradient (fun _ _ => (0 : ℝ)) t x = 0 := by
      funext i
      simp [pressureGradient]
    simp [timeDerivative, convection, spatialDerivative, laplacian, zeroForce, hpg]

/-- The zero velocity satisfies the conclusion of `WholeSpaceEnergyClause`,
including the explicit `Integrable` conjunct and a strict uniform bound.  The
conclusion shape is therefore inhabitable. -/
theorem zero_satisfies_energyClause :
    (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖(0 : Space)‖ ^ 2)) ∧
      (∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, 0 ≤ t →
        kineticEnergy (fun _ _ => (0 : Space)) t < E) := by
  refine ⟨fun t _ => ?_, ⟨1, one_pos, fun t _ => ?_⟩⟩
  · have hz : (fun _ : Space => ‖(0 : Space)‖ ^ 2) = fun _ : Space => (0 : ℝ) := by
      funext y
      simp [norm_zero]
    rw [hz]
    exact integrable_zero Space ℝ volume
  · simp [kineticEnergy]

end Navier.Analysis.GlobalRegularityEndpoint

#print axioms Navier.Analysis.GlobalRegularityEndpoint.contDiffOn_ici_of_forall_before
#print axioms
  Navier.Analysis.GlobalRegularityEndpoint.wholeSpaceGlobalRegularity_of_halfLineExistence_and_energyClause
#print axioms Navier.Analysis.GlobalRegularityEndpoint.zero_is_solution_before
#print axioms Navier.Analysis.GlobalRegularityEndpoint.zero_satisfies_energyClause
