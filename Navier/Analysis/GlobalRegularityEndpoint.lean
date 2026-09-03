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

**SATISFIABILITY.**  The original smoke test checked only that the conclusion
of `WholeSpaceEnergyClause` holds for the zero solution.  That does not inhabit
the universally quantified clause.  In fact `not_wholeSpaceEnergyClause` below
refutes it: the smooth accelerating flow `u(t,x) = t e₀` with linear pressure
`p(t,x) = -x₀` solves the unforced equation from zero data, but has
nonintegrable positive-time energy density.  Thus the conditional endpoint is
vacuous as stated; it cannot serve as a crown reduction until the solution
class includes an honest spatial-growth or pressure-normalization condition.

**NON-VACUITY.**  Neither hypothesis follows from the ambient typeclasses:
`Space`, `VelocityEvolution` and `PressureEvolution` are plain function types
carrying no PDE content, and both hypotheses quantify over the Schwartz data of
the actual problem.

Scope: this implication is kernel-valid but its energy premise is refuted below.
It is NOT a solution, NOT a global-regularity theorem, and not a sound crown
reduction until that false premise is repaired.
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

This is an implication, not a solution.  `HalfLineClassicalExistence` is open;
`WholeSpaceEnergyClause` is false for the current unconstrained smooth solution
class by `not_wholeSpaceEnergyClause` below.  Therefore this theorem is vacuous
as a crown reduction until the energy premise is repaired.

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

/-! ## Boundary tests and falsification

The zero tests show that the local solution body and the energy conclusion are
individually inhabitable.  They do not inhabit the universally quantified
`WholeSpaceEnergyClause`; the accelerating-flow witness below refutes it. -/

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

/-! ### N6 falsification: smoothness and the PDE do not force finite energy -/

/-- A spatially uniform flow accelerating in the first coordinate. -/
def acceleratingVelocity : VelocityEvolution := fun t _ => t • basisVector 0

/-- The linear pressure whose gradient drives `acceleratingVelocity`. -/
def acceleratingPressure : PressureEvolution := fun _ x => -x 0

theorem acceleratingVelocity_smooth :
    SmoothVelocityOnNonnegativeTime acceleratingVelocity := by
  unfold SmoothVelocityOnNonnegativeTime acceleratingVelocity
  fun_prop

theorem acceleratingPressure_smooth :
    SmoothPressureOnNonnegativeTime acceleratingPressure := by
  unfold SmoothPressureOnNonnegativeTime acceleratingPressure
  fun_prop

theorem acceleratingVelocity_initial :
    ∀ x : Space, acceleratingVelocity 0 x = (0 : SchwartzVelocity) x := by
  intro x
  simp [acceleratingVelocity]

theorem acceleratingVelocity_incompressible :
    Incompressible acceleratingVelocity := by
  intro t _ht x
  change ∑ i : Fin 3,
    fderiv ℝ (fun _ : Space => t • basisVector 0) x (basisVector i) i = 0
  simp

/-- The accelerating flow solves the unforced equation for every viscosity.
Its acceleration is supplied by the gradient of the linear pressure. -/
theorem acceleratingVelocity_satisfiesNavierStokes (ν : ℝ) :
    SatisfiesNavierStokes ν zeroForce acceleratingVelocity acceleratingPressure := by
  intro t ht x
  change fderivWithin ℝ (fun s : ℝ => s • basisVector 0) (Set.Ici 0) t 1 +
      fderiv ℝ (fun _ : Space => t • basisVector 0) x (t • basisVector 0) =
    ν • (∑ i : Fin 3,
      fderiv ℝ (fun y : Space =>
        fderiv ℝ (fun _ : Space => t • basisVector 0) y (basisVector i)) x
          (basisVector i)) -
      (fun i => fderiv ℝ (fun y : Space => -y 0) x (basisVector i)) + zeroForce t x
  have htime :
      fderivWithin ℝ (fun s : ℝ => s • basisVector 0) (Set.Ici 0) t =
        (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVector 0) := by
    simpa only [id_eq] using
      ((hasFDerivAt_id t).smul_const (basisVector 0)).hasFDerivWithinAt.fderivWithin
        (uniqueDiffOn_Ici 0 t ht)
  rw [htime]
  simp only [fderiv_fun_neg]
  rw [fderiv_apply differentiableAt_id 0]
  ext i
  fin_cases i <;> simp [basisVector, zeroForce]

/-- At time `1`, the accelerating flow has a nonzero constant energy density on
the infinite-volume space `Space = Fin 3 → ℝ`. -/
theorem acceleratingVelocity_not_integrable :
    ¬ Integrable (fun x : Space => ‖acceleratingVelocity 1 x‖ ^ 2) := by
  have hb : basisVector 0 ≠ 0 := by
    intro h
    have hi := congrFun h 0
    simpa [basisVector] using hi
  have hc : ‖basisVector 0‖ ^ 2 ≠ (0 : ℝ) :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hb)
  have hfinite : ¬ IsFiniteMeasure (volume : Measure Space) := by
    intro h
    have hlt := h.measure_univ_lt_top
    rw [show volume (Set.univ : Set Space) = ⊤ by
      rw [show (Set.univ : Set Space) = Set.pi Set.univ (fun _ => Set.univ) by simp]
      rw [volume_pi_pi]
      simp] at hlt
    exact (lt_self_iff_false ⊤).mp hlt
  rw [show (fun x : Space => ‖acceleratingVelocity 1 x‖ ^ 2) =
      (fun _ : Space => ‖basisVector 0‖ ^ 2) by
        funext x
        simp [acceleratingVelocity]]
  rw [integrable_const_iff]
  exact not_or_intro hc hfinite

/-- **N6 is false as stated.**  Smoothness, incompressibility, the unforced
equation, and Schwartz initial data do not imply the endpoint energy clause
without a spatial-growth or pressure-normalization condition. -/
theorem not_wholeSpaceEnergyClause : ¬ WholeSpaceEnergyClause := by
  intro henergy
  have hconclusion := henergy 1 one_pos (0 : SchwartzVelocity)
    Navier.ProblemStatements.divergenceFreeInitial_zero
    acceleratingVelocity acceleratingPressure
    acceleratingVelocity_smooth acceleratingPressure_smooth
    acceleratingVelocity_initial acceleratingVelocity_incompressible
    (acceleratingVelocity_satisfiesNavierStokes 1)
  exact acceleratingVelocity_not_integrable (hconclusion.1 1 zero_le_one)

end Navier.Analysis.GlobalRegularityEndpoint

#print axioms Navier.Analysis.GlobalRegularityEndpoint.contDiffOn_ici_of_forall_before
#print axioms
  Navier.Analysis.GlobalRegularityEndpoint.wholeSpaceGlobalRegularity_of_halfLineExistence_and_energyClause
#print axioms Navier.Analysis.GlobalRegularityEndpoint.zero_is_solution_before
#print axioms Navier.Analysis.GlobalRegularityEndpoint.zero_satisfies_energyClause
#print axioms Navier.Analysis.GlobalRegularityEndpoint.not_wholeSpaceEnergyClause
