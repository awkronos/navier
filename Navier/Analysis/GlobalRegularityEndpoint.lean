import Navier.Breakdown.MaximalNonextension

/-!
# Half-line smoothness and a counterexample to unrestricted energy recovery

`contDiffOn_ici_of_forall_before` transports smoothness on every finite
half-open horizon to the nonnegative half-space. `HalfLineClassicalExistence`
states the corresponding existence problem without an energy condition.

`WholeSpaceEnergyClause` records a rejected universal claim solely so that
`not_wholeSpaceEnergyClause` can refute its exact statement. The accelerating
flow `u(t,x) = t e₀`, `p(t,x) = -x₀` solves the unforced equation from zero
Schwartz data and has nonintegrable energy at positive times. The former
endpoint implication using this false premise has been removed.

The original `ProblemStatements.WholeSpaceGlobalRegularity` asks for the
existence of a finite-energy solution. This example does not refute it: the
same zero datum also has the zero solution. A construction of the original
endpoint must establish energy control for the solution it actually produces.
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

This supplies the closed-half-space smoothness demanded by
`IsClassicalSolution` from the corresponding half-open smoothness hypotheses. -/
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

/-- Existence, for every
viscosity and every divergence-free Schwartz datum, of a velocity/pressure pair
attaining the datum and solving the unforced equation classically on every
finite horizon `[0,T)`.

This statement demands no energy integrability or uniform energy bound.
Joint smoothness is required on every finite half-open region. -/
def HalfLineClassicalExistence : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ u : VelocityEvolution, ∃ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) ∧
      ∀ T : ℝ, 0 < T →
        SmoothVelocityBefore T u ∧ SmoothPressureBefore T p ∧
          IncompressibleBefore T u ∧
          SatisfiesNavierStokesBefore ν zeroForce T u p

/-- **Rejected claim, refuted by `not_wholeSpaceEnergyClause`.** Every globally smooth
incompressible classical solution of the unforced equation issuing from
Schwartz data has integrable kinetic-energy density at each time and a uniform
strict energy bound.

The unrestricted spatial behavior makes this universal statement false.
It is retained as the target of a counterexample, not as an assumption in an
endpoint reduction. The `Integrable` conjunct is explicit. -/
def WholeSpaceEnergyClause : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      SmoothVelocityOnNonnegativeTime u → SmoothPressureOnNonnegativeTime p →
      (∀ x : Space, u 0 x = u₀ x) → Incompressible u →
      SatisfiesNavierStokes ν zeroForce u p →
      (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)) ∧
        (∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E)

/-! ## Boundary tests and falsification

The zero tests show that the local solution body and the energy conclusion are
individually inhabitable.  They do not inhabit the universally quantified
`WholeSpaceEnergyClause`; the accelerating-flow witness below refutes it. -/

/-- The zero pair satisfies every PDE clause in the body of
`HalfLineClassicalExistence`, for every viscosity and every horizon.
This checks the zero datum only. -/
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
#print axioms Navier.Analysis.GlobalRegularityEndpoint.zero_is_solution_before
#print axioms Navier.Analysis.GlobalRegularityEndpoint.zero_satisfies_energyClause
#print axioms Navier.Analysis.GlobalRegularityEndpoint.not_wholeSpaceEnergyClause
