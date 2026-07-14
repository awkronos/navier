import Navier.OfficialProblem

/-!
# Viscosity transport by time and amplitude rescaling

For a positive scalar `a`, this file studies the rescaling

`u_a(t,x) = a u(a t,x)`, `p_a(t,x) = a^2 p(a t,x)`, and
`f_a(t,x) = a^2 f(a t,x)`.

If `(u,p)` satisfies the pointwise equation with viscosity `mu`, the rescaled
fields satisfy it with viscosity `a * mu`.  In particular, viscosity one
transports to every positive viscosity, and inverse scaling transports a
positive viscosity back to one.

The module also proves preservation of the initial condition,
incompressibility, and spatial periodicity, together with algebraic round-trip
identities.  It deliberately does not claim transport of half-space
smoothness, rapid-decay force predicates, energy clauses, or either complete
classical-solution structure; those require separate analytic bridge theorems.
-/

set_option autoImplicit false

noncomputable section

open scoped Pointwise

namespace Navier.Analysis.ViscosityTransport

open Navier

/-- Time/amplitude rescaling of velocity. -/
def viscosityScaledVelocity (a : ℝ) (u : VelocityEvolution) :
    VelocityEvolution :=
  fun t x ↦ a • u (a * t) x

/-- Time/amplitude rescaling of pressure. -/
def viscosityScaledPressure (a : ℝ) (p : PressureEvolution) :
    PressureEvolution :=
  fun t x ↦ a ^ 2 * p (a * t) x

/-- Time/amplitude rescaling of force. -/
def viscosityScaledForce (a : ℝ) (f : ForceField) : ForceField :=
  fun t x ↦ a ^ 2 • f (a * t) x

/-- Amplitude rescaling of a general initial velocity field. -/
def viscosityScaledDatum (a : ℝ) (u₀ : VelocityField) : VelocityField :=
  fun x ↦ a • u₀ x

/-- Amplitude rescaling inside the bundled Schwartz initial-data class. -/
def viscosityScaledSchwartzDatum (a : ℝ) (u₀ : SchwartzVelocity) :
    SchwartzVelocity :=
  a • u₀

/-- Fréchet differentiation commutes with scalar multiplication of the
codomain.  This local helper makes the pointwise application explicit. -/
theorem fderiv_const_smul_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ) (g : E → F) (x : E) :
    fderiv ℝ (fun y : E ↦ c • g y) x = c • fderiv ℝ g x := by
  rw [show (fun y : E ↦ c • g y) = c • g by rfl]
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply]

/-- The spatial derivative has amplitude weight one. -/
theorem spatialDerivative_viscosityScaled (a : ℝ) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    spatialDerivative (viscosityScaledVelocity a u) t x =
      a • spatialDerivative u (a * t) x :=
  fderiv_const_smul_apply a (u (a * t)) x

/-- Divergence has amplitude weight one. -/
theorem divergence_viscosityScaled (a : ℝ) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    divergence (viscosityScaledVelocity a u) t x =
      a * divergence u (a * t) x := by
  simp only [divergence, spatialDerivative_viscosityScaled,
    smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Static divergence has amplitude weight one. -/
theorem staticDivergence_viscosityScaledDatum
    (a : ℝ) (u₀ : VelocityField) (x : Space) :
    staticDivergence (viscosityScaledDatum a u₀) x =
      a * staticDivergence u₀ x := by
  change
    (∑ i : Fin 3,
      fderiv ℝ (fun y : Space ↦ a • u₀ y) x (basisVector i) i) =
      a * ∑ i : Fin 3, fderiv ℝ u₀ x (basisVector i) i
  simp only [fderiv_const_smul_apply, smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]

/-- The quadratic convection term has amplitude weight two. -/
theorem convection_viscosityScaled (a : ℝ) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    convection (viscosityScaledVelocity a u) t x =
      a ^ 2 • convection u (a * t) x := by
  rw [convection, spatialDerivative_viscosityScaled]
  simp only [viscosityScaledVelocity, smul_apply, map_smul, smul_smul]
  congr 1
  ring

/-- The pressure gradient has amplitude weight two. -/
theorem pressureGradient_viscosityScaled (a : ℝ) (p : PressureEvolution)
    (t : ℝ) (x : Space) :
    pressureGradient (viscosityScaledPressure a p) t x =
      a ^ 2 • pressureGradient p (a * t) x := by
  funext i
  change fderiv ℝ (fun y : Space ↦ a ^ 2 * p (a * t) y) x
      (basisVector i) =
    (a ^ 2 • fderiv ℝ (p (a * t)) x) (basisVector i)
  rw [show (fun y : Space ↦ a ^ 2 * p (a * t) y) =
      a ^ 2 • p (a * t) by rfl]
  rw [fderiv_const_smul_field]
  rfl

/-- The spatial Laplacian has amplitude weight one. -/
theorem laplacian_viscosityScaled (a : ℝ) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    laplacian (viscosityScaledVelocity a u) t x =
      a • laplacian u (a * t) x := by
  simp only [laplacian, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hfirst :
      (fun y : Space ↦
          fderiv ℝ ((viscosityScaledVelocity a u) t) y (basisVector i)) =
        (fun y : Space ↦
          a • fderiv ℝ (u (a * t)) y (basisVector i)) := by
    funext y
    rw [show fderiv ℝ ((viscosityScaledVelocity a u) t) y =
      spatialDerivative (viscosityScaledVelocity a u) t y by rfl]
    rw [spatialDerivative_viscosityScaled]
    rfl
  rw [hfirst]
  rw [fderiv_const_smul_apply]
  simp only [smul_apply]

/-- The right-within time derivative has amplitude weight two.  Positivity of
`a` is essential because multiplication by `a` must preserve `[0,∞)`. -/
theorem timeDerivative_viscosityScaled (a : ℝ) (ha : 0 < a)
    (u : VelocityEvolution) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    timeDerivative (viscosityScaledVelocity a u) t x =
      a ^ 2 • timeDerivative u (a * t) x := by
  have hs : UniqueDiffWithinAt ℝ (Set.Ici 0) t :=
    (uniqueDiffOn_Ici 0) t ht
  have hset : a • Set.Ici (0 : ℝ) = Set.Ici 0 := by
    rw [LinearOrderedField.smul_Ici ha]
    simp only [mul_zero]
  let g : ℝ → Space := fun s ↦ u s x
  change
    fderivWithin ℝ (a • (g <| a • ·)) (Set.Ici 0) t 1 =
      a ^ 2 • fderivWithin ℝ g (Set.Ici 0) (a * t) 1
  rw [fderivWithin_const_smul_field a hs]
  rw [fderivWithin_comp_smul (f := g) a hs]
  rw [hset]
  simp only [smul_apply, smul_smul]
  congr 1
  ring

/-- Scaling by `a > 0` transports the pointwise equation at viscosity `mu` to
the pointwise equation at viscosity `a * mu`. -/
theorem satisfiesNavierStokes_viscosityScaled_mul
    (a : ℝ) (ha : 0 < a) (mu : ℝ)
    (f : ForceField) (u : VelocityEvolution) (p : PressureEvolution)
    (hEquation : SatisfiesNavierStokes mu f u p) :
    SatisfiesNavierStokes (a * mu) (viscosityScaledForce a f)
      (viscosityScaledVelocity a u) (viscosityScaledPressure a p) := by
  intro t ht x
  have hScaledTime : 0 ≤ a * t := mul_nonneg ha.le ht
  have hAtScaledPoint := hEquation (a * t) hScaledTime x
  rw [timeDerivative_viscosityScaled a ha u t ht x]
  rw [convection_viscosityScaled, laplacian_viscosityScaled,
    pressureGradient_viscosityScaled]
  change
    a ^ 2 • timeDerivative u (a * t) x +
        a ^ 2 • convection u (a * t) x =
      (a * mu) • (a • laplacian u (a * t) x) -
          a ^ 2 • pressureGradient p (a * t) x +
        a ^ 2 • f (a * t) x
  rw [← smul_add, hAtScaledPoint]
  simp only [smul_add, smul_sub, smul_smul]
  congr 1
  ring_nf

/-- The requested specialization: viscosity-one solutions transport to
viscosity `nu > 0`. -/
theorem satisfiesNavierStokes_one_to_viscosity
    (nu : ℝ) (hnu : 0 < nu)
    (f : ForceField) (u : VelocityEvolution) (p : PressureEvolution)
    (hEquation : SatisfiesNavierStokes 1 f u p) :
    SatisfiesNavierStokes nu (viscosityScaledForce nu f)
      (viscosityScaledVelocity nu u) (viscosityScaledPressure nu p) := by
  simpa only [mul_one] using
    satisfiesNavierStokes_viscosityScaled_mul nu hnu 1 f u p hEquation

/-- Inverse pointwise PDE transport from positive viscosity back to
viscosity one. -/
theorem satisfiesNavierStokes_viscosity_to_one
    (nu : ℝ) (hnu : 0 < nu)
    (f : ForceField) (u : VelocityEvolution) (p : PressureEvolution)
    (hEquation : SatisfiesNavierStokes nu f u p) :
    SatisfiesNavierStokes 1 (viscosityScaledForce nu⁻¹ f)
      (viscosityScaledVelocity nu⁻¹ u)
      (viscosityScaledPressure nu⁻¹ p) := by
  have hnuInv : 0 < nu⁻¹ := inv_pos.mpr hnu
  simpa only [inv_mul_cancel₀ hnu.ne'] using
    satisfiesNavierStokes_viscosityScaled_mul
      nu⁻¹ hnuInv nu f u p hEquation

/-- Scalar amplitude preserves divergence-free Schwartz initial data. -/
theorem divergenceFreeInitial_viscosityScaledSchwartzDatum
    (a : ℝ) (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀) :
    DivergenceFreeInitial (viscosityScaledSchwartzDatum a u₀) := by
  intro x
  have hfun :
      (fun y : Space ↦ viscosityScaledSchwartzDatum a u₀ y) =
        viscosityScaledDatum a u₀ := by
    funext y
    rfl
  rw [show staticDivergence
      (fun y : Space ↦ viscosityScaledSchwartzDatum a u₀ y) x =
      staticDivergence (viscosityScaledDatum a u₀) x by rw [hfun]]
  rw [staticDivergence_viscosityScaledDatum, hu₀ x, mul_zero]

/-- Initial conditions transport to the amplitude-scaled datum. -/
theorem initialCondition_viscosityScaled
    (a : ℝ) (u₀ : VelocityField) (u : VelocityEvolution)
    (hInitial : ∀ x : Space, u 0 x = u₀ x) :
    ∀ x : Space,
      viscosityScaledVelocity a u 0 x = viscosityScaledDatum a u₀ x := by
  intro x
  simp only [viscosityScaledVelocity, viscosityScaledDatum, mul_zero]
  rw [hInitial x]

/-- Initial conditions for bundled Schwartz data transport to the bundled
amplitude-scaled datum. -/
theorem initialCondition_viscosityScaledSchwartz
    (a : ℝ) (u₀ : SchwartzVelocity) (u : VelocityEvolution)
    (hInitial : ∀ x : Space, u 0 x = u₀ x) :
    ∀ x : Space,
      viscosityScaledVelocity a u 0 x =
        viscosityScaledSchwartzDatum a u₀ x := by
  intro x
  simp only [viscosityScaledVelocity, viscosityScaledSchwartzDatum, mul_zero]
  rw [hInitial x]
  rfl

/-- Positive viscosity scaling preserves incompressibility on nonnegative
time. -/
theorem incompressible_viscosityScaled
    (a : ℝ) (ha : 0 < a) (u : VelocityEvolution) (hu : Incompressible u) :
    Incompressible (viscosityScaledVelocity a u) := by
  intro t ht x
  rw [divergence_viscosityScaled,
    hu (a * t) (mul_nonneg ha.le ht) x, mul_zero]

/-- Amplitude scaling preserves spatial periodicity of a datum. -/
theorem spatiallyPeriodicDatum_viscosityScaled
    (a : ℝ) (u₀ : VelocityField) (hu₀ : SpatiallyPeriodicDatum u₀) :
    SpatiallyPeriodicDatum (viscosityScaledDatum a u₀) := by
  intro x i
  change a • u₀ (x + basisVector i) = a • u₀ x
  rw [hu₀ x i]

/-- Positive viscosity scaling preserves velocity periodicity on
nonnegative time. -/
theorem spatiallyPeriodicVelocity_viscosityScaled
    (a : ℝ) (ha : 0 < a) (u : VelocityEvolution)
    (hu : SpatiallyPeriodicVelocity u) :
    SpatiallyPeriodicVelocity (viscosityScaledVelocity a u) := by
  intro t ht x i
  change a • u (a * t) (x + basisVector i) = a • u (a * t) x
  rw [hu (a * t) (mul_nonneg ha.le ht) x i]

/-- Positive viscosity scaling preserves pressure periodicity on
nonnegative time. -/
theorem spatiallyPeriodicPressure_viscosityScaled
    (a : ℝ) (ha : 0 < a) (p : PressureEvolution)
    (hp : SpatiallyPeriodicPressure p) :
    SpatiallyPeriodicPressure (viscosityScaledPressure a p) := by
  intro t ht x i
  change a ^ 2 * p (a * t) (x + basisVector i) =
    a ^ 2 * p (a * t) x
  rw [hp (a * t) (mul_nonneg ha.le ht) x i]

/-- Positive viscosity scaling preserves force periodicity on nonnegative
time. -/
theorem spatiallyPeriodicForce_viscosityScaled
    (a : ℝ) (ha : 0 < a) (f : ForceField)
    (hf : SpatiallyPeriodicForce f) :
    SpatiallyPeriodicForce (viscosityScaledForce a f) := by
  intro t ht x i
  change a ^ 2 • f (a * t) (x + basisVector i) =
    a ^ 2 • f (a * t) x
  rw [hf (a * t) (mul_nonneg ha.le ht) x i]

/-- The complete periodic initial-datum predicate is preserved by amplitude
scaling. -/
theorem periodicInitialDatum_viscosityScaled
    (a : ℝ) (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    PeriodicInitialDatum (viscosityScaledDatum a u₀) := by
  rcases hu₀ with ⟨hsmooth, hdiv, hperiodic⟩
  refine ⟨?_, ?_, spatiallyPeriodicDatum_viscosityScaled a u₀ hperiodic⟩
  · exact hsmooth.const_smul a
  · intro x
    rw [staticDivergence_viscosityScaledDatum, hdiv x, mul_zero]

/-- Viscosity force scaling fixes the zero force. -/
@[simp] theorem viscosityScaledForce_zero (a : ℝ) :
    viscosityScaledForce a zeroForce = zeroForce := by
  funext t x
  simp [viscosityScaledForce, zeroForce]

/-- Velocity rescaling followed by inverse rescaling is the identity. -/
theorem viscosityScaledVelocity_inv
    (a : ℝ) (ha : a ≠ 0) (u : VelocityEvolution) :
    viscosityScaledVelocity a⁻¹ (viscosityScaledVelocity a u) = u := by
  funext t x
  simp [viscosityScaledVelocity, ha]

/-- Pressure rescaling followed by inverse rescaling is the identity. -/
theorem viscosityScaledPressure_inv
    (a : ℝ) (ha : a ≠ 0) (p : PressureEvolution) :
    viscosityScaledPressure a⁻¹ (viscosityScaledPressure a p) = p := by
  funext t x
  simp [viscosityScaledPressure, ha, pow_two, mul_assoc]

/-- Force rescaling followed by inverse rescaling is the identity. -/
theorem viscosityScaledForce_inv
    (a : ℝ) (ha : a ≠ 0) (f : ForceField) :
    viscosityScaledForce a⁻¹ (viscosityScaledForce a f) = f := by
  funext t x
  simp only [viscosityScaledForce]
  have ht : a * (a⁻¹ * t) = t := by field_simp
  rw [ht, smul_smul]
  convert one_smul ℝ (f t x) using 1
  field_simp

/-- General data rescaling followed by inverse rescaling is the identity. -/
theorem viscosityScaledDatum_inv
    (a : ℝ) (ha : a ≠ 0) (u₀ : VelocityField) :
    viscosityScaledDatum a⁻¹ (viscosityScaledDatum a u₀) = u₀ := by
  funext x
  simp only [viscosityScaledDatum, smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- Schwartz data rescaling followed by inverse rescaling is the identity. -/
theorem viscosityScaledSchwartzDatum_inv
    (a : ℝ) (ha : a ≠ 0) (u₀ : SchwartzVelocity) :
    viscosityScaledSchwartzDatum a⁻¹
      (viscosityScaledSchwartzDatum a u₀) = u₀ := by
  simp only [viscosityScaledSchwartzDatum, smul_smul, inv_mul_cancel₀ ha,
    one_smul]

end Navier.Analysis.ViscosityTransport
