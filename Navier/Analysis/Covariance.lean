import Navier.Problem

/-!
# Parabolic dilation covariance

This module establishes spatial and parabolic scaling identities for the
pointwise Navier--Stokes equation.  It does not assert covariance of the
separate smoothness, energy, or problem endpoint clauses.

The Frechet-derivative identity is universal: Mathlib's
`fderiv_comp_smul` and `fderiv_const_smul_field` include the `c = 0` case and
use the standard zero value of `fderiv` at nondifferentiability points.
-/

set_option autoImplicit false

noncomputable section

open scoped Pointwise

namespace Navier.Analysis.Covariance

open Navier

/-- The spatial derivative of `y |-> c * u(c * y)` scales by `c^2`.

No differentiability hypothesis is needed because the two Mathlib `fderiv`
scaling identities used here are valid universally, including at `c = 0`. -/
theorem fderiv_velocity_dilation (c : ℝ) (u : Space → Space) (x : Space) :
    fderiv ℝ (fun y : Space ↦ c • u (c • y)) x =
      c ^ 2 • fderiv ℝ u (c • x) := by
  rw [show (fun y : Space ↦ c • u (c • y)) =
      c • (fun y : Space ↦ u (c • y)) by rfl]
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply, fderiv_comp_smul, smul_smul, pow_two]

/-- Static divergence scales by `c^2` under spatial velocity dilation. -/
theorem staticDivergence_dilation (c : ℝ) (u : Space → Space) (x : Space) :
    staticDivergence (fun y : Space ↦ c • u (c • y)) x =
      c ^ 2 * staticDivergence u (c • x) := by
  simp only [staticDivergence, fderiv_velocity_dilation,
    smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]

/-- Explicit boundary-case check: at `c = 0` the dilated field is identically
zero, so both its Frechet derivative and its static divergence vanish. -/
theorem zero_dilation_truth_check (u : Space → Space) (x : Space) :
    fderiv ℝ (fun y : Space ↦ (0 : ℝ) • u ((0 : ℝ) • y)) x = 0 ∧
      staticDivergence (fun y : Space ↦ (0 : ℝ) • u ((0 : ℝ) • y)) x = 0 := by
  simp [staticDivergence]

/-- The Schwartz velocity obtained from `u0` by `y |-> c * u0(c * y)`.

For `c = 0` this is the zero Schwartz map.  For `c != 0`, composition uses the
continuous linear equivalence given by scalar multiplication by the unit `c`.
-/
def scaledSchwartzVelocity (c : ℝ) (u₀ : SchwartzVelocity) : SchwartzVelocity :=
  if hc : c = 0 then
    0
  else
    c • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) : Space ≃L[ℝ] Space) u₀

@[simp] theorem scaledSchwartzVelocity_apply
    (c : ℝ) (u₀ : SchwartzVelocity) (x : Space) :
    scaledSchwartzVelocity c u₀ x = c • u₀ (c • x) := by
  by_cases hc : c = 0
  · subst c
    simp [scaledSchwartzVelocity]
  · simp [scaledSchwartzVelocity, hc]

/-- Divergence-free Schwartz initial data remain divergence-free under the
spatial velocity dilation, for every real `c` (hence in particular `c > 0`). -/
theorem divergenceFreeInitial_scaled (c : ℝ) (u₀ : SchwartzVelocity)
    (hu₀ : DivergenceFreeInitial u₀) :
    DivergenceFreeInitial (scaledSchwartzVelocity c u₀) := by
  intro x
  have hfun : (fun y : Space ↦ scaledSchwartzVelocity c u₀ y) =
      (fun y : Space ↦ c • u₀ (c • y)) := by
    funext y
    exact scaledSchwartzVelocity_apply c u₀ y
  rw [hfun, staticDivergence_dilation, hu₀ (c • x), mul_zero]

/-- `u_lambda(x,t) = lambda * u(lambda*x, lambda^2*t)`. -/
def parabolicScaledVelocity (lambda : ℝ) (u : VelocityEvolution) :
    VelocityEvolution :=
  fun t x ↦ lambda • u (lambda ^ 2 * t) (lambda • x)

/-- `p_lambda(x,t) = lambda^2 * p(lambda*x, lambda^2*t)`. -/
def parabolicScaledPressure (lambda : ℝ) (p : PressureEvolution) :
    PressureEvolution :=
  fun t x ↦ lambda ^ 2 * p (lambda ^ 2 * t) (lambda • x)

/-- `f_lambda(x,t) = lambda^3 * f(lambda*x, lambda^2*t)`. -/
def parabolicScaledForce (lambda : ℝ) (f : ForceField) : ForceField :=
  fun t x ↦ lambda ^ 3 • f (lambda ^ 2 * t) (lambda • x)

/-- Universal Frechet scaling with independent output amplitude `a` and input
dilation `c`.  No differentiability hypothesis is needed: both Mathlib
identities used here respect its zero-at-nondifferentiability convention. -/
theorem fderiv_amplitude_dilation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a c : ℝ) (g : E → F) (x : E) :
    fderiv ℝ (fun y : E ↦ a • g (c • y)) x =
      (a * c) • fderiv ℝ g (c • x) := by
  rw [show (fun y : E ↦ a • g (c • y)) =
      a • (fun y : E ↦ g (c • y)) by rfl]
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply, fderiv_comp_smul, smul_smul]

/-- The spatial derivative of the parabolically scaled velocity has weight
`lambda^2`.  This identity is universal in `lambda` and `u`. -/
theorem spatialDerivative_scaled (lambda : ℝ) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    spatialDerivative (parabolicScaledVelocity lambda u) t x =
      lambda ^ 2 • spatialDerivative u (lambda ^ 2 * t) (lambda • x) := by
  exact fderiv_velocity_dilation lambda (u (lambda ^ 2 * t)) x

/-- Divergence has the same spatial weight `lambda^2`. -/
theorem divergence_scaled (lambda : ℝ) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    divergence (parabolicScaledVelocity lambda u) t x =
      lambda ^ 2 * divergence u (lambda ^ 2 * t) (lambda • x) := by
  exact staticDivergence_dilation lambda (u (lambda ^ 2 * t)) x

/-- The convection term has parabolic weight `lambda^3`. -/
theorem convection_scaled (lambda : ℝ) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    convection (parabolicScaledVelocity lambda u) t x =
      lambda ^ 3 • convection u (lambda ^ 2 * t) (lambda • x) := by
  rw [convection, spatialDerivative_scaled]
  simp only [parabolicScaledVelocity, smul_apply, map_smul, smul_smul]
  congr 1
  ring

/-- The pressure gradient of the parabolically scaled pressure has weight
`lambda^3`. -/
theorem pressureGradient_scaled (lambda : ℝ) (p : PressureEvolution)
    (t : ℝ) (x : Space) :
    pressureGradient (parabolicScaledPressure lambda p) t x =
      lambda ^ 3 • pressureGradient p (lambda ^ 2 * t) (lambda • x) := by
  funext i
  change fderiv ℝ
      (fun y : Space ↦ lambda ^ 2 • p (lambda ^ 2 * t) (lambda • y)) x
        (basisVector i) =
    (lambda ^ 3 • fderiv ℝ (p (lambda ^ 2 * t)) (lambda • x))
      (basisVector i)
  rw [fderiv_amplitude_dilation]
  simp only [smul_apply]
  congr 1

/-- Each pure second directional derivative has parabolic weight `lambda^3`.
This remains unconditional because the two first-derivative scaling laws used
in succession both follow Mathlib's zero-at-nondifferentiability convention. -/
theorem secondDirectionalDerivative_scaled (lambda : ℝ)
    (u : VelocityEvolution) (t : ℝ) (x : Space) (i : Fin 3) :
    fderiv ℝ
        (fun y : Space ↦
          fderiv ℝ ((parabolicScaledVelocity lambda u) t) y
            (basisVector i)) x (basisVector i) =
      lambda ^ 3 •
        fderiv ℝ
          (fun y : Space ↦
            fderiv ℝ (u (lambda ^ 2 * t)) y (basisVector i))
          (lambda • x) (basisVector i) := by
  have hfirst :
      (fun y : Space ↦
          fderiv ℝ ((parabolicScaledVelocity lambda u) t) y
            (basisVector i)) =
        (fun y : Space ↦
          lambda ^ 2 •
            fderiv ℝ (u (lambda ^ 2 * t)) (lambda • y)
              (basisVector i)) := by
    funext y
    rw [show fderiv ℝ ((parabolicScaledVelocity lambda u) t) y =
        spatialDerivative (parabolicScaledVelocity lambda u) t y by rfl]
    rw [spatialDerivative_scaled]
    simp only [smul_apply, spatialDerivative]
  rw [hfirst]
  rw [fderiv_amplitude_dilation
    (a := lambda ^ 2) (c := lambda)
    (g := fun y : Space ↦
      fderiv ℝ (u (lambda ^ 2 * t)) y (basisVector i)) (x := x)]
  simp only [smul_apply]
  congr 1

/-- The componentwise spatial Laplacian has parabolic weight `lambda^3`. -/
theorem laplacian_scaled (lambda : ℝ) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    laplacian (parabolicScaledVelocity lambda u) t x =
      lambda ^ 3 • laplacian u (lambda ^ 2 * t) (lambda • x) := by
  simp only [laplacian, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact secondDirectionalDerivative_scaled lambda u t x i

/-- The right-within time derivative has parabolic weight `lambda^3`.
Positivity is essential here: it makes multiplication by `lambda^2` preserve
the half-line `Set.Ici 0` used by `timeDerivative`. -/
theorem timeDerivative_scaled (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    timeDerivative (parabolicScaledVelocity lambda u) t x =
      lambda ^ 3 • timeDerivative u (lambda ^ 2 * t) (lambda • x) := by
  have hs : UniqueDiffWithinAt ℝ (Set.Ici 0) t :=
    (uniqueDiffOn_Ici 0) t ht
  have hLambdaSq : 0 < lambda ^ 2 := sq_pos_of_pos hLambda
  have hset : lambda ^ 2 • Set.Ici (0 : ℝ) = Set.Ici 0 := by
    rw [LinearOrderedField.smul_Ici hLambdaSq]
    simp only [mul_zero]
  let g : ℝ → Space := fun s ↦ u s (lambda • x)
  change
    fderivWithin ℝ (lambda • (g <| (lambda ^ 2) • ·))
        (Set.Ici 0) t 1 =
      lambda ^ 3 •
        fderivWithin ℝ g (Set.Ici 0) ((lambda ^ 2) • t) 1
  rw [fderivWithin_const_smul_field lambda hs]
  rw [fderivWithin_comp_smul (f := g) (lambda ^ 2) hs]
  rw [hset]
  simp only [smul_apply, smul_smul]
  congr 1
  ring

/-- Parabolic covariance of the pointwise forced Navier--Stokes momentum
equation.  This transports only `SatisfiesNavierStokes`; the separate
smoothness, energy, incompressibility, and initial-data clauses are outside
the scope of this theorem. -/
theorem satisfiesNavierStokes_scaled (lambda : ℝ) (hLambda : 0 < lambda)
    (nu : ℝ) (f : ForceField) (u : VelocityEvolution)
    (p : PressureEvolution) (hEquation : SatisfiesNavierStokes nu f u p) :
    SatisfiesNavierStokes nu (parabolicScaledForce lambda f)
      (parabolicScaledVelocity lambda u)
      (parabolicScaledPressure lambda p) := by
  intro t ht x
  have hScaledTime : 0 ≤ lambda ^ 2 * t :=
    mul_nonneg (sq_nonneg lambda) ht
  have hAtScaledPoint :=
    hEquation (lambda ^ 2 * t) hScaledTime (lambda • x)
  rw [timeDerivative_scaled lambda hLambda u t ht x]
  rw [convection_scaled, laplacian_scaled, pressureGradient_scaled]
  change
    lambda ^ 3 • timeDerivative u (lambda ^ 2 * t) (lambda • x) +
        lambda ^ 3 • convection u (lambda ^ 2 * t) (lambda • x) =
      nu • (lambda ^ 3 • laplacian u (lambda ^ 2 * t) (lambda • x)) -
          lambda ^ 3 • pressureGradient p (lambda ^ 2 * t) (lambda • x) +
        lambda ^ 3 • f (lambda ^ 2 * t) (lambda • x)
  rw [← smul_add, hAtScaledPoint]
  simp only [smul_add, smul_sub, smul_smul]
  rw [mul_comm (lambda ^ 3) nu]

/-- Boundary truth check: all three scaled fields are zero at scale zero. -/
theorem zero_scale_fields (u : VelocityEvolution) (p : PressureEvolution)
    (f : ForceField) :
    parabolicScaledVelocity 0 u = 0 ∧
      parabolicScaledPressure 0 p = 0 ∧
      parabolicScaledForce 0 f = 0 := by
  constructor
  · funext t x
    norm_num [parabolicScaledVelocity]
  · constructor
    · funext t x
      norm_num [parabolicScaledPressure]
    · funext t x
      norm_num [parabolicScaledForce]

/-- Positive-scale truth check at `lambda = 1`: scaling is the identity. -/
theorem one_scale_fields (u : VelocityEvolution) (p : PressureEvolution)
    (f : ForceField) :
    parabolicScaledVelocity 1 u = u ∧
      parabolicScaledPressure 1 p = p ∧
      parabolicScaledForce 1 f = f := by
  constructor
  · funext t x
    norm_num [parabolicScaledVelocity]
  · constructor
    · funext t x
      norm_num [parabolicScaledPressure]
    · funext t x
      norm_num [parabolicScaledForce]

end Navier.Analysis.Covariance
