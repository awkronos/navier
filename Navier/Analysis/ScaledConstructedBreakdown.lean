import Navier.Analysis.ConstructedFiniteTimeObstruction
import Navier.Analysis.SelectedCandidateEnergy
import Navier.Analysis.Covariance

/-!
# Deadline-parameterized parabolic rescaling of the constructed candidate

For `0 < lambda`, the selected unit-deadline Euclidean candidate `(u, p, f)` is
rescaled according to

`u_lambda(t,x) = lambda • u(lambda^2 t, lambda x)`,
`p_lambda(t,x) = lambda^2 * p(lambda^2 t, lambda x)`,
`f_lambda(t,x) = lambda^3 • f(lambda^2 t, lambda x)`,

so its singular time moves to `deadlineOf lambda = lambda^(-2)`.
Chain-rule bookkeeping at the repository's exact residual predicate
(`Navier.Construction.ProblemStatement.navierStokesResidual`, viscosity
coefficient one on the Laplacian): every spacetime partial of the residual
gains exactly the common factor `lambda^3`, hence

`navierStokesResidual u_lambda p_lambda t x
   = lambda^3 • navierStokesResidual u p (lambda^2 t) (lambda x)`.

The Laplacian coefficient is therefore unchanged: the rescaling preserves
viscosity one and the equation form (`residual_deadline`, THEOREM below).

For every `T > 0` the instantiated triple satisfies the deadline-`T` profile
(`PropertiesAt T`): smoothness on `Ico 0 T x univ`, zero initial velocity,
divergence-free on `Ico 0 T`, the same-force-scaled PDE on `Ioo 0 T`, a
compactly future-supported force whose support endpoint is `T` times the
original endpoint, speed unbounded as `t -> T-`, uniform finite energy on
`Ico 0 T`, and a force nonzero strictly before `T`.

What is NOT claimed: unit spatial periods are not preserved (the periods
become `lambda^(-1)`); the deadline-`T` force support endpoint is `T * T0`
where `T0` is the original support endpoint, so a strict bound by `T` holds
exactly when the original force already vanishes by time one
(`deadlineForce_vanishing_from` states the exact law); and nothing here
asserts unforced global regularity or existence beyond the constructed
profile.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ScaledConstructedBreakdown

open Set
open MeasureTheory
open scoped ContDiff
open Navier.Construction.ProblemStatement

private abbrev ESpace := Navier.Construction.ProblemStatement.Space
private abbrev EVelocityField := Navier.Construction.ProblemStatement.VelocityField
private abbrev EPressureField := Navier.Construction.ProblemStatement.PressureField
private abbrev ESpaceTime := Navier.Construction.ProblemStatement.SpaceTime

/-- The parabolic spacetime dilation `(t,x) |-> (lambda^2 t, lambda x)`
underlying the deadline rescaling. -/
def parabolicDilation (lambda : ℝ) : ESpaceTime → ESpaceTime :=
  fun z => (lambda ^ 2 * z.1, lambda • z.2)

/-- The singular time produced by scaling with `lambda`. -/
def deadlineOf (lambda : ℝ) : ℝ := lambda⁻¹ * lambda⁻¹

@[simp] theorem parabolicDilation_apply (lambda : ℝ) (t : ℝ) (x : ESpace) :
    parabolicDilation lambda (t, x) = (lambda ^ 2 * t, lambda • x) := rfl

/-- The deadline-`T` analogue of `preSingularDomain`. -/
def preSingularDomainAt (T : ℝ) : Set ESpaceTime := Ico 0 T ×ˢ univ

/-- The deadline-`T` analogue of `SpeedUnboundedAtOne`: pointwise unbounded
speed arbitrarily near `T` from below. -/
def SpeedUnboundedAt (T : ℝ) (u : EVelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ delta : ℝ, 0 < delta →
    ∃ t : ℝ, ∃ x : ESpace, t ∈ Ioo 0 T ∧ T - delta < t ∧ M < ‖u (t, x)‖

/-- The deadline-`T` analogue of the properties carried by
`Navier.Construction.R3CompactCandidate.Properties`, without unit spatial
periods (parabolic rescaling replaces them by `lambda^(-1)`-periods, which is
not claimed here). The PDE is the exact unit-viscosity residual predicate. -/
structure PropertiesAt (T : ℝ) (u : EVelocityField) (p : EPressureField)
    (f : EVelocityField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u (preSingularDomainAt T)
  pressure_smooth : ContDiffOn ℝ ∞ p (preSingularDomainAt T)
  force_smooth : ContDiffOn ℝ ∞ f futureDomain
  zero_initial_velocity : ∀ x : ESpace, u (0, x) = 0
  divergence_free : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : ESpace, spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : ESpace,
    navierStokesResidual u p t x = f (t, x)
  force_time_support : CompactFutureTimeSupport f
  speed_unbounded : SpeedUnboundedAt T u

/-! ## The rescaled fields -/

/-- `u_lambda(t,x) = lambda • u(lambda^2 t, lambda x)`. -/
def deadlineVelocity (lambda : ℝ) (u : EVelocityField) : EVelocityField :=
  fun z => lambda • u (parabolicDilation lambda z)

/-- `p_lambda(t,x) = lambda^2 * p(lambda^2 t, lambda x)`. -/
def deadlinePressure (lambda : ℝ) (p : EPressureField) : EPressureField :=
  fun z => lambda ^ 2 * p (parabolicDilation lambda z)

/-- `f_lambda(t,x) = lambda^3 • f(lambda^2 t, lambda x)`. -/
def deadlineForce (lambda : ℝ) (f : EVelocityField) : EVelocityField :=
  fun z => lambda ^ 3 • f (parabolicDilation lambda z)

@[simp] theorem deadlineVelocity_apply (lambda : ℝ) (t : ℝ) (x : ESpace)
    (u : EVelocityField) :
    deadlineVelocity lambda u (t, x) = lambda • u (lambda ^ 2 * t, lambda • x) := rfl

@[simp] theorem deadlinePressure_apply (lambda : ℝ) (t : ℝ) (x : ESpace)
    (p : EPressureField) :
    deadlinePressure lambda p (t, x) = lambda ^ 2 * p (lambda ^ 2 * t, lambda • x) := rfl

@[simp] theorem deadlineForce_apply (lambda : ℝ) (t : ℝ) (x : ESpace)
    (f : EVelocityField) :
    deadlineForce lambda f (t, x) = lambda ^ 3 • f (lambda ^ 2 * t, lambda • x) := rfl

theorem deadlineOf_pos {lambda : ℝ} (hlambda : 0 < lambda) :
    0 < deadlineOf lambda := by
  unfold deadlineOf
  positivity

theorem mul_deadlineOf {lambda : ℝ} (hlambda : lambda ≠ 0) :
    lambda ^ 2 * deadlineOf lambda = 1 := by
  unfold deadlineOf
  field_simp [hlambda]

theorem deadlineOf_mul_sq {lambda : ℝ} (hlambda : lambda ≠ 0) :
    deadlineOf lambda * lambda ^ 2 = 1 := by
  rw [mul_comm, mul_deadlineOf hlambda]

/-- Times before the deadline map into the unit pre-singular interval. -/
theorem sq_mul_mem_preSingularDomain {lambda : ℝ} (hlambda : 0 < lambda) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (deadlineOf lambda)) : lambda ^ 2 * t ∈ Ico (0 : ℝ) 1 :=
  ⟨mul_nonneg (sq_nonneg lambda) ht.1, by
    have : lambda ^ 2 * t < lambda ^ 2 * deadlineOf lambda :=
      mul_lt_mul_of_pos_left ht.2 (sq_pos_of_pos hlambda)
    rwa [mul_deadlineOf hlambda.ne'] at this⟩

/-- Times strictly before the deadline map into the open unit interval. -/
theorem sq_mul_mem_Ioo {lambda : ℝ} (hlambda : 0 < lambda) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (deadlineOf lambda)) : lambda ^ 2 * t ∈ Ioo (0 : ℝ) 1 :=
  ⟨mul_pos (sq_pos_of_pos hlambda) ht.1, by
    have : lambda ^ 2 * t < lambda ^ 2 * deadlineOf lambda :=
      mul_lt_mul_of_pos_left ht.2 (sq_pos_of_pos hlambda)
    rwa [mul_deadlineOf hlambda.ne'] at this⟩

/-! ## Chain-rule bookkeeping at the repository's residual predicate -/

/-- The spatial derivative of the rescaled velocity has weight `lambda^2`.
Universal in `lambda`: both `fderiv` scaling identities respect Mathlib's
zero-at-nondifferentiability convention. -/
theorem spatialDerivative_deadline (lambda : ℝ) (u : EVelocityField)
    (t : ℝ) (x : ESpace) :
    Navier.Construction.ProblemStatement.spatialDerivative
        (deadlineVelocity lambda u) t x =
      lambda ^ 2 • Navier.Construction.ProblemStatement.spatialDerivative u
        (lambda ^ 2 * t) (lambda • x) := by
  show fderiv ℝ (fun y : ESpace => lambda • u (lambda ^ 2 * t, lambda • y)) x =
      lambda ^ 2 • fderiv ℝ (fun y : ESpace => u (lambda ^ 2 * t, y)) (lambda • x)
  rw [Navier.Analysis.Covariance.fderiv_amplitude_dilation
      (a := lambda) (c := lambda)
      (g := fun y : ESpace => u (lambda ^ 2 * t, y)) (x := x)]
  rw [show (lambda * lambda : ℝ) = lambda ^ 2 by ring]

/-- The time derivative of the rescaled velocity has weight `lambda^3`. -/
theorem temporalDerivative_deadline (lambda : ℝ) (u : EVelocityField)
    (t : ℝ) (x : ESpace) :
    temporalDerivative (deadlineVelocity lambda u) t x =
      lambda ^ 3 • temporalDerivative u (lambda ^ 2 * t) (lambda • x) := by
  have h := Navier.Analysis.Covariance.fderiv_amplitude_dilation
    (a := lambda) (c := lambda ^ 2)
    (g := fun s : ℝ => u (s, lambda • x)) (x := t)
  simp only [smul_eq_mul] at h
  show fderiv ℝ (fun s : ℝ => lambda • u (lambda ^ 2 * s, lambda • x)) t 1 =
      lambda ^ 3 • fderiv ℝ (fun s : ℝ => u (s, lambda • x)) (lambda ^ 2 * t) 1
  rw [h, show (lambda * lambda ^ 2 : ℝ) = lambda ^ 3 by ring]
  rw [smul_apply]

/-- The advection term has weight `lambda^3`. -/
theorem advection_deadline (lambda : ℝ) (u : EVelocityField)
    (t : ℝ) (x : ESpace) :
    advection (deadlineVelocity lambda u) t x =
      lambda ^ 3 • advection u (lambda ^ 2 * t) (lambda • x) := by
  rw [advection, advection, spatialDerivative_deadline, deadlineVelocity_apply,
    smul_apply, map_smul, smul_smul,
    show (lambda ^ 2 * lambda : ℝ) = lambda ^ 3 by ring]

/-- The spatial divergence has weight `lambda^2`: divergence-free transports. -/
theorem spatialDivergence_deadline (lambda : ℝ) (u : EVelocityField)
    (t : ℝ) (x : ESpace) :
    spatialDivergence (deadlineVelocity lambda u) t x =
      lambda ^ 2 * spatialDivergence u (lambda ^ 2 * t) (lambda • x) := by
  rw [spatialDivergence, spatialDivergence, spatialDerivative_deadline,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- The pressure gradient of the rescaled pressure has weight `lambda^3`. -/
theorem pressureGradient_deadline (lambda : ℝ) (p : EPressureField)
    (t : ℝ) (x : ESpace) :
    Navier.Construction.ProblemStatement.pressureGradient
      (deadlinePressure lambda p) t x =
      lambda ^ 3 • Navier.Construction.ProblemStatement.pressureGradient p
        (lambda ^ 2 * t) (lambda • x) := by
  show ∑ i : Fin 3,
      (fderiv ℝ (fun y : ESpace => (lambda ^ 2 : ℝ) • p (lambda ^ 2 * t, lambda • y))
        x (coordinateVector i)) • coordinateVector i =
      lambda ^ 3 • ∑ i : Fin 3,
        (fderiv ℝ (fun y : ESpace => p (lambda ^ 2 * t, y)) (lambda • x)
          (coordinateVector i)) • coordinateVector i
  have hpoint : (fun i : Fin 3 =>
      (fderiv ℝ (fun y : ESpace => (lambda ^ 2 : ℝ) • p (lambda ^ 2 * t, lambda • y))
        x (coordinateVector i)) • coordinateVector i) =
      (fun i : Fin 3 => lambda ^ 3 •
          ((fderiv ℝ (fun y : ESpace => p (lambda ^ 2 * t, y)) (lambda • x)
            (coordinateVector i)) • coordinateVector i)) := by
    funext i
    rw [Navier.Analysis.Covariance.fderiv_amplitude_dilation (a := lambda ^ 2)
        (c := lambda) (g := fun y : ESpace => p (lambda ^ 2 * t, y)) (x := x)]
    show ((lambda ^ 2 * lambda : ℝ) •
          fderiv ℝ (fun y : ESpace => p (lambda ^ 2 * t, y)) (lambda • x))
        (coordinateVector i) • coordinateVector i =
        lambda ^ 3 •
          ((fderiv ℝ (fun y : ESpace => p (lambda ^ 2 * t, y)) (lambda • x))
            (coordinateVector i) • coordinateVector i)
    rw [smul_apply, show (lambda ^ 2 * lambda : ℝ) = lambda ^ 3 by ring,
      smul_eq_mul, ← smul_smul]
  rw [hpoint]
  simp only [Finset.smul_sum]

/-- Each pure second directional derivative has weight `lambda^3`. -/
theorem secondDirectionalDerivative_deadline (lambda : ℝ) (u : EVelocityField)
    (t : ℝ) (x : ESpace) (i : Fin 3) :
    fderiv ℝ
        (fun y : ESpace =>
          fderiv ℝ (fun z : ESpace => (deadlineVelocity lambda u) (t, z)) y
            (coordinateVector i)) x (coordinateVector i) =
      lambda ^ 3 •
        fderiv ℝ
          (fun y : ESpace =>
            fderiv ℝ (fun z : ESpace => u (lambda ^ 2 * t, z)) y
              (coordinateVector i))
          (lambda • x) (coordinateVector i) := by
  have hfirst :
      (fun y : ESpace =>
          fderiv ℝ (fun z : ESpace => (deadlineVelocity lambda u) (t, z)) y
            (coordinateVector i)) =
        (fun y : ESpace =>
          lambda ^ 2 •
            fderiv ℝ (fun z : ESpace => u (lambda ^ 2 * t, z)) (lambda • y)
              (coordinateVector i)) := by
    funext y
    have hb2 : Navier.Construction.ProblemStatement.spatialDerivative u
        (lambda ^ 2 * t) (lambda • y) =
        fderiv ℝ (fun z : ESpace => u (lambda ^ 2 * t, z)) (lambda • y) := rfl
    show Navier.Construction.ProblemStatement.spatialDerivative
          (deadlineVelocity lambda u) t y (coordinateVector i) =
        lambda ^ 2 •
          fderiv ℝ (fun z : ESpace => u (lambda ^ 2 * t, z)) (lambda • y)
            (coordinateVector i)
    rw [spatialDerivative_deadline, smul_apply, hb2]
  rw [hfirst]
  rw [Navier.Analysis.Covariance.fderiv_amplitude_dilation (a := lambda ^ 2)
    (c := lambda)
    (g := fun y : ESpace =>
      fderiv ℝ (fun z : ESpace => u (lambda ^ 2 * t, z)) y (coordinateVector i))
    (x := x)]
  rw [smul_apply, show (lambda ^ 2 * lambda : ℝ) = lambda ^ 3 by ring]

/-- The spatial Laplacian has weight `lambda^3`. -/
theorem spatialLaplacian_deadline (lambda : ℝ) (u : EVelocityField)
    (t : ℝ) (x : ESpace) :
    spatialLaplacian (deadlineVelocity lambda u) t x =
      lambda ^ 3 • spatialLaplacian u (lambda ^ 2 * t) (lambda • x) := by
  show ∑ i : Fin 3,
      fderiv ℝ (fun y : ESpace =>
          fderiv ℝ (fun z : ESpace => (deadlineVelocity lambda u) (t, z)) y
            (coordinateVector i)) x (coordinateVector i) =
      lambda ^ 3 • ∑ i : Fin 3,
        fderiv ℝ (fun y : ESpace =>
          fderiv ℝ (fun z : ESpace => u (lambda ^ 2 * t, z)) y (coordinateVector i))
        (lambda • x) (coordinateVector i)
  have heq : (fun i : Fin 3 =>
      fderiv ℝ (fun y : ESpace =>
          fderiv ℝ (fun z : ESpace => (deadlineVelocity lambda u) (t, z)) y
            (coordinateVector i)) x (coordinateVector i)) =
      (fun i : Fin 3 => lambda ^ 3 •
          fderiv ℝ (fun y : ESpace =>
            fderiv ℝ (fun z : ESpace => u (lambda ^ 2 * t, z)) y (coordinateVector i))
            (lambda • x) (coordinateVector i)) := by
    funext i
    exact secondDirectionalDerivative_deadline lambda u t x i
  rw [heq]
  simp only [Finset.smul_sum]

/-- Truth check for the whole scaling computation, at the repository's exact
residual predicate: the unit-viscosity residual of the rescaled triple is the
`lambda^3` multiple of the original residual at the dilated point. Every term
shares the same factor, so the Laplacian coefficient (viscosity one) is
preserved exactly. -/
theorem residual_deadline (lambda : ℝ) (u : EVelocityField)
    (p : EPressureField) (t : ℝ) (x : ESpace) :
    navierStokesResidual (deadlineVelocity lambda u) (deadlinePressure lambda p) t x =
      lambda ^ 3 • navierStokesResidual u p (lambda ^ 2 * t) (lambda • x) := by
  unfold navierStokesResidual
  show Navier.Construction.ProblemStatement.temporalDerivative
        (deadlineVelocity lambda u) t x
      + Navier.Construction.ProblemStatement.advection
        (deadlineVelocity lambda u) t x
      - Navier.Construction.ProblemStatement.spatialLaplacian
        (deadlineVelocity lambda u) t x
      + Navier.Construction.ProblemStatement.pressureGradient
        (deadlinePressure lambda p) t x
      = lambda ^ 3 •
        (Navier.Construction.ProblemStatement.temporalDerivative u
            (lambda ^ 2 * t) (lambda • x)
          + Navier.Construction.ProblemStatement.advection u
            (lambda ^ 2 * t) (lambda • x)
          - Navier.Construction.ProblemStatement.spatialLaplacian u
            (lambda ^ 2 * t) (lambda • x)
          + Navier.Construction.ProblemStatement.pressureGradient p
            (lambda ^ 2 * t) (lambda • x))
  rw [temporalDerivative_deadline, advection_deadline,
    spatialLaplacian_deadline, pressureGradient_deadline]
  simp only [← smul_add, ← smul_sub]

/-! ## Regularity and support transports -/

/-- The dilation maps the deadline-`T` pre-singular domain into the unit
pre-singular domain. -/
theorem mapsTo_preSingular {lambda : ℝ} (hlambda : 0 < lambda) :
    Set.MapsTo (parabolicDilation lambda)
      (preSingularDomainAt (deadlineOf lambda)) preSingularDomain := by
  intro z hz
  obtain ⟨ht, hx⟩ := hz
  exact ⟨sq_mul_mem_preSingularDomain hlambda ht, hx⟩

theorem contDiff_parabolicDilation (lambda : ℝ) :
    ContDiff ℝ ∞ (parabolicDilation lambda) :=
  (contDiff_fst.const_smul (lambda ^ 2)).prodMk (contDiff_snd.const_smul lambda)

/-- Velocity smoothness transports to the deadline-`T` domain. -/
theorem velocitySmooth_deadline {lambda : ℝ} (hlambda : 0 < lambda)
    {u : EVelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain) :
    ContDiffOn ℝ ∞ (deadlineVelocity lambda u)
      (preSingularDomainAt (deadlineOf lambda)) := by
  have hcomp :=
    hu.comp ((contDiff_parabolicDilation lambda).contDiffOn.mono
      (subset_univ _)) (mapsTo_preSingular hlambda)
  exact hcomp.const_smul lambda

/-- Pressure smoothness transports to the deadline-`T` domain. -/
theorem pressureSmooth_deadline {lambda : ℝ} (hlambda : 0 < lambda)
    {p : EPressureField} (hp : ContDiffOn ℝ ∞ p preSingularDomain) :
    ContDiffOn ℝ ∞ (deadlinePressure lambda p)
      (preSingularDomainAt (deadlineOf lambda)) := by
  have hcomp :=
    hp.comp ((contDiff_parabolicDilation lambda).contDiffOn.mono
      (subset_univ _)) (mapsTo_preSingular hlambda)
  exact hcomp.const_smul (lambda ^ 2)

/-- The future half-domain is preserved by the dilation. -/
theorem mapsTo_futureDomain {lambda : ℝ} :
    Set.MapsTo (parabolicDilation lambda) futureDomain futureDomain := by
  intro z hz
  exact ⟨mul_nonneg (sq_nonneg lambda) hz.1, hz.2⟩

/-- Force smoothness on the future domain transports. -/
theorem forceSmooth_deadline {lambda : ℝ} {f : EVelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) :
    ContDiffOn ℝ ∞ (deadlineForce lambda f) futureDomain := by
  have hcomp :=
    hf.comp ((contDiff_parabolicDilation lambda).contDiffOn.mono
      (subset_univ _)) mapsTo_futureDomain
  exact hcomp.const_smul (lambda ^ 3)

/-- Global smoothness of the force is preserved. -/
theorem contDiff_deadlineForce {lambda : ℝ} {f : EVelocityField}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deadlineForce lambda f) :=
  (hf.comp (contDiff_parabolicDilation lambda)).const_smul (lambda ^ 3)

/-! ## Deadline-`T` consequences -/

/-- Zero initial velocity transports. -/
theorem zeroInitial_deadline (lambda : ℝ) {u : EVelocityField}
    (hu : ∀ x : ESpace, u (0, x) = 0) (x : ESpace) :
    deadlineVelocity lambda u (0, x) = 0 := by
  rw [deadlineVelocity_apply, mul_zero, hu, smul_zero]

/-- Divergence-freeness transports to `Ico 0 T`. -/
theorem divergenceFree_deadline {lambda : ℝ} (hlambda : 0 < lambda)
    {u : EVelocityField}
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : ESpace, spatialDivergence u t x = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (deadlineOf lambda)) (x : ESpace) :
    spatialDivergence (deadlineVelocity lambda u) t x = 0 := by
  have hz := hu (lambda ^ 2 * t) (sq_mul_mem_preSingularDomain hlambda ht) (lambda • x)
  rw [spatialDivergence_deadline, hz, mul_zero]

/-- The same-force-scaled PDE transports to `Ioo 0 T`. This is the viscosity
preservation statement at the residual predicate: both sides solve the unit
viscosity equation. -/
theorem navierStokes_deadline {lambda : ℝ} (hlambda : 0 < lambda)
    {u : EVelocityField} {p : EPressureField} {f : EVelocityField}
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : ESpace,
        navierStokesResidual u p t x = f (t, x))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (deadlineOf lambda)) (x : ESpace) :
    navierStokesResidual (deadlineVelocity lambda u) (deadlinePressure lambda p) t x =
      deadlineForce lambda f (t, x) := by
  have hz := h (lambda ^ 2 * t) (sq_mul_mem_Ioo hlambda ht) (lambda • x)
  rw [residual_deadline, hz, deadlineForce_apply]

/-- The force's future time support transports, with endpoint scaled by
`deadlineOf lambda`: if `f` vanishes from `T0`, then `f_lambda` vanishes from
`deadlineOf lambda * T0`. -/
theorem forceTimeSupport_deadline {lambda : ℝ} (hlambda : 0 < lambda)
    {f : EVelocityField} (hf : CompactFutureTimeSupport f) :
    CompactFutureTimeSupport (deadlineForce lambda f) := by
  obtain ⟨T0, hT0, hz⟩ := hf
  refine ⟨deadlineOf lambda * T0, mul_nonneg (deadlineOf_pos hlambda).le hT0, ?_⟩
  intro t ht x
  have h2 : lambda ^ 2 * (deadlineOf lambda * T0) ≤ lambda ^ 2 * t :=
    mul_le_mul_of_nonneg_left ht (sq_nonneg lambda)
  rw [← mul_assoc, mul_deadlineOf hlambda.ne', one_mul] at h2
  rw [deadlineForce_apply, hz (lambda ^ 2 * t) h2, smul_zero]

/-- The speed blow-up transports: the rescaled velocity is unbounded as
`t -> (deadlineOf lambda)-`. -/
theorem speedUnbounded_deadline {lambda : ℝ} (hlambda : 0 < lambda)
    {u : EVelocityField} (hu : SpeedUnboundedAtOne u) :
    SpeedUnboundedAt (deadlineOf lambda) (deadlineVelocity lambda u) := by
  have hpos := deadlineOf_pos hlambda
  have hl2 : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  intro M hM delta hdelta
  obtain ⟨s, y, hs, hnear, hlarge⟩ :=
    hu (M / lambda) (div_pos hM hlambda) (lambda ^ 2 * delta) (mul_pos hl2 hdelta)
  have hmul : lambda ^ 2 * (deadlineOf lambda * s) = s := by
    rw [← mul_assoc, mul_deadlineOf hlambda.ne', one_mul]
  have hd2 : deadlineOf lambda * (lambda ^ 2 * delta) = delta := by
    rw [← mul_assoc, deadlineOf_mul_sq hlambda.ne', one_mul]
  have hscale :
      (lambda ^ 2 * (deadlineOf lambda * s), lambda • (lambda⁻¹ • y)) = (s, y) :=
    Prod.ext hmul
      (by rw [smul_smul, mul_inv_cancel₀ hlambda.ne', one_smul])
  refine ⟨deadlineOf lambda * s, lambda⁻¹ • y,
    ⟨mul_pos hpos hs.1, by simpa using mul_lt_mul_of_pos_left hs.2 hpos⟩, ?_, ?_⟩
  · have hnear' : deadlineOf lambda * (1 - lambda ^ 2 * delta) <
      deadlineOf lambda * s :=
      mul_lt_mul_of_pos_left hnear hpos
    rw [mul_sub, mul_one, hd2] at hnear'
    exact hnear'
  · rw [deadlineVelocity_apply, hscale, norm_smul, Real.norm_eq_abs,
      abs_of_pos hlambda]
    have hlt := (div_lt_iff₀ hlambda).mp hlarge
    rw [mul_comm] at hlt
    exact hlt

/-- The force is genuinely nonzero strictly before the deadline. -/
theorem forceNonzero_deadline {lambda : ℝ} (hlambda : 0 < lambda)
    {f : EVelocityField}
    (hf : ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : ESpace, f (t, x) ≠ 0) :
    ∃ t ∈ Ioo (0 : ℝ) (deadlineOf lambda), ∃ x : ESpace,
      deadlineForce lambda f (t, x) ≠ 0 := by
  have hpos := deadlineOf_pos hlambda
  obtain ⟨s, hs, y, hy⟩ := hf
  refine ⟨deadlineOf lambda * s,
    ⟨mul_pos hpos hs.1, by simpa using mul_lt_mul_of_pos_left hs.2 hpos⟩,
    lambda⁻¹ • y, ?_⟩
  rw [deadlineForce_apply]
  have hscale :
      (lambda ^ 2 * (deadlineOf lambda * s), lambda • (lambda⁻¹ • y)) = (s, y) :=
    Prod.ext (by rw [← mul_assoc, mul_deadlineOf hlambda.ne', one_mul])
      (by rw [smul_smul, mul_inv_cancel₀ hlambda.ne', one_smul])
  rw [hscale]
  intro hzero
  apply hy
  have h1 : f (s, y) = ((lambda ^ 3 : ℝ)⁻¹ * lambda ^ 3) • f (s, y) := by
    rw [inv_mul_cancel₀ (pow_ne_zero 3 hlambda.ne'), one_smul]
  rw [h1, ← smul_smul, hzero, smul_zero]

/-- Squared norms gain the exact factor `lambda^2` under positive scalar
multiplication in the Euclidean carrier. -/
theorem norm_sq_deadlineVelocity (lambda : ℝ) (hlambda : 0 < lambda)
    (u : EVelocityField) (t : ℝ) (x : ESpace) :
    ‖deadlineVelocity lambda u (t, x)‖ ^ 2 =
      lambda ^ 2 * ‖u (lambda ^ 2 * t, lambda • x)‖ ^ 2 := by
  rw [deadlineVelocity_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
  ring

/-- The deadline-`T` kinetic energy gains the exact factor `lambda⁻¹`
(amplitude `lambda^2` times the volume factor `lambda^(-3)` in dimension
three). -/
theorem kineticEnergy_deadline (lambda : ℝ) (hlambda : 0 < lambda)
    (u : EVelocityField) (t : ℝ) :
    Navier.ConstructionR3.ProblemStatement.kineticEnergy
        (deadlineVelocity lambda u) t =
      lambda⁻¹ * Navier.ConstructionR3.ProblemStatement.kineticEnergy u
        (lambda ^ 2 * t) := by
  have hdim : Module.finrank ℝ ESpace = 3 := by
    show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    exact finrank_euclideanSpace_fin
  have hpt : ∀ y : ESpace, ‖deadlineVelocity lambda u (t, y)‖ ^ 2 =
      lambda ^ 2 • ‖u (lambda ^ 2 * t, lambda • y)‖ ^ 2 := by
    intro y
    rw [norm_sq_deadlineVelocity lambda hlambda u t y]
    rw [smul_eq_mul]
  have hint :
      ∫ z : ESpace, ‖deadlineVelocity lambda u (t, z)‖ ^ 2 ∂volume =
        lambda⁻¹ * ∫ x : ESpace, ‖u (lambda ^ 2 * t, x)‖ ^ 2 ∂volume := by
    rw [show (fun y : ESpace => ‖deadlineVelocity lambda u (t, y)‖ ^ 2) =
        (fun y : ESpace => lambda ^ 2 • ‖u (lambda ^ 2 * t, lambda • y)‖ ^ 2)
        from funext hpt]
    rw [integral_smul,
      MeasureTheory.Measure.integral_comp_smul volume
        (fun x : ESpace => ‖u (lambda ^ 2 * t, x)‖ ^ 2) lambda, hdim]
    rw [abs_of_pos (inv_pos.mpr (pow_pos hlambda 3)), smul_smul,
      show (lambda ^ 2 * (lambda ^ 3)⁻¹ : ℝ) = lambda⁻¹ by field_simp, smul_eq_mul]
  unfold Navier.ConstructionR3.ProblemStatement.kineticEnergy
  rw [hint]
  ring

/-- Square integrability transports to each rescaled time. -/
theorem squareIntegrable_deadline {lambda : ℝ} (hlambda : 0 < lambda)
    {u : EVelocityField} {t : ℝ}
    (ht : Navier.ConstructionR3.ProblemStatement.SquareIntegrableAtTime
      u (lambda ^ 2 * t)) :
    Navier.ConstructionR3.ProblemStatement.SquareIntegrableAtTime
      (deadlineVelocity lambda u) t := by
  unfold Navier.ConstructionR3.ProblemStatement.SquareIntegrableAtTime at ht ⊢
  have h := MeasureTheory.Integrable.comp_smul ht (ne_of_gt hlambda)
  have hfun : (fun x : ESpace => ‖deadlineVelocity lambda u (t, x)‖ ^ 2) =
      (lambda ^ 2 : ℝ) •
        (fun x : ESpace => ‖u (lambda ^ 2 * t, lambda • x)‖ ^ 2) := by
    funext x
    rw [norm_sq_deadlineVelocity lambda hlambda u t x]
    exact (smul_eq_mul _ _).symm
  rw [hfun]
  exact MeasureTheory.Integrable.smul (lambda ^ 2) h

/-- Uniform finite energy on `Ico 0 1` transports to uniform finite energy on
`Ico 0 (deadlineOf lambda)`. -/
theorem uniformFiniteEnergy_deadline {lambda : ℝ} (hlambda : 0 < lambda)
    {u : EVelocityField}
    (hu : Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy
      (Ico (0 : ℝ) 1) u) :
    Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy
      (Ico (0 : ℝ) (deadlineOf lambda)) (deadlineVelocity lambda u) := by
  obtain ⟨E, hE, hbound⟩ := hu
  refine ⟨lambda⁻¹ * E, mul_nonneg (le_of_lt (inv_pos.mpr hlambda)) hE, ?_⟩
  intro t ht
  obtain ⟨hint, hle⟩ := hbound _ (sq_mul_mem_preSingularDomain hlambda ht)
  exact ⟨squareIntegrable_deadline hlambda hint, by
    rw [kineticEnergy_deadline lambda hlambda]
    exact mul_le_mul_of_nonneg_left hle (le_of_lt (inv_pos.mpr hlambda))⟩

/-! ## The deadline-package theorem and the `forall T > 0` corollary -/

/-- Every selected unit-deadline candidate rescales to a complete deadline-`T`
profile at `T = lambda^(-2)`: the full `PropertiesAt` bundle. -/
theorem deadlinePackage {u : EVelocityField} {p : EPressureField}
    {f : EVelocityField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    PropertiesAt (deadlineOf lambda) (deadlineVelocity lambda u)
      (deadlinePressure lambda p) (deadlineForce lambda f) :=
  ⟨velocitySmooth_deadline hlambda h.velocity_smooth,
    pressureSmooth_deadline hlambda h.pressure_smooth,
    forceSmooth_deadline h.force_smooth,
    zeroInitial_deadline lambda h.zero_initial_velocity,
    fun _t ht x => divergenceFree_deadline hlambda h.divergence_free ht x,
    fun _t ht x => navierStokes_deadline hlambda h.navier_stokes ht x,
    forceTimeSupport_deadline hlambda h.force_time_support,
    speedUnbounded_deadline hlambda h.speed_unbounded⟩

/-- THEOREM. For every prescribed singular deadline `T > 0`, the selected
constructed Euclidean candidate rescales to a velocity--pressure--force triple
satisfying the deadline-`T` profile: smoothness on `Ico 0 T x univ`, zero
initial velocity, divergence-free on `Ico 0 T`, the unit-viscosity forced
equation on `Ioo 0 T` with the rescaled force, a globally smooth compactly
future-time-supported force, uniform finite energy on `Ico 0 T`, pointwise
speed unbounded as `t -> T-`, and a force nonzero strictly before `T`. This
does not prove unforced breakdown and does not preserve unit spatial periods. -/
theorem exists_deadlineT_profile (T : ℝ) (hT : 0 < T) :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField,
      PropertiesAt T u p f ∧
      ContDiff ℝ ∞ f ∧
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico 0 T) u ∧
      ∃ t ∈ Ioo (0 : ℝ) T, ∃ x : ESpace, f (t, x) ≠ 0 := by
  obtain ⟨eu, ep, ef, hcandidate, hef, henergy⟩ :=
    Navier.Analysis.SelectedCandidateEnergy.selected_compact_candidate_with_energy
  have hnonzero := Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_force_nonzero_before_one hcandidate
  set lambda : ℝ := (Real.sqrt T)⁻¹ with hlambdaDef
  have hlambda : 0 < lambda := inv_pos.mpr (Real.sqrt_pos.mpr hT)
  have hdeadline : deadlineOf lambda = T := by
    rw [deadlineOf]
    show ((Real.sqrt T)⁻¹)⁻¹ * ((Real.sqrt T)⁻¹)⁻¹ = T
    have hinv : (Real.sqrt T)⁻¹⁻¹ = Real.sqrt T := by field_simp
    rw [hinv, Real.mul_self_sqrt hT.le]
  refine ⟨deadlineVelocity lambda eu, deadlinePressure lambda ep,
    deadlineForce lambda ef, ?_, contDiff_deadlineForce hef, ?_, ?_⟩
  · simpa only [hdeadline] using deadlinePackage hcandidate hlambda
  · simpa only [hdeadline] using uniformFiniteEnergy_deadline hlambda henergy
  · simpa only [hdeadline] using forceNonzero_deadline hlambda hnonzero

/-- THEOREM. The exact support-endpoint law: if the unit-deadline force
vanishes from time `T0`, then the deadline-`T` force (at `T = deadlineOf
lambda`) vanishes from `T * T0`; the bound by `T` itself holds exactly when
the original force vanishes by time one. -/
theorem deadlineForce_vanishing_from {f : EVelocityField} {lambda T0 ht : ℝ}
    (hT0 : ∀ t : ℝ, T0 ≤ t → ∀ x : ESpace, f (t, x) = 0)
    (h : deadlineOf lambda * T0 ≤ ht) (x : ESpace) :
    deadlineForce lambda f (ht, x) = 0 := by
  by_cases hlambda : lambda = 0
  · subst hlambda
    rw [deadlineForce_apply]
    rw [show ((0 : ℝ) ^ 3) = 0 by norm_num, zero_smul]
  · rw [deadlineForce_apply]
    have h2 : lambda ^ 2 * (deadlineOf lambda * T0) ≤ lambda ^ 2 * ht :=
      mul_le_mul_of_nonneg_left h (sq_nonneg lambda)
    rw [← mul_assoc, mul_deadlineOf hlambda, one_mul] at h2
    rw [hT0 (lambda ^ 2 * ht) h2, smul_zero]

#print axioms Navier.Analysis.ScaledConstructedBreakdown.residual_deadline
#print axioms Navier.Analysis.ScaledConstructedBreakdown.speedUnbounded_deadline
#print axioms Navier.Analysis.ScaledConstructedBreakdown.kineticEnergy_deadline
#print axioms Navier.Analysis.ScaledConstructedBreakdown.uniformFiniteEnergy_deadline
#print axioms Navier.Analysis.ScaledConstructedBreakdown.deadlinePackage
#print axioms Navier.Analysis.ScaledConstructedBreakdown.exists_deadlineT_profile
#print axioms Navier.Analysis.ScaledConstructedBreakdown.deadlineForce_vanishing_from

end Navier.Analysis.ScaledConstructedBreakdown
