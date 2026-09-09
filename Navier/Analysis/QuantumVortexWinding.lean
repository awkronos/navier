import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Navier.Analysis.QuantumVortexRegularity

/-!
# Quantized circulation for the canonical complex vortex phase

For the standard phase loop `exp (n θ i)`, this file computes the physical
phase current and its circulation exactly.  The quotient by `2π` is the
integer `n`.  The proofs use Mathlib's complex exponential and interval
integral rather than introducing a bespoke degree invariant.
-/

set_option autoImplicit false
noncomputable section

open scoped Interval
open Set MeasureTheory intervalIntegral

namespace Navier.Analysis.QuantumVortexWinding

open Navier.Analysis.QuantumVortexRegularity

/-- A unit-modulus phase with an a priori real circulation parameter. -/
def realChargePhase (kappa theta : ℝ) : ℂ :=
  Complex.exp ((((kappa * theta : ℝ) : ℂ)) * Complex.I)

/-- Closure after one full turn forces, and is forced by, integer charge.
This is the necessity part of circulation quantization. -/
theorem realChargePhase_closes_iff_integer (kappa : ℝ) :
    realChargePhase kappa (2 * Real.pi) = realChargePhase kappa 0 ↔
      ∃ n : ℤ, kappa = n := by
  constructor
  · intro hclose
    have hexp : Complex.exp
        ((((kappa * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I) = 1 := by
      simpa [realChargePhase] using hclose
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    refine ⟨n, ?_⟩
    have hfactor : ((kappa : ℂ) * (2 * Real.pi * Complex.I)) =
        (n : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [← hn]
      push_cast
      ring
    have hnonzero : (2 * Real.pi : ℂ) * Complex.I ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    have hcast : (kappa : ℂ) = (n : ℂ) :=
      mul_right_cancel₀ hnonzero hfactor
    exact_mod_cast hcast
  · rintro ⟨n, rfl⟩
    unfold realChargePhase
    rw [show (((((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I) =
        (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- The standard unit-modulus phase loop of integer charge `n`. -/
def vortexPhase (n : ℤ) (theta : ℝ) : ℂ :=
  circleMap 0 1 ((n : ℝ) * theta)

/-- The actual derivative of the standard vortex phase. -/
def vortexPhaseDerivative (n : ℤ) (theta : ℝ) : ℂ :=
  ((n : ℝ) : ℂ) * Complex.I * vortexPhase n theta

theorem vortexPhase_eq_exp (n : ℤ) (theta : ℝ) :
    vortexPhase n theta = Complex.exp ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I) := by
  simp [vortexPhase, circleMap]

theorem norm_vortexPhase (n : ℤ) (theta : ℝ) :
    ‖vortexPhase n theta‖ = 1 := by
  rw [vortexPhase_eq_exp, Complex.norm_exp]
  simp

theorem vortexPhase_ne_zero (n : ℤ) (theta : ℝ) :
    vortexPhase n theta ≠ 0 := by
  rw [vortexPhase_eq_exp]
  exact Complex.exp_ne_zero _

theorem hasDerivAt_vortexPhase (n : ℤ) (theta : ℝ) :
    HasDerivAt (vortexPhase n) (vortexPhaseDerivative n theta) theta := by
  have hlin : HasDerivAt (fun s : ℝ => (n : ℝ) * s) (n : ℝ) theta := by
    simpa using (hasDerivAt_id theta).const_mul (n : ℝ)
  have h := (hasDerivAt_circleMap 0 1 ((n : ℝ) * theta)).scomp theta hlin
  change HasDerivAt
    ((circleMap 0 1) ∘ fun s : ℝ => (n : ℝ) * s)
    (vortexPhaseDerivative n theta) theta
  have hd : vortexPhaseDerivative n theta =
      (n : ℝ) • (circleMap 0 1 ((n : ℝ) * theta) * Complex.I) := by
    unfold vortexPhaseDerivative vortexPhase
    rw [Complex.real_smul]
    ring
  rw [hd]
  exact h

/-- The unit-density phase current is the integer charge at
every point of the parameter circle. -/
theorem vortex_phase_current_eq_charge (n : ℤ) (theta : ℝ) :
    (star (vortexPhase n theta) * vortexPhaseDerivative n theta).im = n := by
  have hstar : star (vortexPhase n theta) = Complex.exp
      (-((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I)) := by
    rw [vortexPhase_eq_exp, Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hstar]
  unfold vortexPhaseDerivative
  rw [vortexPhase_eq_exp]
  have hcancel : Complex.exp
        (-((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I)) *
      Complex.exp ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hproduct : Complex.exp
        (-((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I)) *
      (((n : ℝ) : ℂ) * Complex.I *
        Complex.exp ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I)) =
      ((n : ℝ) : ℂ) * Complex.I := by
    calc
      _ = ((n : ℝ) : ℂ) * Complex.I *
          (Complex.exp
            (-((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I)) *
           Complex.exp ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  rw [hproduct]
  simp

theorem vortexPhase_two_pi_periodic (n : ℤ) :
    Function.Periodic (vortexPhase n) (2 * Real.pi) := by
  intro theta
  rw [vortexPhase_eq_exp, vortexPhase_eq_exp]
  rw [show ((((n : ℝ) * (theta + 2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      (((n : ℝ) * theta : ℝ) : ℂ) * Complex.I +
        (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- The standard phase current integrates to exactly `2π n`. -/
theorem vortex_phase_circulation (n : ℤ) :
    (∫ theta in (0 : ℝ)..(2 * Real.pi),
      (star (vortexPhase n theta) * vortexPhaseDerivative n theta).im) =
        2 * Real.pi * n := by
  rw [show (fun theta : ℝ =>
      (star (vortexPhase n theta) * vortexPhaseDerivative n theta).im) =
      fun _ => (n : ℝ) by
        funext theta
        exact vortex_phase_current_eq_charge n theta]
  rw [intervalIntegral.integral_const]
  simp

/-- Dividing circulation by one quantum `2π` returns the integer charge. -/
theorem vortex_phase_circulation_quantized (n : ℤ) :
    (∫ theta in (0 : ℝ)..(2 * Real.pi),
      (star (vortexPhase n theta) * vortexPhaseDerivative n theta).im) /
        (2 * Real.pi) = n := by
  rw [vortex_phase_circulation]
  field_simp [Real.pi_ne_zero]

/-- The charge-one phase loop is the restriction of the same smooth
wavefunction `ψ(z)=z` whose Madelung velocity becomes singular at its core. -/
theorem unitVortex_on_phase_loop (theta : ℝ) :
    unitVortex (vortexPhase 1 theta) = vortexPhase 1 theta :=
  rfl

theorem unitVortex_current_on_phase_loop (theta : ℝ) :
    current unitVortex (vortexPhase 1 theta) = vortexPhaseDerivative 1 theta := by
  rw [unitVortex_current]
  unfold vortexPhaseDerivative
  norm_num

/-- Along the unit circle the density is one, so the actual decoded velocity
equals its positively oriented tangent. -/
theorem unitVortex_velocity_on_phase_loop (theta : ℝ) :
    velocity unitVortex (vortexPhase 1 theta) = vortexPhaseDerivative 1 theta := by
  have hρ : density unitVortex (vortexPhase 1 theta) = 1 := by
    unfold density unitVortex
    rw [Complex.normSq_eq_norm_sq, norm_vortexPhase]
    norm_num
  unfold velocity
  rw [hρ, Complex.ofReal_one, div_one, unitVortex_current_on_phase_loop]

/-- Circulation of the actual Madelung velocity of psi(z)=z on the unit
circle, using the Euclidean dot product Re(conj(v)*tangent). -/
theorem unitVortex_velocity_circulation :
    (∫ theta in (0 : ℝ)..(2 * Real.pi),
      (star (velocity unitVortex (vortexPhase 1 theta)) *
        vortexPhaseDerivative 1 theta).re) = 2 * Real.pi := by
  have hpoint : ∀ theta : ℝ,
      (star (velocity unitVortex (vortexPhase 1 theta)) *
        vortexPhaseDerivative 1 theta).re = 1 := by
    intro theta
    rw [unitVortex_velocity_on_phase_loop]
    have hn : ‖vortexPhaseDerivative 1 theta‖ = 1 := by
      simp [vortexPhaseDerivative, norm_vortexPhase]
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hn]
  simp_rw [hpoint]
  simp

/-- Any differentiable real phase lift of the charge-`n` loop has constant
derivative `n`.  This derives the lift increment from the exponential map;
it is not imposed as a premise. -/
theorem hasDerivAt_phaseLift_eq_charge
    (n : ℤ) (α : ℝ → ℝ) (hα : ∀ theta, DifferentiableAt ℝ α theta)
    (hlift : ∀ theta,
      Complex.exp (((α theta : ℝ) : ℂ) * Complex.I) = vortexPhase n theta)
    (theta : ℝ) : HasDerivAt α (n : ℝ) theta := by
  let g : ℝ → ℂ := fun s => Complex.exp (((α s : ℝ) : ℂ) * Complex.I)
  have hcoe : HasDerivAt (fun s : ℝ => ((α s : ℝ) : ℂ))
      ((deriv α theta : ℝ) : ℂ) theta :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt theta (hα theta).hasDerivAt
  have harg : HasDerivAt (fun s : ℝ => ((α s : ℝ) : ℂ) * Complex.I)
      (((deriv α theta : ℝ) : ℂ) * Complex.I) theta :=
    hcoe.mul_const Complex.I
  have hg : HasDerivAt g
      ((((deriv α theta : ℝ) : ℂ) * Complex.I) * g theta) theta := by
    have he := (Complex.hasDerivAt_exp
      (((α theta : ℝ) : ℂ) * Complex.I)).scomp theta harg
    simpa [g, Function.comp_def, smul_eq_mul] using he
  have hgv : HasDerivAt (vortexPhase n)
      ((((deriv α theta : ℝ) : ℂ) * Complex.I) * g theta) theta := by
    exact hg.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => (hlift s).symm)
  have hderiv := hgv.unique (hasDerivAt_vortexPhase n theta)
  have hphase : g theta = vortexPhase n theta := hlift theta
  rw [hphase] at hderiv
  have hcancel : (((deriv α theta : ℝ) : ℂ) * Complex.I) =
      ((n : ℝ) : ℂ) * Complex.I := by
    apply mul_right_cancel₀ (vortexPhase_ne_zero n theta)
    simpa [vortexPhaseDerivative, mul_assoc] using hderiv
  have hi : ((deriv α theta : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    exact hcancel
  have hr : deriv α theta = (n : ℝ) := by
    exact_mod_cast hi
  simpa [hr] using (hα theta).hasDerivAt

/-- A differentiable single-valued real phase that closes after one turn can
only lift the zero-charge loop.  Thus nonzero quantized circulation obstructs
a globally periodic differentiable phase choice. -/
theorem charge_eq_zero_of_differentiable_periodic_phaseLift
    (n : ℤ) (α : ℝ → ℝ) (hα : ∀ theta, DifferentiableAt ℝ α theta)
    (hlift : ∀ theta,
      Complex.exp (((α theta : ℝ) : ℂ) * Complex.I) = vortexPhase n theta)
    (hperiod : α (2 * Real.pi) = α 0) : n = 0 := by
  have hder : ∀ theta, HasDerivAt α (n : ℝ) theta :=
    fun theta => hasDerivAt_phaseLift_eq_charge n α hα hlift theta
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (f := α) (f' := fun _ => (n : ℝ))
    (fun theta _ => hder theta) (_root_.intervalIntegrable_const (c := (n : ℝ)))
  rw [intervalIntegral.integral_const, hperiod, sub_self] at hfund
  have hcast : (n : ℝ) = 0 := by
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    apply mul_left_cancel₀ htwoPi
    simpa [smul_eq_mul] using hfund
  exact_mod_cast hcast

theorem no_differentiable_periodic_phaseLift_of_nonzero
    (n : ℤ) (hn : n ≠ 0) :
    ¬ ∃ α : ℝ → ℝ,
      (∀ theta, DifferentiableAt ℝ α theta) ∧
      (∀ theta,
        Complex.exp (((α theta : ℝ) : ℂ) * Complex.I) = vortexPhase n theta) ∧
      α (2 * Real.pi) = α 0 := by
  rintro ⟨α, hα, hlift, hperiod⟩
  exact hn (charge_eq_zero_of_differentiable_periodic_phaseLift
    n α hα hlift hperiod)

end Navier.Analysis.QuantumVortexWinding
