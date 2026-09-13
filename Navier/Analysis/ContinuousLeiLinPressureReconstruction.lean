import Navier.Analysis.ContinuousLeiLinDissipation
import Mathlib.Analysis.SchwartzMap.Basic

/-!
# Pressure reconstruction on the continuous whole-space Lei--Lin carrier

The named missing primitive of `docs/OPEN_FRONTIER_MAP.md` ("no
pressure-reconstruction primitive exists on the continuous carrier",
2026-09-13).  Given a velocity profile on the repo's actual continuous
whole-space Fourier carrier (`u : ES → ComplexSpace`, the pointwise type
produced by
`ContinuousLeiLinEverywhereRepresentative.everywhereRawRepresentative`),
this module defines the pressure density by the Poisson relation

  `-Δp = ∑ᵢ ∑ⱼ ∂ᵢ∂ⱼ (uᵢ uⱼ)`,  i.e.  `p̂(ξ) = -∑ᵢ ∑ⱼ (ξᵢξⱼ / ‖ξ‖²)(ûᵢ ⋆ ûⱼ)(ξ)`

with the Riesz symbol totalized at `ξ = 0` (`0 / 0 = 0`).  Under the repo's
own Schwartz derivative convention `𝓕(∂ₘ f) = 2πi⟨ξ, m⟩ · 𝓕 f`
(`Navier/Analysis/FourierWeightedPlancherel.lean`), the factor `(2π)²`
multiplies both sides of the Poisson relation and cancels, so the symbol
above is the exact Fourier image of `-Δp = ∑ᵢ ∑ⱼ ∂ᵢ∂ⱼ(uᵢuⱼ)`; the sign
matches `Construction/R3/ComparisonFourierSetup.rieszSymbol`
(`-(ξ i * ξ j) / ‖ξ‖²`).

## Mean-zero normalization (explicit)

The pressure is reconstructed as an `L¹` frequency density, not as an
equivalence class modulo constants: `p̂ ∈ L¹`
(`integrable_norm_continuousPressureFourier`) makes the inverse transform a
bounded function, and the totalized symbol gives `p̂(0) = 0`
(`continuousPressureFourier_zero`), so no Dirac mass at the zero frequency
and hence no additive constant is introduced.  This is the continuous twin
of the lattice zero-mode normalization
`PeriodicPressureRecovery.pressureCoefficient_zero_mode`.  Any other
whole-space pressure representing the same velocity differs from this one
by an additive (time-dependent: a function of time only) constant.

## Which weighted budgets are true on this carrier (truth check)

* `X⁰` (Wiener) mass of `p̂`: bounded by `coordinateX0Mass u ^ 2`
  (`integral_norm_continuousPressureFourier_le`) because the symbol
  satisfies `|ξᵢξⱼ|/‖ξ‖² ≤ 1`.
* `X¹` mass of `p̂`: bounded by
  `2 * coordinateX0Mass u * coordinateX1Mass u`
  (`normX1_continuousPressureFourier_le`) via the frequency-triangle
  allocation `weighted_convolution_mass_le`.
* `X⁻¹`-side budget: the pressure's own `X⁻¹` mass is FALSE in general on
  this carrier and is deliberately not stated.  Take approximate-identity
  bumps `ûᵢ ≈ φ_ε(· - ξ₀)`, `ûⱼ ≈ φ_ε(· + ξ₀)`, `ξ₀ ≠ 0`: the slot masses
  `coordinateXm1Mass`, `coordinateX1Mass` stay bounded, but
  `ûᵢ ⋆ ûⱼ` concentrates at `ξ = 0` and `∫ ‖ξ‖⁻¹|p̂| ≳ ε⁻¹ → ∞`.  The
  bilinear term escapes this obstruction because its symbol has degree `1`
  (`‖ξ‖` cancels `‖ξ‖⁻¹` via `inv_mul_derivative_le`); the Riesz symbol has
  degree `0`.  What does hold, and what the Duhamel feed consumes, is the
  `X⁻¹` mass of `∇p`: each gradient coordinate is bounded by
  `coordinateX0Mass u ^ 2` (`normXm1_continuousPressureGrad_le`), and the
  heat-propagated, time-integrated version
  (`normXm1_continuousPressureDuhamel_grad_le`) matches the exact shape of
  `ContinuousLeiLinDissipation.normXm1_continuousDuhamel_le`, with the
  interpolated `X⁻¹X¹` form matching
  `normXm1_continuousDuhamel_self_le_coordinateXm1X1`.

## Residual

The physical-space distributional identity `∫ p Δφ = -∫ ∑ᵢ ∑ⱼ (uᵢuⱼ) ∂ᵢ∂ⱼφ`
against physical test functions requires the `L¹` inversion bridge plus
transport of the derivative multipliers to the physical side; that is the
downstream pointwise-PDE reconstruction, and the "carrier equality, not the
pointwise PDE" clause of the frontier row.  This module lands the exact
frequency-carrier substitute: the everywhere pointwise Poisson identity
(`continuousPressurePoisson_pointwise`, including `ξ = 0` by totalization)
and its Schwartz-test pairing (`continuousPressurePoisson_pairing`, with the
pairing integrand shown integrable in
`integrable_pairing_continuousPressureFourier`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Navier.Analysis.ContinuousLeiLinPressureReconstruction

open MeasureTheory Set Filter
open scoped BigOperators SchwartzMap Convolution
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation

/-!
## The Riesz symbol on the continuous carrier
-/

/-- A frequency of zero Euclidean norm has every coordinate zero. -/
private theorem coord_eq_zero_of_norm_eq_zero (ξ : ES) (h : ‖ξ‖ = 0) (i : Fin 3) :
    ξ i = 0 := by
  have hle : ‖(ξ i : ℝ)‖ ≤ ‖ξ‖ := PiLp.norm_apply_le ξ i
  rw [← norm_eq_zero]
  exact (hle.trans (le_of_eq h)).antisymm (norm_nonneg _)

/-- The whole-space Riesz--Poisson symbol `ξᵢξⱼ/|ξ|²`, totalized to `0` at
`ξ = 0`.  This is the Fourier multiplier of `-∂ᵢ(-Δ)⁻¹∂ⱼ`, the operator that
turns `uᵢuⱼ` into the corresponding pressure summand. -/
def pressureSymbol (ξ : ES) (i j : Fin 3) : ℝ :=
  ξ i * ξ j / ‖ξ‖ ^ 2

/-- The symbol is a bounded multiplier: `|ξᵢξⱼ/‖ξ‖²| ≤ 1`. -/
theorem pressureSymbol_abs_le (ξ : ES) (i j : Fin 3) :
    |pressureSymbol ξ i j| ≤ 1 := by
  by_cases hz : ‖ξ‖ = 0
  · unfold pressureSymbol
    rw [coord_eq_zero_of_norm_eq_zero ξ hz i, coord_eq_zero_of_norm_eq_zero ξ hz j]
    simp
  · unfold pressureSymbol
    refine div_le_one_of_le ?_ (pow_nonneg (norm_nonneg _) 2)
    rw [abs_mul]
    have hi : |ξ i| ≤ ‖ξ‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le ξ i
    have hj : |ξ j| ≤ ‖ξ‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le ξ j
    calc |ξ i| * |ξ j| ≤ ‖ξ‖ * ‖ξ‖ :=
        mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
      _ = ‖ξ‖ ^ 2 := by ring

/-- The defining cancellation `‖ξ‖² · pressureSymbol ξ i j = ξ i * ξ j`,
valid at every frequency including `ξ = 0` where both sides vanish; this is
the algebraic content of the Poisson relation on the carrier. -/
theorem pressureSymbol_mul_normSq (ξ : ES) (i j : Fin 3) :
    ‖ξ‖ ^ 2 * pressureSymbol ξ i j = ξ i * ξ j := by
  by_cases hz : ‖ξ‖ = 0
  · unfold pressureSymbol
    rw [coord_eq_zero_of_norm_eq_zero ξ hz i, coord_eq_zero_of_norm_eq_zero ξ hz j]
    simp
  · unfold pressureSymbol
    field_simp [hz, pow_ne_zero]

/-!
## The pressure density of a continuous Lei--Lin velocity profile
-/

/-- The Fourier-side pressure density of a velocity profile on the actual
continuous carrier: `p̂ = -∑ᵢ ∑ⱼ (ξᵢξⱼ/‖ξ‖²)(ûᵢ ⋆ ûⱼ)`, the Riesz form of
the Poisson relation `-Δp = ∑ᵢ ∑ⱼ ∂ᵢ∂ⱼ(uᵢuⱼ)`.  The convolution is the
literal Lebesgue convolution on `R³` (`Convolution.convolution` with the
scalar multiplication, matching `rawNavierConvection`).  Mean-zero
normalization: the totalized symbol gives `p̂(0) = 0`, so the reconstructed
density carries no zero-frequency component. -/
noncomputable def continuousPressureFourier (u : ES → ComplexSpace) : ES → ℂ :=
  fun ξ => −∑ i : Fin 3, ∑ j : Fin 3,
    (pressureSymbol ξ i j : ℂ) *
      ((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => u η j)) ξ

/-- The time-dependent pressure source, in the exact shape of
`ContinuousLeiLinTimeDuhamel.continuousNavierSource`. -/
def continuousPressureSource (u : ℝ → ES → ComplexSpace) (t : ℝ) : ES → ℂ :=
  continuousPressureFourier (u t)

/-- The `i`-th Fourier multiplier of `∂ᵢ p`: `ξ ↦ (ξ i : ℂ) · p̂(ξ)`, stored
as a vector profile on the same coordinate carrier as the velocity (up to
the `2πi` derivative phase of `FourierWeightedPlancherel`). -/
noncomputable def continuousPressureGrad (u : ES → ComplexSpace) :
    ES → ComplexSpace :=
  fun ξ i => (ξ i : ℂ) • continuousPressureFourier u ξ

@[simp] theorem continuousPressureGrad_apply (u : ES → ComplexSpace) (ξ : ES)
    (i : Fin 3) :
    continuousPressureGrad u ξ i = (ξ i : ℂ) * continuousPressureFourier u ξ :=
  smul_eq_mul _ _

/-- Normalization: the reconstructed density vanishes at the zero frequency;
no Dirac (constant) component is added. -/
theorem continuousPressureFourier_zero (u : ES → ComplexSpace) :
    continuousPressureFourier u 0 = 0 := by
  unfold continuousPressureFourier
  simp [pressureSymbol]

/-- Degenerate data: the zero velocity profile reconstructs the zero
pressure density. -/
theorem continuousPressureFourier_zero_velocity :
    continuousPressureFourier (0 : ES → ComplexSpace) = 0 := by
  funext ξ
  unfold continuousPressureFourier
  simp [Convolution.convolution]

/-- Pointwise majorant of the pressure density by the coordinate-norm
convolutions: the Riesz symbol contributes no growth. -/
theorem norm_continuousPressureFourier_le (u : ES → ComplexSpace) (ξ : ES) :
    ‖continuousPressureFourier u ξ‖ ≤
      ∑ i : Fin 3, ∑ j : Fin 3,
        convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ := by
  unfold continuousPressureFourier
  refine le_trans (norm_neg _) (Finset.norm_sum_le _)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  calc ‖(pressureSymbol ξ i j : ℂ) *
        ((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => u η j)) ξ‖
      _ = ‖(pressureSymbol ξ i j : ℂ)‖ *
            ‖((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (fun η => u η j)) ξ‖ := norm_mul _ _
      _ ≤ 1 * ‖((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun η => u η j)) ξ‖ :=
          mul_le_mul_of_nonneg_right (by
            rw [Complex.norm_real]
            exact pressureSymbol_abs_le ξ i j) (norm_nonneg _)
      _ ≤ convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ := by
          rw [one_mul]
          exact norm_complex_convolution_le (fun η => u η i) (fun η => u η j) ξ

/-- The pressure density is a.e. strongly measurable once every velocity
coordinate is a.e. strongly measurable and integrable; the route is the
coordinatewise `L¹` convolution, exactly as in
`continuousNavierBilinear_aestronglyMeasurable`. -/
theorem aesstronglyMeasurable_continuousPressureFourier
    (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) :
    AEStronglyMeasurable (continuousPressureFourier u) := by
  have hconv : ∀ i j : Fin 3, AEStronglyMeasurable
      ((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => u η j)) := by
    intro i j
    exact ((integrable_norm_iff (hu i)).mp (hu0 i)).integrable_convolution
      (ContinuousLinearMap.mul ℂ ℂ)
        ((integrable_norm_iff (hu j)).mp (hu0 j)) |>.aestronglyMeasurable
  have hsymb : ∀ i j : Fin 3,
      AEStronglyMeasurable (fun ξ : ES => (pressureSymbol ξ i j : ℂ)) := by
    intro i j
    have heq : (fun ξ : ES => Complex.ofReal (ξ i * ξ j) *
        (Complex.ofReal (‖ξ‖ ^ 2))⁻¹) = (fun ξ : ES => (pressureSymbol ξ i j : ℂ)) := by
      funext ξ
      simp [pressureSymbol]
    rw [← heq]
    have hnum : AEStronglyMeasurable (fun ξ : ES => Complex.ofReal (ξ i * ξ j)) :=
      (Complex.continuous_ofReal.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).mul
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j))).aestronglyMeasurable
    have hden : AEStronglyMeasurable (fun ξ : ES => (Complex.ofReal (‖ξ‖ ^ 2))⁻¹) :=
      (Complex.continuous_ofReal.comp (continuous_norm.pow 2)).aestronglyMeasurable.inv₀
    exact hnum.mul hden
  unfold continuousPressureFourier
  refine AEStronglyMeasurable.neg (AEStronglyMeasurable.sum Finset.univ ?_)
  intro i hi
  exact AEStronglyMeasurable.sum Finset.univ fun j hj =>
    (hsymb i j).mul (hconv i j)

/-- The pressure density is integrable once every velocity coordinate is
integrable; this is what makes the reconstruction an `L¹` representative
(hence a bounded function after inversion) rather than a quotient. -/
theorem integrable_norm_continuousPressureFourier (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) :
    Integrable (fun ξ : ES => ‖continuousPressureFourier u ξ‖) := by
  have hsum : Integrable (fun ξ : ES => ∑ i : Fin 3, ∑ j : Fin 3,
      convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ =>
        integrable_scalar_convolution _ _ (hu0 i) (hu0 j)
  refine hsum.mono' (aesstronglyMeasurable_continuousPressureFourier u hu hu0).norm ?_
  filter_upwards with ξ
  rw [norm_norm]
  exact norm_continuousPressureFourier_le u ξ

/-!
## The `X⁰` and `X¹` budgets of the pressure density
-/

/-- The weighted norm of a convolution of nonnegative profiles is integrable;
this packages the internal majorization step of
`weighted_convolution_mass_le` for reuse. -/
private theorem integrable_norm_weighted_convolution (f g : ES → ℝ)
    (hf0 : Integrable f) (hg0 : Integrable g)
    (hf1 : Integrable (fun η : ES => ‖η‖ * f η))
    (hg1 : Integrable (fun η : ES => ‖η‖ * g η))
    (hfn : ∀ η, 0 ≤ f η) (hgn : ∀ η, 0 ≤ g η) :
    Integrable (fun ξ : ES => ‖ξ‖ * convolution f g ξ) := by
  have hae := ae_frequency_weighted_convolution_pointwise f g hf0 hg0 hf1 hg1 hfn hgn
  have hconv := integrable_scalar_convolution f g hf0 hg0
  have hrhs : Integrable (fun ξ : ES => convolution (fun η : ES => ‖η‖ * f η) g ξ +
      convolution f (fun η : ES => ‖η‖ * g η) ξ) :=
    (integrable_scalar_convolution (fun η : ES => ‖η‖ * f η) g hf1 hg0).add
      (integrable_scalar_convolution f (fun η : ES => ‖η‖ * g η) hf0 hg1)
  have hconv_nonneg : ∀ ξ : ES, 0 ≤ convolution f g ξ := by
    intro ξ
    change 0 ≤ ∫ η : ES, f η * g (ξ - η)
    exact integral_nonneg fun η => mul_nonneg (hfn η) (hgn (ξ - η))
  refine hrhs.mono'
    (continuous_norm.aestronglyMeasurable.mul hconv.aestronglyMeasurable) ?_
  filter_upwards [hae] with ξ hξ
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg ξ) (hconv_nonneg ξ))]
  exact hξ

/-- The coordinate-sum mass identity: `∫ ∑ᵢ ∑ⱼ conv(‖uᵢ‖,‖uⱼ‖) =
(∑ᵢ ∫ ‖uᵢ‖)² = coordinateX0Mass²`, the continuous analogue of the lattice
mass factorization. -/
private theorem sum_convolution_eq_coordinateX0Mass_sq (u : ES → ComplexSpace)
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) :
    (∫ ξ : ES, ∑ i : Fin 3, ∑ j : Fin 3,
        convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ) =
      coordinateX0Mass u ^ 2 := by
  unfold coordinateX0Mass
  have hinner : ∀ i : Fin 3, Integrable (fun ξ : ES => ∑ j : Fin 3,
      convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ) := by
    intro i
    refine integrable_finsetSum Finset.univ ?_
    intro j hj
    exact integrable_scalar_convolution _ _ (hu0 i) (hu0 j)
  calc (∫ ξ : ES, ∑ i : Fin 3, ∑ j : Fin 3,
        convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ)
      _ = ∑ i : Fin 3, ∫ ξ : ES, ∑ j : Fin 3,
            convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ :=
        integral_finsetSum Finset.univ hinner
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ ξ : ES,
            convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ := by
        refine Finset.sum_congr rfl fun i _ =>
          integral_finsetSum Finset.univ (fun j _ =>
            integrable_scalar_convolution _ _ (hu0 i) (hu0 j))
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
            (∫ η : ES, ‖u η i‖) * (∫ η : ES, ‖u η j‖) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          normX0_convolution_eq (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖)
            (hu0 i) (hu0 j)
      _ = (∑ i : Fin 3, ∫ η : ES, ‖u η i‖) *
            (∑ j : Fin 3, ∫ η : ES, ‖u η j‖) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
      _ = (∑ i : Fin 3, ∫ ξ : ES, ‖u ξ i‖) ^ 2 := by ring

/-- The `X⁰` (Wiener) budget of the pressure density:
`∫ ‖p̂‖ ≤ coordinateX0Mass u ^ 2`. -/
theorem integral_norm_continuousPressureFourier_le (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) :
    (∫ ξ : ES, ‖continuousPressureFourier u ξ‖) ≤ coordinateX0Mass u ^ 2 := by
  have hsum : Integrable (fun ξ : ES => ∑ i : Fin 3, ∑ j : Fin 3,
      convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ =>
        integrable_scalar_convolution _ _ (hu0 i) (hu0 j)
  refine le_trans (integral_mono (integrable_norm_continuousPressureFourier u hu hu0)
    hsum (fun ξ => norm_continuousPressureFourier_le u ξ)) ?_
  rw [sum_convolution_eq_coordinateX0Mass_sq u hu0]

/-- The first-moment norm density of the pressure is integrable. -/
theorem integrable_normX1_continuousPressureFourier (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖))
    (hu1 : ∀ j : Fin 3, Integrable (fun η : ES => ‖η‖ * ‖u η j‖)) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖continuousPressureFourier u ξ‖) := by
  have hsum : Integrable (fun ξ : ES => ∑ i : Fin 3, ∑ j : Fin 3,
      ‖ξ‖ * convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ =>
        integrable_norm_weighted_convolution (fun η : ES => ‖u η i‖)
          (fun η : ES => ‖u η j‖) (hu0 i) (hu0 j) (hu1 i) (hu1 j)
          (fun η => norm_nonneg _) (fun η => norm_nonneg _)
  refine hsum.mono'
    (continuous_norm.aestronglyMeasurable).mul
      (integrable_norm_continuousPressureFourier u hu hu0).aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [norm_mul, norm_norm, norm_norm, ← Finset.sum_mul, ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_left (norm_continuousPressureFourier_le u ξ)
    (norm_nonneg ξ)

/-- The `X¹` budget of the pressure density:
`∫ ‖ξ‖ ‖p̂‖ ≤ 2 · coordinateX0Mass u · coordinateX1Mass u`.  The factor `2`
counts the two derivative allocations of the frequency triangle. -/
theorem normX1_continuousPressureFourier_le (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖))
    (hu1 : ∀ j : Fin 3, Integrable (fun η : ES => ‖η‖ * ‖u η j‖)) :
    normX1 (continuousPressureFourier u) ≤
      2 * coordinateX0Mass u * coordinateX1Mass u := by
  unfold coordinateX0Mass coordinateX1Mass
  unfold normX1
  have hconv : ∀ i j : Fin 3, Integrable (fun ξ : ES =>
      ‖ξ‖ * convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ) := by
    intro i j
    exact integrable_norm_weighted_convolution (fun η : ES => ‖u η i‖)
      (fun η : ES => ‖u η j‖) (hu0 i) (hu0 j) (hu1 i) (hu1 j)
      (fun η => norm_nonneg _) (fun η => norm_nonneg _)
  have hsum : Integrable (fun ξ : ES => ∑ i : Fin 3, ∑ j : Fin 3,
      ‖ξ‖ * convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hconv i j
  calc (∫ ξ : ES, ‖ξ‖ * ‖continuousPressureFourier u ξ‖)
      _ ≤ ∫ ξ : ES, ∑ i : Fin 3, ∑ j : Fin 3,
            ‖ξ‖ * convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ :=
        integral_mono (integrable_normX1_continuousPressureFourier u hu hu0 hu1)
          hsum (fun ξ => by
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            exact mul_le_mul_of_nonneg_left (norm_continuousPressureFourier_le u ξ)
              (norm_nonneg ξ))
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ ξ : ES, ‖ξ‖ *
            convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ := by
        rw [integral_finsetSum Finset.univ (fun i _ =>
            integrable_finsetSum Finset.univ (fun j _ => hconv i j)),
          Finset.sum_congr rfl (fun i _ => integral_finsetSum Finset.univ (hconv i))]
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
            ((∫ η : ES, ‖η‖ * ‖u η i‖) * (∫ η : ES, ‖u η j‖) +
              (∫ η : ES, ‖u η i‖) * (∫ η : ES, ‖η‖ * ‖u η j‖)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          weighted_convolution_mass_le (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖)
            (hu0 i) (hu0 j) (hu1 i) (hu1 j)
            (fun η => norm_nonneg _) (fun η => norm_nonneg _)
      _ = (∑ i : Fin 3, ∫ η : ES, ‖η‖ * ‖u η i‖) *
            (∑ j : Fin 3, ∫ η : ES, ‖u η j‖) +
          (∑ i : Fin 3, ∫ η : ES, ‖u η i‖) *
            (∑ j : Fin 3, ∫ η : ES, ‖η‖ * ‖u η j‖) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      _ = 2 * (∑ i : Fin 3, ∫ η : ES, ‖η‖ * ‖u η i‖) *
            (∑ j : Fin 3, ∫ η : ES, ‖u η j‖) := by ring
