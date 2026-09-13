import Navier.Analysis.ContinuousLeiLinDissipation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

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
    rw [abs_div, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
    have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr (mt norm_eq_zero.mpr hz)
    refine (div_le_one₀ (pow_pos hpos 2)).mpr ?_
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
  fun ξ => -∑ i : Fin 3, ∑ j : Fin 3,
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
  simp [MeasureTheory.convolution]

/-- Pointwise majorant of the pressure density by the coordinate-norm
convolutions: the Riesz symbol contributes no growth. -/
theorem norm_continuousPressureFourier_le (u : ES → ComplexSpace) (ξ : ES) :
    ‖continuousPressureFourier u ξ‖ ≤
      ∑ i : Fin 3, ∑ j : Fin 3,
        convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ := by
  unfold continuousPressureFourier
  rw [norm_neg]
  refine (norm_sum_le Finset.univ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (norm_sum_le Finset.univ _).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
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
      simp [pressureSymbol, div_eq_mul_inv]
    rw [← heq]
    have hnum : AEStronglyMeasurable (fun ξ : ES => Complex.ofReal (ξ i * ξ j)) :=
      (Complex.continuous_ofReal.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).mul
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j))).aestronglyMeasurable
    have hden : AEStronglyMeasurable (fun ξ : ES => (Complex.ofReal (‖ξ‖ ^ 2))⁻¹) :=
      (Complex.continuous_ofReal.comp (continuous_norm.pow 2)).aestronglyMeasurable.inv₀
    exact hnum.mul hden
  unfold continuousPressureFourier
  refine AEStronglyMeasurable.neg ?_
  exact Finset.aestronglyMeasurable_sum Finset.univ fun i _ =>
    Finset.aestronglyMeasurable_sum Finset.univ fun j _ =>
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

/-- The finite double-sum expansion of a square: `(∑ a)² = ∑ᵢ ∑ⱼ aᵢaⱼ`. -/
private theorem sq_eq_sum_double (a : Fin 3 → ℝ) :
    (∑ i : Fin 3, a i) ^ 2 = ∑ i : Fin 3, ∑ j : Fin 3, a i * a j := by
  simp only [pow_two, ← Finset.sum_mul_sum]

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
        integral_finsetSum Finset.univ (fun i _ => hinner i)
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
      _ = (∑ i : Fin 3, ∫ η : ES, ‖u η i‖) ^ 2 :=
        (sq_eq_sum_double (fun i => ∫ η : ES, ‖u η i‖)).symm
      _ = (∑ i : Fin 3, ∫ ξ : ES, ‖u ξ i‖) ^ 2 := rfl

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
    (continuous_norm.aestronglyMeasurable.mul
      ((integrable_norm_continuousPressureFourier u hu hu0).aestronglyMeasurable)) ?_
  filter_upwards with ξ
  rw [norm_mul, norm_norm, norm_norm]
  simp only [← Finset.mul_sum]
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
  show (∫ ξ : ES, ‖ξ‖ * ‖continuousPressureFourier u ξ‖) ≤
      2 * (∑ i : Fin 3, ∫ ξ : ES, ‖u ξ i‖) *
        (∑ i : Fin 3, ∫ ξ : ES, ‖ξ‖ * ‖u ξ i‖)
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
            simp only [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (norm_continuousPressureFourier_le u ξ)
              (norm_nonneg ξ))
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ ξ : ES, ‖ξ‖ *
            convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ := by
        rw [integral_finsetSum Finset.univ (fun i _ =>
            integrable_finsetSum Finset.univ (fun j _ => hconv i j)),
          Finset.sum_congr rfl (fun i _ =>
            integral_finsetSum Finset.univ (fun j _ => hconv i j))]
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
        simp only [← Finset.sum_mul_sum, Finset.sum_add_distrib]
      _ = 2 * (∑ i : Fin 3, ∫ ξ : ES, ‖u ξ i‖) *
            (∑ i : Fin 3, ∫ ξ : ES, ‖ξ‖ * ‖u ξ i‖) := by
        ring

/-!
## The `X⁻¹`-side budget: the gradient of the pressure
-/

/-- Weighted pointwise bound for one pressure-gradient coordinate:
`‖ξ‖⁻¹ ‖(ξ i)·p̂(ξ)‖ ≤ Σ conv`.  The coordinate `ξ i` contributes the
degree-`1` factor that cancels the `X⁻¹` weight (`inv_mul_derivative_le`):
the `X⁻¹`-side statement is true for `∇p` and, per the header truth check,
false for `p`. -/
theorem normXm1_continuousPressureGrad_pointwise (u : ES → ComplexSpace) (ξ : ES)
    (i : Fin 3) :
    ‖ξ‖⁻¹ * ‖continuousPressureGrad u ξ i‖ ≤
      ∑ j : Fin 3, ∑ k : Fin 3,
        convolution (fun η : ES => ‖u η j‖) (fun η : ES => ‖u η k‖) ξ := by
  have hcoord : ‖continuousPressureGrad u ξ i‖ =
      ‖(ξ i : ℂ)‖ * ‖continuousPressureFourier u ξ‖ := by
    rw [continuousPressureGrad_apply, norm_mul]
  have hle : ‖ξ‖⁻¹ * (‖(ξ i : ℂ)‖ * ‖continuousPressureFourier u ξ‖) ≤
      ‖ξ‖⁻¹ * (‖ξ‖ * ‖continuousPressureFourier u ξ‖) := by
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (norm_nonneg ξ))
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Complex.norm_real]
    exact PiLp.norm_apply_le ξ i
  calc ‖ξ‖⁻¹ * ‖continuousPressureGrad u ξ i‖
      _ = ‖ξ‖⁻¹ * (‖(ξ i : ℂ)‖ * ‖continuousPressureFourier u ξ‖) := by rw [hcoord]
      _ ≤ ‖ξ‖⁻¹ * (‖ξ‖ * ‖continuousPressureFourier u ξ‖) := hle
      _ ≤ ‖continuousPressureFourier u ξ‖ :=
          inv_mul_derivative_le ‖ξ‖ ‖continuousPressureFourier u ξ‖
            (norm_nonneg ξ) (norm_nonneg _)
      _ ≤ ∑ j : Fin 3, ∑ k : Fin 3,
            convolution (fun η : ES => ‖u η j‖) (fun η : ES => ‖u η k‖) ξ :=
          norm_continuousPressureFourier_le u ξ

/-- The `X⁻¹` budget of one pressure-gradient coordinate:
`∫ ‖ξ‖⁻¹ ‖(ξ i)·p̂(ξ)‖ ≤ coordinateX0Mass u ^ 2`.  This is the fixed-time
`X⁻¹`-side estimate that the Duhamel feed below consumes. -/
theorem normXm1_continuousPressureGrad_le (u : ES → ComplexSpace) (i : Fin 3)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) :
    normXm1 (fun ξ : ES => continuousPressureGrad u ξ i) ≤
      coordinateX0Mass u ^ 2 := by
  have hsum : Integrable (fun ξ : ES => ∑ j : Fin 3, ∑ k : Fin 3,
      convolution (fun η : ES => ‖u η j‖) (fun η : ES => ‖u η k‖) ξ) :=
    integrable_finsetSum Finset.univ fun j _ =>
      integrable_finsetSum Finset.univ fun k _ =>
        integrable_scalar_convolution _ _ (hu0 j) (hu0 k)
  have hmeas : AEStronglyMeasurable (fun ξ : ES =>
      ‖ξ‖⁻¹ * ‖continuousPressureGrad u ξ i‖) := by
    have hc : AEStronglyMeasurable (fun ξ : ES => (ξ i : ℂ)) :=
      (Complex.continuous_ofReal.comp
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i)).aestronglyMeasurable
    have h1 : AEStronglyMeasurable (fun ξ : ES => ‖continuousPressureGrad u ξ i‖) := by
      refine ((hc.mul
        (aesstronglyMeasurable_continuousPressureFourier u hu hu0)).norm.congr ?_)
      filter_upwards with ξ
      simp only [continuousPressureGrad_apply, Pi.mul_apply]
    refine (continuous_norm.aestronglyMeasurable.inv₀).mul h1
  have hint : Integrable (fun ξ : ES =>
      ‖ξ‖⁻¹ * ‖continuousPressureGrad u ξ i‖) :=
    hsum.mono' hmeas (by
      filter_upwards with ξ
      rw [norm_mul, norm_inv, norm_norm, norm_norm]
      exact normXm1_continuousPressureGrad_pointwise u ξ i)
  unfold normXm1
  refine le_trans (integral_mono hint hsum
    (fun ξ => normXm1_continuousPressureGrad_pointwise u ξ i)) ?_
  rw [sum_convolution_eq_coordinateX0Mass_sq u hu0]

/-!
## The Poisson relation on the carrier
-/

/-- Pointwise Poisson identity on the continuous carrier, valid at every
frequency (totalization makes both sides vanish at `ξ = 0`):
`‖ξ‖²·p̂(ξ) = -∑ᵢ ∑ⱼ ξᵢξⱼ·(ûᵢ ⋆ ûⱼ)(ξ)`, the Fourier image of
`-Δp = ∑ᵢ ∑ⱼ ∂ᵢ∂ⱼ(uᵢuⱼ)` under the repo's derivative convention. -/
theorem continuousPressurePoisson_pointwise (u : ES → ComplexSpace) (ξ : ES) :
    (‖ξ‖ ^ 2 : ℂ) * continuousPressureFourier u ξ =
      -∑ i : Fin 3, ∑ j : Fin 3,
        (ξ i * ξ j : ℂ) *
          ((fun η : ES => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun η : ES => u η j)) ξ := by
  unfold continuousPressureFourier
  rw [mul_neg]
  refine neg_inj.mpr ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, pow_two, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← pow_two, pressureSymbol_mul_normSq, Complex.ofReal_mul]

/-- The Poisson pairing integrand is integrable against every Schwartz
frequency test: `‖ξ‖²·p̂·φ` is dominated by `C · Σ conv`, where `C` bounds
`‖ξ‖²‖φ ξ‖` by Schwartz decay. -/
theorem integrable_pairing_continuousPressureFourier (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖))
    (φ : SchwartzMap ES ℂ) :
    Integrable (fun ξ : ES =>
      (‖ξ‖ ^ 2 : ℂ) * continuousPressureFourier u ξ * φ ξ) := by
  obtain ⟨C, hC0, hC⟩ := φ.decay 2 0
  have hCφ : ∀ ξ : ES, ‖ξ‖ ^ 2 * ‖φ ξ‖ ≤ C := fun ξ => by simpa using hC ξ
  have hsum : Integrable (fun ξ : ES => ∑ i : Fin 3, ∑ j : Fin 3,
      convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ =>
        integrable_scalar_convolution _ _ (hu0 i) (hu0 j)
  have hmaj : Integrable (fun ξ : ES =>
      C * ∑ i : Fin 3, ∑ j : Fin 3,
        convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ) := by
    convert hsum.const_mul C using 1
  have hq : AEStronglyMeasurable (fun ξ : ES => (‖ξ‖ ^ 2 : ℂ)) :=
    ((Complex.continuous_ofReal.pow 2).comp continuous_norm).aestronglyMeasurable
  have hp : AEStronglyMeasurable (continuousPressureFourier u) :=
    aesstronglyMeasurable_continuousPressureFourier u hu hu0
  have hmeas : AEStronglyMeasurable (fun ξ : ES =>
      (‖ξ‖ ^ 2 : ℂ) * continuousPressureFourier u ξ * φ ξ) :=
    (hq.mul hp).mul φ.continuous.aestronglyMeasurable
  refine hmaj.mono' hmeas ?_
  filter_upwards with ξ
  calc ‖(‖ξ‖ ^ 2 : ℂ) * continuousPressureFourier u ξ * φ ξ‖
      _ = ‖ξ‖ ^ 2 * ‖continuousPressureFourier u ξ‖ * ‖φ ξ‖ := by
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, norm_norm]
      _ = (‖ξ‖ ^ 2 * ‖φ ξ‖) * ‖continuousPressureFourier u ξ‖ := by ring
      _ ≤ C * ‖continuousPressureFourier u ξ‖ :=
          mul_le_mul_of_nonneg_right (hCφ ξ) (norm_nonneg _)
      _ ≤ C * ∑ i : Fin 3, ∑ j : Fin 3,
            convolution (fun η : ES => ‖u η i‖) (fun η : ES => ‖u η j‖) ξ :=
          mul_le_mul_of_nonneg_left (norm_continuousPressureFourier_le u ξ) hC0.le

/-- Distributional Poisson identity on the frequency carrier: against a
Schwartz test density `φ` on `R³`,
`∫ ‖ξ‖²·p̂·φ = ∫ (-∑ᵢ ∑ⱼ ξᵢξⱼ·(ûᵢ ⋆ ûⱼ))·φ`, whose left pairing integrand
is integrable (`integrable_pairing_continuousPressureFourier`; the right
side by congruence with the pointwise identity).  This is the whole-space,
no-lattice replacement of the periodic `∫ p Δφ` pairing; the physical-space
identity `∫ p Δφ = -∫ ∑ᵢ ∑ⱼ (uᵢuⱼ) ∂ᵢ∂ⱼφ` is the downstream inversion
residual. -/
theorem continuousPressurePoisson_pairing (u : ES → ComplexSpace)
    (φ : SchwartzMap ES ℂ) :
    (∫ ξ : ES, (‖ξ‖ ^ 2 : ℂ) * continuousPressureFourier u ξ * φ ξ) =
      ∫ ξ : ES,
        (-∑ i : Fin 3, ∑ j : Fin 3,
          (ξ i * ξ j : ℂ) *
            ((fun η : ES => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (fun η : ES => u η j)) ξ) * φ ξ :=
  integral_congr_ae (Eventually.of_forall fun _ => by
    simp only [continuousPressurePoisson_pointwise])

/-!
## The Duhamel-shaped `X⁻¹` feed
-/

/-- The pressure-gradient Duhamel term has finite `X⁻¹` mass bounded by the
time integral of the coordinate `X⁰` masses: the heat propagator first
contracts each `X⁻¹` mass and the mass then passes through the time integral
via the Fubini bridge `normXm1_setIntegral_le`, exactly as in
`ContinuousLeiLinDissipation.normXm1_continuousDuhamel_le`.  The joint and
per-time integrabilities are explicit hypotheses, matching that file's
convention. -/
theorem normXm1_continuousPressureDuhamel_grad_le
    (u : ℝ → ES → ComplexSpace) (ν t : ℝ) (i : Fin 3) (hν : 0 < ν)
    (hu : ∀ s j, AEStronglyMeasurable (fun η : ES => u s η j))
    (hu0 : ∀ s j, Integrable (fun η : ES => ‖u s η j‖))
    (hb : Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) •
          heatMode ν (t - p.2)
            (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u p.2 ζ) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : Integrable (fun s : ℝ => normXm1 (heatMode ν (t - s)
        (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖(ξ i : ℂ) • continuousPressureSource u s ξ‖))
    (h0 : Integrable (fun s : ℝ => coordinateX0Mass (u s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t))) :
    normXm1 (fun ξ : ES => ∫ s in Icc (0 : ℝ) t,
        heatMode ν (t - s)
          (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ) ξ) ≤
      ∫ s in Icc (0 : ℝ) t, coordinateX0Mass (u s) ^ 2 := by
  refine le_trans
    (normXm1_setIntegral_le (fun s : ℝ =>
        fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ) ν t hb) ?_
  refine integral_mono_ae hf h0 ?_
  filter_upwards [ae_restrict_mem (isClosed_Icc.measurableSet)] with s hs
  calc normXm1 (heatMode ν (t - s)
          (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ))
      _ ≤ normXm1 (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ) :=
          normXm1_heatMode_le (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ)
            (hb0 s hs) ν (t - s) hν (sub_nonneg.mpr hs.2)
      _ ≤ coordinateX0Mass (u s) ^ 2 :=
          normXm1_continuousPressureGrad_le (u s) i (hu s) (hu0 s)

/-- The Duhamel-shaped `X⁻¹` feed written in the interpolated `X⁻¹X¹`
coordinate masses — the exact continuous-carrier analogue of
`ContinuousLeiLinDissipation.normXm1_continuousDuhamel_self_le_coordinateXm1X1`
— obtained by composing `normXm1_continuousPressureDuhamel_grad_le` with the
finite-coordinate Cauchy--Schwarz interpolation
`coordinateX0Mass_sq_le_coordinateXm1Mass_mul_coordinateX1Mass`. -/
theorem normXm1_continuousPressureDuhamel_grad_le_coordinateXm1X1
    (u : ℝ → ES → ComplexSpace) (ν t : ℝ) (i : Fin 3) (hν : 0 < ν)
    (hu : ∀ s j, AEStronglyMeasurable (fun η : ES => u s η j))
    (hu0 : ∀ s j, Integrable (fun η : ES => ‖u s η j‖))
    (hum1 : ∀ s j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u s η j‖))
    (hu1 : ∀ s j, Integrable (fun η : ES => ‖η‖ * ‖u s η j‖))
    (hb : Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) •
          heatMode ν (t - p.2)
            (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u p.2 ζ) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : Integrable (fun s : ℝ => normXm1 (heatMode ν (t - s)
        (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖(ξ i : ℂ) • continuousPressureSource u s ξ‖))
    (h0sq : IntegrableOn (fun s : ℝ => coordinateX0Mass (u s) ^ 2)
        (Icc (0 : ℝ) t))
    (hmixed : IntegrableOn (fun s : ℝ =>
        coordinateXm1Mass (u s) * coordinateX1Mass (u s)) (Icc (0 : ℝ) t)) :
    normXm1 (fun ξ : ES => ∫ s in Icc (0 : ℝ) t,
        heatMode ν (t - s)
          (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ) ξ) ≤
      ∫ s in Icc (0 : ℝ) t, coordinateXm1Mass (u s) * coordinateX1Mass (u s) := by
  refine le_trans (normXm1_continuousPressureDuhamel_grad_le
    u ν t i hν hu hu0 hb hf hb0 h0sq) ?_
  refine integral_mono_ae h0sq hmixed ?_
  filter_upwards [ae_restrict_mem (isClosed_Icc.measurableSet)] with s hs
  exact coordinateX0Mass_sq_le_coordinateXm1Mass_mul_coordinateX1Mass (u s)
    (hum1 s) (hu1 s)

end Navier.Analysis.ContinuousLeiLinPressureReconstruction

#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.pressureSymbol
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.pressureSymbol_abs_le
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.pressureSymbol_mul_normSq
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressureFourier
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressureSource
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressureGrad
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressureGrad_apply
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressureFourier_zero
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressureFourier_zero_velocity
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.norm_continuousPressureFourier_le
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.aesstronglyMeasurable_continuousPressureFourier
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.integrable_norm_continuousPressureFourier
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.integral_norm_continuousPressureFourier_le
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.integrable_normX1_continuousPressureFourier
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.normX1_continuousPressureFourier_le
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureGrad_pointwise
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureGrad_le
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressurePoisson_pointwise
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.integrable_pairing_continuousPressureFourier
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressurePoisson_pairing
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureDuhamel_grad_le
#check @Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureDuhamel_grad_le_coordinateXm1X1

#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.pressureSymbol_abs_le
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.pressureSymbol_mul_normSq
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressureFourier_zero
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressureFourier_zero_velocity
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.norm_continuousPressureFourier_le
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.aesstronglyMeasurable_continuousPressureFourier
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.integrable_norm_continuousPressureFourier
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.integral_norm_continuousPressureFourier_le
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.integrable_normX1_continuousPressureFourier
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.normX1_continuousPressureFourier_le
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureGrad_pointwise
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureGrad_le
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressurePoisson_pointwise
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.integrable_pairing_continuousPressureFourier
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressurePoisson_pairing
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureDuhamel_grad_le
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureDuhamel_grad_le_coordinateXm1X1
