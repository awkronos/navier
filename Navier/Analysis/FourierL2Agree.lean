import Navier.Analysis.WienerSmoothPath
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The `L²` and `L¹` Fourier transforms agree on `L¹ ∩ L²`

Mathlib's `L²` Fourier transform (`MeasureTheory.Lp.fourierTransformₗᵢ`, the isometric
extension from Schwartz space) and the integral transform `𝓕⁻ f ξ = ∫ 𝐞⟪v, ξ⟫ f v dv`
used throughout the Wiener carrier are the SAME operator on `L¹ ∩ L²`, with the same
`2π` normalization (`fourierInv_toLp_ae_eq`).  Consequently the integral transform is an
`L²` isometry there (`lintegral_sq_fourierInv_eq`): Plancherel's identity, not only the
inequality of `WienerPlancherel`.

Route: both sides define the same tempered distribution.  The `L²` side by Mathlib's
`Lp.fourierInv_toTemperedDistribution_eq`; the integral side by the self-adjointness
`∫ 𝓕⁻g · f = ∫ g · 𝓕⁻f` for integrable `f` and Schwartz `g`.  Testing against smooth
compactly supported functions identifies them almost everywhere
(`ae_eq_of_integral_contDiff_smul_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform RealInnerProductSpace ContDiff SchwartzMap

namespace Navier.Analysis.FourierL2Agree

open Navier.Analysis.ContinuousLeiLinSpace (ES)

/-- Self-adjointness of the inverse transform against a Schwartz test function. -/
theorem integral_fourierInv_smul_eq (g : 𝓢(ES, ℂ)) {f : ES → ℂ} (hf : Integrable f) :
    ∫ x, 𝓕⁻ (⇑g) x • f x = ∫ x, g x • 𝓕⁻ f x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ ES)
    Real.continuous_fourierChar (by
      have e : (fun p : ES × ES => ((-innerₗ ES) p.1) p.2) = fun p => -⟪p.1, p.2⟫ := by
        ext p; simp
      rw [e]; exact (continuous_fst.inner continuous_snd).neg) (g.integrable (μ := volume)) hf
  have hflip : (-innerₗ ES).flip = -innerₗ ES := by
    ext v w; simp [real_inner_comm]
  rw [hflip] at h
  exact h

/-- **The two inverse Fourier transforms agree on `L¹ ∩ L²`.** -/
theorem fourierInv_toLp_ae_eq {f : ES → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (⇑(𝓕⁻ (hf2.toLp f) : Lp ℂ 2 (volume : Measure ES))) =ᵐ[volume] 𝓕⁻ f := by
  set F₂ : Lp ℂ 2 (volume : Measure ES) := 𝓕⁻ (hf2.toLp f) with hF₂
  have key : ∀ g : 𝓢(ES, ℂ), ∫ x, g x • F₂ x = ∫ x, g x • 𝓕⁻ f x := by
    intro g
    have h1 : ∫ x, g x • F₂ x = (F₂ : 𝓢'(ES, ℂ)) g :=
      (Lp.toTemperedDistribution_apply F₂ g).symm
    have h2 : (F₂ : 𝓢'(ES, ℂ)) = 𝓕⁻ ((hf2.toLp f : Lp ℂ 2 (volume : Measure ES)) : 𝓢'(ES, ℂ)) :=
      (Lp.fourierInv_toTemperedDistribution_eq _).symm
    rw [h1, h2, TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
    have h3 : ∫ x, (𝓕⁻ g) x • (hf2.toLp f) x = ∫ x, 𝓕⁻ (⇑g) x • f x := by
      refine integral_congr_ae ?_
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx, SchwartzMap.fourierInv_coe]
    rw [h3, integral_fourierInv_smul_eq g hf1]
  have hloc1 : LocallyIntegrable (⇑F₂) volume :=
    (Lp.memLp F₂).locallyIntegrable (by norm_num)
  have hloc2 : LocallyIntegrable (𝓕⁻ f) volume :=
    (Navier.Analysis.WienerSmoothPath.continuous_fourierInv hf1).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hloc1 hloc2 fun g₀ hg₀ hsupp => ?_
  set gc : ES → ℂ := fun x => (g₀ x : ℂ) with hgc
  have hgcd : ContDiff ℝ ∞ gc := Complex.ofRealCLM.contDiff.comp hg₀
  have hgcs : HasCompactSupport gc := hsupp.comp_left Complex.ofReal_zero
  set G : 𝓢(ES, ℂ) := hgcs.toSchwartzMap hgcd with hG
  have hGapp : ∀ x, G x = (g₀ x : ℂ) := fun x => rfl
  have e1 : ∫ x, g₀ x • F₂ x = ∫ x, G x • F₂ x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hGapp, Complex.real_smul, smul_eq_mul]
  have e2 : ∫ x, g₀ x • 𝓕⁻ f x = ∫ x, G x • 𝓕⁻ f x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hGapp, Complex.real_smul, smul_eq_mul]
  rw [e1, e2]
  exact key G

theorem eLpNorm_toLp_eq_lintegral {f : ES → ℂ} :
    eLpNorm f 2 volume = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num

/-- **Plancherel's identity for the integral transform on `L¹ ∩ L²`.** -/
theorem lintegral_sq_fourierInv_eq {f : ES → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ∫⁻ y, ‖𝓕⁻ f y‖ₑ ^ 2 = ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 := by
  set F₂ : Lp ℂ 2 (volume : Measure ES) := 𝓕⁻ (hf2.toLp f)
  have hnorm : ‖F₂‖ = ‖hf2.toLp f‖ :=
    (Lp.fourierTransformₗᵢ ES ℂ).symm.norm_map (hf2.toLp f)
  have hE : eLpNorm (⇑F₂) 2 volume = eLpNorm (⇑(hf2.toLp f)) 2 volume := by
    rw [Lp.norm_def, Lp.norm_def] at hnorm
    exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).mp hnorm
  rw [eLpNorm_congr_ae (fourierInv_toLp_ae_eq hf1 hf2),
    eLpNorm_congr_ae hf2.coeFn_toLp, eLpNorm_toLp_eq_lintegral, eLpNorm_toLp_eq_lintegral] at hE
  have hinj := ENNReal.rpow_left_injective (x := 1 / (2 : ℝ)) (by norm_num) hE
  simp only [ENNReal.rpow_two] at hinj
  exact hinj

end Navier.Analysis.FourierL2Agree

set_option pp.fullNames true in
#check @Navier.Analysis.FourierL2Agree.fourierInv_toLp_ae_eq
set_option pp.fullNames true in
#print axioms Navier.Analysis.FourierL2Agree.fourierInv_toLp_ae_eq
set_option pp.fullNames true in
#print axioms Navier.Analysis.FourierL2Agree.lintegral_sq_fourierInv_eq
