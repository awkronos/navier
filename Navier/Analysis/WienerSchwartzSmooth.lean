import Navier.Analysis.WienerMildGood
import Navier.Analysis.WienerSchwartzLocal

/-!
# Joint smoothness of the large-data local Wiener solution from Schwartz data

For every Schwartz velocity `u₀`, viscosity `ν > 0` and horizon `T > 0` with
`10⁴ T ‖𝓕 u₀‖²_{L¹} ≤ ν`, the Wiener-carrier fixed point is represented by a
pointwise fixed point `w` of the repository's mild map with datum
`fourierDatum u₀`, and each physical coordinate `(t, x) ↦ physicalCoord (w t) i x`
is `C^∞` jointly on `[0, T) × ℝ³` (`exists_smooth_wienerSolution`).

Scope: the pointwise Navier–Stokes identity in physical variables (with the
`2π` convention of `WienerConvention`), the pressure, reality and energy clauses
of `SolvesBefore` are not claimed here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff

namespace Navier.Analysis.WienerSchwartzSmooth

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.FourierMajorant
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerLocalMild
open Navier.Analysis.WienerMoments
open Navier.Analysis.WienerPointwiseBridge
open Navier.Analysis.WienerSchwartzLocal
open Navier.Analysis.WienerPointwiseODE
open Navier.Analysis.WienerMildGood

theorem measurable_fourierDatum (u₀ : Navier.SchwartzVelocity) :
    Measurable (fourierDatum u₀) :=
  measurable_pi_lambda _ fun i =>
    ((𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).continuous).measurable

theorem lintegral_weight_le_sum (n : ℕ) (f : ES → ComplexSpace) (hf : Measurable f) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖f ξ‖ₑ ≤
      ∑ i : Fin 3, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖f ξ i‖ₑ := by
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Measurable fun ξ : ES =>
      ENNReal.ofReal (‖ξ‖ ^ n) * ‖f ξ i‖ₑ := fun i _ =>
    (ENNReal.measurable_ofReal.comp (continuous_norm.pow n).measurable).mul
      ((measurable_pi_apply i).comp hf).enorm
  rw [← lintegral_finsetSum _ hm]
  refine lintegral_mono fun ξ => ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul' le_rfl (enorm_le_sum_coord (f ξ))

theorem fourierDatum_mom_ne_top (u₀ : Navier.SchwartzVelocity) (n : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖fourierDatum u₀ ξ‖ₑ ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_weight_le_sum n _ (measurable_fourierDatum u₀))
  refine ENNReal.sum_ne_top.mpr fun i _ => ?_
  have h := mom_wienerDatum_ne_top u₀ n i
  unfold mom at h
  rwa [lintegral_congr_ae (by
    filter_upwards [coeFn_wienerDatum u₀ i] with ξ hξ
    rw [hξ])] at h

/-- **Joint `C^∞` smoothness of the large-data local Wiener solution from
Schwartz data.** -/
theorem exists_smooth_wienerSolution {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (u₀ : Navier.SchwartzVelocity) (hsmall : 10 ^ 4 * T * ‖wienerDatum u₀‖ ^ 2 ≤ ν) :
    ∃ x : C(Icc (0 : ℝ) T, V1),
      x = heatPath hν (wienerDatum u₀) + duhamelPath hν hT.le x x ∧
      ∃ w : ℝ → ES → ComplexSpace,
        (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
          (fun ξ => w t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i)) ∧
        (∀ t ∈ Icc (0 : ℝ) T, ∀ ξ : ES,
          w t ξ = continuousMildImage ν hν (fourierDatum u₀) w t ξ) ∧
        ∀ i : Fin 3, ContDiffOn ℝ ∞ (fun z : ℝ × ES => physicalCoord (w z.1) i z.2)
          (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) := by
  set a₀ := wienerDatum u₀ with ha₀
  set a := fourierDatum u₀ with ha
  obtain ⟨x, -, hxeq, hmom⟩ := exists_wienerMildSolution_moments hν hT a₀ hsmall
  obtain ⟨v, hvm, hv⟩ := exists_joint_rep hT.le x
  set wv : ℝ → ES → ComplexSpace := continuousMildImage ν hν a v with hwv
  set w : ℝ → ES → ComplexSpace := fun t => wv (projIcc 0 T hT.le t) with hw
  have hext : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T), extend hT.le x t = x ⟨t, ht⟩ := by
    intro t ht; unfold WienerLocalMild.extend; rw [projIcc_of_mem hT.le ht]
  have hwt : ∀ t ∈ Icc (0 : ℝ) T, w t = wv t := fun t ht => by
    show wv (projIcc 0 T hT.le t) = wv t
    rw [projIcc_of_mem hT.le ht]
  -- the mild image of the joint representative represents the path
  have key : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
      (fun ξ => wv t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i) := by
    intro t ht i
    have hx : x ⟨t, ht⟩ = heatOp ν t a₀ + duhamel ν hT.le x x t := by
      conv_lhs => rw [hxeq]
      rfl
    rw [hx]
    filter_upwards [Lp.coeFn_add (heatOp ν t a₀ i) (duhamel ν hT.le x x t i),
      heatOp_coord_ae_eq hν a₀ ht.1 i, duhamel_coord_ae_eq hν hT.le x v hvm hv ht i,
      coeFn_wienerDatum u₀ i] with ξ h1 h2 h3 h4
    rw [Pi.add_apply, h1, Pi.add_apply, h2, h3]
    show heatVec ν t a ξ i + continuousDuhamel ν v v t ξ i = _
    congr 1
    show ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * a ξ i =
      ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * a₀ i ξ
    rw [h4]
  -- moments of the joint representative
  have hvmom : ∀ n : ℕ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)),
      ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖v s ξ‖ₑ ≤ C := by
    intro n
    set m : ℝ := (momV n a₀).toReal with hm
    have hma : momV n a₀ ≤ ENNReal.ofReal m := by
      rw [hm, ENNReal.ofReal_toReal (momV_wienerDatum_ne_top u₀ n)]
    have hx := hmom n m ENNReal.toReal_nonneg hma
    have hγ : 0 ≤ momRate ν n a₀ := by unfold momRate; positivity
    refine ⟨ENNReal.ofReal (2 * m * Real.exp (momRate ν n a₀ * T)), ENNReal.ofReal_ne_top, ?_⟩
    filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with s hs hmem
    refine (lintegral_weight_le_sum n _ (measurable_slice hvm s)).trans ?_
    have heq : ∀ i : Fin 3, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖v s ξ i‖ₑ =
        mom n (x ⟨s, hmem⟩ i) := fun i => by
      unfold mom
      apply lintegral_congr_ae
      have h2 := hs i
      rw [hext s hmem] at h2
      filter_upwards [h2] with ξ hξ
      rw [hξ]
    simp_rw [heq]
    refine (hx ⟨s, hmem⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    have : Real.exp (momRate ν n a₀ * s) ≤ Real.exp (momRate ν n a₀ * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmem.2 hγ)
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
    nlinarith
  -- fixed point of the clamped field
  have hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ : ES, w t ξ = continuousMildImage ν hν a w t ξ := by
    intro t ht ξ
    have huv : ∀ᵐ s ∂leiLinTimeMeasure T, v s =ᵐ[volume] w s := by
      filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with s hs hmem
      have hc : ∀ i : Fin 3, (fun ξ => v s ξ i) =ᵐ[volume] fun ξ => w s ξ i := fun i => by
        have h2 := hs i
        rw [hext s hmem] at h2
        rw [hwt s hmem]
        exact h2.trans (key s hmem i).symm
      filter_upwards [ae_all_iff.mpr hc] with ξ h
      funext i
      exact h i
    rw [hwt t ht,
      ← Navier.Analysis.ContinuousLeiLinRepresentativeInvariant.continuousMildImage_congr_ae_on_horizon
        ν hν T a v w huv t ht ξ]
  have hG : Good T w := good_mildImage hν hT (measurable_fourierDatum u₀)
    (fourierDatum_mom_ne_top u₀) hvm hvmom
  refine ⟨x, hxeq, w, fun t ht i => ?_, hfix, fun i =>
    contDiffOn_physicalCoord_of_mild hT hν a hfix hG i⟩
  rw [hwt t ht]
  exact key t ht i

end Navier.Analysis.WienerSchwartzSmooth

set_option pp.fullNames true in
#check @Navier.Analysis.WienerSchwartzSmooth.exists_smooth_wienerSolution
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerSchwartzSmooth.exists_smooth_wienerSolution
