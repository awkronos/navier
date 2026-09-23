import Navier.Analysis.WienerReality

/-!
# The smooth real Wiener solution from a general frequency datum

`WienerSchwartzSmooth.exists_smooth_wienerSolution` and
`WienerReality.exists_real_smooth_wienerSolution` are stated for the Fourier datum of a
Schwartz velocity, but their proofs use only: a measurable pointwise datum `a`, every
Fourier moment of `a` finite, and (for reality) the Hermitian symmetry
`a(-ξ) = conj a(ξ)` almost everywhere.  This file restates both for such data
(`exists_real_smooth_of_datum`).

This is step 1 of item 6: the restart datum of a Wiener piece is the frequency profile
of the previous piece, which is not the transform of a Schwartz velocity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate

namespace Navier.Analysis.WienerDatumSmooth

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerLocalMild
open Navier.Analysis.WienerMoments
open Navier.Analysis.WienerPointwiseBridge
open Navier.Analysis.WienerPointwiseODE
open Navier.Analysis.WienerMildGood
open Navier.Analysis.WienerSchwartzSmooth
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerReality

/-- Data hypotheses on a pointwise frequency profile. -/
structure WDatum (a : ES → ComplexSpace) : Prop where
  meas : Measurable a
  mom : ∀ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖a ξ‖ₑ ≠ ⊤
  sym : ∀ i : Fin 3, ∀ᵐ ξ ∂(volume : Measure ES), a (-ξ) i = conj (a ξ i)

theorem WDatum.mom_coord {a : ES → ComplexSpace} (hd : WDatum a) (n : ℕ) (i : Fin 3) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖a ξ i‖ₑ ≠ ⊤ :=
  ne_top_of_le_ne_top (hd.mom n) (lintegral_mono fun ξ =>
    mul_le_mul' le_rfl (enorm_coord_le (a ξ) i))

theorem WDatum.integrable {a : ES → ComplexSpace} (hd : WDatum a) (i : Fin 3) :
    Integrable (fun ξ => a ξ i) := by
  refine ⟨((measurable_pi_apply i).comp hd.meas).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have h := hd.mom_coord 0 i
  simpa using h.lt_top

/-- The `L¹` class of a datum. -/
def wdatum {a : ES → ComplexSpace} (hd : WDatum a) : V1 := fun i => (hd.integrable i).toL1 _

theorem coeFn_wdatum {a : ES → ComplexSpace} (hd : WDatum a) (i : Fin 3) :
    ⇑(wdatum hd i) =ᵐ[volume] fun ξ => a ξ i :=
  Integrable.coeFn_toL1 _

theorem momV_wdatum_ne_top {a : ES → ComplexSpace} (hd : WDatum a) (n : ℕ) :
    momV n (wdatum hd) ≠ ⊤ := by
  unfold momV
  refine ENNReal.sum_ne_top.mpr fun i _ => ?_
  have h := hd.mom_coord n i
  unfold mom
  rwa [lintegral_congr_ae (by
    filter_upwards [coeFn_wdatum hd i] with ξ hξ
    rw [hξ])]

theorem RV_wdatum {a : ES → ComplexSpace} (hd : WDatum a) : RV (wdatum hd) = wdatum hd := by
  funext i
  apply Lp.ext
  filter_upwards [coeFn_Rc (wdatum hd i), reflC_congr (coeFn_wdatum hd i),
    coeFn_wdatum hd i, ae_neg (hd.sym i)] with ξ h1 h2 h3 h4
  rw [show RV (wdatum hd) i = Rc (wdatum hd i) from rfl, h1, h2, h3]
  simp only [reflC]
  have h5 : a (-(-ξ)) i = conj (a (-ξ) i) := h4
  rw [neg_neg] at h5
  rw [h5]

/-- **Smooth and real large-data local Wiener solution from a general datum.** -/
theorem exists_real_smooth_of_datum {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T)
    {a : ES → ComplexSpace} (hd : WDatum a) (hsmall : 10 ^ 4 * T * ‖wdatum hd‖ ^ 2 ≤ ν) :
    ∃ x : C(Icc (0 : ℝ) T, V1), ‖x‖ ≤ 2 * ‖wdatum hd‖ ∧
      x = heatPath hν (wdatum hd) + duhamelPath hν hT.le x x ∧
      ∃ w : ℝ → ES → ComplexSpace,
        (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
          (fun ξ => w t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i)) ∧
        (∀ t ∈ Icc (0 : ℝ) T, ∀ ξ : ES, w t ξ = continuousMildImage ν hν a w t ξ) ∧
        Good T w ∧
        (∀ i : Fin 3, ContDiffOn ℝ ∞ (fun z : ℝ × ES => physicalCoord (w z.1) i z.2)
          (Ico (0 : ℝ) T ×ˢ (univ : Set ES))) ∧
        (∀ t ∈ Icc (0 : ℝ) T, ∀ (i : Fin 3) (y : ES),
          conj (physicalCoord (w t) i y) = physicalCoord (w t) i y) ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∀ i : Fin 3,
          ∀ᵐ ξ ∂(volume : Measure ES), w t (-ξ) i = conj (w t ξ i) := by
  set a₀ := wdatum hd with ha₀
  obtain ⟨x, hxle, hxeq, hmom⟩ := exists_wienerMildSolution_moments hν hT a₀ hsmall
  obtain ⟨v, hvm, hv⟩ := exists_joint_rep hT.le x
  set wv : ℝ → ES → ComplexSpace := continuousMildImage ν hν a v with hwv
  set w : ℝ → ES → ComplexSpace := fun t => wv (projIcc 0 T hT.le t) with hw
  have hext : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T), extend hT.le x t = x ⟨t, ht⟩ := by
    intro t ht; unfold WienerLocalMild.extend; rw [projIcc_of_mem hT.le ht]
  have hwt : ∀ t ∈ Icc (0 : ℝ) T, w t = wv t := fun t ht => by
    show wv (projIcc 0 T hT.le t) = wv t
    rw [projIcc_of_mem hT.le ht]
  have key : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
      (fun ξ => wv t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i) := by
    intro t ht i
    have hx : x ⟨t, ht⟩ = heatOp ν t a₀ + duhamel ν hT.le x x t := by
      conv_lhs => rw [hxeq]
      rfl
    rw [hx]
    filter_upwards [Lp.coeFn_add (heatOp ν t a₀ i) (duhamel ν hT.le x x t i),
      heatOp_coord_ae_eq hν a₀ ht.1 i, duhamel_coord_ae_eq hν hT.le x v hvm hv ht i,
      coeFn_wdatum hd i] with ξ h1 h2 h3 h4
    rw [Pi.add_apply, h1, Pi.add_apply, h2, h3]
    show heatVec ν t a ξ i + continuousDuhamel ν v v t ξ i = _
    congr 1
    show ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * a ξ i =
      ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * a₀ i ξ
    rw [h4]
  have hvmom : ∀ n : ℕ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)),
      ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖v s ξ‖ₑ ≤ C := by
    intro n
    set m : ℝ := (momV n a₀).toReal with hm
    have hma : momV n a₀ ≤ ENNReal.ofReal m := by
      rw [hm, ENNReal.ofReal_toReal (momV_wdatum_ne_top hd n)]
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
  have hG : Good T w := good_mildImage hν hT hd.meas hd.mom hvm hvmom
  have hw : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
      (fun ξ => w t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i) := fun t ht i => by
    rw [hwt t ht]; exact key t ht i
  have hR : Rpath x = x := Rpath_fixed hν hT a₀ hsmall (RV_wdatum hd) x hxle hxeq
  have hRt : ∀ t (ht : t ∈ Icc (0 : ℝ) T) i, Rc (x ⟨t, ht⟩ i) = x ⟨t, ht⟩ i := by
    intro t ht i
    exact congrArg (fun z : C(Icc (0 : ℝ) T, V1) => z ⟨t, ht⟩ i) hR
  refine ⟨x, hxle, hxeq, w, hw, hfix, hG, fun i =>
    contDiffOn_physicalCoord_of_mild hT hν a hfix hG i, fun t ht i y => ?_, fun t ht i => ?_⟩
  · unfold physicalCoord
    rw [fourierInv_congr (hw t ht i) y]
    exact conj_fourierInv_of_Rc (hRt t ht i) y
  · have h1 := coeFn_Rc (x ⟨t, ht⟩ i)
    rw [hRt t ht i] at h1
    filter_upwards [hw t ht i, ae_neg (hw t ht i), h1] with ξ ha hb hc
    rw [hb, ha, hc]
    simp [reflC]

end Navier.Analysis.WienerDatumSmooth

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerDatumSmooth.exists_real_smooth_of_datum
