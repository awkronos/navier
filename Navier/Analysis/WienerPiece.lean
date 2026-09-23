import Navier.Analysis.WienerDatumSmooth
import Navier.Analysis.WienerRegularityFull
import Navier.Analysis.FourierL2Agree

/-!
# A Wiener piece from a bounded frequency datum

For a frequency profile `a` that is measurable, bounded, transverse
(`ProfileDivergenceFree`), Hermitian-symmetric and has every Fourier moment finite
(`BDatum a A`), and any horizon with `10⁶ T ‖a‖²_{L¹} ≤ 4π²νp`, the physical pair
`u = -(2π)⁻¹ Re 𝓕⁻ w`, `p = -(4π²)⁻¹ Re 𝓕⁻ Q̂` of the pointwise mild solution `w` with
datum `a` satisfies:

* `SolvesBefore νp T u p` (classical clauses, finite energy, energy inequality relative to
  the start; the start energy is identified with `∫|a|²` by Plancherel's IDENTITY,
  `FourierL2Agree.lintegral_sq_fourierInv_eq`);
* `RegularOnCompacts T u p` (the class `R`);
* `w 0 = a`, and every slice `w t`, `t ∈ [0, T]`, is again a datum of the same kind up to
  a null set (measurable, bounded a.e., transverse a.e., symmetric a.e., every moment),
  with `L¹` mass at most `2‖a‖_{L¹}`.

This is step 1b of item 6: the piece theorem the restart chain iterates.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate

namespace Navier.Analysis.WienerPiece

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinReality (ProfileDivergenceFree)
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.FourierMajorant (spaceProj)
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerLocalMild
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerPointwiseODE
open Navier.Analysis.WienerPhysicalPDE
open Navier.Analysis.WienerPhysicalAssembly
open Navier.Analysis.WienerLocalClassical
open Navier.Analysis.WienerRegularityFull
open Navier.Analysis.WienerDatumSmooth
open Navier.Analysis.WienerLocalExistence (mild_zero)
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.CriticalControlDecomposition (SolvesBefore)

/-- A bounded transverse datum. -/
structure BDatum (a : ES → ComplexSpace) (A : ℝ) : Prop extends WDatum a where
  bdd : ∀ ξ (i : Fin 3), ‖a ξ i‖ ≤ A
  div : ProfileDivergenceFree a

/-- `∫ ‖f‖² = ∫ ‖g‖²` from the lintegral identity. -/
theorem integral_sq_eq_of_lintegral {f g : ES → ℂ} (hf : Integrable (fun y => ‖f y‖ ^ 2))
    (hg : Integrable (fun y => ‖g y‖ ^ 2)) (h : ∫⁻ y, ‖f y‖ₑ ^ 2 = ∫⁻ y, ‖g y‖ₑ ^ 2) :
    ∫ y, ‖f y‖ ^ 2 = ∫ y, ‖g y‖ ^ 2 :=
  le_antisymm (integral_sq_le_of_lintegral hf hg h.le) (integral_sq_le_of_lintegral hg hf h.ge)

/-- **The Wiener piece.** -/
theorem wienerPiece {νp T A : ℝ} (hνp : 0 < νp) (hT : 0 < T) (hA : 0 ≤ A)
    {a : ES → ComplexSpace} (hd : BDatum a A)
    (hsmall6 : 10 ^ 6 * T * ‖wdatum hd.toWDatum‖ ^ 2 ≤ 4 * Real.pi ^ 2 * νp) :
    ∃ w : ℝ → ES → ComplexSpace,
      (∀ ξ, w 0 ξ = a ξ) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ =
        continuousMildImage (4 * Real.pi ^ 2 * νp) (by positivity) a w t ξ) ∧
      Good T w ∧
      SolvesBefore νp T (physU w) (physP w) ∧
      RegularOnCompacts T (physU w) (physP w) ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) T,
        WDatum (w t) ∧ (∀ᵐ ξ ∂(volume : Measure ES), ∀ i, ‖w t ξ i‖ ≤ R) ∧
        (∀ᵐ ξ ∂(volume : Measure ES), ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * w t ξ i = 0) ∧
        ∀ i : Fin 3, ∫⁻ ξ, ‖w t ξ i‖ₑ ≤ ENNReal.ofReal (2 * ‖wdatum hd.toWDatum‖) := by
  set ν : ℝ := 4 * Real.pi ^ 2 * νp with hνdef
  have hν : 0 < ν := by positivity
  set a₀ : V1 := wdatum hd.toWDatum with ha₀def
  have hsmall4 : 10 ^ 4 * T * ‖a₀‖ ^ 2 ≤ ν := by
    have : 0 ≤ T * ‖a₀‖ ^ 2 := by positivity
    nlinarith
  obtain ⟨x, hxle, hxeq, w, hxw, hfix, hG, hsm, hreal, hsym⟩ :=
    exists_real_smooth_of_datum hν hT hd.toWDatum hsmall4
  have ha₀ : ∀ i, a₀ i ∈ Navier.Analysis.WienerLinfBound.Zb A := by
    intro i
    show ∀ᵐ ξ ∂(volume : Measure ES), ‖(a₀ i) ξ‖ ≤ A
    filter_upwards [coeFn_wdatum hd.toWDatum i] with ξ h
    rw [h]; exact hd.bdd ξ i
  have hxS := Navier.Analysis.WienerLinfBound.fixedPoint_mem_linfSet hν hT a₀ hsmall6 hA ha₀ x
    hxle hxeq
  have hRb := Navier.Analysis.WienerEnergy.ae_uniform_bound hT hν a hfix x hG.1 hxw hA
    (by positivity) hxS hxle (Eventually.of_forall fun ξ i => hd.bdd ξ i)
  set Rt : ℝ := A + 27 * (2 * A) * (2 * ‖a₀‖) * (2 * (Real.sqrt ν)⁻¹ * Real.sqrt T) with hRt
  have hR0 : 0 ≤ Rt := by positivity
  have ha : ProfileDivergenceFree a := hd.div
  have hw0 : ∀ ξ, w 0 ξ = a ξ := fun ξ => by
    rw [hfix 0 ⟨le_rfl, hT.le⟩ ξ, mild_zero]
  -- per-slice facts
  have hwint : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, Integrable (fun ξ => w t ξ k) :=
    fun t ht k => integrable_of_hmom (hmom_w hT hν hG ht k)
  have hwm : ∀ t (k : Fin 3), StronglyMeasurable (fun ξ => w t ξ k) :=
    fun t k => (continuous_apply k).comp_stronglyMeasurable (hG.1 t)
  have hwb : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, ∀ᵐ ξ ∂(volume : Measure ES), ‖w t ξ k‖ ≤ Rt := by
    intro t ht k
    filter_upwards [hRb] with ξ h using (norm_le_pi_norm _ k).trans (h t ht)
  have hLw : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, ∫⁻ ξ, ‖w t ξ k‖ₑ ^ 2 ≠ ⊤ :=
    fun t ht k => lintegral_sq_ne_top (hwint t ht k) (hwb t ht k)
  have hPl : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3,
      ∫⁻ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ₑ ^ 2 ≤ ∫⁻ ξ, ‖w t ξ k‖ₑ ^ 2 :=
    fun t ht k => Navier.Analysis.WienerPlancherel.lintegral_sq_fourierInv_le (hwm t k)
      (hwint t ht k)
  have hUc : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, Continuous (𝓕⁻ (fun ξ => w t ξ k)) :=
    fun t ht k => continuous_fourierInv (hwint t ht k)
  have hUint : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3,
      Integrable (fun y => ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2) :=
    fun t ht k => integrable_norm_sq_of_lintegral (hUc t ht k)
      (ne_top_of_le_ne_top (hLw t ht k) (hPl t ht k))
  have hwsq : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, Integrable (fun ξ => ‖w t ξ k‖ ^ 2) :=
    fun t ht k => integrable_norm_sq_of_lintegral' (hwm t k).aestronglyMeasurable (hLw t ht k)
  set c : ℝ := 1 / (2 * Real.pi) with hc
  have hbound : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun x : Space =>
      c ^ 2 * ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => w t ξ k) (euclidPoint x)‖ ^ 2) := fun t ht =>
    integrable_space_euclid (g := fun y => c ^ 2 * ∑ k : Fin 3,
      ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2)
      ((integrable_finsetSum _ fun k _ => hUint t ht k).const_mul _)
  have hKt : ∀ t ∈ Icc (0 : ℝ) T, kineticEnergy (physU w) t =
      c ^ 2 * ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2 := by
    intro t ht
    unfold kineticEnergy
    have hpt : ∀ x : Space, ∑ i : Fin 3, (physU w t x i) ^ 2 =
        c ^ 2 * ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => w t ξ k) (euclidPoint x)‖ ^ 2 := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => physU_sq_eq w t x k ?_
      exact Complex.conj_eq_iff_im.mp (hreal t ht k (euclidPoint x))
    simp_rw [hpt]
    rw [integral_space_euclid (fun y => c ^ 2 * ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2),
      integral_const_mul, integral_finsetSum _ fun k _ => hUint t ht k]
  have hEW : ∀ s ∈ Icc (0 : ℝ) T, Navier.Analysis.WienerEnergy.EW w s =
      ∑ k : Fin 3, ∫ ξ, ‖w s ξ k‖ ^ 2 := by
    intro s hs
    unfold Navier.Analysis.WienerEnergy.EW Navier.Analysis.WienerEnergy.eW
    exact integral_finsetSum _ fun k _ => hwsq s hs k
  -- Plancherel's identity at the start
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hPl0 : ∀ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => w 0 ξ k) y‖ ^ 2 = ∫ ξ, ‖w 0 ξ k‖ ^ 2 := by
    intro k
    have hmem : MemLp (fun ξ => w 0 ξ k) 2 :=
      (memLp_two_iff_integrable_sq_norm (hwm 0 k).aestronglyMeasurable).mpr (hwsq 0 h0I k)
    exact integral_sq_eq_of_lintegral (hUint 0 h0I k) (hwsq 0 h0I k)
      (Navier.Analysis.FourierL2Agree.lintegral_sq_fourierInv_eq (hwint 0 h0I k) hmem)
  refine ⟨w, hw0, hfix, hG, ⟨⟨smoothVelocityBefore_physU hsm,
    Navier.Analysis.WienerPressureSmooth.smoothPressureBefore_physP hT hν a hfix hG,
    incompressibleBefore_physU hT hν a hfix hG ha,
    satisfiesNavierStokesBefore_physU_visc hT hν a hfix hG rfl ha hreal⟩, ?_, ?_⟩,
    regularOnCompacts_phys hT hν a hfix hG hR0 hRb, Rt, hR0, fun t ht => ?_⟩
  · -- finite energy
    intro t ht0 htT
    have ht : t ∈ Icc (0 : ℝ) T := ⟨ht0, htT.le⟩
    have hcont : Continuous (fun x : Space => physU w t x) := by
      refine continuous_pi fun k => ?_
      exact continuous_const.mul (Complex.continuous_re.comp ((hUc t ht k).comp
        (PiLp.continuous_toLp 2 _)))
    refine (hbound t ht).mono' ((continuous_norm.comp hcont).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (sq_norm_le_sum _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => physU_sq_le w t x k
  · -- energy inequality relative to the start
    intro t ht0 htT
    have ht : t ∈ Icc (0 : ℝ) T := ⟨ht0, htT.le⟩
    have hE := Navier.Analysis.WienerEnergy.energy_antitone hT hν a hfix hG hR0 hRb hsym ha ht
    rw [hEW t ht, hEW 0 h0I] at hE
    have hle : ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2 ≤
        ∑ k : Fin 3, ∫ ξ, ‖w t ξ k‖ ^ 2 :=
      Finset.sum_le_sum fun k _ => integral_sq_le_of_lintegral (hUint t ht k) (hwsq t ht k)
        (hPl t ht k)
    have h0 : ∑ k : Fin 3, ∫ ξ, ‖w 0 ξ k‖ ^ 2 =
        ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => w 0 ξ k) y‖ ^ 2 :=
      Finset.sum_congr rfl fun k _ => (hPl0 k).symm
    rw [hKt t ht, hKt 0 h0I, ← h0]
    exact mul_le_mul_of_nonneg_left (hle.trans hE) (by positivity)
  · -- the slice is again a datum
    obtain ⟨hmeas, M, hM, hb, hmomM, -⟩ := id hG
    refine ⟨⟨(hmeas t).measurable, fun n => ?_, fun i => ?_⟩, ?_, ?_, fun i => ?_⟩
    · refine ne_top_of_le_ne_top (hmomM n) (lintegral_mono_ae ?_)
      filter_upwards [hb] with ξ h
      exact mul_le_mul' le_rfl (h t ht)
    · filter_upwards [hsym t ht i] with ξ h using h
    · filter_upwards [hRb] with ξ h i using (norm_le_pi_norm _ i).trans (h t ht)
    · exact transverse_mild hν a hfix hG ha ht
    · have hx := (x.norm_coe_le_norm ⟨t, ht⟩).trans hxle
      have hxi : ‖x ⟨t, ht⟩ i‖ ≤ 2 * ‖a₀‖ := (norm_le_pi_norm _ i).trans hx
      calc ∫⁻ ξ, ‖w t ξ i‖ₑ = ∫⁻ ξ, ‖(x ⟨t, ht⟩ i) ξ‖ₑ := by
            refine lintegral_congr_ae ?_
            filter_upwards [hxw t ht i] with ξ h
            rw [h]
        _ = ENNReal.ofReal ‖x ⟨t, ht⟩ i‖ := (L1.ofReal_norm_eq_lintegral _).symm
        _ ≤ ENNReal.ofReal (2 * ‖a₀‖) := ENNReal.ofReal_le_ofReal hxi

end Navier.Analysis.WienerPiece

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPiece.wienerPiece
