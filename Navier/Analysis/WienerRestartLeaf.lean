import Navier.Analysis.WienerPiece
import Navier.Analysis.WienerSobolevL1
import Navier.Analysis.StripOfPiece
import Navier.Analysis.WienerLocalClassical

/-!
# The R-restart leaf from a uniform Fourier `H³` bound (piece-restart chain)

`WienerH3Apriori N` (the named premise) says: for every viscosity, divergence-free
Schwartz datum `u₀` and budget `M`, there is ONE constant `K = K(ν, u₀, M)` such that
every `R`-solution `u` from `u₀` with `N T u ≤ M`, at every time `τ < T`, has every
Fourier profile representing `u τ` of Fourier `H³` weight at most `K`.

Under it the R-restart leaf holds (`datumRestartR_of_wienerH3Apriori`) with the step
`h = 4π²ν / (3·10⁶ (C_W K + 1))`, which depends on `(ν, u₀, M)` through `K` only:
no piece index and no per-piece qualitative bound enters.  The proof is the
piece-restart chain:

* `rep_base`: the Schwartz datum is represented (profile `𝓕(-2π u₀)`);
* `piece_at`: a represented slice with `H³` weight `≤ K` starts a Wiener piece of any
  length `L` with `10⁶ L C_W K ≤ 4π²ν` (bounded data after an a.e. cleaning,
  `WienerPiece.wienerPiece`), whose slices are again represented;
* `rep_all`: by induction on `n` with step `h`, every slice `u τ`, `τ < T`, is
  represented (`StripOfPiece.uniqueness_piece` identifies `u` with each piece);
* the leaf: restart at `T₀ = max (T - h) 0` with a piece of length `T - T₀ + h ≤ 2h`,
  glued by `StripOfPiece.strip_of_piece`.

`crown_of_wienerH3Apriori` records the resulting crown reduction:
`WienerH3Apriori N → APrioriIn RegularOnCompacts N → WholeSpaceGlobalRegularity`.
`WienerH3Apriori` is a TRAVELLING PREMISE (OPEN); its intended discharge is the damped
`H³` estimate on Wiener pieces transferred by uniqueness.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate

namespace Navier.Analysis.WienerRestartLeaf

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinReality (ProfileDivergenceFree)
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerPhysicalAssembly
open Navier.Analysis.WienerDatumSmooth
open Navier.Analysis.WienerPiece
open Navier.Analysis.WienerSobolevL1
open Navier.Analysis.StripOfPiece
open Navier.Analysis.RegularRestart
open Navier.Analysis.RestartPaste
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.CriticalControlDecomposition

/-- The physical field of a frequency profile, in the Wiener convention. -/
def physOf (a : ES → ComplexSpace) : VelocityField := physU (fun _ => a) 0

/-- `a` is a bounded transverse profile representing the velocity slice `v`. -/
structure Rep (v : VelocityField) (a : ES → ComplexSpace) : Prop where
  datum : WDatum a
  bdd : ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ ξ ∂(volume : Measure ES), ∀ i, ‖a ξ i‖ ≤ A
  div : ∀ᵐ ξ ∂(volume : Measure ES), ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * a ξ i = 0
  eq : ∀ x, v x = physOf a x

/-- **The named premise: a uniform Fourier `H³` bound on represented slices.** -/
def WienerH3Apriori (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ M : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → RegularOnCompacts T u p →
        N T u ≤ (M : ℝ≥0∞) →
        ∀ τ : ℝ, 0 ≤ τ → τ < T → ∀ a : ES → ComplexSpace, Rep (u τ) a →
          ∀ i : Fin 3, h3F (fun ξ => a ξ i) ≤ ENNReal.ofReal K

/-! ## Cleaning a representing profile on a null set -/

theorem clean {a : ES → ComplexSpace} {A : ℝ} (hA : 0 ≤ A) (hd : WDatum a)
    (hb : ∀ᵐ ξ ∂(volume : Measure ES), ∀ i, ‖a ξ i‖ ≤ A)
    (hdiv : ∀ᵐ ξ ∂(volume : Measure ES), ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * a ξ i = 0) :
    ∃ a' : ES → ComplexSpace, BDatum a' A ∧ a' =ᵐ[volume] a := by
  set S : Set ES := {ξ | ∀ i, ‖a ξ i‖ ≤ A} ∩ {ξ | ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * a ξ i = 0}
    with hS
  have hmi : ∀ i : Fin 3, Measurable fun ξ => a ξ i := fun i => (measurable_pi_apply i).comp hd.meas
  have hSm : MeasurableSet S := by
    refine MeasurableSet.inter ?_ ?_
    · have : {ξ : ES | ∀ i, ‖a ξ i‖ ≤ A} = ⋂ i : Fin 3, {ξ | ‖a ξ i‖ ≤ A} := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun i => measurableSet_le (hmi i).norm measurable_const
    · refine measurableSet_eq_fun ?_ measurable_const
      exact Finset.measurable_sum _ fun i _ =>
        (Complex.measurable_ofReal.comp ((PiLp.continuous_apply 2 _ i).measurable)).mul (hmi i)
  set a' : ES → ComplexSpace := S.indicator a with ha'
  have hae : a' =ᵐ[volume] a := by
    filter_upwards [hb, hdiv] with ξ h1 h2
    exact Set.indicator_of_mem (show ξ ∈ S from ⟨h1, h2⟩) a
  refine ⟨a', ?_, hae⟩
  refine ⟨⟨hd.meas.indicator hSm, fun n => ?_, fun i => ?_⟩, fun ξ i => ?_, fun ξ => ?_⟩
  · rw [lintegral_congr_ae (by filter_upwards [hae] with ξ h; rw [h])]
    exact hd.mom n
  · filter_upwards [hae, Navier.Analysis.WienerReality.ae_neg hae, hd.sym i] with ξ h1 h2 h3
    rw [h2, h1, h3]
  · by_cases h : ξ ∈ S
    · rw [ha', Set.indicator_of_mem h]; exact h.1 i
    · rw [ha', Set.indicator_of_notMem h]; simpa using hA
  · by_cases h : ξ ∈ S
    · show ∑ i : Fin 3, ((Navier.Analysis.FourierMajorant.spaceProj ξ i : ℝ) : ℂ) * a' ξ i = 0
      rw [ha', Set.indicator_of_mem h]; exact h.2
    · show ∑ i : Fin 3, ((Navier.Analysis.FourierMajorant.spaceProj ξ i : ℝ) : ℂ) * a' ξ i = 0
      rw [ha', Set.indicator_of_notMem h]; simp

theorem physOf_congr {a a' : ES → ComplexSpace} (h : a' =ᵐ[volume] a) : physOf a' = physOf a := by
  funext x k
  unfold physOf physU
  congr 3
  refine fourierInv_congr ?_ _
  filter_upwards [h] with ξ hξ
  rw [hξ]

theorem h3F_congr {f g : ES → ℂ} (h : f =ᵐ[volume] g) : h3F f = h3F g := by
  unfold h3F
  exact lintegral_congr_ae (by filter_upwards [h] with ξ hξ; rw [hξ])

/-- The Wiener norm of a datum is controlled by its Fourier `H³` weight. -/
theorem norm_wdatum_sq_le {a : ES → ComplexSpace} (hd : WDatum a) {K : ℝ} (hK : 0 ≤ K)
    (hKa : ∀ i, h3F (fun ξ => a ξ i) ≤ ENNReal.ofReal K) :
    ‖wdatum hd‖ ^ 2 ≤ CW.toReal * K := by
  have hcoord : ∀ i : Fin 3, ‖wdatum hd i‖ ≤ Real.sqrt (CW.toReal * K) := by
    intro i
    have hn : ‖wdatum hd i‖ = (∫⁻ ξ, ‖a ξ i‖ₑ).toReal := by
      rw [← toReal_enorm]
      exact congrArg ENNReal.toReal (Integrable.enorm_toL1 (hd.integrable i))
    have hsq := lintegral_enorm_sq_le (f := fun ξ => a ξ i)
      ((measurable_pi_apply i).comp hd.meas).aemeasurable
    have hle : (∫⁻ ξ, ‖a ξ i‖ₑ) ^ 2 ≤ CW * ENNReal.ofReal K := hsq.trans (mul_le_mul' le_rfl (hKa i))
    have hfin : CW * ENNReal.ofReal K ≠ ⊤ := ENNReal.mul_ne_top CW_ne_top ENNReal.ofReal_ne_top
    have hreal : ((∫⁻ ξ, ‖a ξ i‖ₑ).toReal) ^ 2 ≤ CW.toReal * K := by
      rw [← ENNReal.toReal_pow, ← ENNReal.toReal_ofReal hK, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono hfin hle
    rw [hn]
    exact Real.le_sqrt_of_sq_le hreal
  have hs0 : 0 ≤ Real.sqrt (CW.toReal * K) := Real.sqrt_nonneg _
  have hnorm : ‖wdatum hd‖ ≤ Real.sqrt (CW.toReal * K) :=
    (pi_norm_le_iff_of_nonneg hs0).mpr hcoord
  calc ‖wdatum hd‖ ^ 2 ≤ Real.sqrt (CW.toReal * K) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = CW.toReal * K := Real.sq_sqrt (mul_nonneg ENNReal.toReal_nonneg hK)

/-! ## A piece at a represented slice -/

/-- **A Wiener piece started at a represented slice.** -/
theorem piece_at {ν K L : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hL : 0 < L) {v : VelocityField}
    {a : ES → ComplexSpace} (hr : Rep v a) (hKa : ∀ i, h3F (fun ξ => a ξ i) ≤ ENNReal.ofReal K)
    (hsmall : 10 ^ 6 * L * (CW.toReal * K) ≤ 4 * Real.pi ^ 2 * ν) :
    ∃ w : ℝ → ES → ComplexSpace,
      SolvesBefore ν L (physU w) (physP w) ∧ RegularOnCompacts L (physU w) (physP w) ∧
      physU w 0 = v ∧ ∀ s ∈ Icc (0 : ℝ) L, Rep (physU w s) (w s) := by
  obtain ⟨A, hA, hb⟩ := hr.bdd
  obtain ⟨a', hd', hae⟩ := clean hA hr.datum hb hr.div
  have hKa' : ∀ i, h3F (fun ξ => a' ξ i) ≤ ENNReal.ofReal K := fun i => by
    rw [h3F_congr (f := fun ξ => a' ξ i) (g := fun ξ => a ξ i)
      (by filter_upwards [hae] with ξ h; rw [h])]
    exact hKa i
  have hn := norm_wdatum_sq_le hd'.toWDatum hK hKa'
  have hs6 : 10 ^ 6 * L * ‖wdatum hd'.toWDatum‖ ^ 2 ≤ 4 * Real.pi ^ 2 * ν :=
    le_trans (mul_le_mul_of_nonneg_left hn (by positivity)) hsmall
  obtain ⟨w, hw0, -, -, hsol, hR, Rb, -, hslice⟩ := wienerPiece hν hL hA hd' hs6
  refine ⟨w, hsol, hR, ?_, fun s hs => ?_⟩
  · have e : (w 0) = a' := funext hw0
    funext x
    rw [hr.eq x, ← physOf_congr hae]
    show physU w 0 x = physU (fun _ => a') 0 x
    unfold physU
    rw [e]
  · obtain ⟨hwd, hwb, hwdiv, -⟩ := hslice s hs
    exact ⟨hwd, ⟨max Rb 0, le_max_right _ _, by
      filter_upwards [hwb] with ξ h i using (h i).trans (le_max_left _ _)⟩, hwdiv, fun x => rfl⟩

/-! ## The Schwartz start is represented -/

open Navier.Analysis.WienerSchwartzSmooth Navier.Analysis.WienerLocalExistence
  Navier.Analysis.FourierMajorant in
theorem rep_base (u₀ : SchwartzVelocity) (hdiv : DivergenceFreeInitial u₀) :
    Rep (fun x => u₀ x) (fourierDatum ((-(2 * Real.pi)) • u₀)) := by
  set v₀ : SchwartzVelocity := (-(2 * Real.pi)) • u₀ with hv₀
  set a := fourierDatum v₀ with hadef
  set A : ℝ := ∑ i : Fin 3,
    ‖(𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction‖ with hAdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => norm_nonneg _
  have haA : ∀ ξ (i : Fin 3), ‖a ξ i‖ ≤ A := by
    intro ξ i
    have h1 : ‖a ξ i‖ ≤
        ‖(𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction‖ :=
      ((𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction.norm_coe_le_norm
        ξ)
    exact h1.trans (Finset.single_le_sum (f := fun i =>
      ‖(𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ i))
  have hpd : ProfileDivergenceFree a :=
    profileDivergenceFree_fourierDatum v₀ (divergenceFreeInitial_smul _ hdiv)
  refine ⟨⟨measurable_fourierDatum v₀, fourierDatum_mom_ne_top v₀, fun i => ?_⟩,
    ⟨A, hA, Eventually.of_forall fun ξ i => haA ξ i⟩, Eventually.of_forall fun ξ => hpd ξ,
    fun x => ?_⟩
  · refine Eventually.of_forall fun ξ => ?_
    have h := congrFun (Navier.Analysis.WienerReality.reflC_fourierDatum v₀ i) (-ξ)
    simp only [Navier.Analysis.WienerReality.reflC, neg_neg] at h
    exact h.symm
  · funext i
    have h := physicalCoord_fourierDatum v₀ i (euclidPoint x)
    unfold physicalCoord at h
    show u₀ x i = -(1 / (2 * Real.pi)) * (𝓕⁻ (fun ξ => a ξ i) (euclidPoint x)).re
    rw [h, Complex.ofReal_re]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    show u₀ x i = -(1 / (2 * Real.pi)) * ((-(2 * Real.pi)) • u₀) (spaceProj (euclidPoint x)) i
    simp only [SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    have hsp : spaceProj (euclidPoint x) = x := rfl
    rw [hsp]
    field_simp

/-! ## Every slice is represented -/

theorem rep_all {ν K h T : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hh : 0 < h)
    (hsmall : 10 ^ 6 * (2 * h) * (CW.toReal * K) ≤ 4 * Real.pi ^ 2 * ν)
    {u : VelocityEvolution} {p : PressureEvolution} (hu : SolvesBefore ν T u p)
    (hRu : RegularOnCompacts T u p) {a0 : ES → ComplexSpace} (h0 : Rep (u 0) a0)
    (hKall : ∀ τ, 0 ≤ τ → τ < T → ∀ a, Rep (u τ) a → ∀ i,
      h3F (fun ξ => a ξ i) ≤ ENNReal.ofReal K) :
    ∀ τ, 0 ≤ τ → τ < T → ∃ a, Rep (u τ) a := by
  have hstep : ∀ n : ℕ, ∀ τ, 0 ≤ τ → τ < T → τ ≤ n * h → ∃ a, Rep (u τ) a := by
    intro n
    induction n with
    | zero =>
        intro τ h1 _ h3
        have : τ = 0 := le_antisymm (by simpa using h3) h1
        subst this
        exact ⟨a0, h0⟩
    | succ n ih =>
        intro τ h1 h2 h3
        by_cases hle : τ ≤ n * h
        · exact ih τ h1 h2 hle
        push_neg at hle
        set τ₀ : ℝ := n * h with hτ₀
        have hτ₀0 : 0 ≤ τ₀ := by positivity
        obtain ⟨a₀, hr₀⟩ := ih τ₀ hτ₀0 (lt_trans hle h2) le_rfl
        obtain ⟨w, hsol, hR, hw0, hrep⟩ := piece_at hν hK (by positivity : (0 : ℝ) < 2 * h) hr₀
          (hKall τ₀ hτ₀0 (lt_trans hle h2) a₀ hr₀) hsmall
        have hstep1 : τ - τ₀ ≤ h := by push_cast at h3; nlinarith
        have heq := uniqueness_piece hν hτ₀0 hu hRu hsol hR hw0 τ hle.le
          (lt_min h2 (by linarith))
        refine ⟨w (τ - τ₀), ?_⟩
        rw [← heq]
        exact hrep (τ - τ₀) ⟨by linarith, by linarith⟩
  intro τ h1 h2
  refine hstep ⌈τ / h⌉₊ τ h1 h2 ?_
  have := Nat.le_ceil (τ / h)
  rwa [div_le_iff₀ hh] at this

/-! ## The R-restart leaf -/

/-- **The R-restart leaf, conditional on the named premise `WienerH3Apriori`.** -/
theorem datumRestartR_of_wienerH3Apriori (N : CriticalQuantity)
    (hK : WienerH3Apriori N) : DatumHorizonIndependentRestartR N := by
  intro ν hν u₀ hdiv M
  obtain ⟨K, hK0, hKb⟩ := hK ν hν u₀ hdiv M
  set C : ℝ := CW.toReal * K with hC
  have hC0 : 0 ≤ C := mul_nonneg ENNReal.toReal_nonneg hK0
  set h : ℝ := 4 * Real.pi ^ 2 * ν / (3 * 10 ^ 6 * (C + 1)) with hhdef
  have hh : 0 < h := by positivity
  have hkey : 10 ^ 6 * (3 * h) * (C + 1) = 4 * Real.pi ^ 2 * ν := by
    rw [hhdef]; field_simp
  have hsmall2 : ∀ L, 0 ≤ L → L ≤ 2 * h → 10 ^ 6 * L * C ≤ 4 * Real.pi ^ 2 * ν := by
    intro L hL0 hL
    rw [← hkey]
    have : L * C ≤ (3 * h) * (C + 1) := by nlinarith
    nlinarith
  refine ⟨h, hh, fun T hT u p hu0 hu hRu hpn hN => ?_⟩
  have hKall := hKb T hT u p hu0 hu hRu hN
  have h0 : Rep (u 0) (fourierDatum ((-(2 * Real.pi)) • u₀)) := by
    have e : u 0 = fun x => u₀ x := funext hu0
    rw [e]; exact rep_base u₀ hdiv
  have hrep := rep_all hν hK0 hh (hsmall2 _ (by positivity) le_rfl) hu hRu h0 hKall
  set T₀ : ℝ := max (T - h) 0 with hT₀
  have hT₀0 : 0 ≤ T₀ := le_max_right _ _
  have hT₀T : T₀ < T := max_lt (by linarith) hT
  have hT₀h : T - h ≤ T₀ := le_max_left _ _
  set L : ℝ := T - T₀ + h with hLdef
  have hL0 : 0 < L := by rw [hLdef]; linarith
  have hL2 : L ≤ 2 * h := by rw [hLdef]; linarith
  obtain ⟨a, ha⟩ := hrep T₀ hT₀0 hT₀T
  obtain ⟨w, hsol, hR, hw0, -⟩ := piece_at hν hK0 hL0 ha (hKall T₀ hT₀0 hT₀T a ha)
    (hsmall2 L hL0.le hL2)
  obtain ⟨hSF, hRF, hqn, -⟩ := strip_of_piece hν hT₀0 hT₀T (by rw [hLdef]; linarith) hu hRu hpn
    (hsol.normalizePressure) (regularOnCompacts_normalize _ _ _ hR)
    (normalizePressure_normalizedBefore _ _) hw0
  refine ⟨T₀, hT₀0, hT₀T, _, _, fun t _ ht => (if_pos ht).symm, fun t _ ht => (if_pos ht).symm,
    hSF, hRF, fun t h1 h2 => hqn t h1 (by rw [hLdef]; linarith)⟩

/-- **The crown from the named premise and the R a priori leaf.** -/
theorem crown_of_wienerH3Apriori (N : CriticalQuantity) (hK : WienerH3Apriori N)
    (hapriori : APrioriIn RegularOnCompacts N) : ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_R_restart_apriori N (datumRestartR_of_wienerH3Apriori N hK)
    hapriori

end Navier.Analysis.WienerRestartLeaf

set_option pp.fullNames true in
#check @Navier.Analysis.WienerRestartLeaf.WienerH3Apriori
set_option pp.fullNames true in
#check @Navier.Analysis.WienerRestartLeaf.crown_of_wienerH3Apriori
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerRestartLeaf.datumRestartR_of_wienerH3Apriori
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerRestartLeaf.crown_of_wienerH3Apriori
