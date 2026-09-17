/-
W7O-NV3 (O50 swarm, 2026-09-17): discharge of `hprojectedWeak` from the
curl-projection error primitive.

`GalerkinEnergyBudget.galerkinModeData_of_modalFlow` reduces the mode-data
assembly to one named analytic input, `hprojectedWeak`.  The banked provider
`modalFlow_fixedTest_projectedResidual_tendsto_of_commutators` [GalerkinBasis]
shows the fixed-test residual splits into exactly two projection-commutator
integrals, and the ladder
`hlap_tendsto_zero_of_curlSqError_tendsto_zero` /
`intervalIntegral_convectionTestProjectionCommutator_tendsto_zero_of_curlSqError_tendsto_zero`
[GalerkinWeakConsistency] squeezes both to zero from control of the *curl
projection error* `‖curl(Pₘφ(t) − φ(t))‖₂`: a uniform bound on the test window
plus vanishing of its spacetime `L²` norm.  This file packages that pair as the
exactly-typed primitive `GalerkinBasisFamily.fixedTestCurlErrorVanishing`,
discharges every remaining provider premise (modal coefficient regularity of a
fixed test, interval integrability of the three pairings, the enstrophy and
error integrabilities) from the structure of `DivergenceFreeTestFunction` and
the ODE hypothesis alone, and lands `hprojectedWeak` — hence a fully inhabited
`GalerkinModeData ν u₀` — from the primitive.

The primitive is the sole residual, and it is the classical `H¹`/`H(curl)`
projection consistency the commutator docstrings identify as the content
beyond `L²` basis density [Temam III §3; Robinson–Rodrigo–Sadowski Ch. 4].
It is *not* the exact curl–projection commutation that is algebraically
impossible for a Schwartz basis
(`not_curl_proj_commutes_of_first_mode_not_eigenfield` [GalerkinModeData]);
it only requires boundedness and spacetime vanishing of the error, and it
follows from the banked `hCurlStable` hypotheses via
`curlSqError_integral_tendsto_zero` [GalerkinModeData].

No `sorry` is introduced here; the bridge consumes only certified providers.
-/

import Navier.Analysis.GalerkinBasis
import Navier.Analysis.GalerkinWeakConsistency
import Navier.Analysis.GalerkinModeData
import Navier.Analysis.GalerkinEnergyBudget
import Navier.Analysis.EnergyOfficialClause

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Navier.Analysis.GalerkinProjectedWeak

open Navier
open Navier.Analysis.LerayWeak
open Navier.Analysis.GalerkinBasis
open Navier.Analysis.GalerkinEnergyBudget
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity
open Navier.Analysis.EnergyPressureIntegral
open Navier.Analysis.Enstrophy
open Set MeasureTheory Filter Topology
open scoped BigOperators
open scoped LineDeriv

/-! ### The primitive -/

/-- The modal curl-projection error of a test slice family: the `L²` size of
`curl(Pₘφ(t) − φ(t))`. -/
def err (W : GalerkinBasisFamily) (φ : ℝ → SchwartzVelocity) (m : ℕ) (t : ℝ) : ℝ :=
  ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖

/-- **[The exactly-typed residual of `hprojectedWeak`.]**  For every fixed
divergence-free test function and every window `[0, T]` covering its time
support, the modal curl-projection error of its slices is uniformly bounded on
the window and vanishes in spacetime `L²(0, T)`:

* `∃ M, ∀ m t, 0 ≤ t ≤ T → ‖curl(Pₘφ(t) − φ(t))‖₂ ≤ M`;
* `∫₀ᵀ ‖curl(Pₘφ(t) − φ(t))‖₂² dt → 0`.

Plain `L²` basis density does *not* imply this — that is the content of the
`laplacianProjectionCommutator` docstring — while exact curl–projection
commutation (which no Schwartz basis can have) is far stronger than needed. -/
def GalerkinBasisFamily.fixedTestCurlErrorVanishing (W : GalerkinBasisFamily) : Prop :=
  ∀ (φ : DivergenceFreeTestFunction) (T : ℝ) (_hT : 0 ≤ T),
    (∃ M : ℝ, ∀ (m : ℕ) (t : ℝ), 0 ≤ t → t ≤ T → err W φ.field m t ≤ M) ∧
      Filter.Tendsto (fun m => ∫ t in Set.Ioc (0 : ℝ) T,
        err W φ.field m t ^ 2) Filter.atTop (nhds 0)

/-! ### Joint continuity of the fixed-test derivative bundles -/

theorem evalContinuousOn (phi : DivergenceFreeTestFunction) :
    ContinuousOn (fun z : ℝ × Space => phi.field z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
  phi.smooth.continuousOn

theorem timeDerivContinuousOn (phi : DivergenceFreeTestFunction) :
    ContinuousOn (fun z : ℝ × Space => phi.timeDerivSchwartz z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  let S : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let F : ℝ × Space → Space := fun z => phi.field z.1 z.2
  have hUD : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD : ContinuousOn
      (fun z : ℝ × Space => fderivWithin ℝ F S z (1, 0)) S :=
    ((phi.smooth.continuousOn_fderivWithin hUD (by norm_num)).clm_apply
      continuousOn_const)
  have hbridge : ∀ z ∈ S,
      fderivWithin ℝ F S z (1, 0) = phi.timeDerivSchwartz z.1 z.2 := by
    rintro ⟨t, x⟩ hz
    rw [← phi.timeDeriv_eq t hz.1 x]
    unfold timeDerivative
    have hF : HasFDerivWithinAt F (fderivWithin ℝ F S (t, x)) S (t, x) :=
      ((phi.smooth (t, x) hz).differentiableWithinAt (by simp)).hasFDerivWithinAt
    have hi : HasFDerivAt (fun s : ℝ => (s, x))
        (ContinuousLinearMap.inl ℝ ℝ Space) t := hasFDerivAt_prodMk_left t x
    have hmaps : Set.MapsTo (fun s : ℝ => (s, x)) (Set.Ici 0) S :=
      fun s hs => ⟨hs, Set.mem_univ x⟩
    have hcomp := HasFDerivWithinAt.comp t hF hi.hasFDerivWithinAt hmaps
    rw [show (F ∘ (fun s : ℝ => (s, x))) = (fun s => phi.field s x) from rfl] at hcomp
    rw [hcomp.fderivWithin ((uniqueDiffOn_Ici 0) t hz.1),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  exact hD.congr (fun z hz => (hbridge z hz).symm)

theorem curlContinuousOn (phi : DivergenceFreeTestFunction) :
    ContinuousOn (fun z : ℝ × Space => curlSchwartzCLM (phi.field z.1) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  let S : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let F : ℝ × Space → Space := fun z => phi.field z.1 z.2
  let J : Space →L[ℝ] ℝ × Space := ContinuousLinearMap.inr ℝ ℝ Space
  have hUD : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD : ContinuousOn (fun z : ℝ × Space => fderivWithin ℝ F S z) S :=
    phi.smooth.continuousOn_fderivWithin hUD (by norm_num)
  have hbridge : ∀ z ∈ S,
      (fderivWithin ℝ F S z).comp J = fderiv ℝ (⇑(phi.field z.1)) z.2 := by
    rintro ⟨t, x⟩ hz
    have hF : HasFDerivWithinAt F (fderivWithin ℝ F S (t, x)) S (t, x) :=
      ((phi.smooth (t, x) hz).differentiableWithinAt (by simp)).hasFDerivWithinAt
    have hi : HasFDerivAt (fun y : Space => (t, y)) J x :=
      hasFDerivAt_prodMk_right t x
    have hmaps : Set.MapsTo (fun y : Space => (t, y)) Set.univ S :=
      fun y _ => ⟨hz.1, Set.mem_univ y⟩
    have hcomp := HasFDerivWithinAt.comp x hF hi.hasFDerivWithinAt hmaps
    rw [show (F ∘ (fun y : Space => (t, y))) = (⇑(phi.field t) : Space → Space)
      from rfl] at hcomp
    have heq := hcomp.fderivWithin (uniqueDiffOn_univ x (Set.mem_univ x))
    simpa only [fderivWithin_univ] using heq.symm
  have hspatial : ContinuousOn
      (fun z : ℝ × Space => fderiv ℝ (⇑(phi.field z.1)) z.2) S :=
    (hD.clm_comp (show ContinuousOn (fun _ : ℝ × Space => J) S from
      continuousOn_const)).congr (fun z hz => (hbridge z hz).symm)
  rw [show (fun z : ℝ × Space => curlSchwartzCLM (phi.field z.1) z.2) =
      fun z => ∑ i : Fin 3,
        (crossProduct (basisVector i)).toContinuousLinearMap
          ((fderiv ℝ (⇑(phi.field z.1)) z.2) (basisVector i)) by
    funext z
    rw [curlSchwartzCLM_apply]
    rfl]
  apply continuousOn_finsetSum
  intro i _
  exact (crossProduct (basisVector i)).toContinuousLinearMap.continuous.comp_continuousOn
    (hspatial.clm_apply continuousOn_const)

theorem testCurl_eq_zero_of_not_mem (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0)
    (t : ℝ) {x : Space} (hx : x ∉ K) :
    curlSchwartzCLM (phi.field t) x = 0 := by
  have hevent : (⇑(phi.field t) : Space → Space) =ᶠ[nhds x]
      (fun _ : Space => (0 : Space)) := by
    filter_upwards [hK.isClosed.isOpen_compl.eventually_mem hx] with y hy
    exact hspace t y hy
  have hfd : fderiv ℝ (⇑(phi.field t)) x = 0 := by
    simpa using hevent.fderiv_eq
  rw [curlSchwartzCLM_apply]
  simp [staticCurl, hfd]

/-! ### Pairing continuity for compactly-carried families -/

theorem pairing_continuousOn
    {f : ℝ → SchwartzVelocity} {s : Set ℝ}
    (hjoint : ContinuousOn (fun z : ℝ × Space => f z.1 z.2) (s ×ˢ Set.univ))
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → f t x = 0)
    (w : SchwartzVelocity) : ContinuousOn (fun t => schwartzL2Inner (f t) w) s := by
  unfold schwartzL2Inner
  apply continuousOn_integral_of_compact_support hK
  · simp only [officialInner_eq_sum]
    apply continuousOn_finsetSum
    intro i _
    exact ((continuous_apply i).comp_continuousOn hjoint).mul
      ((((continuous_apply i).comp w.continuous).comp continuous_snd).continuousOn)
  · intro t x _ht hx
    rw [hspace t x hx, officialInner_zero_left]

theorem selfPairing_continuousOn
    {f : ℝ → SchwartzVelocity} {s : Set ℝ}
    (hjoint : ContinuousOn (fun z : ℝ × Space => f z.1 z.2) (s ×ˢ Set.univ))
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → f t x = 0) :
    ContinuousOn (fun t => schwartzL2Inner (f t) (f t)) s := by
  unfold schwartzL2Inner
  apply continuousOn_integral_of_compact_support hK
  · simp only [officialInner_eq_sum]
    apply continuousOn_finsetSum
    intro i _
    exact ((continuous_apply i).comp_continuousOn hjoint).mul
      ((continuous_apply i).comp_continuousOn hjoint)
  · intro t x _ht hx
    rw [hspace t x hx, officialInner_zero_left]

theorem norm_toL2_continuousOn
    {f : ℝ → SchwartzVelocity} {s : Set ℝ}
    (hjoint : ContinuousOn (fun z : ℝ × Space => f z.1 z.2) (s ×ˢ Set.univ))
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → f t x = 0) :
    ContinuousOn (fun t => ‖toL2 (f t)‖) s := by
  have h := selfPairing_continuousOn hjoint hK hspace
  refine (h.sqrt).congr fun t _ => ?_
  show ‖toL2 (f t)‖ = Real.sqrt (schwartzL2Inner (f t) (f t))
  rw [← norm_toL2_sq, Real.sqrt_sq (norm_nonneg _)]

/-! ### Modal test coefficient regularity -/

private theorem testField_eval_hasDerivAt
    (phi : DivergenceFreeTestFunction) {t : ℝ} (ht : 0 < t) (x : Space) :
    HasDerivAt (fun s : ℝ => phi.field s x) (phi.timeDerivSchwartz t x) t := by
  let S : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let F : ℝ × Space → Space := fun z => phi.field z.1 z.2
  have hz : (t, x) ∈ S := ⟨ht.le, Set.mem_univ x⟩
  have hF : HasFDerivWithinAt F (fderivWithin ℝ F S (t, x)) S (t, x) :=
    ((phi.smooth (t, x) hz).differentiableWithinAt
      (by simp)).hasFDerivWithinAt
  have hi : HasFDerivAt (fun s : ℝ => (s, x))
      (ContinuousLinearMap.inl ℝ ℝ Space) t := hasFDerivAt_prodMk_left t x
  have hmaps : Set.MapsTo (fun s : ℝ => (s, x)) (Set.Ici 0) S :=
    fun s hs => ⟨hs, Set.mem_univ x⟩
  have hcomp := HasFDerivWithinAt.comp t hF hi.hasFDerivWithinAt hmaps
  rw [show (F ∘ (fun s : ℝ => (s, x))) = (fun s => phi.field s x) from rfl] at hcomp
  have hwithin : HasDerivWithinAt (fun s : ℝ => phi.field s x)
      (phi.timeDerivSchwartz t x) (Set.Ici 0) t := by
    rw [← phi.timeDeriv_eq t ht.le x]
    unfold timeDerivative
    rw [hcomp.fderivWithin ((uniqueDiffOn_Ici 0) t ht.le),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    exact hcomp.hasDerivWithinAt
  exact hwithin.hasDerivAt
    (Filter.mem_of_superset (Ioi_mem_nhds ht) (Set.Ioi_subset_Ici_self))

private theorem officialInner_hasDerivAt_left {f : ℝ → Space} {f' : Space}
    {t : ℝ} (h : HasDerivAt f f' t) (y : Space) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s => officialInner (f s) y) (officialInner f' y) t := by
  let L : Space →L[ℝ] ℝ := LinearMap.mkContinuous
    { toFun := fun x => officialInner x y
      map_add' := fun x z => officialInner_add_left x z y
      map_smul' := fun c x => officialInner_smul_left c x y }
    (3 * ‖y‖) (fun x => by
      rw [Real.norm_eq_abs]
      calc
        |officialInner x y| ≤ 3 * (‖x‖ * ‖y‖) := abs_officialInner_le_three x y
        _ = (3 * ‖y‖) * ‖x‖ := by ring)
  change @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule _ _ (L ∘ f) (L f') t
  exact L.hasFDerivAt.comp_hasDerivAt t h

private theorem testPairing_hasDerivAt
    (phi : DivergenceFreeTestFunction) {t : ℝ} (ht : 0 < t)
    (w : SchwartzVelocity) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s => schwartzL2Inner (phi.field s) w)
      (schwartzL2Inner (phi.timeDerivSchwartz t) w) t := by
  obtain ⟨K, hK, hspace⟩ := phi.compact_space_deriv
  obtain ⟨C, _hC, hCbound⟩ :=
    phi.exists_uniform_timeDeriv_bound (T := 2 * t) hK
  let s : Set ℝ := Set.Icc (t / 2) (3 * t / 2)
  let bound : Space → ℝ := fun x => (3 * C) * ‖w x‖
  have ht2 : 0 < t / 2 := by linarith
  have htop : 3 * t / 2 ≤ 2 * t := by linarith
  have hs : s ∈ nhds t := by
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ r in nhds t,
      AEStronglyMeasurable (fun x => officialInner (phi.field r x) (w x)) volume :=
    Filter.Eventually.of_forall fun r =>
      (schwartzPairing_integrable (phi.field r) w).aestronglyMeasurable
  have hF_int : Integrable (fun x => officialInner (phi.field t x) (w x)) volume :=
    schwartzPairing_integrable (phi.field t) w
  have hF'_meas : AEStronglyMeasurable
      (fun x => officialInner (phi.timeDerivSchwartz t x) (w x)) volume :=
    (schwartzPairing_integrable (phi.timeDerivSchwartz t) w).aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    exact (SchwartzMap.integrable w).norm.const_mul (3 * C)
  have hbound : ∀ᵐ x ∂(volume : Measure Space), ∀ r ∈ s,
      ‖officialInner (phi.timeDerivSchwartz r x) (w x)‖ ≤ bound x := by
    filter_upwards with x
    intro r hr
    by_cases hx : x ∈ K
    · have hrange : r ∈ Set.Icc (0 : ℝ) (2 * t) := by
        dsimp [s] at hr
        exact ⟨(le_of_lt ht2).trans hr.1, hr.2.trans htop⟩
      have htd := hCbound r hrange x hx
      rw [Real.norm_eq_abs]
      calc
        |officialInner (phi.timeDerivSchwartz r x) (w x)|
            ≤ 3 * (‖phi.timeDerivSchwartz r x‖ * ‖w x‖) :=
          abs_officialInner_le_three _ _
        _ ≤ 3 * (C * ‖w x‖) := by gcongr
        _ = bound x := by simp only [bound]; ring
    · rw [hspace r x hx, officialInner_zero_left, norm_zero]
      dsimp [bound]
      positivity
  have hdiff : ∀ᵐ x ∂(volume : Measure Space), ∀ r ∈ s,
      @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
        RCLike.toInnerProductSpaceReal.toModule _ _
        (fun q => officialInner (phi.field q x) (w x))
        (officialInner (phi.timeDerivSchwartz r x) (w x)) r := by
    filter_upwards with x
    intro r hr
    apply officialInner_hasDerivAt_left
    apply testField_eval_hasDerivAt phi
    dsimp [s] at hr
    exact lt_of_lt_of_le ht2 hr.1
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas hF_int hF'_meas hbound hbound_int hdiff).2

theorem modalTestCoefficients_continuousOn (W : GalerkinBasisFamily)
    {f : ℝ → SchwartzVelocity} {s : Set ℝ}
    (hjoint : ContinuousOn (fun z : ℝ × Space => f z.1 z.2) (s ×ˢ Set.univ))
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → f t x = 0)
    (m : ℕ) : ContinuousOn (W.modalTestCoefficients f m) s := by
  let L : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap
  have hraw : ContinuousOn
      (fun t : ℝ => fun i : Fin m => schwartzL2Inner (f t) (W.w i)) s := by
    rw [continuousOn_pi]
    intro i
    exact pairing_continuousOn hjoint hK hspace (W.w i)
  change ContinuousOn
      (fun t : ℝ => L (fun i : Fin m => schwartzL2Inner (f t) (W.w i))) s
  exact L.continuous.comp_continuousOn hraw

theorem modalTestCoefficients_hasDerivAt (W : GalerkinBasisFamily)
    (phi : DivergenceFreeTestFunction) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (W.modalTestCoefficients phi.field m)
      (W.modalTestCoefficients phi.timeDerivSchwartz m t) t := by
  let L : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap
  have hraw : HasDerivAt
      (fun s : ℝ => fun i : Fin m => schwartzL2Inner (phi.field s) (W.w i))
      (fun i : Fin m => schwartzL2Inner (phi.timeDerivSchwartz t) (W.w i)) t := by
    rw [hasDerivAt_pi]
    intro i
    exact testPairing_hasDerivAt phi ht (W.w i)
  change HasDerivAt
      (fun s : ℝ => L (fun i : Fin m => schwartzL2Inner (phi.field s) (W.w i)))
      (L (fun i : Fin m => schwartzL2Inner (phi.timeDerivSchwartz t) (W.w i))) t
  exact L.hasFDerivAt.comp_hasDerivAt t hraw

/-! ### Schwartz-space bilinear algebra -/

private theorem inner_zero_right (f : SchwartzVelocity) :
    schwartzL2Inner f 0 = 0 := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_zero_left]

private theorem inner_neg_right (f g : SchwartzVelocity) :
    schwartzL2Inner f (-g) = -schwartzL2Inner f g := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_neg_left, schwartzL2Inner_comm]

private theorem inner_sum_left {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → SchwartzVelocity) (g : SchwartzVelocity) :
    schwartzL2Inner (∑ i ∈ s, f i) g = ∑ i ∈ s, schwartzL2Inner (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, schwartzL2Inner_zero_left]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, schwartzL2Inner_add_left, ih, Finset.sum_insert ha]

private theorem inner_sum_right {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : SchwartzVelocity) (g : ι → SchwartzVelocity) :
    schwartzL2Inner f (∑ i ∈ s, g i) = ∑ i ∈ s, schwartzL2Inner f (g i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, inner_zero_right]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, schwartzL2Inner_add_right, ih, Finset.sum_insert ha]

private theorem inner_smul_right (c : ℝ) (f g : SchwartzVelocity) :
    schwartzL2Inner f (c • g) = c * schwartzL2Inner f g := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_smul_left, schwartzL2Inner_comm]

private theorem inner_sub_left (f g h : SchwartzVelocity) :
    schwartzL2Inner (f - g) h = schwartzL2Inner f h - schwartzL2Inner g h := by
  rw [sub_eq_add_neg, schwartzL2Inner_add_left, schwartzL2Inner_neg_left,
    ← sub_eq_add_neg]

private theorem inner_sub_right (f g h : SchwartzVelocity) :
    schwartzL2Inner f (g - h) = schwartzL2Inner f g - schwartzL2Inner f h := by
  rw [sub_eq_add_neg, schwartzL2Inner_add_right, inner_neg_right, ← sub_eq_add_neg]

private theorem bilin_add_left (u v z : SchwartzVelocity) :
    convectionSchwartzBilin (u + v) z =
      convectionSchwartzBilin u z + convectionSchwartzBilin v z := by
  simp [convectionSchwartzBilin, componentSchwartz, Finset.sum_add_distrib]

private theorem bilin_add_right (u v z : SchwartzVelocity) :
    convectionSchwartzBilin u (v + z) =
      convectionSchwartzBilin u v + convectionSchwartzBilin u z := by
  have hderiv : ∀ i : Fin 3, ∂_{basisVector i} (v + z) =
      ∂_{basisVector i} v + ∂_{basisVector i} z := by
    intro i
    exact map_add (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i)) v z
  simp [convectionSchwartzBilin, hderiv, Finset.sum_add_distrib]

private theorem bilin_smul_left (r : ℝ) (u v : SchwartzVelocity) :
    convectionSchwartzBilin (r • u) v = r • convectionSchwartzBilin u v := by
  simp [convectionSchwartzBilin, componentSchwartz, Finset.smul_sum]

private theorem bilin_smul_right (r : ℝ) (u v : SchwartzVelocity) :
    convectionSchwartzBilin u (r • v) = r • convectionSchwartzBilin u v := by
  have hderiv : ∀ i : Fin 3, ∂_{basisVector i} (r • v) =
      r • ∂_{basisVector i} v := by
    intro i
    exact map_smul (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i)) r v
  simp [convectionSchwartzBilin, hderiv, Finset.smul_sum]

private theorem bilin_zero_left (v : SchwartzVelocity) :
    convectionSchwartzBilin 0 v = 0 := by
  simp [convectionSchwartzBilin, componentSchwartz]

private theorem bilin_zero_right (u : SchwartzVelocity) :
    convectionSchwartzBilin u 0 = 0 := by
  have hderiv : ∀ i : Fin 3, ∂_{basisVector i} (0 : SchwartzVelocity) = 0 := by
    intro i
    exact map_zero (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i))
  simp [convectionSchwartzBilin, hderiv]

private theorem bilin_neg_left (u v : SchwartzVelocity) :
    convectionSchwartzBilin (-u) v = -convectionSchwartzBilin u v := by
  rw [show (-u : SchwartzVelocity) = (-1 : ℝ) • u by simp, bilin_smul_left]
  simp

private theorem bilin_neg_right (u v : SchwartzVelocity) :
    convectionSchwartzBilin u (-v) = -convectionSchwartzBilin u v := by
  rw [show (-v : SchwartzVelocity) = (-1 : ℝ) • v by simp, bilin_smul_right]
  simp

private theorem bilin_sum_left {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → SchwartzVelocity) (v : SchwartzVelocity) :
    convectionSchwartzBilin (∑ i ∈ s, f i) v = ∑ i ∈ s,
      convectionSchwartzBilin (f i) v := by
  induction s using Finset.induction_on with
  | empty => simp [bilin_zero_left]
  | insert a s ha ih => simp [bilin_add_left, *]

private theorem bilin_sum_right {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (u : SchwartzVelocity) (f : ι → SchwartzVelocity) :
    convectionSchwartzBilin u (∑ i ∈ s, f i) = ∑ i ∈ s,
      convectionSchwartzBilin u (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [bilin_zero_right]
  | insert a s ha ih => simp [bilin_add_right, *]

private theorem bilin_sub_left (u v z : SchwartzVelocity) :
    convectionSchwartzBilin (u - v) z =
      convectionSchwartzBilin u z - convectionSchwartzBilin v z := by
  rw [sub_eq_add_neg, bilin_add_left, bilin_neg_left, ← sub_eq_add_neg]

private theorem bilin_sub_right (u v z : SchwartzVelocity) :
    convectionSchwartzBilin u (v - z) =
      convectionSchwartzBilin u v - convectionSchwartzBilin u z := by
  rw [sub_eq_add_neg, bilin_add_right, bilin_neg_right, ← sub_eq_add_neg]

private theorem lineDeriv_add (i : Fin 3) (a b : SchwartzVelocity) :
    ∂_{basisVector i} (a + b) = ∂_{basisVector i} a + ∂_{basisVector i} b :=
  map_add (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i)) a b

private theorem lineDeriv_smul (i : Fin 3) (r : ℝ) (a : SchwartzVelocity) :
    ∂_{basisVector i} (r • a) = r • ∂_{basisVector i} a :=
  map_smul (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i)) r a

private theorem laplacianSchwartz_zero : laplacianSchwartz (0 : SchwartzVelocity) = 0 := by
  have hderiv : ∀ i : Fin 3, ∂_{basisVector i} (0 : SchwartzVelocity) = 0 := by
    intro i
    exact map_zero (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i))
  unfold laplacianSchwartz
  simp only [hderiv, Finset.sum_const_zero]

private theorem laplacianSchwartz_add (f g : SchwartzVelocity) :
    laplacianSchwartz (f + g) = laplacianSchwartz f + laplacianSchwartz g := by
  unfold laplacianSchwartz
  simp only [lineDeriv_add, Finset.sum_add_distrib]

private theorem laplacianSchwartz_smul (r : ℝ) (f : SchwartzVelocity) :
    laplacianSchwartz (r • f) = r • laplacianSchwartz f := by
  unfold laplacianSchwartz
  simp only [lineDeriv_smul, Finset.smul_sum]

private theorem laplacianSchwartz_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → SchwartzVelocity) :
    laplacianSchwartz (∑ i ∈ s, f i) = ∑ i ∈ s, laplacianSchwartz (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [laplacianSchwartz_zero]
  | insert a s ha ih => simp [laplacianSchwartz_add, *]

private theorem curl_coefficientField (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) :
    curlSchwartzCLM (W.coefficientField a) =
      ∑ i : Fin m, a i • curlSchwartzCLM (W.w i) := by
  unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]

/-! ### Expanding a coefficient-field pairing into a scalar polynomial -/

theorem inner_coefficientField_left (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (x : SchwartzVelocity) :
    schwartzL2Inner (W.coefficientField a) x =
      ∑ i : Fin m, a i * schwartzL2Inner (W.w i) x := by
  unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
  rw [inner_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [schwartzL2Inner_smul_left]

/-! ### Spatial-derivative and fixed-slot convection families -/

private theorem spatialFderivContinuousOn (phi : DivergenceFreeTestFunction) :
    ContinuousOn (fun z : ℝ × Space => fderiv ℝ (⇑(phi.field z.1)) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  let S : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let F : ℝ × Space → Space := fun z => phi.field z.1 z.2
  let J : Space →L[ℝ] ℝ × Space := ContinuousLinearMap.inr ℝ ℝ Space
  have hUD : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD : ContinuousOn (fun z : ℝ × Space => fderivWithin ℝ F S z) S :=
    phi.smooth.continuousOn_fderivWithin hUD (by norm_num)
  have hbridge : ∀ z ∈ S,
      (fderivWithin ℝ F S z).comp J = fderiv ℝ (⇑(phi.field z.1)) z.2 := by
    rintro ⟨t, x⟩ hz
    have hF : HasFDerivWithinAt F (fderivWithin ℝ F S (t, x)) S (t, x) :=
      ((phi.smooth (t, x) hz).differentiableWithinAt
        (by simp)).hasFDerivWithinAt
    have hi : HasFDerivAt (fun y : Space => (t, y)) J x :=
      hasFDerivAt_prodMk_right t x
    have hmaps : Set.MapsTo (fun y : Space => (t, y)) Set.univ S :=
      fun y _ => ⟨hz.1, Set.mem_univ y⟩
    have hcomp := HasFDerivWithinAt.comp x hF hi.hasFDerivWithinAt hmaps
    rw [show (F ∘ (fun y : Space => (t, y))) = (⇑(phi.field t) : Space → Space)
      from rfl] at hcomp
    have heq := hcomp.fderivWithin (uniqueDiffOn_univ x (Set.mem_univ x))
    simpa only [fderivWithin_univ] using heq.symm
  exact (hD.clm_comp (show ContinuousOn (fun _ : ℝ × Space => J) S from
    continuousOn_const)).congr (fun z hz => (hbridge z hz).symm)

/-- The fixed-first-slot convective family `(t, x) ↦ (w·∇)φ(t)(x)` of a test
function is jointly continuous on the evolution domain. -/
theorem convectionSlotContinuousOn (phi : DivergenceFreeTestFunction)
    (w : SchwartzVelocity) :
    ContinuousOn (fun z : ℝ × Space =>
        convectionSchwartzBilin w (phi.field z.1) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hs := spatialFderivContinuousOn phi
  have key : (fun z : ℝ × Space =>
      convectionSchwartzBilin w (phi.field z.1) z.2) =
      fun z => ∑ i : Fin 3, (w z.2 i) •
        (fderiv ℝ (⇑(phi.field z.1)) z.2 (basisVector i)) := by
    funext z
    rw [convectionSchwartzBilin_apply, spatialDerivative]
    conv_lhs => rw [show w z.2 = ∑ i : Fin 3, (w z.2 i) • basisVector i from
      pi_eq_sum_univ' (w z.2)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  rw [key]
  apply continuousOn_finsetSum
  intro i _
  exact (((continuous_apply i).comp w.continuous).comp continuous_snd).continuousOn.smul
    (hs.clm_apply continuousOn_const)

/-- Off the compact carrier of the test slices, the fixed-slot convective
family vanishes: spatial derivatives of a slice that is locally zero are
zero. -/
theorem convectionSlot_eq_zero_of_not_mem (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0)
    (w : SchwartzVelocity) (t : ℝ) {x : Space} (hx : x ∉ K) :
    convectionSchwartzBilin w (phi.field t) x = 0 := by
  have hevent : (⇑(phi.field t) : Space → Space) =ᶠ[nhds x]
      (fun _ : Space => (0 : Space)) := by
    filter_upwards [hK.isClosed.isOpen_compl.eventually_mem hx] with y hy
    exact hspace t y hy
  have hfd : fderiv ℝ (⇑(phi.field t)) x = 0 := by
    simpa using hevent.fderiv_eq
  have hkey : convectionSchwartzBilin w (phi.field t) x
      = fderiv ℝ (⇑(phi.field t)) x (⇑w x) := by
    rw [convectionSchwartzBilin_apply, spatialDerivative]
  rw [hkey, hfd]
  simp

/-! ### Bridge part 2A: scalar continuity leaves and the squared curl error -/

/-- A fixed field paired against a compactly carried, jointly continuous
slice family is continuous in time. -/
theorem fixedPairingContinuousOn (w : SchwartzVelocity)
    {f : ℝ → SchwartzVelocity} {s : Set ℝ}
    (hjoint : ContinuousOn (fun z : ℝ × Space => f z.1 z.2) (s ×ˢ Set.univ))
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → f t x = 0) :
    ContinuousOn (fun t => schwartzL2Inner w (f t)) s :=
  (pairing_continuousOn hjoint hK hspace w).congr fun t _ => schwartzL2Inner_comm w (f t)

/-- The modal coefficient family `t ↦ ⟨f(t), wⱼ⟩` of a compactly carried,
jointly continuous slice family is continuous. -/
theorem coeffContinuousOn {f : ℝ → SchwartzVelocity} {s : Set ℝ}
    (hjoint : ContinuousOn (fun z : ℝ × Space => f z.1 z.2) (s ×ˢ Set.univ))
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → f t x = 0)
    (W : GalerkinBasisFamily) (j : ℕ) :
    ContinuousOn (fun t => W.coeff (f t) j) s :=
  pairing_continuousOn hjoint hK hspace (W.w j)

/-- The curl–curl pairing of a fixed mode against the test curl family is
continuous on the nonnegative half-line. -/
theorem curlSlotContinuousOn (W : GalerkinBasisFamily)
    (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0) (j : ℕ) :
    ContinuousOn (fun t => schwartzL2Inner (curlSchwartzCLM (W.w j))
        (curlSchwartzCLM (phi.field t))) (Set.Ici (0 : ℝ)) :=
  fixedPairingContinuousOn (curlSchwartzCLM (W.w j)) (curlContinuousOn phi) hK
    (fun t x hx => testCurl_eq_zero_of_not_mem phi hK hspace t hx)

/-- The squared curl norm of the test family is continuous on the
nonnegative half-line. -/
theorem selfCurlSqContinuousOn (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0) :
    ContinuousOn (fun t => schwartzL2Inner (curlSchwartzCLM (phi.field t))
        (curlSchwartzCLM (phi.field t))) (Set.Ici (0 : ℝ)) :=
  selfPairing_continuousOn (curlContinuousOn phi) hK
    (fun t x hx => testCurl_eq_zero_of_not_mem phi hK hspace t hx)

/-- The fixed-slot convection family paired against a retained mode is
continuous on the nonnegative half-line. -/
theorem convectionPairingContinuousOn (W : GalerkinBasisFamily)
    (phi : DivergenceFreeTestFunction) (w : SchwartzVelocity)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0) (j : ℕ) :
    ContinuousOn (fun t => schwartzL2Inner (W.w j)
        (convectionSchwartzBilin w (phi.field t))) (Set.Ici (0 : ℝ)) :=
  (pairing_continuousOn (convectionSlotContinuousOn phi w) hK
    (fun t x hx => convectionSlot_eq_zero_of_not_mem phi hK hspace w t hx)
    (W.w j)).congr fun t _ =>
    schwartzL2Inner_comm (W.w j) (convectionSchwartzBilin w (phi.field t))

/-- Each coefficient of a Galerkin coefficient flow is continuous on the
nonnegative half-line (the flow is differentiable there). -/
theorem cSlotContinuousOn (W : GalerkinBasisFamily) {ν : ℝ}
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) (i : Fin m) :
    ContinuousOn (fun t : ℝ => (c m t) i) (Set.Ici (0 : ℝ)) := by
  have hc_cont : ContinuousOn (c m) (Set.Ici (0 : ℝ)) :=
    fun s hs => (hc m s hs).continuousWithinAt
  have heval : Continuous fun v : EuclideanSpace ℝ (Fin m) => v i :=
    PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i
  exact heval.comp_continuousOn hc_cont

/-- The enstrophy density along a coefficient flow is integrable on every
`(0, T]` window (host continuity on `[0,∞)` plus the standard
`Icc`/`Ioc` squeeze). -/
theorem henstrophyIntegrable_of_flow (W : GalerkinBasisFamily) {ν : ℝ}
    (T : ℝ) (hT : 0 ≤ T)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) :
    IntegrableOn (fun t => W.coefficientEnstrophy (c m t)) (Set.Ioc (0 : ℝ) T) :=
  (((coefficientFlow_enstrophy_continuousOn W c hc m).mono Set.Icc_subset_Ici_self).integrableOn_Icc).mono_set
    Set.Ioc_subset_Icc_self

/-- The realized modal energy of a coefficient vector: the official Euclidean
spatial energy integral is exactly the squared Euclidean norm (orthonormality,
no dimension factor). -/
theorem energyField_eq_norm_sq (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) :
    (∫ x : Space, officialEuclideanNorm ((W.coefficientField a) x) ^ 2) = ‖a‖ ^ 2 := by
  rw [← coefficientField_l2_isometry W, schwartzL2Inner]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [officialInner_eq_sum]
  refine (Navier.Analysis.EnergyOfficialClause.officialEuclideanNorm_sq_eq_sum_sq
      (W.coefficientField a x)).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_two]

/-- The modal test projection does not change the pairing with a retained
mode: `⟨wⱼ, Pₘ u⟩ = ⟨wⱼ, u⟩` for `j < m` (orthonormality). -/
theorem wPair_proj (W : GalerkinBasisFamily) {m : ℕ} (j : Fin m)
    (u : SchwartzVelocity) :
    schwartzL2Inner (W.w j) (W.proj m u) = schwartzL2Inner (W.w j) u := by
  unfold GalerkinBasisFamily.proj
  rw [inner_sum_right]
  simp_rw [schwartzL2Inner_smul_right]
  rw [Finset.sum_eq_single (j : ℕ)]
  · rw [W.orthonormal (j : ℕ) (j : ℕ), if_pos rfl, mul_one]
    unfold GalerkinBasisFamily.coeff
    exact schwartzL2Inner_comm u (W.w j)
  · intro i _ hj
    rw [W.orthonormal j i, if_neg (by omega : ¬((j : ℕ) = i)), mul_zero]
  · intro h
    exact absurd h (by simpa [Finset.mem_range] using Fin.is_lt j)

/-- Distribution of the Schwartz Laplacian into the curl pairing (the sign
half of the viscous-commutator expansion). -/
private theorem lapFlip (u v : SchwartzVelocity) (hv : DivergenceFreeInitial v) :
    schwartzL2Inner u (laplacianSchwartz v) =
      -schwartzL2Inner (curlSchwartzCLM u) (curlSchwartzCLM v) := by
  linarith [schwartzL2Inner_curl_eq_neg_laplacian u v hv]

/-- The curl of the modal projection as a coefficient expansion. -/
private theorem curl_proj_expand (W : GalerkinBasisFamily) {m : ℕ}
    (u : SchwartzVelocity) :
    curlSchwartzCLM (W.proj m u) =
      ∑ i ∈ Finset.range m, (W.coeff u i) • curlSchwartzCLM (W.w i) := by
  unfold GalerkinBasisFamily.proj
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]

/-- The squared modal curl error, expanded as a scalar polynomial in the
modal coefficients of the slice: `‖curl(Pₘx − x)‖₂²` equals
`Σᵢₖ αᵢ αₖ ⟨curl wᵢ, curl wₖ⟩ − Σᵢ αᵢ ⟨curl wᵢ, curl x⟩ −
Σᵢ αᵢ ⟨curl x, curl wᵢ⟩ + ⟨curl x, curl x⟩`, pairings of fixed Schwartz
fields and their scalar coefficients. -/
private theorem errSqExpand (W : GalerkinBasisFamily) {m : ℕ} (x : SchwartzVelocity) :
    ‖toL2 (curlSchwartzCLM (W.proj m x - x))‖ ^ 2 =
      (∑ i ∈ Finset.range m, ∑ k ∈ Finset.range m,
          W.coeff x i * (W.coeff x k * schwartzL2Inner (curlSchwartzCLM (W.w i))
            (curlSchwartzCLM (W.w k))))
        - ∑ i ∈ Finset.range m, W.coeff x i *
            schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM x)
        - ∑ i ∈ Finset.range m, W.coeff x i *
            schwartzL2Inner (curlSchwartzCLM x) (curlSchwartzCLM (W.w i))
        + schwartzL2Inner (curlSchwartzCLM x) (curlSchwartzCLM x) := by
  rw [norm_toL2_sq, map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    curl_proj_expand]
  simp_rw [inner_sum_left, schwartzL2Inner_smul_left, inner_sum_right,
    schwartzL2Inner_smul_right, Finset.mul_sum]
  ring

/-- The squared modal curl error of a test family,
`t ↦ ‖curl(Pₘφ(t) − φ(t))‖₂²`, is continuous on the nonnegative half-line:
it is the scalar polynomial from `errSqExpand` in continuous modal
coefficients, fixed curl Gram constants, continuous curl pairings, and the
continuous self curl norm. -/
theorem errSqContinuousOn (W : GalerkinBasisFamily) (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0) (m : ℕ) :
    ContinuousOn (fun t => err W phi.field m t ^ 2) (Set.Ici (0 : ℝ)) := by
  have hj : ContinuousOn (fun z : ℝ × Space => phi.field z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := evalContinuousOn phi
  have hα (i : ℕ) :
      ContinuousOn (fun t => W.coeff (phi.field t) i) (Set.Ici (0 : ℝ)) :=
    coeffContinuousOn hj hK hspace W i
  have hδ (i : ℕ) :
      ContinuousOn (fun t => schwartzL2Inner (curlSchwartzCLM (W.w i))
          (curlSchwartzCLM (phi.field t))) (Set.Ici (0 : ℝ)) :=
    curlSlotContinuousOn W phi hK hspace i
  have hδ' (i : ℕ) :
      ContinuousOn (fun t => schwartzL2Inner (curlSchwartzCLM (phi.field t))
          (curlSchwartzCLM (W.w i))) (Set.Ici (0 : ℝ)) :=
    (hδ i).congr fun t _ => schwartzL2Inner_comm _ _
  have hS : ContinuousOn (fun t => schwartzL2Inner (curlSchwartzCLM (phi.field t))
      (curlSchwartzCLM (phi.field t))) (Set.Ici (0 : ℝ)) :=
    selfCurlSqContinuousOn phi hK hspace
  have hA : ContinuousOn (fun t => ∑ i ∈ Finset.range m, ∑ k ∈ Finset.range m,
      W.coeff (phi.field t) i * (W.coeff (phi.field t) k *
        schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM (W.w k))))
      (Set.Ici (0 : ℝ)) :=
    continuousOn_finsetSum (Finset.range m) fun i _ =>
      continuousOn_finsetSum (Finset.range m) fun k _ =>
        (hα i).mul ((hα k).mul continuousOn_const)
  have hB : ContinuousOn (fun t => ∑ i ∈ Finset.range m, W.coeff (phi.field t) i *
      schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM (phi.field t)))
      (Set.Ici (0 : ℝ)) :=
    continuousOn_finsetSum (Finset.range m) fun i _ => (hα i).mul (hδ i)
  have hC : ContinuousOn (fun t => ∑ i ∈ Finset.range m, W.coeff (phi.field t) i *
      schwartzL2Inner (curlSchwartzCLM (phi.field t)) (curlSchwartzCLM (W.w i)))
      (Set.Ici (0 : ℝ)) :=
    continuousOn_finsetSum (Finset.range m) fun i _ => (hα i).mul (hδ' i)
  have heq : (fun t => err W phi.field m t ^ 2) = fun t =>
      (∑ i ∈ Finset.range m, ∑ k ∈ Finset.range m,
          W.coeff (phi.field t) i * (W.coeff (phi.field t) k *
            schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM (W.w k))))
        - ∑ i ∈ Finset.range m, W.coeff (phi.field t) i *
            schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM (phi.field t))
        - ∑ i ∈ Finset.range m, W.coeff (phi.field t) i *
            schwartzL2Inner (curlSchwartzCLM (phi.field t))
              (curlSchwartzCLM (W.w i))
        + schwartzL2Inner (curlSchwartzCLM (phi.field t))
            (curlSchwartzCLM (phi.field t)) := by
    funext t
    exact errSqExpand W (phi.field t)
  rw [heq]
  exact ((hA.sub hB).sub hC).add hS

/-- The squared modal curl error is integrable on every `(0, T]` window. -/
theorem errSqIntegrableOn (W : GalerkinBasisFamily) (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0)
    (T : ℝ) (hT : 0 ≤ T) (m : ℕ) :
    IntegrableOn (fun t => err W phi.field m t ^ 2) (Set.Ioc (0 : ℝ) T) :=
  (((errSqContinuousOn W phi hK hspace m).mono Set.Icc_subset_Ici_self).integrableOn_Icc).mono_set
    Set.Ioc_subset_Icc_self

/-- The zero coefficient vector realizes the zero modal field. -/
private theorem coefficientField_zero (W : GalerkinBasisFamily) {m : ℕ} :
    W.coefficientField (0 : EuclideanSpace ℝ (Fin m)) = 0 := by
  ext x
  unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
  simp

/-- The `L²` norm of `toL2` vanishes at zero. -/
private theorem norm_toL2_zero : ‖toL2 (0 : SchwartzVelocity)‖ = 0 := by
  have h : ‖toL2 (0 : SchwartzVelocity)‖ ^ 2 = 0 := by
    rw [norm_toL2_sq, schwartzL2Inner_zero_left]
  have : (‖toL2 (0 : SchwartzVelocity)‖ : ℝ) ^ 2 = ‖toL2 (0 : SchwartzVelocity)‖ *
      ‖toL2 (0 : SchwartzVelocity)‖ := by ring
  rw [this, mul_self_eq_zero] at h
  exact h


/-! ### Bridge part 2B: provider integrand expansions and interval integrability -/

/-- Realize a coefficient field as the explicit mode sum (the definitional
form of `coefficientField` through `finiteModes`). -/
private theorem coefficientField_sum (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) :
    W.coefficientField a = ∑ i : Fin m, a i • W.w i := by
  unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
  rfl

/-- Pointwise scalar-polynomial expansion of the provider's main integrand at
a fixed coefficient vector: the fixed-test time-derivative pairing, the
viscous Laplacian pairing (through the curl flip), and the retained-slot
convection pairing all expand into a single `Fin m`-sum of continuous scalar
factors. -/
private theorem mainExpand (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (ν : ℝ)
    (v w' : SchwartzVelocity) (hv : DivergenceFreeInitial v) :
    schwartzL2Inner (W.coefficientField a) w' +
        schwartzL2Inner (W.coefficientField a)
          (ν • laplacianSchwartz v +
            convectionSchwartzBilin (W.coefficientField a) v) =
    ∑ i : Fin m, a i * (schwartzL2Inner (W.w i) w'
        - ν * schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM v)
        + ∑ k : Fin m, a k *
            schwartzL2Inner (W.w i) (convectionSchwartzBilin (W.w k) v)) := by
  rw [schwartzL2Inner_add_right, inner_smul_right]
  simp_rw [inner_coefficientField_left]
  simp_rw [Finset.mul_sum]
  rw [coefficientField_sum W]
  simp_rw [bilin_sum_left, bilin_smul_left, inner_sum_right, inner_smul_right]
  have hflip : ∀ u : SchwartzVelocity,
      schwartzL2Inner u (laplacianSchwartz v) =
        -schwartzL2Inner (curlSchwartzCLM u) (curlSchwartzCLM v) :=
    fun u => lapFlip u v hv
  simp_rw [hflip]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Pointwise scalar-polynomial expansion of the viscous commutator pairing
`⟨cf a, Δ(Pₘv) − Pₘ(Δv)⟩`: against the retained-mode span, the projected-Laplacian
term collapses to modal coefficient pairings of `v` against the fixed curl Gram,
and the physical term to the continuous curl pairing. -/
private theorem lapCommExpand (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (v : SchwartzVelocity)
    (hv : DivergenceFreeInitial v) :
    schwartzL2Inner (W.coefficientField a)
        (W.laplacianProjectionCommutator m v) =
    ∑ i : Fin m, a i * (schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM v)
        - ∑ k ∈ Finset.range m, W.coeff v k *
            schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM (W.w k))) := by
  unfold GalerkinBasisFamily.laplacianProjectionCommutator
  rw [inner_sub_right, coefficientField_pairing_proj W a]
  have hproj : W.proj m v = ∑ k ∈ Finset.range m, W.coeff v k • W.w k := rfl
  rw [hproj, laplacianSchwartz_sum]
  simp_rw [laplacianSchwartz_smul, inner_coefficientField_left, inner_sum_right,
    inner_smul_right]
  have hflip : ∀ u : SchwartzVelocity,
      schwartzL2Inner u (laplacianSchwartz v) =
        -schwartzL2Inner (curlSchwartzCLM u) (curlSchwartzCLM v) :=
    fun u => lapFlip u v hv
  have hflipW : ∀ (u : SchwartzVelocity) (k : ℕ),
      schwartzL2Inner u (laplacianSchwartz (W.w k)) =
        -schwartzL2Inner (curlSchwartzCLM u) (curlSchwartzCLM (W.w k)) :=
    fun u k => lapFlip u (W.w k) (W.divergence_free k)
  rw [← Finset.sum_sub_distrib]
  simp_rw [hflip, hflipW]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_neg, Finset.sum_neg_distrib, mul_sub]
  ring

/-- Pointwise scalar-polynomial expansion of the nonlinear commutator pairing
`⟨cf a, B(cf a)(Pₘv − v)⟩` into products of coefficients and fixed trilinear
constants. -/
private theorem convCommExpand (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (v : SchwartzVelocity) :
    schwartzL2Inner (W.coefficientField a)
        (W.convectionTestProjectionCommutator m (W.coefficientField a) v) =
    ∑ i : Fin m, a i * (∑ k : Fin m, a k *
        (∑ l ∈ Finset.range m, W.coeff v l *
            schwartzL2Inner (W.w i)
              (convectionSchwartzBilin (W.w k) (W.w l)) -
          schwartzL2Inner (W.w i) (convectionSchwartzBilin (W.w k) v))) := by
  unfold GalerkinBasisFamily.convectionTestProjectionCommutator
  rw [inner_coefficientField_left]
  simp_rw [coefficientField_sum W, bilin_sum_left, bilin_smul_left,
    inner_sum_right, inner_smul_right]
  have hproj : W.proj m v = ∑ l ∈ Finset.range m, W.coeff v l • W.w l := rfl
  rw [hproj]
  simp_rw [bilin_sub_right, bilin_sum_right, bilin_smul_right, inner_sub_right,
    inner_sum_right, inner_smul_right]

/-- The provider's main integrand is continuous on `[0,∞)`: through
`mainExpand` it is a polynomial in the continuous coefficient slots, the
continuous fixed-test pairings, and constants. -/
private theorem mainIntegrandContinuousOn (W : GalerkinBasisFamily)
    (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0)
    {K₂ : Set Space} (hK₂ : IsCompact K₂)
    (hspace₂ : ∀ t : ℝ, ∀ x : Space, x ∉ K₂ → phi.timeDerivSchwartz t x = 0)
    {ν : ℝ} (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) :
    ContinuousOn (fun t =>
        schwartzL2Inner (W.coefficientField (c m t)) (phi.timeDerivSchwartz t) +
          schwartzL2Inner (W.coefficientField (c m t))
            (ν • laplacianSchwartz (phi.field t) +
              convectionSchwartzBilin (W.coefficientField (c m t)) (phi.field t)))
      (Set.Ici (0 : ℝ)) := by
  have hj : ContinuousOn (fun z : ℝ × Space => phi.field z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := evalContinuousOn phi
  have heq : (fun t =>
      schwartzL2Inner (W.coefficientField (c m t)) (phi.timeDerivSchwartz t) +
        schwartzL2Inner (W.coefficientField (c m t))
          (ν • laplacianSchwartz (phi.field t) +
            convectionSchwartzBilin (W.coefficientField (c m t)) (phi.field t))) =
      fun t => ∑ i : Fin m, (c m t) i *
        (schwartzL2Inner (W.w i) (phi.timeDerivSchwartz t)
          - ν * schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM (phi.field t))
          + ∑ k : Fin m, (c m t) k *
              schwartzL2Inner (W.w i)
                (convectionSchwartzBilin (W.w k) (phi.field t))) := by
    funext t
    exact mainExpand W (c m t) ν (phi.field t) (phi.timeDerivSchwartz t)
      (phi.divergence_free t)
  rw [heq]
  refine continuousOn_finsetSum Finset.univ fun i _ => ?_
  have hci : ContinuousOn (fun t : ℝ => (c m t) i) (Set.Ici (0 : ℝ)) :=
    cSlotContinuousOn W c hc m i
  have hw' : ContinuousOn (fun t => schwartzL2Inner (W.w i) (phi.timeDerivSchwartz t))
      (Set.Ici (0 : ℝ)) :=
    fixedPairingContinuousOn (W.w i) (timeDerivContinuousOn phi) hK₂ hspace₂
  have hδ : ContinuousOn (fun t => schwartzL2Inner (curlSchwartzCLM (W.w i))
      (curlSchwartzCLM (phi.field t))) (Set.Ici (0 : ℝ)) :=
    curlSlotContinuousOn W phi hK hspace i
  have hS : ContinuousOn (fun t => ∑ k : Fin m, (c m t) k *
      schwartzL2Inner (W.w i) (convectionSchwartzBilin (W.w k) (phi.field t)))
      (Set.Ici (0 : ℝ)) :=
    continuousOn_finsetSum Finset.univ fun k _ =>
      (cSlotContinuousOn W c hc m k).mul
        (convectionPairingContinuousOn W phi (W.w k) hK hspace i)
  exact hci.mul ((hw'.sub (ContinuousOn.const_mul hδ ν)).add hS)

/-- The provider's viscous-commutator integrand is continuous on `[0,∞)`. -/
private theorem hlapIntegrandContinuousOn (W : GalerkinBasisFamily)
    (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0)
    {ν : ℝ} (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) :
    ContinuousOn (fun t => ν * schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (phi.field t)))
      (Set.Ici (0 : ℝ)) := by
  have hj : ContinuousOn (fun z : ℝ × Space => phi.field z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := evalContinuousOn phi
  have heq : (fun t => ν * schwartzL2Inner (W.coefficientField (c m t))
      (W.laplacianProjectionCommutator m (phi.field t))) = fun t =>
      ν * ∑ i : Fin m, (c m t) i *
        (schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM (phi.field t))
          - ∑ k ∈ Finset.range m, W.coeff (phi.field t) k *
              schwartzL2Inner (curlSchwartzCLM (W.w i))
                (curlSchwartzCLM (W.w k))) := by
    funext t
    rw [lapCommExpand W (c m t) (phi.field t) (phi.divergence_free t)]
  rw [heq]
  refine ContinuousOn.const_mul ?_ ν
  refine continuousOn_finsetSum Finset.univ fun i _ => ?_
  have hδ : ContinuousOn (fun t => schwartzL2Inner (curlSchwartzCLM (W.w i))
      (curlSchwartzCLM (phi.field t))) (Set.Ici (0 : ℝ)) :=
    curlSlotContinuousOn W phi hK hspace i
  have hG : ContinuousOn (fun t => ∑ k ∈ Finset.range m, W.coeff (phi.field t) k *
      schwartzL2Inner (curlSchwartzCLM (W.w i)) (curlSchwartzCLM (W.w k)))
      (Set.Ici (0 : ℝ)) :=
    continuousOn_finsetSum (Finset.range m) fun k _ =>
      (coeffContinuousOn hj hK hspace W k).mul continuousOn_const
  exact (cSlotContinuousOn W c hc m i).mul (hδ.sub hG)

/-- The provider's nonlinear-commutator integrand is continuous on `[0,∞)`. -/
private theorem hconvIntegrandContinuousOn (W : GalerkinBasisFamily)
    (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0)
    {ν : ℝ} (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) :
    ContinuousOn (fun t => schwartzL2Inner (W.coefficientField (c m t))
        (W.convectionTestProjectionCommutator m (W.coefficientField (c m t))
          (phi.field t)))
      (Set.Ici (0 : ℝ)) := by
  have hj : ContinuousOn (fun z : ℝ × Space => phi.field z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := evalContinuousOn phi
  have heq : (fun t => schwartzL2Inner (W.coefficientField (c m t))
      (W.convectionTestProjectionCommutator m (W.coefficientField (c m t))
        (phi.field t))) = fun t =>
      ∑ i : Fin m, (c m t) i * (∑ k : Fin m, (c m t) k *
        (∑ l ∈ Finset.range m, W.coeff (phi.field t) l *
            schwartzL2Inner (W.w i)
              (convectionSchwartzBilin (W.w k) (W.w l)) -
          schwartzL2Inner (W.w i)
            (convectionSchwartzBilin (W.w k) (phi.field t)))) := by
    funext t
    exact convCommExpand W (c m t) (phi.field t)
  rw [heq]
  refine continuousOn_finsetSum Finset.univ fun i _ => ?_
  refine (cSlotContinuousOn W c hc m i).mul ?_
  refine continuousOn_finsetSum Finset.univ fun k _ => ?_
  have hG : ContinuousOn (fun t => ∑ l ∈ Finset.range m, W.coeff (phi.field t) l *
      schwartzL2Inner (W.w i) (convectionSchwartzBilin (W.w k) (W.w l)))
      (Set.Ici (0 : ℝ)) :=
    continuousOn_finsetSum (Finset.range m) fun l _ =>
      (coeffContinuousOn hj hK hspace W l).mul continuousOn_const
  have hE : ContinuousOn (fun t => schwartzL2Inner (W.w i)
      (convectionSchwartzBilin (W.w k) (phi.field t))) (Set.Ici (0 : ℝ)) :=
    convectionPairingContinuousOn W phi (W.w k) hK hspace i
  exact (cSlotContinuousOn W c hc m k).mul (hG.sub hE)

/-- **Provider premise `hmainInt`.**  For every mode count and window, the
main fixed-test integrand is interval integrable. -/
theorem hmainInt_of_flow (W : GalerkinBasisFamily) (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0)
    {K₂ : Set Space} (hK₂ : IsCompact K₂)
    (hspace₂ : ∀ t : ℝ, ∀ x : Space, x ∉ K₂ → phi.timeDerivSchwartz t x = 0)
    {ν : ℝ} (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (T : ℝ) (hT : 0 ≤ T) (m : ℕ) :
    IntervalIntegrable (fun t =>
        schwartzL2Inner (W.coefficientField (c m t)) (phi.timeDerivSchwartz t) +
          schwartzL2Inner (W.coefficientField (c m t))
            (ν • laplacianSchwartz (phi.field t) +
              convectionSchwartzBilin (W.coefficientField (c m t)) (phi.field t)))
      volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hT]
  exact (mainIntegrandContinuousOn W phi hK hspace hK₂ hspace₂ c hc m).mono
    Set.Icc_subset_Ici_self

/-- **Provider premise `hlapInt`.** -/
theorem hlapInt_of_flow (W : GalerkinBasisFamily) (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0)
    {ν : ℝ} (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (T : ℝ) (hT : 0 ≤ T) (m : ℕ) :
    IntervalIntegrable (fun t => ν * schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (phi.field t))) volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hT]
  exact (hlapIntegrandContinuousOn W phi hK hspace c hc m).mono
    Set.Icc_subset_Ici_self

/-- **Provider premise `hconvInt`.** -/
theorem hconvInt_of_flow (W : GalerkinBasisFamily) (phi : DivergenceFreeTestFunction)
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → phi.field t x = 0)
    {ν : ℝ} (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (T : ℝ) (hT : 0 ≤ T) (m : ℕ) :
    IntervalIntegrable (fun t => schwartzL2Inner (W.coefficientField (c m t))
        (W.convectionTestProjectionCommutator m (W.coefficientField (c m t))
          (phi.field t))) volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hT]
  exact (hconvIntegrandContinuousOn W phi hK hspace c hc m).mono
    Set.Icc_subset_Ici_self
