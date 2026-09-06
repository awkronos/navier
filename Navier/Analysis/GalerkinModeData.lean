import Navier.Analysis.ConvectionLadyzhenskaya
import Navier.Analysis.GalerkinWeakConsistency

/-!
# Certified Galerkin support lemmas

This file retains the proved coefficient-flow equicontinuity, projection
identities, and conditional curl-error limit.  The former general
`H(curl)`-stable basis existence claim and the mode-data construction have
been removed because their source proofs contained admissions.  In
particular, this file makes no general Galerkin existence claim.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped LineDeriv

namespace Navier.Analysis.GalerkinBasis

open Navier
open Navier.Analysis.EnergyNormBridge
open Navier.Analysis.Enstrophy
open Navier.Analysis.LerayWeak
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity

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

private theorem timeDeriv_joint_continuousOn
    (phi : DivergenceFreeTestFunction) :
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
    rw [show (F ∘ (fun s : ℝ => (s, x))) = (fun s => phi.field s x) from rfl]
      at hcomp
    rw [hcomp.fderivWithin ((uniqueDiffOn_Ici 0) t hz.1),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  exact hD.congr (fun z hz => (hbridge z hz).symm)

private theorem testPairing_continuousOn_of_joint_compact
    {f : ℝ → SchwartzVelocity} {s : Set ℝ}
    (hjoint : ContinuousOn (fun z : ℝ × Space => f z.1 z.2)
      (s ×ˢ Set.univ))
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → f t x = 0)
    (w : SchwartzVelocity) :
    ContinuousOn (fun t => schwartzL2Inner (f t) w) s := by
  unfold schwartzL2Inner
  apply continuousOn_integral_of_compact_support hK
  · simp only [officialInner_eq_sum]
    apply continuousOn_finsetSum
    intro i _
    exact ((continuous_apply i).comp_continuousOn hjoint).mul
      ((((continuous_apply i).comp w.continuous).comp continuous_snd).continuousOn)
  · intro t x _ht hx
    rw [hspace t x hx, officialInner_zero_left]

private theorem modalTestCoefficients_continuousOn_of_joint_compact
    (W : GalerkinBasisFamily) {f : ℝ → SchwartzVelocity} {s : Set ℝ}
    (hjoint : ContinuousOn (fun z : ℝ × Space => f z.1 z.2)
      (s ×ˢ Set.univ))
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → f t x = 0)
    (m : ℕ) : ContinuousOn (W.modalTestCoefficients f m) s := by
  let L : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap
  have hraw : ContinuousOn
      (fun t : ℝ => fun i : Fin m => schwartzL2Inner (f t) (W.w i)) s := by
    rw [continuousOn_pi]
    intro i
    exact testPairing_continuousOn_of_joint_compact hjoint hK hspace (W.w i)
  change ContinuousOn
    (fun t : ℝ => L (fun i : Fin m => schwartzL2Inner (f t) (W.w i))) s
  exact L.continuous.comp_continuousOn hraw

private theorem modalTestCoefficients_hasDerivAt
    (W : GalerkinBasisFamily) (phi : DivergenceFreeTestFunction)
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
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

private theorem testCurl_joint_continuousOn
    (phi : DivergenceFreeTestFunction) :
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

private theorem testCurl_eq_zero_of_not_mem
    (phi : DivergenceFreeTestFunction) {K : Set Space} (hK : IsCompact K)
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

private theorem testSelfPairing_continuousOn_of_joint_compact
    {f : ℝ → SchwartzVelocity} {s : Set ℝ}
    (hjoint : ContinuousOn (fun z : ℝ × Space => f z.1 z.2)
      (s ×ˢ Set.univ))
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

private theorem schwartzL2Inner_finset_sum_left_local
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → SchwartzVelocity) (g : SchwartzVelocity) :
    schwartzL2Inner (∑ i ∈ s, f i) g = ∑ i ∈ s, schwartzL2Inner (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, schwartzL2Inner_zero_left]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, schwartzL2Inner_add_left, ih, Finset.sum_insert ha]

private theorem schwartzL2Inner_neg_right_local (f g : SchwartzVelocity) :
    schwartzL2Inner f (-g) = -schwartzL2Inner f g := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_neg_left,
    schwartzL2Inner_comm g f]

private theorem schwartzL2Inner_sub_right_local (f g h : SchwartzVelocity) :
    schwartzL2Inner f (g - h) =
      schwartzL2Inner f g - schwartzL2Inner f h := by
  rw [sub_eq_add_neg, schwartzL2Inner_add_right,
    schwartzL2Inner_neg_right_local, ← sub_eq_add_neg]

private theorem schwartzL2Inner_neg_neg_local (f g : SchwartzVelocity) :
    schwartzL2Inner (-f) (-g) = schwartzL2Inner f g := by
  rw [schwartzL2Inner_neg_left, schwartzL2Inner_neg_right_local]
  ring

private theorem convectionSchwartzBilin_add_left_local
    (u v z : SchwartzVelocity) :
    convectionSchwartzBilin (u + v) z =
      convectionSchwartzBilin u z + convectionSchwartzBilin v z := by
  simp [convectionSchwartzBilin, componentSchwartz, Finset.sum_add_distrib]

private theorem convectionSchwartzBilin_add_right_local
    (u v z : SchwartzVelocity) :
    convectionSchwartzBilin u (v + z) =
      convectionSchwartzBilin u v + convectionSchwartzBilin u z := by
  have hderiv : ∀ i : Fin 3, ∂_{basisVector i} (v + z) =
      ∂_{basisVector i} v + ∂_{basisVector i} z := by
    intro i
    exact map_add (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i)) v z
  simp [convectionSchwartzBilin, hderiv, Finset.sum_add_distrib]

private theorem convectionSchwartzBilin_smul_left_local
    (r : ℝ) (u v : SchwartzVelocity) :
    convectionSchwartzBilin (r • u) v = r • convectionSchwartzBilin u v := by
  simp [convectionSchwartzBilin, componentSchwartz, Finset.smul_sum]

private theorem convectionSchwartzBilin_smul_right_local
    (r : ℝ) (u v : SchwartzVelocity) :
    convectionSchwartzBilin u (r • v) = r • convectionSchwartzBilin u v := by
  have hderiv : ∀ i : Fin 3, ∂_{basisVector i} (r • v) =
      r • ∂_{basisVector i} v := by
    intro i
    exact map_smul (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i)) r v
  simp [convectionSchwartzBilin, hderiv, Finset.smul_sum]

private theorem convectionSchwartzBilin_sum_left_local
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (u : ι → SchwartzVelocity) (v : SchwartzVelocity) :
    convectionSchwartzBilin (∑ i ∈ s, u i) v =
      ∑ i ∈ s, convectionSchwartzBilin (u i) v := by
  induction s using Finset.induction_on with
  | empty => simp [convectionSchwartzBilin, componentSchwartz]
  | insert i s hi => simp [convectionSchwartzBilin_add_left_local, *]

private theorem convectionSchwartzBilin_sum_right_local
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (u : SchwartzVelocity) (v : ι → SchwartzVelocity) :
    convectionSchwartzBilin u (∑ i ∈ s, v i) =
      ∑ i ∈ s, convectionSchwartzBilin u (v i) := by
  induction s using Finset.induction_on with
  | empty =>
      have hderiv : ∀ i : Fin 3,
          ∂_{basisVector i} (0 : SchwartzVelocity) = 0 := by
        intro i
        exact map_zero (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i))
      simp [convectionSchwartzBilin, hderiv]
  | insert i s hi => simp [convectionSchwartzBilin_add_right_local, *]

private theorem convectionSchwartz_coefficientField_local
    (W : GalerkinBasisFamily) (m : ℕ) (a : EuclideanSpace ℝ (Fin m)) :
    convectionSchwartz (W.coefficientField a) =
      ∑ j : Fin m, ∑ k : Fin m,
        (a j * a k) • convectionSchwartzBilin (W.w j) (W.w k) := by
  unfold convectionSchwartz
  rw [show W.coefficientField a = ∑ i : Fin m, a i • W.w i from rfl,
    convectionSchwartzBilin_sum_left_local]
  apply Finset.sum_congr rfl
  intro j _
  rw [convectionSchwartzBilin_smul_left_local,
    convectionSchwartzBilin_sum_right_local, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [convectionSchwartzBilin_smul_right_local, smul_smul]

private theorem convectionSchwartzBilin_sub_right_local
    (u v z : SchwartzVelocity) :
    convectionSchwartzBilin u (v - z) =
      convectionSchwartzBilin u v - convectionSchwartzBilin u z := by
  rw [sub_eq_add_neg, convectionSchwartzBilin_add_right_local,
    show -z = (-1 : ℝ) • z by simp,
    convectionSchwartzBilin_smul_right_local]
  simp only [neg_smul, one_smul, sub_eq_add_neg]

/-- **Aubin–Lions time regularity for the Galerkin coefficient flow
(certified, no `sorry`).**  A coefficient flow solving the projected Galerkin
ODE, with a uniform time-integrated enstrophy bound, is `L²`-in-time
translation equicontinuous *uniformly in the mode count `m`*.

This is the residual of the `time_equicontinuous` field of
`exists_galerkinModeData` after `timeEquicontinuous_of_coefficientDisplacement`
discharges the spatial half.  It is strictly lower than what it replaces: the
conclusion mentions only `ℝ^m`-valued curves — no Schwartz field, no spatial
integral, no basis property — and it is not circular, since nothing in its
proof may use the time equicontinuity it supplies.

**Quantifier order is load-bearing and is the strong form.**  `∃ δ` stands
*outside* `∀ m`.  The per-`m` form `∀ m, ∃ δ` is dischargeable from continuity
of each individual curve alone and carries no compactness content whatsoever;
it is exactly the weakening that would make `aubin_lions_l2loc_compactness`
false.  The family `c m t = (sin (m t)) • e₀` satisfies the per-`m` form and
violates this one, so the statement is not vacuous.  It is also satisfiable —
`c ≡ 0` inhabits it — so no consumer is vacuously true through it.

Classical route: pair the Galerkin ODE with the displacement itself,
`‖c(t+h) − c(t)‖² = ∫_t^{t+h} ⟨c'(s), c(t+h) − c(t)⟩ ds`, and integrate in `t`.
The viscous term is handled by the certified Stokes Cauchy–Schwarz
`abs_stokesOperator_inner_le` together with `henst`: Fubini over the strip of
width `h` and Cauchy–Schwarz in `(s,t)` give `O(ν · h · enstrophyBound)`, which
is uniform in `m` and vanishes with `h`.  This is the linear half, and its
ingredients are now all in the estate.
The convective term `⟨B(c(s)), c(t+h) − c(t)⟩` now has an off-diagonal size
estimate: `ConvectionTrilinear.abs_convectionOperator_inner_le` (certified,
downstream of this file) gives
`|⟨B(a), b⟩| ≤ √3 · ‖u_a‖²_{L⁴} · ‖∇u_b‖_{L²}` with `u_a = W.coefficientField a`
— the exact counterpart of `convectionOperator_inner_self` on the diagonal
[Temam, *Navier–Stokes Equations* III §3; Robinson–Rodrigo–Sadowski Ch. 4;
Simon, Ann. Mat. Pura Appl. 146 (1987) 65–96, Thm 1 condition (iii)].

The Ladyzhenskaya estimate this leaf needs is now certified end to end and in
this statement's own coordinates:
`ConvectionLadyzhenskaya.abs_convectionOperator_inner_pow_four_le_enstrophy`
gives `|⟨B(a), b⟩|⁴ ≤ C·‖a‖²·Ω(a)³·Ω(b)²` with `Ω = W.coefficientEnstrophy`,
one constant for every `m` and every `W`.  Its chain is
`ConvectionTrilinear.abs_convectionOperator_inner_le` (Hölder `(4,2,4)`) →
`Ladyzhenskaya.integral_pow_four_le_sqrt` (interpolation) →
`SobolevGNS.exists_gns_six` (the Gagliardo–Nirenberg–Sobolev endpoint for
Schwartz fields, obtained by removing Mathlib's `HasCompactSupport` hypothesis
with a cutoff-and-limit argument) →
`DivFreeGradientEnstrophy.integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree`
(Dirichlet energy ≤ 3·enstrophy for divergence-free fields).

Remaining: only the Aubin–Lions assembly itself.  Both halves of the
integrand are now stocked — viscous by `abs_stokesOperator_inner_le`,
convective by the estimate above — and what is left is pairing the ODE with
the displacement, Fubini over the strip of width `h`, and Cauchy–Schwarz in
`(s, t)`, with `henst` supplying the uniform-in-`m` `Ω` budget on both.
Estimated ~250 LOC, no missing analytic ingredient. -/
theorem galerkinCoefficientFlow_timeEquicontinuous (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (enstrophyBound : ℝ)
    (henst : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound) :
    ∀ T ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ) (h : ℝ), |h| < δ →
      (∫ t in Set.Ioc (0:ℝ) T,
        ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2) ≤ ε := by
  obtain ⟨C, hC0, hC⟩ :=
    Navier.Analysis.ConvectionLadyzhenskaya.abs_convectionOperator_inner_pow_four_le_enstrophy
  exact galerkinCoefficientFlow_timeEquicontinuous_of_convectionEstimate W hν c hc
    enstrophyBound henst hC0 (fun m a b => hC W m a b)

/-- `‖·‖_{L²}` of a Schwartz velocity as the square root of its own `L²`
pairing.  Bridges `norm_toL2_sq` to the continuity lemmas, which are stated
for the pairing. -/
private theorem norm_toL2_eq_sqrt (u : SchwartzVelocity) :
    ‖toL2 u‖ = Real.sqrt (schwartzL2Inner u u) := by
  rw [← norm_toL2_sq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- Time continuity of `t ↦ ‖f t‖_{L²}` for a jointly continuous, uniformly
compactly supported slice family. -/
private theorem norm_toL2_continuousOn_of_joint_compact
    {f : ℝ → SchwartzVelocity} {s : Set ℝ}
    (hjoint : ContinuousOn (fun z : ℝ × Space => f z.1 z.2) (s ×ˢ Set.univ))
    {K : Set Space} (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → f t x = 0) :
    ContinuousOn (fun t => ‖toL2 (f t)‖) s := by
  have h := testSelfPairing_continuousOn_of_joint_compact hjoint hK hspace
  exact (Real.continuous_sqrt.comp_continuousOn h).congr
    fun t _ => norm_toL2_eq_sqrt (f t)

/-- Exact curl--projection commutation forces the first Galerkin mode to be a
curl eigenfield.  This is the finite-dimensional algebraic half of the
whole-space obstruction: ruling out Schwartz curl eigenfields is sufficient
to refute the commutation route. -/
theorem curl_proj_commutes_forces_first_mode_eigenfield
    (W : GalerkinBasisFamily)
    (hcurl_commutes : ∀ (m : ℕ) (u : SchwartzVelocity),
      curlSchwartzCLM (W.proj m u) = W.proj m (curlSchwartzCLM u)) :
    curlSchwartzCLM (W.w 0) =
      schwartzL2Inner (curlSchwartzCLM (W.w 0)) (W.w 0) • W.w 0 := by
  calc
    curlSchwartzCLM (W.w 0) = curlSchwartzCLM (W.proj 1 (W.w 0)) := by
      rw [proj_basis W (by omega)]
    _ = W.proj 1 (curlSchwartzCLM (W.w 0)) := hcurl_commutes 1 (W.w 0)
    _ = schwartzL2Inner (curlSchwartzCLM (W.w 0)) (W.w 0) • W.w 0 := by
      simp [GalerkinBasisFamily.proj, GalerkinBasisFamily.coeff]

/-- A no-eigenfield theorem for the first mode refutes exact projection--curl
commutation.  The remaining analytic leaf is precisely the absence of
Schwartz curl eigenfields on `ℝ³`; no basis-construction assumptions are hidden
in this reduction. -/
theorem not_curl_proj_commutes_of_first_mode_not_eigenfield
    (W : GalerkinBasisFamily)
    (hnoeig : ∀ a : ℝ, curlSchwartzCLM (W.w 0) ≠ a • W.w 0) :
    ¬ ∀ (m : ℕ) (u : SchwartzVelocity),
      curlSchwartzCLM (W.proj m u) = W.proj m (curlSchwartzCLM u) := by
  intro hcomm
  exact hnoeig _ (curl_proj_commutes_forces_first_mode_eigenfield W hcomm)

/-- **[CERTIFIED — no `sorry` in this declaration.]**  The spacetime curl
projection error of a fixed test function vanishes in the limit.

Given graph-density and uniform `H(curl)`-stability of the projections — the
two clauses of `exists_hCurlStableGalerkinBasisFamily` — the pointwise-in-time
limit is `curl_proj_converges`, and the dominating function is the uniform
stability bound applied to the test slice itself, which is continuous in time
and hence integrable on the finite window.  Dominated convergence closes it.

This replaces the former inline "Banach–Steinhaus + DCT" conjecture of
`exists_galerkinModeData`: no equicontinuity argument is needed once the
stability constant is a hypothesis rather than something to be extracted. -/
theorem curlSqError_integral_tendsto_zero (W : GalerkinBasisFamily)
    (hgraph_dense : ∀ u : SchwartzVelocity, DivergenceFreeInitial u →
      ∀ ε : ℝ, 0 < ε → ∃ (M : ℕ) (c : ℕ → ℝ),
        ‖toL2 (u - ∑ j ∈ Finset.range M, c j • W.w j)‖ < ε ∧
        ‖toL2 (curlSchwartzCLM
          (u - ∑ j ∈ Finset.range M, c j • W.w j))‖ < ε)
    (hstable : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (u : SchwartzVelocity),
      ‖toL2 (curlSchwartzCLM (W.proj m u))‖ ≤
        C * (‖toL2 u‖ + ‖toL2 (curlSchwartzCLM u)‖))
    (phi : DivergenceFreeTestFunction) {T : ℝ}
    (hint : ∀ m : ℕ, IntegrableOn (fun t =>
      ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2)
      (Set.Ioc (0 : ℝ) T)) :
    Filter.Tendsto (fun m : ℕ =>
        ∫ t in Set.Ioc (0 : ℝ) T,
          ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2)
      Filter.atTop (nhds 0) := by
  classical
  obtain ⟨C, hC, hstab⟩ := hstable
  obtain ⟨Kfield, hKfield, hfield_space⟩ := phi.compact_space
  have hfield_joint : ContinuousOn (fun z : ℝ × Space => phi.field z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := phi.smooth.continuousOn
  have hcurl_joint : ContinuousOn
      (fun z : ℝ × Space => curlSchwartzCLM (phi.field z.1) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := testCurl_joint_continuousOn phi
  have hcurl_space : ∀ t : ℝ, ∀ x : Space, x ∉ Kfield →
      curlSchwartzCLM (phi.field t) x = 0 :=
    fun t x hx => testCurl_eq_zero_of_not_mem phi hKfield hfield_space t hx
  have hn0 : ContinuousOn (fun t => ‖toL2 (phi.field t)‖) (Set.Ici (0 : ℝ)) :=
    norm_toL2_continuousOn_of_joint_compact hfield_joint hKfield hfield_space
  have hn1 : ContinuousOn (fun t => ‖toL2 (curlSchwartzCLM (phi.field t))‖)
      (Set.Ici (0 : ℝ)) :=
    norm_toL2_continuousOn_of_joint_compact hcurl_joint hKfield hcurl_space
  set g : ℝ → ℝ := fun t =>
    (C * (‖toL2 (phi.field t)‖ + ‖toL2 (curlSchwartzCLM (phi.field t))‖)
      + ‖toL2 (curlSchwartzCLM (phi.field t))‖) ^ 2 with hgdef
  have hgcont : ContinuousOn g (Set.Ici (0 : ℝ)) :=
    (((hn0.add hn1).const_mul C).add hn1).pow 2
  have hgint : IntegrableOn g (Set.Ioc (0 : ℝ) T) :=
    ((hgcont.mono Set.Icc_subset_Ici_self).integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hbd : ∀ (m : ℕ) (t : ℝ),
      ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ≤
        C * (‖toL2 (phi.field t)‖ + ‖toL2 (curlSchwartzCLM (phi.field t))‖)
          + ‖toL2 (curlSchwartzCLM (phi.field t))‖ := by
    intro m t
    rw [map_sub, toL2_sub]
    exact (norm_sub_le _ _).trans
      (add_le_add (hstab m (phi.field t)) le_rfl)
  have hlim : ∀ t : ℝ, Filter.Tendsto (fun m : ℕ =>
      ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2)
      Filter.atTop (nhds 0) := by
    intro t
    have h := curl_proj_converges W hgraph_dense ⟨C, hC, hstab⟩
      (phi.field t) (phi.divergence_free t)
    simpa using h.pow 2
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume.restrict (Set.Ioc (0 : ℝ) T)))
    (F := fun (m : ℕ) (t : ℝ) =>
      ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2)
    (f := fun _ : ℝ => (0 : ℝ)) g
    (fun m => (hint m).aestronglyMeasurable) hgint
    (fun m => Filter.Eventually.of_forall fun t => by
      have h0 : (0 : ℝ) ≤
          ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2 := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0, hgdef]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbd m t) 2)
    (Filter.Eventually.of_forall hlim)
  simpa using hmain

end Navier.Analysis.GalerkinBasis
