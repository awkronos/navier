import Navier.Analysis.ConvectionLadyzhenskaya
import Navier.Analysis.GalerkinWeakConsistency

/-!
# The Galerkin mode-data construction, downstream of the convective estimate

This file is the downstream home of the two declarations that cannot live in
`Navier.Analysis.GalerkinBasis`:

* `galerkinCoefficientFlow_timeEquicontinuous` — the Aubin–Lions time-regularity
  theorem for the coefficient flow.  Its whole mathematical content is
  certified upstream as
  `galerkinCoefficientFlow_timeEquicontinuous_of_convectionEstimate`; what it
  additionally needs is
  `ConvectionLadyzhenskaya.abs_convectionOperator_inner_pow_four_le_enstrophy`,
  and that estimate is *strictly downstream* of `GalerkinBasis`, since
  `ConvectionTrilinear` imports `GalerkinBasis` for the definition of
  `convectionOperator` itself.  The import cycle is the only reason this
  declaration is not in `GalerkinBasis`; the statement is unchanged, and in
  particular its `∃ δ` still stands outside `∀ m`.

* `exists_galerkinModeData` — the finite-mode Galerkin construction, which
  consumes the theorem above.  It moved with its consumer for the same reason.

Both keep the namespace `Navier.Analysis.GalerkinBasis`, so every existing
reference to `GalerkinBasis.exists_galerkinModeData` resolves unchanged.
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

/-- **[NAMED RESIDUAL — an `H(curl)`-stable divergence-free Galerkin basis of
`ℝ³`; Lemarié-Rieusset, *Rev. Mat. Iberoamericana* **8** (1992) 221–237
(divergence-free wavelet bases); Urban, *Wavelet Methods for Elliptic PDEs*
(2009) Ch. 5; Robinson–Rodrigo–Sadowski, *The Three-Dimensional Navier–Stokes
Equations* Ch. 4; est ~450 LOC.]**

A `GalerkinBasisFamily` whose finite spans are dense in the *graph* norm of
`curl` and whose `L²`-orthogonal projections are uniformly `H(curl)`-bounded.

**Why this is a genuinely new obligation, and not a repackaging of
`exists_galerkinBasisFamily`.**  `dense_span` is `L²`-density only, and an
`L²`-orthogonal projection is not `H¹`-bounded for an arbitrary ordering; the
two clauses here are exactly the hypotheses `curl_proj_converges` consumes,
and they are what the weak-consistency limit passage of
`exists_galerkinModeData` needs (see `curlSqError_integral_tendsto_zero`
immediately below, which is kernel-clean given them).

**The exact-commutation route is not an alternative: it is unsatisfiable.**
`curl_proj_converges_of_commutes` and `curl_proj_sq_le_of_commutes` assume
`curl ∘ P_m = P_m ∘ curl`.  That hypothesis has no witness on `ℝ³`.  Taking
`m = 1` and `u = w 0` gives `curl (w 0) = λ • w 0` with
`λ = ⟪curl (w 0), w 0⟫`; since `w 0` is divergence-free,
`-Δ (w 0) = curl (curl (w 0)) = λ² • w 0`, so the Fourier transform of `w 0`
— itself Schwartz, hence continuous — is supported in the sphere `‖ξ‖ = |λ|`,
a null set, forcing `w 0 = 0` against `⟪w 0, w 0⟫ = 1`.  The finite-mode
reduction is now mechanized by
`curl_proj_commutes_forces_first_mode_eigenfield` and
`not_curl_proj_commutes_of_first_mode_not_eigenfield`; the exact remaining
leaf is the no-Schwartz-curl-eigenfield theorem.  (The same argument
kills the "Stokes-eigenbasis realization" suggested in the route analysis of
`exists_galerkinModeData`: the Stokes operator on the whole space has no
`L²` eigenfunctions.)  Status of that argument: **ARGUED, NOT MECHANIZED** —
it needs vector-valued Plancherel on `ℝ³`, which the pinned Mathlib
does not carry for `SchwartzVelocity`; it is recorded here so the dead route
is not attempted again, and it is why this leaf asks for *stability*
(`C`-bounded) rather than *commutation* (`C = 1`, equality).

**Satisfiability.**  Divergence-free wavelet bases on `ℝ³` supply both
clauses: their multiresolution spans are dense in `H(curl)` and the
associated `L²`-orthogonal projections are `H^s`-stable for `|s| < 3/2`
uniformly in the level, with `C` the Riesz constant of the basis.  This
existence is not certified in-repo; it is the whole content of this leaf. -/
theorem exists_hCurlStableGalerkinBasisFamily :
    ∃ W : GalerkinBasisFamily,
      (∀ u : SchwartzVelocity, DivergenceFreeInitial u →
        ∀ ε : ℝ, 0 < ε → ∃ (M : ℕ) (c : ℕ → ℝ),
          ‖toL2 (u - ∑ j ∈ Finset.range M, c j • W.w j)‖ < ε ∧
          ‖toL2 (curlSchwartzCLM
            (u - ∑ j ∈ Finset.range M, c j • W.w j))‖ < ε) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (u : SchwartzVelocity),
        ‖toL2 (curlSchwartzCLM (W.proj m u))‖ ≤
          C * (‖toL2 u‖ + ‖toL2 (curlSchwartzCLM u)‖)) := by
  sorry

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

/-- **Finite-mode Galerkin construction from the certified divergence-free
    basis (Temam III.3; Constantin--Foias II; Leray, Acta Math. 63 (1934) sections 18--20).**

    Given the LerayWeak divergence-free basis, this constructs a concrete
    `GalerkinModeData` for any divergence-free Schwartz datum and any positive
    viscosity.  The proof:

    1. Obtain a certified `GalerkinBasisFamily` from `exists_galerkinBasisFamily`.
    2. For each mode count `m`, apply `exists_forward_galerkinCoefficientFlow`
       to the projected Stokes and convection operators, obtaining a forward
       differentiable coefficient curve with the projected initial data.
    3. Realise the coefficient curves as physical velocity fields via
       `GalerkinBasisFamily.modalApprox`.

    All fields of `GalerkinModeData` that follow from basis orthonormality,
    the coefficient ODE structure, or the projected energy-dissipation identity
    are discharged here.

    **Residual inventory, corrected 2026-08-22 (lane sorry-close).**  The
    previous text listed `hspace`, `htime` and `hweak` as NAMED RESIDUALS.
    That is stale: `hspace` is discharged at step 5 through
    `GalerkinSpaceEquicontinuity.spaceEquicontinuous_of_modalFamily`, and
    `htime` at step 6 through `timeEquicontinuous_of_coefficientDisplacement`
    composed with `galerkinCoefficientFlow_timeEquicontinuous` (closed in
    `435a6eb`).  **`hweak` is the sole remaining residual of this theorem.**
  -/
  theorem exists_galerkinModeData (nu : ℝ) (hnu : 0 < nu)
      (u0 : SchwartzVelocity) (hu0 : DivergenceFreeInitial u0) :
      Nonempty (GalerkinModeData nu u0) := by
    -- 1. Divergence-free basis with graph-density and uniform H(curl)-stable
    -- projections (`exists_hCurlStableGalerkinBasisFamily`).  This is a
    -- STRENGTHENING of step 1: `exists_galerkinBasisFamily` alone gives only
    -- `L²`-density, which is provably insufficient for the weak-consistency
    -- limit passage at step 10 (see the leaf's docstring).
    obtain ⟨W, hgraph_dense, hstable⟩ := exists_hCurlStableGalerkinBasisFamily
    -- 2. For each m, get a forward coefficient curve solving the projected ODE
    have hB_skew (m : ℕ) (a : EuclideanSpace ℝ (Fin m)) :
        inner ℝ (W.convectionOperator m a) a = 0 :=
      convectionOperator_inner_self W m a
    have hB_C1 (m : ℕ) : ContDiff ℝ 1 (W.convectionOperator m) :=
      convectionOperator_contDiff W m
    have hcoeff (m : ℕ) :
        exists u : ℝ → EuclideanSpace ℝ (Fin m),
          u 0 = W.initialCoefficients u0 m ∧
          (∀ t : ℝ, 0 ≤ t →
            HasDerivWithinAt u
              (-(nu • W.stokesOperator m (u t)) + W.convectionOperator m (u t))
              (Set.Ici (0 : ℝ)) t) ∧
          ∀ t : ℝ, 0 ≤ t → ‖u t‖ ^ 2 ≤ ‖W.initialCoefficients u0 m‖ ^ 2 :=
      exists_forward_galerkinCoefficientFlow nu hnu.le (W.stokesOperator m)
        (stokesOperator_nonneg W m) (W.convectionOperator m)
        (convectionOperator_contDiff W m) (hB_skew m)
        (W.initialCoefficients u0 m)
    let cChoice (m : ℕ) : ℝ → EuclideanSpace ℝ (Fin m) := (hcoeff m).choose
    have hc0 (m : ℕ) : cChoice m 0 = W.initialCoefficients u0 m :=
      (hcoeff m).choose_spec.1
    have hc_deriv (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
        HasDerivWithinAt (cChoice m)
          (-(nu • W.stokesOperator m (cChoice m t)) + W.convectionOperator m (cChoice m t))
          (Set.Ici (0 : ℝ)) t := by
      rcases (hcoeff m).choose_spec with ⟨hc0', hcderiv', hcnorm'⟩
      exact hcderiv' t ht
    have hc_norm (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
        ‖cChoice m t‖ ^ 2 ≤ ‖W.initialCoefficients u0 m‖ ^ 2 :=
      (hcoeff m).choose_spec.2.2 t ht
    -- 3. Constant and kinetic bounds (Euclidean datum energy)
    let bound : ℝ := ∫ x : Space, ∑ i : Fin 3, (u0 x i) ^ 2
    have hbound_nonneg : 0 ≤ bound := by
      refine integral_nonneg fun x => ?_
      exact Finset.sum_nonneg fun i _ => pow_two_nonneg _
    have hbound_le : bound ≤ bound := le_rfl
    have hinner_eq : schwartzL2Inner u0 u0 = bound := by
      simp [bound, schwartzL2Inner, officialEuclideanNorm_sq_eq_sum_sq]
    have hofficial : UniformOfficialKineticBound (W.modalApprox cChoice) bound := by
      intro m' t' ht'
      rw [modalApprox_kineticEnergy_eq W cChoice m' t',
        forwardExtend_eq_of_nonneg (cChoice m') ht']
      calc
        ‖cChoice m' t'‖ ^ 2 ≤ ‖W.initialCoefficients u0 m'‖ ^ 2 := hc_norm m' t' ht'
        _ ≤ schwartzL2Inner u0 u0 := initialCoefficients_norm_sq_le W u0 m'
        _ = bound := hinner_eq
    have hkin : UniformKineticBound (W.modalApprox cChoice) bound := by
      have hmeas : ∀ (m' : ℕ) (t' : ℝ), 0 ≤ t' → AEStronglyMeasurable (W.modalApprox cChoice m' t') := by
        intro m' t' ht'
        refine (Continuous.aestronglyMeasurable ?_)
        unfold GalerkinBasisFamily.modalApprox galerkinModalApprox
        refine (continuous_finsetSum (Finset.univ : Finset (Fin m')) fun i hi => ?_)
        have hw : Continuous (W.finiteModes m' i) :=
          (W.finiteModes m' i).continuous
        have hc : Continuous fun (x : Space) => forwardExtend (cChoice m') t' i := continuous_const
        exact hc.smul hw
      have hint : ∀ (m' : ℕ) (t' : ℝ), 0 ≤ t' →
          Integrable (fun x : Space => ‖W.modalApprox cChoice m' t' x‖ ^ 2) := by
        intro m' t' ht'
        simpa [GalerkinBasisFamily.modalApprox] using
          galerkinModalApprox_sq_integrable (fun m => m) cChoice (fun m => W.finiteModes m) m' t' ht'
      exact uniformKineticBound_of_official hmeas hint hofficial
    -- 4. Enstrophy bound (separate constant, handles all nu > 0)
    let enstrophyBound : ℝ := bound / (2 * nu)
    have henstrophyBound_nonneg : 0 ≤ enstrophyBound := by
      positivity
    have henstrophy_budget (m : ℕ) : ‖cChoice m 0‖ ^ 2 / (2 * nu) ≤ enstrophyBound := by
      have h0norm : ‖cChoice m 0‖ ^ 2 ≤ schwartzL2Inner u0 u0 := by
        calc
          ‖cChoice m 0‖ ^ 2 = ‖W.initialCoefficients u0 m‖ ^ 2 := by rw [hc0 m]
          _ ≤ schwartzL2Inner u0 u0 := initialCoefficients_norm_sq_le W u0 m
      dsimp [enstrophyBound]
      have hpos : 0 < 2 * nu := by positivity
      have hpos_nonneg : 0 ≤ 2 * nu := by positivity
      have hdiv : ‖cChoice m 0‖ ^ 2 / (2 * nu) ≤ schwartzL2Inner u0 u0 / (2 * nu) := by
        have := div_le_div_of_nonneg_right h0norm hpos_nonneg
        -- div_le_div_of_nonneg_right has type: a ≤ b → 0 ≤ c → a / c ≤ b / c
        simpa using this
      calc
        ‖cChoice m 0‖ ^ 2 / (2 * nu) ≤ schwartzL2Inner u0 u0 / (2 * nu) := hdiv
        _ = bound / (2 * nu) := by rw [hinner_eq]
    have henstrophy : UniformEnstrophyBound (W.modalApprox cChoice) enstrophyBound :=
      modalApprox_uniformEnstrophyBound W hnu
        (fun m => W.stokesOperator m) (fun m => W.convectionOperator m) cChoice hc_deriv
        (convectionOperator_inner_self W) (stokesOperator_inner_eq_enstrophy W) enstrophyBound
        henstrophy_budget
    -- 5. Space equicontinuity -- CLOSED (Brezis + dissipation, via
    -- `GalerkinSpaceEquicontinuity.spaceEquicontinuous_of_modalFamily`)
    let cChoiceExt (m : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin m) := cChoice m (max t 0)
    have hc_cont : ∀ m, Continuous (cChoiceExt m) := by
      intro m
      have hc_contOn : ContinuousOn (cChoice m) (Set.Ici (0 : ℝ)) := by
        intro t ht
        exact (hc_deriv m t ht).continuousWithinAt
      have hc_max : Continuous (fun (t : ℝ) => max t 0) :=
        continuous_id.max continuous_zero
      have hc_range : ∀ t : ℝ, max t 0 ∈ Set.Ici (0 : ℝ) := by
        intro t; exact Set.mem_Ici.mpr (by simpa using le_max_right 0 t)
      exact hc_contOn.comp_continuous hc_max hc_range
    have hdiv : ∀ (m : ℕ) (i : Fin m), DivergenceFreeInitial (W.finiteModes m i) := by
      intro m i
      have h := W.divergence_free (i : ℕ)
      simpa [GalerkinBasisFamily.finiteModes] using h
    have h_modal_eq : ∀ (m : ℕ) (t : ℝ) (x : Space),
        W.modalApprox cChoice m t x = (Navier.Analysis.GalerkinSpaceEquicontinuity.modalField
          (W.finiteModes) cChoiceExt m t) x := by
      intro m t x
      simp [GalerkinBasisFamily.modalApprox, galerkinModalApprox, forwardExtend,
        cChoiceExt, Navier.Analysis.GalerkinSpaceEquicontinuity.modalField,
        GalerkinBasisFamily.finiteModes]
    have h_modal_eq_fun : W.modalApprox cChoice =
        (fun (m : ℕ) (t : ℝ) (x : Space) =>
          (Navier.Analysis.GalerkinSpaceEquicontinuity.modalField (W.finiteModes) cChoiceExt m t) x) := by
      funext m t x; exact h_modal_eq m t x
    have henst' : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
        ∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space,
          Navier.Analysis.OfficialABEncoding.officialEuclideanNorm
            (Navier.Analysis.Vorticity.staticCurl (⇑(Navier.Analysis.GalerkinSpaceEquicontinuity.modalField
              (W.finiteModes) cChoiceExt m t)) x) ^ 2 ≤ enstrophyBound := by
      intro m T hT
      have h_ens := henstrophy m T hT
      have h_eq_int : (∫ t in Set.Ioc (0:ℝ) T, enstrophy (W.modalApprox cChoice m) t) =
          ∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space,
            Navier.Analysis.OfficialABEncoding.officialEuclideanNorm
              (Navier.Analysis.Vorticity.staticCurl (⇑(Navier.Analysis.GalerkinSpaceEquicontinuity.modalField
                (W.finiteModes) cChoiceExt m t)) x) ^ 2 := by
        refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioc ?_
        filter_upwards with t ht
        have ht_nonneg : 0 ≤ t := ht.1.le
        calc
          enstrophy (W.modalApprox cChoice m) t
              = ∫ x : Space, officialEuclideanNorm (staticCurl ((W.modalApprox cChoice m) t) x) ^ 2 := rfl
          _ = ∫ x : Space, officialEuclideanNorm (staticCurl ((Navier.Analysis.GalerkinSpaceEquicontinuity.modalField
                (W.finiteModes) cChoiceExt m) t) x) ^ 2 := by
            have hfun_eq : (W.modalApprox cChoice m) t = (Navier.Analysis.GalerkinSpaceEquicontinuity.modalField
                (W.finiteModes) cChoiceExt m) t := by
              funext x; exact h_modal_eq m t x
            simp [hfun_eq]
      rw [h_eq_int] at h_ens
      exact h_ens
    have hspace_raw : SpaceEquicontinuous
        (fun (m : ℕ) (t : ℝ) (x : Space) =>
          (Navier.Analysis.GalerkinSpaceEquicontinuity.modalField (W.finiteModes) cChoiceExt m t) x) :=
      Navier.Analysis.GalerkinSpaceEquicontinuity.spaceEquicontinuous_of_modalFamily
        (W.finiteModes) hdiv cChoiceExt hc_cont enstrophyBound henstrophyBound_nonneg henst'
    have hspace : SpaceEquicontinuous (W.modalApprox cChoice) := by
      rw [h_modal_eq_fun]; exact hspace_raw
    -- 6. Time equicontinuity -- REDUCED to the coefficient-level Aubin-Lions
    -- leaf `galerkinCoefficientFlow_timeEquicontinuous`.  The spatial half is
    -- certified (`timeEquicontinuous_of_coefficientDisplacement`), so nothing
    -- about Schwartz fields, spatial integrals or the basis survives into the
    -- residual; what remains is a statement about `ℝ^m`-valued curves.
    have hcontFE : ∀ m : ℕ, Continuous (fun t : ℝ => forwardExtend (cChoice m) t) :=
      fun m => hc_cont m
    have henstCoef : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
        (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (cChoice m t)) ≤
          enstrophyBound := by
      intro m T hT
      have hcongr : (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (cChoice m t)) =
          ∫ t in Set.Ioc (0:ℝ) T, enstrophy (W.modalApprox cChoice m) t := by
        refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioc ?_
        filter_upwards with t ht
        exact (modalApprox_enstrophy_eq W cChoice m ht.1.le).symm
      rw [hcongr]
      exact henstrophy m T hT
    have htime : TimeEquicontinuous (W.modalApprox cChoice) :=
      timeEquicontinuous_of_coefficientDisplacement W cChoice hcontFE
        (galerkinCoefficientFlow_timeEquicontinuous W hnu cChoice hc_deriv
          enstrophyBound henstCoef)
    -- 7. Joint measurability -- discharged from the ODE forward-extension
    have hjoint : JointlyMeasurable (W.modalApprox cChoice) := by
      simpa [GalerkinBasisFamily.modalApprox] using
        galerkinModalApprox_jointlyMeasurable (fun m => m) cChoice
          (fun m t => -(nu • W.stokesOperator m (cChoice m t)) + W.convectionOperator m (cChoice m t))
          hc_deriv (fun m => W.finiteModes m)
    -- 8. Square integrability -- discharged via finite Schwartz modes
    have hsq : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
        Integrable (fun x : Space => ‖W.modalApprox cChoice m t x‖ ^ 2) := by
      intro m t ht
      simpa [GalerkinBasisFamily.modalApprox] using
        galerkinModalApprox_sq_integrable (fun m => m) cChoice (fun m => W.finiteModes m) m t ht
    -- 9. Initial convergence in L^2 -- banked
    have hinit : Filter.Tendsto (fun m => ∫ x : Space,
        officialInner ((W.proj m u0 - u0) x) ((W.proj m u0 - u0) x))
        Filter.atTop (nhds 0) :=
      proj_initial_converges_L2 W u0 hu0
    -- 10. Weak consistency -- NAMED RESIDUAL (Galerkin equation limit passage)
    --
    -- Reference: Temam, `Navier-Stokes Equations` III.3; Constantin-Foias II;
    -- Leray, Acta Math. 63 (1934) sections 18-20.
    --
    -- ROUTE ANALYSIS (lane sorry-close, 2026-08-22).  The assembly in
    -- `GalerkinBasis` already reduces this to two scalar commutator integrals:
    -- `modalFlow_fixedTest_projectedResidual_tendsto_of_commutators` consumes
    -- `hlap`/`hconv` (the Laplacian- and convection-test projection
    -- commutators paired against the retained field, integrated on `[0,T]`),
    -- and `modalApprox_fixedTest_weakConsistent_of_projectedDatum` removes the
    -- projected-datum correction via `proj_error_pairing_tendsto_zero`.  So
    -- everything except `hlap`, `hconv` and their interval-integrability is
    -- banked.
    --
    -- The Laplacian commutator is NOT an unmotivated extra hypothesis, and it
    -- is not the graph-norm obstruction the definition's docstring warns
    -- about, once the retained field is used.  Because `cChoice m t` lies in
    -- the retained span and `W.proj m` is the `L^2`-orthogonal projection onto
    -- that span, `⟪u_m, P_m(Δφ)⟫ = ⟪P_m u_m, Δφ⟫ = ⟪u_m, Δφ⟫`, hence
    --
    --   ⟪u_m, Δ(P_m φ) - P_m(Δφ)⟫ = ⟪u_m, Δ(P_m φ - φ)⟫ = -⟪∇u_m, ∇(P_m φ - φ)⟫
    --
    -- by integration by parts (both arguments are Schwartz).  Cauchy-Schwarz in
    -- spacetime against the enstrophy budget already established above
    -- (`henstCoef`/`henstrophy`, using `∫‖curl u‖² = ∫‖∇u‖²` for
    -- divergence-free fields) then gives
    --
    --   |∫₀^T ν⟪u_m, comm⟫| ≤ ν √enstrophyBound · √(∫₀^T ‖∇(P_m φ(t) - φ(t))‖²)
    --
    -- So `hlap` follows from a STRICTLY LOWER leaf: `H¹`-convergence of the
    -- basis projections on the fixed test slices,
    --   `∫₀^T ‖∇(P_m φ(t) - φ(t))‖² dt → 0`,
    -- which is a property of `GalerkinBasisFamily` alone (no PDE content).
    -- This is NOT available from the current basis interface: the family is
    -- Gram-Schmidt of a family dense in `L²` only, and an `L²`-orthogonal
    -- projection is not `H¹`-bounded in general.  Closing `hweak` therefore
    -- needs either (i) an `H¹`-density/`H¹`-boundedness clause added to
    -- `GalerkinBasisFamily` (a statement-level change, deliberately not taken
    -- here), or (ii) a Stokes-eigenbasis realization, for which the commutator
    -- is identically zero because `Δ` commutes with the spectral projection.
    -- Estimated ~250 LOC for `hlap` given (i); `hconv` is the same
    -- Cauchy-Schwarz against `convectionTestProjectionCommutator`, whose
    -- `L²`-bound layer is already certified at `GalerkinBasis:3696-3790`.
    have hweak : ∀ phi : DivergenceFreeTestFunction,
        Filter.Tendsto (fun m => weakFormResidual nu u0 (W.modalApprox cChoice m) phi)
          Filter.atTop (nhds 0) := by
      intro phi
      -- 1. Compactly supported test function: pick T large enough
      obtain ⟨T_phi, hTpos, hφzero⟩ := phi.compact_time
      obtain ⟨T_phi', hTpos', hφ'zero⟩ := phi.compact_time_deriv
      let T := max T_phi T_phi'
      have hTpos : 0 < T := lt_max_of_lt_left hTpos
      have hT : 0 ≤ T := by linarith
      have hφzero' : ∀ t, T ≤ t → phi.field t = 0 := by
        intro t ht; exact hφzero t (le_trans (le_max_left _ _) ht)
      have hφ''zero : ∀ t, T ≤ t → phi.timeDerivSchwartz t = 0 := by
        intro t ht; exact hφ'zero t (le_trans (le_max_right _ _) ht)
      -- 2. Modal coefficient regularity on the actual FTC window.
      obtain ⟨Kfield, hKfield, hfield_space⟩ := phi.compact_space
      obtain ⟨Kderiv, hKderiv, hderiv_space⟩ := phi.compact_space_deriv
      have hwindow : Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set Space) ⊆
          Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space) := by
        rintro ⟨t, x⟩ htx
        exact ⟨htx.1.1, Set.mem_univ x⟩
      have hfield_joint : ContinuousOn
          (fun z : ℝ × Space => phi.field z.1 z.2)
          (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
        phi.smooth.continuousOn.mono hwindow
      have hderiv_joint : ContinuousOn
          (fun z : ℝ × Space => phi.timeDerivSchwartz z.1 z.2)
          (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
        (timeDeriv_joint_continuousOn phi).mono hwindow
      have hmodal_cont : ∀ m, ContinuousOn
          (W.modalTestCoefficients phi.field m) (Set.Icc (0 : ℝ) T) := by
        intro m
        exact modalTestCoefficients_continuousOn_of_joint_compact W
          hfield_joint hKfield hfield_space m
      have hmodal_deriv : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) T →
          HasDerivAt (W.modalTestCoefficients phi.field m)
            (W.modalTestCoefficients phi.timeDerivSchwartz m t) t := by
        intro m t ht
        exact modalTestCoefficients_hasDerivAt W phi m ht.1
      have hmodal_deriv_cont : ∀ m, ContinuousOn
          (W.modalTestCoefficients phi.timeDerivSchwartz m)
          (Set.Icc (0 : ℝ) T) := by
        intro m
        exact modalTestCoefficients_continuousOn_of_joint_compact W
          hderiv_joint hKderiv hderiv_space m
      -- 3. All integrability hypotheses: the integrands are continuous on ℝ,
      -- hence integrable on the compact interval [0,T].  The proofs are
      -- straightforward from the continuity of the various maps
      -- (coefficientEnstrophy, curlSchwartzCLM, etc.) but are not yet
      -- mechanized as standalone lemmas, so we leave them as CONJECTURE.
      have henstrophyIntegrable : ∀ m, IntegrableOn
          (fun t => W.coefficientEnstrophy (cChoice m t)) (Set.Ioc (0 : ℝ) T) := by
        intro m
        have hcont : ContinuousOn
            (fun t => W.coefficientEnstrophy (cChoice m t))
            (Set.Icc (0 : ℝ) T) :=
          (coefficientFlow_enstrophy_continuousOn W cChoice hc_deriv m).mono
            (fun _ ht => Set.mem_Ici.mpr ht.1)
        exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      have errorSqIntegrable : ∀ m, IntegrableOn (fun t =>
          ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2)
          (Set.Ioc (0 : ℝ) T) := by
        intro m
        have hcurl_joint : ContinuousOn
            (fun z : ℝ × Space => curlSchwartzCLM (phi.field z.1) z.2)
            (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
          (testCurl_joint_continuousOn phi).mono hwindow
        have hcurl_space : ∀ t : ℝ, ∀ x : Space, x ∉ Kfield →
            curlSchwartzCLM (phi.field t) x = 0 :=
          fun t x hx => testCurl_eq_zero_of_not_mem phi hKfield hfield_space t hx
        have hprojSelf : ContinuousOn (fun t =>
            W.coefficientEnstrophy (W.modalTestCoefficients phi.field m t))
            (Set.Icc (0 : ℝ) T) := by
          have hbase : ContinuousOn (fun t => inner ℝ
              (W.stokesOperator m (W.modalTestCoefficients phi.field m t))
              (W.modalTestCoefficients phi.field m t)) (Set.Icc (0 : ℝ) T) :=
            ((W.stokesOperator m).continuous.comp_continuousOn (hmodal_cont m)).inner
              (hmodal_cont m)
          exact hbase.congr fun t _ =>
            (stokesOperator_inner_eq_enstrophy W m
              (W.modalTestCoefficients phi.field m t)).symm
        have hmix : ContinuousOn (fun t =>
            schwartzL2Inner
              (curlSchwartzCLM
                (W.coefficientField (W.modalTestCoefficients phi.field m t)))
              (curlSchwartzCLM (phi.field t))) (Set.Icc (0 : ℝ) T) := by
          have hsum : ContinuousOn (fun t => ∑ i : Fin m,
              W.modalTestCoefficients phi.field m t i *
                schwartzL2Inner (curlSchwartzCLM (phi.field t))
                  (curlSchwartzCLM (W.w i))) (Set.Icc (0 : ℝ) T) := by
            apply continuousOn_finsetSum
            intro i _
            have hcoord : ContinuousOn
                (fun t => W.modalTestCoefficients phi.field m t i)
                (Set.Icc (0 : ℝ) T) :=
              (PiLp.proj (p := (2 : ENNReal)) (𝕜 := ℝ)
                (β := fun _ : Fin m => ℝ) i).continuous.comp_continuousOn (hmodal_cont m)
            exact hcoord.mul
              (testPairing_continuousOn_of_joint_compact hcurl_joint hKfield
                hcurl_space (curlSchwartzCLM (W.w i)))
          refine hsum.congr ?_
          intro t _
          change schwartzL2Inner
              (curlSchwartzCLM
                (W.coefficientField (W.modalTestCoefficients phi.field m t)))
              (curlSchwartzCLM (phi.field t)) = _
          rw [show W.coefficientField (W.modalTestCoefficients phi.field m t) =
              ∑ i : Fin m, W.modalTestCoefficients phi.field m t i • W.w i from rfl,
            map_sum, schwartzL2Inner_finset_sum_left_local]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul, schwartzL2Inner_smul_left, schwartzL2Inner_comm]
        have htestSelf : ContinuousOn (fun t =>
            schwartzL2Inner (curlSchwartzCLM (phi.field t))
              (curlSchwartzCLM (phi.field t))) (Set.Icc (0 : ℝ) T) :=
          testSelfPairing_continuousOn_of_joint_compact
            hcurl_joint hKfield hcurl_space
        have herr (t : ℝ) :
            ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2 =
              W.coefficientEnstrophy (W.modalTestCoefficients phi.field m t) -
                2 * schwartzL2Inner
                  (curlSchwartzCLM
                    (W.coefficientField (W.modalTestCoefficients phi.field m t)))
                  (curlSchwartzCLM (phi.field t)) +
                schwartzL2Inner (curlSchwartzCLM (phi.field t))
                  (curlSchwartzCLM (phi.field t)) := by
          rw [norm_toL2_sq,
            ← coefficientField_modalTestCoefficients W phi.field m t, map_sub,
            sub_eq_add_neg, schwartzL2Inner_add_left, schwartzL2Inner_add_right,
            schwartzL2Inner_add_right,
            schwartzL2Inner_neg_left, schwartzL2Inner_neg_right_local,
            schwartzL2Inner_neg_neg_local,
            coefficientEnstrophy_eq_curlSchwartz,
            schwartzL2Inner_comm (curlSchwartzCLM (phi.field t))
              (curlSchwartzCLM
                (W.coefficientField (W.modalTestCoefficients phi.field m t)))]
          ring
        have hcont : ContinuousOn (fun t =>
            ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2)
            (Set.Icc (0 : ℝ) T) := by
          exact (hprojSelf.sub (hmix.const_mul 2)).add htestSelf |>.congr
            (fun t _ => herr t)
        exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      have pairingIntervalIntegrable : ∀ m, IntervalIntegrable (fun t =>
          nu * schwartzL2Inner (W.coefficientField (cChoice m t))
            (W.laplacianProjectionCommutator m (phi.field t))) volume 0 T := by
        intro m
        have hcChoice_cont : ContinuousOn (cChoice m) (Set.Icc (0 : ℝ) T) := by
          intro t ht
          exact (hc_deriv m t ht.1).continuousWithinAt.mono Set.Icc_subset_Ici_self
        have hcurl_joint : ContinuousOn
            (fun z : ℝ × Space => curlSchwartzCLM (phi.field z.1) z.2)
            (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
          (testCurl_joint_continuousOn phi).mono hwindow
        have hcurl_space : ∀ t : ℝ, ∀ x : Space, x ∉ Kfield →
            curlSchwartzCLM (phi.field t) x = 0 :=
          fun t x hx => testCurl_eq_zero_of_not_mem phi hKfield hfield_space t hx
        have hmodeError (i : Fin m) : ContinuousOn (fun t =>
            schwartzL2Inner (curlSchwartzCLM (W.w i))
              (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t)))
            (Set.Icc (0 : ℝ) T) := by
          have hprojMode : ContinuousOn (fun t =>
              W.stokesOperator m (W.modalTestCoefficients phi.field m t) i)
              (Set.Icc (0 : ℝ) T) :=
            (PiLp.proj (p := (2 : ENNReal)) (𝕜 := ℝ)
              (β := fun _ : Fin m => ℝ) i).continuous.comp_continuousOn
                ((W.stokesOperator m).continuous.comp_continuousOn (hmodal_cont m))
          have htestMode : ContinuousOn (fun t =>
              schwartzL2Inner (curlSchwartzCLM (W.w i))
                (curlSchwartzCLM (phi.field t))) (Set.Icc (0 : ℝ) T) :=
            (testPairing_continuousOn_of_joint_compact hcurl_joint hKfield
              hcurl_space (curlSchwartzCLM (W.w i))).congr
                (fun t _ => schwartzL2Inner_comm _ _)
          refine (hprojMode.sub htestMode).congr ?_
          intro t _
          change schwartzL2Inner (curlSchwartzCLM (W.w i))
              (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t)) =
            W.stokesOperator m (W.modalTestCoefficients phi.field m t) i -
              schwartzL2Inner (curlSchwartzCLM (W.w i))
                (curlSchwartzCLM (phi.field t))
          rw [← coefficientField_modalTestCoefficients W phi.field m t, map_sub,
            schwartzL2Inner_sub_right_local, stokesOperator_apply]
        have hcurlPair : ContinuousOn (fun t =>
            schwartzL2Inner (curlSchwartzCLM (W.coefficientField (cChoice m t)))
              (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t)))
            (Set.Icc (0 : ℝ) T) := by
          have hsum : ContinuousOn (fun t => ∑ i : Fin m,
              cChoice m t i * schwartzL2Inner (curlSchwartzCLM (W.w i))
                (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t)))
              (Set.Icc (0 : ℝ) T) := by
            apply continuousOn_finsetSum
            intro i _
            have hcoord : ContinuousOn (fun t => cChoice m t i)
                (Set.Icc (0 : ℝ) T) :=
              (PiLp.proj (p := (2 : ENNReal)) (𝕜 := ℝ)
                (β := fun _ : Fin m => ℝ) i).continuous.comp_continuousOn
                  hcChoice_cont
            exact hcoord.mul (hmodeError i)
          refine hsum.congr ?_
          intro t _
          change schwartzL2Inner
              (curlSchwartzCLM (W.coefficientField (cChoice m t)))
              (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t)) =
            ∑ i : Fin m, cChoice m t i *
              schwartzL2Inner (curlSchwartzCLM (W.w i))
                (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))
          rw [show W.coefficientField (cChoice m t) =
              ∑ i : Fin m, cChoice m t i • W.w i from rfl,
            map_sum, schwartzL2Inner_finset_sum_left_local]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul, schwartzL2Inner_smul_left]
        have hpairing : ContinuousOn (fun t =>
            schwartzL2Inner (W.coefficientField (cChoice m t))
              (W.laplacianProjectionCommutator m (phi.field t)))
            (Set.Icc (0 : ℝ) T) := by
          exact hcurlPair.neg.congr fun t _ =>
            coefficientField_laplacianProjectionCommutator_pairing_eq_neg_curl_error
              W (cChoice m t) (phi.field t) (phi.divergence_free t)
        exact (hpairing.const_mul nu).intervalIntegrable_of_Icc hT
      have hlapInt : ∀ m, IntervalIntegrable (fun t =>
          nu * schwartzL2Inner (W.coefficientField (cChoice m t))
            (W.laplacianProjectionCommutator m (phi.field t))) volume 0 T :=
        pairingIntervalIntegrable
      have hconvInt : ∀ m, IntervalIntegrable (fun t =>
          schwartzL2Inner (W.coefficientField (cChoice m t))
            (W.convectionTestProjectionCommutator m (W.coefficientField (cChoice m t))
              (phi.field t))) volume 0 T := by
        intro m
        have hcChoice_cont : ContinuousOn (cChoice m) (Set.Icc (0 : ℝ) T) := by
          intro t ht
          exact (hc_deriv m t ht.1).continuousWithinAt.mono Set.Icc_subset_Ici_self
        have hcoord (i : Fin m) : ContinuousOn (fun t => cChoice m t i)
            (Set.Icc (0 : ℝ) T) :=
          (PiLp.proj (p := (2 : ENNReal)) (𝕜 := ℝ)
            (β := fun _ : Fin m => ℝ) i).continuous.comp_continuousOn hcChoice_cont
        have hprojected : ContinuousOn (fun t =>
            schwartzL2Inner (W.coefficientField (cChoice m t))
              (convectionSchwartzBilin (W.coefficientField (cChoice m t))
                (W.coefficientField (W.modalTestCoefficients phi.field m t))))
            (Set.Icc (0 : ℝ) T) := by
          have hB : ContinuousOn (fun t => W.convectionOperator m (cChoice m t))
              (Set.Icc (0 : ℝ) T) :=
            (convectionOperator_contDiff W m).continuous.comp_continuousOn hcChoice_cont
          refine (hB.inner (hmodal_cont m)).congr ?_
          intro t _
          change schwartzL2Inner (W.coefficientField (cChoice m t))
              (convectionSchwartzBilin (W.coefficientField (cChoice m t))
                (W.coefficientField (W.modalTestCoefficients phi.field m t))) =
            inner ℝ (W.convectionOperator m (cChoice m t))
              (W.modalTestCoefficients phi.field m t)
          rw [← coefficientField_l2_inner,
            convectionOperator_pairing]
        have hfixedConvection : ContinuousOn (fun t =>
            schwartzL2Inner (convectionSchwartz (W.coefficientField (cChoice m t)))
              (phi.field t)) (Set.Icc (0 : ℝ) T) := by
          have hsum : ContinuousOn (fun t => ∑ j : Fin m, ∑ k : Fin m,
              (cChoice m t j * cChoice m t k) *
                schwartzL2Inner (convectionSchwartzBilin (W.w j) (W.w k))
                  (phi.field t)) (Set.Icc (0 : ℝ) T) := by
            apply continuousOn_finsetSum
            intro j _
            apply continuousOn_finsetSum
            intro k _
            have htest : ContinuousOn (fun t =>
                schwartzL2Inner (convectionSchwartzBilin (W.w j) (W.w k))
                  (phi.field t)) (Set.Icc (0 : ℝ) T) :=
              (testPairing_continuousOn_of_joint_compact hfield_joint hKfield
                hfield_space (convectionSchwartzBilin (W.w j) (W.w k))).congr
                  (fun t _ => schwartzL2Inner_comm _ _)
            exact ((hcoord j).mul (hcoord k)).mul htest
          refine hsum.congr ?_
          intro t _
          change schwartzL2Inner
              (convectionSchwartz (W.coefficientField (cChoice m t)))
              (phi.field t) = ∑ j : Fin m, ∑ k : Fin m,
                (cChoice m t j * cChoice m t k) *
                  schwartzL2Inner (convectionSchwartzBilin (W.w j) (W.w k))
                    (phi.field t)
          rw [convectionSchwartz_coefficientField_local,
            schwartzL2Inner_finset_sum_left_local]
          apply Finset.sum_congr rfl
          intro j _
          rw [schwartzL2Inner_finset_sum_left_local]
          apply Finset.sum_congr rfl
          intro k _
          rw [schwartzL2Inner_smul_left]
        have hfixed : ContinuousOn (fun t =>
            schwartzL2Inner (W.coefficientField (cChoice m t))
              (convectionSchwartzBilin (W.coefficientField (cChoice m t))
                (phi.field t))) (Set.Icc (0 : ℝ) T) := by
          exact hfixedConvection.neg.congr fun t _ =>
            schwartzL2Inner_convection_skew
              (W.coefficientField (cChoice m t)) (phi.field t)
              (coefficientField_divergenceFree W (cChoice m t))
        have hcomm : ContinuousOn (fun t =>
            schwartzL2Inner (W.coefficientField (cChoice m t))
              (W.convectionTestProjectionCommutator m
                (W.coefficientField (cChoice m t)) (phi.field t)))
            (Set.Icc (0 : ℝ) T) := by
          refine (hprojected.sub hfixed).congr ?_
          intro t _
          change schwartzL2Inner (W.coefficientField (cChoice m t))
              (convectionSchwartzBilin (W.coefficientField (cChoice m t))
                (W.proj m (phi.field t) - phi.field t)) =
            schwartzL2Inner (W.coefficientField (cChoice m t))
                (convectionSchwartzBilin (W.coefficientField (cChoice m t))
                  (W.coefficientField (W.modalTestCoefficients phi.field m t))) -
              schwartzL2Inner (W.coefficientField (cChoice m t))
                (convectionSchwartzBilin (W.coefficientField (cChoice m t))
                  (phi.field t))
          rw [convectionSchwartzBilin_sub_right_local,
            schwartzL2Inner_sub_right_local,
            ← coefficientField_modalTestCoefficients W phi.field m t]
        exact hcomm.intervalIntegrable_of_Icc hT
      have hmainInt : ∀ m, IntervalIntegrable (fun t =>
          schwartzL2Inner (W.coefficientField (cChoice m t)) (phi.timeDerivSchwartz t) +
          schwartzL2Inner (W.coefficientField (cChoice m t))
            (nu • laplacianSchwartz (phi.field t) +
              convectionSchwartzBilin (W.coefficientField (cChoice m t)) (phi.field t)))
          volume 0 T := by
        intro m
        have hcChoice_cont : ContinuousOn (cChoice m) (Set.Icc (0 : ℝ) T) := by
          intro t ht
          exact (hc_deriv m t ht.1).continuousWithinAt.mono Set.Icc_subset_Ici_self
        have hcoord (i : Fin m) : ContinuousOn (fun t => cChoice m t i)
            (Set.Icc (0 : ℝ) T) :=
          (PiLp.proj (p := (2 : ENNReal)) (𝕜 := ℝ)
            (β := fun _ : Fin m => ℝ) i).continuous.comp_continuousOn hcChoice_cont
        have htimePairing : ContinuousOn (fun t =>
            schwartzL2Inner (W.coefficientField (cChoice m t))
              (phi.timeDerivSchwartz t)) (Set.Icc (0 : ℝ) T) := by
          have hsum : ContinuousOn (fun t => ∑ i : Fin m,
              cChoice m t i * schwartzL2Inner (W.w i)
                (phi.timeDerivSchwartz t)) (Set.Icc (0 : ℝ) T) := by
            apply continuousOn_finsetSum
            intro i _
            have htest : ContinuousOn (fun t =>
                schwartzL2Inner (W.w i) (phi.timeDerivSchwartz t))
                (Set.Icc (0 : ℝ) T) :=
              (testPairing_continuousOn_of_joint_compact hderiv_joint hKderiv
                hderiv_space (W.w i)).congr
                  (fun t _ => schwartzL2Inner_comm _ _)
            exact (hcoord i).mul htest
          refine hsum.congr ?_
          intro t _
          change schwartzL2Inner (W.coefficientField (cChoice m t))
              (phi.timeDerivSchwartz t) = ∑ i : Fin m,
                cChoice m t i * schwartzL2Inner (W.w i)
                  (phi.timeDerivSchwartz t)
          rw [show W.coefficientField (cChoice m t) =
              ∑ i : Fin m, cChoice m t i • W.w i from rfl,
            schwartzL2Inner_finset_sum_left_local]
          apply Finset.sum_congr rfl
          intro i _
          rw [schwartzL2Inner_smul_left]
        have hcurl_joint : ContinuousOn
            (fun z : ℝ × Space => curlSchwartzCLM (phi.field z.1) z.2)
            (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
          (testCurl_joint_continuousOn phi).mono hwindow
        have hcurl_space : ∀ t : ℝ, ∀ x : Space, x ∉ Kfield →
            curlSchwartzCLM (phi.field t) x = 0 :=
          fun t x hx => testCurl_eq_zero_of_not_mem phi hKfield hfield_space t hx
        have hcurlPairing : ContinuousOn (fun t =>
            schwartzL2Inner (curlSchwartzCLM (W.coefficientField (cChoice m t)))
              (curlSchwartzCLM (phi.field t))) (Set.Icc (0 : ℝ) T) := by
          have hsum : ContinuousOn (fun t => ∑ i : Fin m,
              cChoice m t i * schwartzL2Inner (curlSchwartzCLM (W.w i))
                (curlSchwartzCLM (phi.field t))) (Set.Icc (0 : ℝ) T) := by
            apply continuousOn_finsetSum
            intro i _
            have htest : ContinuousOn (fun t =>
                schwartzL2Inner (curlSchwartzCLM (W.w i))
                  (curlSchwartzCLM (phi.field t))) (Set.Icc (0 : ℝ) T) :=
              (testPairing_continuousOn_of_joint_compact hcurl_joint hKfield
                hcurl_space (curlSchwartzCLM (W.w i))).congr
                  (fun t _ => schwartzL2Inner_comm _ _)
            exact (hcoord i).mul htest
          refine hsum.congr ?_
          intro t _
          change schwartzL2Inner
              (curlSchwartzCLM (W.coefficientField (cChoice m t)))
              (curlSchwartzCLM (phi.field t)) = ∑ i : Fin m,
                cChoice m t i * schwartzL2Inner (curlSchwartzCLM (W.w i))
                  (curlSchwartzCLM (phi.field t))
          rw [show W.coefficientField (cChoice m t) =
              ∑ i : Fin m, cChoice m t i • W.w i from rfl,
            map_sum, schwartzL2Inner_finset_sum_left_local]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul, schwartzL2Inner_smul_left]
        have hlaplacianPairing : ContinuousOn (fun t =>
            schwartzL2Inner (W.coefficientField (cChoice m t))
              (laplacianSchwartz (phi.field t))) (Set.Icc (0 : ℝ) T) := by
          refine hcurlPairing.neg.congr ?_
          intro t _
          have hcurl := schwartzL2Inner_curl_eq_neg_laplacian
            (W.coefficientField (cChoice m t)) (phi.field t)
              (phi.divergence_free t)
          linarith
        have hfixedConvection : ContinuousOn (fun t =>
            schwartzL2Inner (convectionSchwartz (W.coefficientField (cChoice m t)))
              (phi.field t)) (Set.Icc (0 : ℝ) T) := by
          have hsum : ContinuousOn (fun t => ∑ j : Fin m, ∑ k : Fin m,
              (cChoice m t j * cChoice m t k) *
                schwartzL2Inner (convectionSchwartzBilin (W.w j) (W.w k))
                  (phi.field t)) (Set.Icc (0 : ℝ) T) := by
            apply continuousOn_finsetSum
            intro j _
            apply continuousOn_finsetSum
            intro k _
            have htest : ContinuousOn (fun t =>
                schwartzL2Inner (convectionSchwartzBilin (W.w j) (W.w k))
                  (phi.field t)) (Set.Icc (0 : ℝ) T) :=
              (testPairing_continuousOn_of_joint_compact hfield_joint hKfield
                hfield_space (convectionSchwartzBilin (W.w j) (W.w k))).congr
                  (fun t _ => schwartzL2Inner_comm _ _)
            exact ((hcoord j).mul (hcoord k)).mul htest
          refine hsum.congr ?_
          intro t _
          change schwartzL2Inner
              (convectionSchwartz (W.coefficientField (cChoice m t)))
              (phi.field t) = ∑ j : Fin m, ∑ k : Fin m,
                (cChoice m t j * cChoice m t k) *
                  schwartzL2Inner (convectionSchwartzBilin (W.w j) (W.w k))
                    (phi.field t)
          rw [convectionSchwartz_coefficientField_local,
            schwartzL2Inner_finset_sum_left_local]
          apply Finset.sum_congr rfl
          intro j _
          rw [schwartzL2Inner_finset_sum_left_local]
          apply Finset.sum_congr rfl
          intro k _
          rw [schwartzL2Inner_smul_left]
        have hconvectionPairing : ContinuousOn (fun t =>
            schwartzL2Inner (W.coefficientField (cChoice m t))
              (convectionSchwartzBilin (W.coefficientField (cChoice m t))
                (phi.field t))) (Set.Icc (0 : ℝ) T) := by
          exact hfixedConvection.neg.congr fun t _ =>
            schwartzL2Inner_convection_skew
              (W.coefficientField (cChoice m t)) (phi.field t)
              (coefficientField_divergenceFree W (cChoice m t))
        have hmain : ContinuousOn (fun t =>
            schwartzL2Inner (W.coefficientField (cChoice m t))
                (phi.timeDerivSchwartz t) +
              schwartzL2Inner (W.coefficientField (cChoice m t))
                (nu • laplacianSchwartz (phi.field t) +
                  convectionSchwartzBilin (W.coefficientField (cChoice m t))
                    (phi.field t))) (Set.Icc (0 : ℝ) T) := by
          refine (htimePairing.add
            ((hlaplacianPairing.const_mul nu).add hconvectionPairing)).congr ?_
          intro t _
          change schwartzL2Inner (W.coefficientField (cChoice m t))
                (phi.timeDerivSchwartz t) +
              schwartzL2Inner (W.coefficientField (cChoice m t))
                (nu • laplacianSchwartz (phi.field t) +
                  convectionSchwartzBilin (W.coefficientField (cChoice m t))
                    (phi.field t)) =
            schwartzL2Inner (W.coefficientField (cChoice m t))
                (phi.timeDerivSchwartz t) +
              (nu * schwartzL2Inner (W.coefficientField (cChoice m t))
                  (laplacianSchwartz (phi.field t)) +
                schwartzL2Inner (W.coefficientField (cChoice m t))
                  (convectionSchwartzBilin (W.coefficientField (cChoice m t))
                    (phi.field t)))
          rw [schwartzL2Inner_add_right, schwartzL2Inner_smul_right]
        exact hmain.intervalIntegrable_of_Icc hT
      -- 4. hcurlError: the spacetime integral of the squared curl error → 0.
      -- CLOSED, kernel-clean, by `curlSqError_integral_tendsto_zero` above:
      -- pointwise-in-time convergence is `curl_proj_converges` against
      -- `hgraph_dense`/`hstable`, and the dominating function is the uniform
      -- stability bound applied to the test slice itself, continuous in time
      -- hence integrable on the finite window.  No Banach-Steinhaus argument
      -- is needed: the stability constant is supplied by step 1's basis leaf
      -- instead of being extracted.
      have hcurlError : Filter.Tendsto (fun m =>
          ∫ t in Set.Ioc (0 : ℝ) T,
            ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2)
          Filter.atTop (nhds 0) :=
        curlSqError_integral_tendsto_zero W hgraph_dense hstable phi
          errorSqIntegrable
      -- 5. hlap: from hcurlError via the Cauchy-Schwarz estimate
      have hlap : Filter.Tendsto (fun m =>
          ∫ t in (0 : ℝ)..T, nu * schwartzL2Inner (W.coefficientField (cChoice m t))
            (W.laplacianProjectionCommutator m (phi.field t)))
          Filter.atTop (nhds 0) := by
        apply hlap_tendsto_zero_of_curlSqError_tendsto_zero W cChoice (phi.field)
          phi.divergence_free nu T enstrophyBound hT ?_ ?_ ?_ ?_ hcurlError
        · intro m; exact henstCoef m T hT
        · exact henstrophyIntegrable
        · exact errorSqIntegrable
        · exact pairingIntervalIntegrable
      -- 6. hconv: the integral of the convection commutator → 0.
      -- CONJECTURE: The L² norm of the convection commutator,
      --   ‖convectionSchwartzBilin (W.coefficientField (cChoice m t))
      --      (W.proj m (phi.field t) - phi.field t)‖,
      -- tends to 0 as m → ∞, uniformly in t.  This follows from the curl
      -- convergence (curl_proj_converges W), the identity ‖∇v‖² = ‖curl v‖²
      -- for divergence-free v, and the Ladyzhenskaya inequality.  Together
      -- with the L² bound on the coefficient field (hc_norm), the lemma
      -- convectionTestProjection_pairing_tendsto_zero_of_L2 then gives hconv.
      -- The full proof requires ~200 LOC and is the second open sub-leaf.
      have hconv : Filter.Tendsto (fun m =>
          ∫ t in (0 : ℝ)..T, schwartzL2Inner (W.coefficientField (cChoice m t))
            (W.convectionTestProjectionCommutator m (W.coefficientField (cChoice m t))
              (phi.field t)))
          Filter.atTop (nhds 0) := by
        sorry
      -- 7. Apply modalFlow_fixedTest_projectedResidual_tendsto_of_commutators
      have hprojected : Filter.Tendsto
          (fun m => weakFormResidual nu (W.proj m u0) (W.modalApprox cChoice m) phi)
          Filter.atTop (nhds 0) :=
        modalFlow_fixedTest_projectedResidual_tendsto_of_commutators W nu u0 cChoice
          hc_deriv hc0 phi T hT hφzero' hφ''zero
          hmodal_cont hmodal_deriv hmodal_deriv_cont hmainInt hlapInt hconvInt hlap hconv
      -- 8. Apply modalApprox_fixedTest_weakConsistent_of_projectedDatum
      exact modalApprox_fixedTest_weakConsistent_of_projectedDatum W nu u0 hu0 cChoice
        phi hprojected
    -- Assemble
    refine ⟨{
      approx := W.modalApprox cChoice
      initialMode := fun m => W.proj m u0
      initial_eq := modalApprox_initial_eq_proj W u0 cChoice hc0
      bound := bound
      bound_nonneg := hbound_nonneg
      bound_le := hbound_le
      kinetic_bounded := hkin
      official_kinetic_bounded := hofficial
      enstrophyBound := enstrophyBound
      enstrophyBound_nonneg := henstrophyBound_nonneg
      enstrophy_bounded := henstrophy
      time_equicontinuous := htime
      space_equicontinuous := hspace
      jointly_measurable := hjoint
      sq_integrable := hsq
      initial_converges_L2 := hinit
      weak_consistent := hweak
    }⟩

end Navier.Analysis.GalerkinBasis
