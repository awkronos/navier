import Navier.Analysis.ClassDecomposition

/-!
# Strong–strong uniqueness inside the regular class `R`

Two solutions in `SolvesBefore ν T` that both lie in `R = RegularOnCompacts` and
share their initial slice coincide on `[0, T)`.  Energy method for `w = u - v`:
`‖w(t)‖² - ‖w(0)‖² = ∫₀ᵗ ∫ 2 w·∂ₛw`, with
`∫ w·Δw ≤ 0`, `∫ w·∇(p - q) = 0` (the pressures are `L²` modulo constants),
`∫ w·(v·∇)w = 0` (incompressibility), `|∫ w·(w·∇)u| ≤ 3K ‖w‖²` (sup bound on `∇u`),
closed by an iterated Gronwall bound.

This file: the time-derivative and slice-regularity facts extracted from joint
smoothness.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal

namespace Navier.Analysis.RegularUniqueness

open Navier Navier.Breakdown

/-- Slices of a jointly smooth velocity are smooth. -/
theorem contDiff_slice {T t : ℝ} {u : VelocityEvolution} (hsm : SmoothVelocityBefore T u)
    (ht : t ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ (u t) := by
  rw [← contDiffOn_univ]
  exact hsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun y _ => ⟨ht, mem_univ _⟩)

theorem contDiff_pslice {T t : ℝ} {p : PressureEvolution} (hsm : SmoothPressureBefore T p)
    (ht : t ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ (p t) := by
  rw [← contDiffOn_univ]
  exact hsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun y _ => ⟨ht, mem_univ _⟩)

/-- The jointly defined time derivative `∂ₛu(s,x)`. -/
def tD (u : VelocityEvolution) (s : ℝ) (x : Space) : Space :=
  fderiv ℝ (fun z : ℝ × Space => u z.1 z.2) (s, x) (1, 0)

theorem isOpen_strip (T : ℝ) : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) :=
  isOpen_Ioo.prod isOpen_univ

theorem hasDerivAt_tD {T s : ℝ} {u : VelocityEvolution} (hsm : SmoothVelocityBefore T u)
    (hs : s ∈ Ioo (0 : ℝ) T) (x : Space) :
    HasDerivAt (fun s' => u s' x) (tD u s x) s := by
  have hmem : Ioo (0 : ℝ) T ×ˢ (univ : Set Space) ∈ 𝓝 (s, x) :=
    (isOpen_strip T).mem_nhds ⟨hs, mem_univ _⟩
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) T ×ˢ univ :=
    prod_mono Ioo_subset_Ico_self subset_rfl
  have hca : ContDiffAt ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (s, x) :=
    (hsm.mono hsub).contDiffAt hmem
  have hF := (hca.differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun s' : ℝ => ((s', x) : ℝ × Space)) ((1, 0) : ℝ × Space) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hF.comp_hasDerivAt s hl

theorem timeDerivative_eq_tD {T s : ℝ} {u : VelocityEvolution} (hsm : SmoothVelocityBefore T u)
    (hs : s ∈ Ioo (0 : ℝ) T) (x : Space) : timeDerivative u s x = tD u s x := by
  have h := (hasDerivAt_tD hsm hs x).hasDerivWithinAt (s := Ici (0 : ℝ))
  exact h.derivWithin (uniqueDiffOn_Ici 0 s hs.1.le)

theorem continuousOn_tD {T : ℝ} {u : VelocityEvolution} (hsm : SmoothVelocityBefore T u) :
    ContinuousOn (fun z : ℝ × Space => tD u z.1 z.2) (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) := by
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) T ×ˢ univ :=
    prod_mono Ioo_subset_Ico_self subset_rfl
  have h := ((hsm.mono hsub).continuousOn_fderiv_of_isOpen (isOpen_strip T) (by simp))
  exact h.clm_apply continuousOn_const

theorem continuousOn_vel {T : ℝ} {u : VelocityEvolution} (hsm : SmoothVelocityBefore T u) :
    ContinuousOn (fun z : ℝ × Space => u z.1 z.2) (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
  hsm.continuousOn

/-! ## Real-variable helpers on `Space` -/

theorem integrable_mul_of_sq {f g : Space → ℝ} (hf : AEStronglyMeasurable f)
    (hg : AEStronglyMeasurable g) (hf2 : Integrable (fun x => f x ^ 2))
    (hg2 : Integrable (fun x => g x ^ 2)) : Integrable (fun x => f x * g x) := by
  refine ((hf2.add hg2).div_const 2).mono' (hf.mul hg) (Eventually.of_forall fun x => ?_)
  show ‖f x * g x‖ ≤ (f x ^ 2 + g x ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]

theorem fderiv_component {F : Space → Space} {x : Space} (hF : DifferentiableAt ℝ F x)
    (i : Fin 3) (v : Space) :
    fderiv ℝ (fun y => F y i) x v = fderiv ℝ F x v i := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x
    hF.hasFDerivAt)
  have e : (fun y => F y i) = (⇑(ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 3 => ℝ) i)) ∘ F := rfl
  rw [e, h.fderiv]
  rfl

theorem sq_component_le (v : Space) (i : Fin 3) : v i ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [← sq_abs, ← Real.norm_eq_abs]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2

theorem integrable_component_sq {F : Space → Space} (hFc : Continuous F)
    (hF2 : Integrable (fun x => ‖F x‖ ^ 2)) (i : Fin 3) :
    Integrable (fun x => F x i ^ 2) :=
  hF2.mono' (((continuous_apply i).comp hFc).pow 2).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact sq_component_le _ i)

theorem basis_expand (v : Space) : v = ∑ j : Fin 3, v j • basisVector j := by
  funext i
  simp [basisVector, Pi.single_apply, Finset.sum_apply]

/-- `∑ᵢⱼ |aᵢ||aⱼ| ≤ 3 ∑ aᵢ²`. -/
theorem sum_abs_mul_le (a : Fin 3 → ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, |a i| * |a j| ≤ 3 * ∑ i : Fin 3, a i ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (|a 0| - |a 1|), sq_nonneg (|a 0| - |a 2|), sq_nonneg (|a 1| - |a 2|),
    sq_abs (a 0), sq_abs (a 1), sq_abs (a 2)]

/-! ## Square-integrable continuous scalars -/

/-- A continuous scalar field with integrable square. -/
def SqInt (f : Space → ℝ) : Prop := Continuous f ∧ Integrable (fun x => f x ^ 2)

theorem SqInt.sub {f g : Space → ℝ} (hf : SqInt f) (hg : SqInt g) : SqInt (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, ((hf.2.add hg.2).const_mul 2).mono'
    ((hf.1.sub hg.1).pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)⟩
  show ‖(f x - g x) ^ 2‖ ≤ 2 * (f x ^ 2 + g x ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (f x + g x)]

theorem SqInt.sub_const_sub {f g : Space → ℝ} {a b : ℝ} (hf : SqInt (fun x => f x - a))
    (hg : SqInt (fun x => g x - b)) : SqInt (fun x => (f x - a) - (g x - b)) := hf.sub hg

theorem SqInt.mul {f g : Space → ℝ} (hf : SqInt f) (hg : SqInt g) :
    Integrable (fun x => f x * g x) :=
  integrable_mul_of_sq hf.1.aestronglyMeasurable hg.1.aestronglyMeasurable hf.2 hg.2

theorem SqInt.of_le {f : Space → ℝ} {F : Space → Space} (hf : Continuous f)
    (hF : Integrable (fun x => ‖F x‖ ^ 2)) (hle : ∀ x, |f x| ≤ ‖F x‖) : SqInt f := by
  refine ⟨hf, hF.mono' (hf.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hle x) 2

theorem SqInt.of_le_real {f g : Space → ℝ} (hf : Continuous f)
    (hg : Integrable (fun x => g x ^ 2)) (hle : ∀ x, |f x| ≤ |g x|) : SqInt f := by
  refine ⟨hf, hg.mono' (hf.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs, ← sq_abs (g x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hle x) 2

/-- **Whole-space integration by parts for smooth scalars.** -/
theorem ibp {f g : Space → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v : Space)
    (h1 : Integrable (fun x => fderiv ℝ f x v * g x))
    (h2 : Integrable (fun x => f x * fderiv ℝ g x v))
    (h3 : Integrable (fun x => f x * g x)) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => (hf.differentiable one_ne_zero) x) (fun x _ => (hg.differentiable one_ne_zero) x)

/-! ## Derivatives of smooth fields -/

theorem cd_dir {U : Space → Space} (hU : ContDiff ℝ ∞ U) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ U y v) :=
  (hU.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cd_dir_s {P : Space → ℝ} (hP : ContDiff ℝ ∞ P) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ P y v) :=
  (hP.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cd_comp {U : Space → Space} (hU : ContDiff ℝ ∞ U) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => U y i) :=
  (contDiff_apply ℝ ℝ i).comp hU

theorem fderiv_sub_fields {U V : Space → Space} (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (x v : Space) : fderiv ℝ (fun y => U y - V y) x v = fderiv ℝ U x v - fderiv ℝ V x v := by
  rw [fderiv_fun_sub ((hU.differentiable (by simp)) x) ((hV.differentiable (by simp)) x)]
  rfl

/-- The `j`-th partial derivative of the `i`-th component. -/
def pd (U : Space → Space) (j i : Fin 3) (x : Space) : ℝ := fderiv ℝ U x (basisVector j) i

theorem fderiv_comp_eq_pd {U : Space → Space} (hU : ContDiff ℝ ∞ U) (i j : Fin 3) (x : Space) :
    fderiv ℝ (fun y => U y i) x (basisVector j) = pd U j i x :=
  fderiv_component ((hU.differentiable (by simp)) x) i _

theorem fderiv_pd {U : Space → Space} (hU : ContDiff ℝ ∞ U) (i j l : Fin 3) (x : Space) :
    fderiv ℝ (pd U j i) x (basisVector l) =
      fderiv ℝ (fun y => fderiv ℝ U y (basisVector j)) x (basisVector l) i :=
  fderiv_component (((cd_dir hU _).differentiable (by simp)) x) i _

theorem continuous_pd {U : Space → Space} (hU : ContDiff ℝ ∞ U) (j i : Fin 3) :
    Continuous (pd U j i) :=
  (continuous_apply i).comp (cd_dir hU _).continuous

theorem contDiff_pd {U : Space → Space} (hU : ContDiff ℝ ∞ U) (j i : Fin 3) :
    ContDiff ℝ ∞ (pd U j i) :=
  (contDiff_apply ℝ ℝ i).comp (cd_dir hU _)

/-! ## The three integral identities -/

/-- **Viscous term**: `∫ f ∂ᵥ g = -∫ g² ≤ 0` when `∂ᵥ f = g`. -/
theorem viscous_term {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v : Space)
    (hfg : ∀ x, fderiv ℝ f x v = g x) (sf : SqInt f) (sg : SqInt g)
    (sg' : SqInt (fun x => fderiv ℝ g x v)) :
    Integrable (fun x => f x * fderiv ℝ g x v) ∧ ∫ x, f x * fderiv ℝ g x v ≤ 0 := by
  have i1 : Integrable (fun x => fderiv ℝ f x v * g x) := by
    simp_rw [hfg]; exact sg.mul sg
  have i2 : Integrable (fun x => f x * fderiv ℝ g x v) := sf.mul sg'
  have i3 : Integrable (fun x => f x * g x) := sf.mul sg
  refine ⟨i2, ?_⟩
  rw [ibp (hf.of_le (by simp)) (hg.of_le (by simp)) v i1 i2 i3]
  simp_rw [hfg]
  have : 0 ≤ ∫ x, g x * g x := integral_nonneg fun x => mul_self_nonneg _
  linarith

/-- **Pressure term**: `∑ᵢ ∫ Wᵢ ∂ᵢπ = 0` for divergence-free `W`. -/
theorem pressure_term {W : Space → Space} {π : Space → ℝ} (hW : ContDiff ℝ ∞ W)
    (hπ : ContDiff ℝ ∞ π) (sπ : SqInt π) (sdπ : ∀ i, SqInt (fun x => fderiv ℝ π x (basisVector i)))
    (sW : ∀ i, SqInt (fun x => W x i)) (sdW : ∀ i, SqInt (pd W i i))
    (hdiv : ∀ x, ∑ i : Fin 3, pd W i i x = 0) :
    (∀ i, Integrable (fun x => W x i * fderiv ℝ π x (basisVector i))) ∧
      ∑ i : Fin 3, ∫ x, W x i * fderiv ℝ π x (basisVector i) = 0 := by
  have hint : ∀ i, Integrable (fun x => W x i * fderiv ℝ π x (basisVector i)) := fun i =>
    (sW i).mul (sdπ i)
  refine ⟨hint, ?_⟩
  have hibp : ∀ i : Fin 3, ∫ x, W x i * fderiv ℝ π x (basisVector i) =
      -∫ x, pd W i i x * π x := by
    intro i
    have h := ibp (cd_comp hW i |>.of_le (by simp)) (hπ.of_le (by simp)) (basisVector i)
      (by simp_rw [fderiv_comp_eq_pd hW]; exact (sdW i).mul sπ) (hint i) ((sW i).mul sπ)
    simp_rw [fderiv_comp_eq_pd hW] at h
    exact h
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => (sdW i).mul sπ]
  have : ∀ x, ∑ i : Fin 3, pd W i i x * π x = (∑ i : Fin 3, pd W i i x) * π x := by
    intro x; rw [Finset.sum_mul]
  simp_rw [this, hdiv, zero_mul, integral_zero, neg_zero]

theorem integrable_bdd_mul {f g : Space → ℝ} {K : ℝ} (hf : Continuous f) (hK : ∀ x, |f x| ≤ K)
    (hg : Integrable g) : Integrable (fun x => f x * g x) := by
  refine (hg.norm.const_mul K).mono' (hf.aestronglyMeasurable.mul hg.1)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hK x) (abs_nonneg _)

theorem fderiv_apply_expand (L : Space →L[ℝ] Space) (v : Space) (i : Fin 3) :
    L v i = ∑ j : Fin 3, v j * L (basisVector j) i := by
  conv_lhs => rw [basis_expand v]
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The half squared length of a field. -/
def halfSq (W : Space → Space) (x : Space) : ℝ := (∑ i : Fin 3, W x i ^ 2) / 2

theorem contDiff_halfSq {W : Space → Space} (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (halfSq W) := by
  unfold halfSq
  exact (ContDiff.sum fun i _ => (cd_comp hW i).pow 2).div_const 2

theorem fderiv_halfSq {W : Space → Space} (hW : ContDiff ℝ ∞ W) (x : Space) (j : Fin 3) :
    fderiv ℝ (halfSq W) x (basisVector j) = ∑ i : Fin 3, W x i * pd W j i x := by
  have hd : ∀ i : Fin 3, HasFDerivAt (fun y => W y i) (fderiv ℝ (fun y => W y i) x) x :=
    fun i => (((cd_comp hW i).differentiable (by simp)) x).hasFDerivAt
  have hs : HasFDerivAt (fun y => ∑ i : Fin 3, W y i ^ 2)
      (∑ i : Fin 3, ((2 : ℕ) * W x i ^ (2 - 1)) • fderiv ℝ (fun y => W y i) x) x := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (hd i).pow 2
    simpa using this
  have hh := hs.const_mul (1 / 2 : ℝ)
  have e : halfSq W = fun y => (1 / 2 : ℝ) * ∑ i : Fin 3, W y i ^ 2 := by
    funext y; unfold halfSq; ring
  rw [e, hh.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_comp_eq_pd hW]
  push_cast; ring

/-- **Transport term**: `∑ᵢ ∫ Wᵢ (∇W · V)ᵢ = 0` for divergence-free bounded `V`. -/
theorem transport_term {W V : Space → Space} {K : ℝ} (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (sW : ∀ i, SqInt (fun x => W x i)) (sdW : ∀ j i, SqInt (pd W j i))
    (hVb : ∀ x j, |V x j| ≤ K) (hdVb : ∀ x j, |pd V j j x| ≤ K)
    (hdiv : ∀ x, ∑ j : Fin 3, pd V j j x = 0) :
    Integrable (fun x => ∑ i : Fin 3, W x i * fderiv ℝ W x (V x) i) ∧
      ∫ x, ∑ i : Fin 3, W x i * fderiv ℝ W x (V x) i = 0 := by
  have hG : Integrable (halfSq W) := by
    unfold halfSq
    exact (integrable_finsetSum _ fun i _ => (sW i).2).div_const 2
  have hdG : ∀ j, Integrable (fun x => fderiv ℝ (halfSq W) x (basisVector j)) := by
    intro j
    simp_rw [fderiv_halfSq hW]
    exact integrable_finsetSum _ fun i _ => (sW i).mul (sdW j i)
  have hVc : ∀ j, Continuous (fun x => V x j) := fun j => (cd_comp hV j).continuous
  have hpt : ∀ x, ∑ i : Fin 3, W x i * fderiv ℝ W x (V x) i =
      ∑ j : Fin 3, V x j * fderiv ℝ (halfSq W) x (basisVector j) := by
    intro x
    simp_rw [fderiv_halfSq hW, fderiv_apply_expand (fderiv ℝ W x) (V x)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    unfold pd; ring
  have hterm : ∀ j, Integrable (fun x => V x j * fderiv ℝ (halfSq W) x (basisVector j)) :=
    fun j => integrable_bdd_mul (hVc j) (fun x => hVb x j) (hdG j)
  have hint : Integrable (fun x => ∑ i : Fin 3, W x i * fderiv ℝ W x (V x) i) := by
    simp_rw [hpt]; exact integrable_finsetSum _ fun j _ => hterm j
  refine ⟨hint, ?_⟩
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j _ => hterm j]
  have hibp : ∀ j : Fin 3, ∫ x, V x j * fderiv ℝ (halfSq W) x (basisVector j) =
      -∫ x, pd V j j x * halfSq W x := by
    intro j
    have h := ibp ((cd_comp hV j).of_le (by simp)) ((contDiff_halfSq hW).of_le (by simp))
      (basisVector j)
      (by simp_rw [fderiv_comp_eq_pd hV]
          exact integrable_bdd_mul (continuous_pd hV j j) (fun x => hdVb x j) hG)
      (hterm j) (integrable_bdd_mul (hVc j) (fun x => hVb x j) hG)
    simp_rw [fderiv_comp_eq_pd hV] at h
    exact h
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ =>
    integrable_bdd_mul (continuous_pd hV j j) (fun x => hdVb x j) hG]
  have : ∀ x, ∑ j : Fin 3, pd V j j x * halfSq W x = (∑ j : Fin 3, pd V j j x) * halfSq W x := by
    intro x; rw [Finset.sum_mul]
  simp_rw [this, hdiv, zero_mul, integral_zero, neg_zero]

/-- **The Gronwall term, pointwise**: `|∑ᵢ Wᵢ (∇U·W)ᵢ| ≤ 3K ∑ Wᵢ²` when `|∂ⱼUᵢ| ≤ K`. -/
theorem gronwall_term_bound {K : ℝ} (hK0 : 0 ≤ K) {L : Space →L[ℝ] Space} {w : Space}
    (hL : ∀ j i : Fin 3, |L (basisVector j) i| ≤ K) :
    |∑ i : Fin 3, w i * L w i| ≤ 3 * K * ∑ i : Fin 3, w i ^ 2 := by
  have e : ∑ i : Fin 3, w i * L w i = ∑ i : Fin 3, ∑ j : Fin 3, w i * (w j * L (basisVector j) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_apply_expand L w i, Finset.mul_sum]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin 3, |∑ j : Fin 3, w i * (w j * L (basisVector j) i)|
      ≤ ∑ i : Fin 3, ∑ j : Fin 3, K * (|w i| * |w j|) := by
        refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        have := hL j i
        have h1 : 0 ≤ |w i| * |w j| := by positivity
        nlinarith
    _ = K * ∑ i : Fin 3, ∑ j : Fin 3, |w i| * |w j| := by simp only [Finset.mul_sum]
    _ ≤ K * (3 * ∑ i : Fin 3, w i ^ 2) := mul_le_mul_of_nonneg_left (sum_abs_mul_le w) hK0
    _ = 3 * K * ∑ i : Fin 3, w i ^ 2 := by ring

/-! ## The slice energy inequality -/

open Navier.Analysis.ClassDecomposition

/-- The Laplacian of a field, in the repository's form. -/
def lapF (U : Space → Space) (x : Space) : Space :=
  ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ U y (basisVector j)) x (basisVector j)

/-- The pressure gradient of a scalar field. -/
def gradF (P : Space → ℝ) (x : Space) : Space := fun i => fderiv ℝ P x (basisVector i)

theorem sqInt_congr {f g : Space → ℝ} (h : f = g) (hf : SqInt f) : SqInt g := h ▸ hf

theorem sqInt_real {f : Space → ℝ} (hf : Continuous f) (h : Integrable (fun x => ‖f x‖ ^ 2)) :
    SqInt f := ⟨hf, h.congr (Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, sq_abs])⟩

/-- **The slice energy inequality**: `∫ W·(DU - DV) ≤ 3K ∫ |W|²`. -/
theorem slice_energy {ν K : ℝ} (hν : 0 ≤ ν) {U V DU DV : Space → Space} {P Q : Space → ℝ}
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hU2 : Integrable (fun x => ‖U x‖ ^ 2)) (hV2 : Integrable (fun x => ‖V x‖ ^ 2))
    (hRU : RegSlice K U) (hRV : RegSlice K V) (hPU : PresSlice K P) (hPV : PresSlice K Q)
    (hSU : SupSlice K U) (hSV : SupSlice K V) (hLU : PresL2 K P) (hLV : PresL2 K Q)
    (hdivU : ∀ x, ∑ i : Fin 3, pd U i i x = 0) (hdivV : ∀ x, ∑ i : Fin 3, pd V i i x = 0)
    (heqU : ∀ x, DU x = ν • lapF U x - gradF P x - fderiv ℝ U x (U x))
    (heqV : ∀ x, DV x = ν • lapF V x - gradF Q x - fderiv ℝ V x (V x)) :
    Integrable (fun x => ∑ i : Fin 3, (U x i - V x i) * (DU x i - DV x i)) ∧
      ∫ x, ∑ i : Fin 3, (U x i - V x i) * (DU x i - DV x i) ≤
        3 * K * ∫ x, ∑ i : Fin 3, (U x i - V x i) ^ 2 := by
  set W : Space → Space := fun x => U x - V x with hWdef
  have hW : ContDiff ℝ ∞ W := hU.sub hV
  have hUd : ∀ x, DifferentiableAt ℝ U x := fun x => (hU.differentiable (by simp)) x
  have hVd : ∀ x, DifferentiableAt ℝ V x := fun x => (hV.differentiable (by simp)) x
  -- component and derivative square-integrability
  have sU : ∀ i, SqInt (fun x => U x i) := fun i =>
    SqInt.of_le (cd_comp hU i).continuous hU2 (fun x => by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i)
  have sV : ∀ i, SqInt (fun x => V x i) := fun i =>
    SqInt.of_le (cd_comp hV i).continuous hV2 (fun x => by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i)
  have sW : ∀ i, SqInt (fun x => W x i) := fun i => (sU i).sub (sV i)
  have hpdW : ∀ j i, pd W j i = fun x => pd U j i x - pd V j i x := by
    intro j i; funext x
    unfold pd
    rw [fderiv_sub_fields hU hV]; rfl
  have sdU : ∀ j i, SqInt (pd U j i) := fun j i =>
    SqInt.of_le (continuous_pd hU j i) (hRU j j j).1 (fun x => by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i)
  have sdV : ∀ j i, SqInt (pd V j i) := fun j i =>
    SqInt.of_le (continuous_pd hV j i) (hRV j j j).1 (fun x => by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i)
  have sdW : ∀ j i, SqInt (pd W j i) := fun j i => by
    rw [hpdW]; exact (sdU j i).sub (sdV j i)
  have hdirW : ∀ j, (fun y => fderiv ℝ W y (basisVector j)) =
      fun y => fderiv ℝ U y (basisVector j) - fderiv ℝ V y (basisVector j) := by
    intro j; funext y; exact fderiv_sub_fields hU hV y _
  have h2W : ∀ j i l x, fderiv ℝ (pd W j i) x (basisVector l) =
      fderiv ℝ (fun y => fderiv ℝ U y (basisVector j)) x (basisVector l) i -
        fderiv ℝ (fun y => fderiv ℝ V y (basisVector j)) x (basisVector l) i := by
    intro j i l x
    rw [fderiv_pd hW, hdirW, fderiv_sub_fields (cd_dir hU _) (cd_dir hV _)]
    rfl
  have s2W : ∀ j i l, SqInt (fun x => fderiv ℝ (pd W j i) x (basisVector l)) := by
    intro j i l
    have hfun : (fun x => fderiv ℝ (pd W j i) x (basisVector l)) = fun x =>
        fderiv ℝ (fun y => fderiv ℝ U y (basisVector j)) x (basisVector l) i -
          fderiv ℝ (fun y => fderiv ℝ V y (basisVector j)) x (basisVector l) i := by
      funext x; exact h2W j i l x
    rw [hfun]
    refine SqInt.sub ?_ ?_
    · exact SqInt.of_le ((continuous_apply i).comp (cd_dir (cd_dir hU _) _).continuous)
        (hRU j l l).2.2.1 (fun x => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i)
    · exact SqInt.of_le ((continuous_apply i).comp (cd_dir (cd_dir hV _) _).continuous)
        (hRV j l l).2.2.1 (fun x => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i)
  -- the pressure difference, normalised to be square-integrable
  obtain ⟨cP, hcP, -⟩ := hLU
  obtain ⟨cQ, hcQ, -⟩ := hLV
  set π : Space → ℝ := fun x => (P x - cP) - (Q x - cQ) with hπdef
  have hπ : ContDiff ℝ ∞ π := (hP.sub contDiff_const).sub (hQ.sub contDiff_const)
  have sπ : SqInt π :=
    SqInt.sub ⟨hP.continuous.sub continuous_const, hcP⟩ ⟨hQ.continuous.sub continuous_const, hcQ⟩
  have hdπ : ∀ i x, fderiv ℝ π x (basisVector i) =
      fderiv ℝ P x (basisVector i) - fderiv ℝ Q x (basisVector i) := by
    intro i x
    rw [hπdef, fderiv_fun_sub (((hP.sub contDiff_const).differentiable (by simp)) x)
      (((hQ.sub contDiff_const).differentiable (by simp)) x),
      fderiv_sub_const, fderiv_sub_const]
    rfl
  have sdπ : ∀ i, SqInt (fun x => fderiv ℝ π x (basisVector i)) := by
    intro i
    have hfun : (fun x => fderiv ℝ π x (basisVector i)) =
        fun x => fderiv ℝ P x (basisVector i) - fderiv ℝ Q x (basisVector i) := by
      funext x; exact hdπ i x
    rw [hfun]
    exact (sqInt_real (cd_dir_s hP _).continuous (hPU i i).1).sub
      (sqInt_real (cd_dir_s hQ _).continuous (hPV i i).1)
  -- the pointwise decomposition
  have hdivW : ∀ x, ∑ i : Fin 3, pd W i i x = 0 := by
    intro x
    simp_rw [hpdW]
    rw [Finset.sum_sub_distrib, hdivU, hdivV, sub_zero]
  have hdecomp : ∀ x, ∑ i : Fin 3, (U x i - V x i) * (DU x i - DV x i) =
      ν * (∑ i : Fin 3, ∑ j : Fin 3, W x i * fderiv ℝ (pd W j i) x (basisVector j)) -
        ∑ i : Fin 3, W x i * fderiv ℝ π x (basisVector i) -
        ∑ i : Fin 3, W x i * fderiv ℝ U x (W x) i -
        ∑ i : Fin 3, W x i * fderiv ℝ W x (V x) i := by
    intro x
    have hc : fderiv ℝ U x (U x) - fderiv ℝ V x (V x) =
        fderiv ℝ U x (W x) + fderiv ℝ W x (V x) := by
      show _ = fderiv ℝ U x (U x - V x) + fderiv ℝ (fun y => U y - V y) x (V x)
      rw [fderiv_sub_fields hU hV, map_sub]; abel
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hci := congrFun hc i
    simp only [Pi.sub_apply, Pi.add_apply] at hci
    rw [heqU x, heqV x]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lapF, gradF, Finset.sum_apply]
    have hlap : ∀ j : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ U y (basisVector j)) x (basisVector j) i -
          fderiv ℝ (fun y => fderiv ℝ V y (basisVector j)) x (basisVector j) i =
        fderiv ℝ (pd W j i) x (basisVector j) := fun j => (h2W j i j x).symm
    have hlapsum : ∑ c : Fin 3, fderiv ℝ (fun y => fderiv ℝ U y (basisVector c)) x (basisVector c) i -
        ∑ c : Fin 3, fderiv ℝ (fun y => fderiv ℝ V y (basisVector c)) x (basisVector c) i =
        ∑ j : Fin 3, fderiv ℝ (pd W j i) x (basisVector j) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => hlap j
    have e : ∑ j : Fin 3, W x i * fderiv ℝ (pd W j i) x (basisVector j) =
        W x i * ∑ j : Fin 3, fderiv ℝ (pd W j i) x (basisVector j) := by
      rw [Finset.mul_sum]
    rw [e]
    have hWi : W x i = U x i - V x i := rfl
    rw [hWi]
    linear_combination ν * (U x i - V x i) * hlapsum + (U x i - V x i) * hdπ i x -
      (U x i - V x i) * hci
  -- the four integrals
  have iA : ∀ i j, Integrable (fun x => W x i * fderiv ℝ (pd W j i) x (basisVector j)) ∧
      ∫ x, W x i * fderiv ℝ (pd W j i) x (basisVector j) ≤ 0 := fun i j =>
    viscous_term (cd_comp hW i) (contDiff_pd hW j i) (basisVector j)
      (fun x => fderiv_comp_eq_pd hW i j x) (sW i) (sdW j i) (s2W j i j)
  have hAint : Integrable (fun x =>
      ∑ i : Fin 3, ∑ j : Fin 3, W x i * fderiv ℝ (pd W j i) x (basisVector j)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (iA i j).1
  have hAle : ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, W x i * fderiv ℝ (pd W j i) x (basisVector j) ≤ 0 := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (iA i j).1]
    refine Finset.sum_nonpos fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (iA i j).1]
    exact Finset.sum_nonpos fun j _ => (iA i j).2
  obtain ⟨hBi, hB0⟩ := pressure_term hW hπ sπ sdπ sW (fun i => sdW i i) hdivW
  have hBint : Integrable (fun x => ∑ i : Fin 3, W x i * fderiv ℝ π x (basisVector i)) :=
    integrable_finsetSum _ fun i _ => hBi i
  have hBval : ∫ x, ∑ i : Fin 3, W x i * fderiv ℝ π x (basisVector i) = 0 := by
    rw [integral_finsetSum _ fun i _ => hBi i]; exact hB0
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hSU.1 0)
  have hVb : ∀ x j, |V x j| ≤ K := fun x j => by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm _ j).trans (hSV.1 x)
  have hdVb : ∀ x j, |pd V j j x| ≤ K := fun x j => by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm _ j).trans (hSV.2 x j)
  obtain ⟨hC2int, hC2val⟩ := transport_term hW hV sW sdW hVb hdVb hdivV
  -- the Gronwall term
  have hdUb : ∀ x j i, |pd U j i x| ≤ K := fun x j i => by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm _ i).trans (hSU.2 x j)
  have hC1c : Continuous (fun x => ∑ i : Fin 3, W x i * fderiv ℝ U x (W x) i) := by
    refine continuous_finsetSum _ fun i _ => ((cd_comp hW i).continuous).mul ?_
    exact (continuous_apply i).comp
      ((hU.continuous_fderiv (by simp)).clm_apply hW.continuous)
  have hsq : Integrable (fun x => ∑ i : Fin 3, W x i ^ 2) :=
    integrable_finsetSum _ fun i _ => (sW i).2
  have hC1b : ∀ x, |∑ i : Fin 3, W x i * fderiv ℝ U x (W x) i| ≤
      3 * K * ∑ i : Fin 3, W x i ^ 2 := fun x => gronwall_term_bound hK0 (fun j i => hdUb x j i)
  have hC1int : Integrable (fun x => ∑ i : Fin 3, W x i * fderiv ℝ U x (W x) i) :=
    (hsq.const_mul (3 * K)).mono' hC1c.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC1b x)
  -- assembly
  have hfun : (fun x => ∑ i : Fin 3, (U x i - V x i) * (DU x i - DV x i)) = fun x =>
      ν * (∑ i : Fin 3, ∑ j : Fin 3, W x i * fderiv ℝ (pd W j i) x (basisVector j)) -
        ∑ i : Fin 3, W x i * fderiv ℝ π x (basisVector i) -
        ∑ i : Fin 3, W x i * fderiv ℝ U x (W x) i -
        ∑ i : Fin 3, W x i * fderiv ℝ W x (V x) i := funext hdecomp
  have hint : Integrable (fun x => ∑ i : Fin 3, (U x i - V x i) * (DU x i - DV x i)) := by
    rw [hfun]
    exact (((hAint.const_mul ν).sub hBint).sub hC1int).sub hC2int
  refine ⟨hint, ?_⟩
  set A : Space → ℝ := fun x =>
    ∑ i : Fin 3, ∑ j : Fin 3, W x i * fderiv ℝ (pd W j i) x (basisVector j) with hAdef
  set B : Space → ℝ := fun x => ∑ i : Fin 3, W x i * fderiv ℝ π x (basisVector i) with hBdef
  set C1 : Space → ℝ := fun x => ∑ i : Fin 3, W x i * fderiv ℝ U x (W x) i with hC1def
  set C2 : Space → ℝ := fun x => ∑ i : Fin 3, W x i * fderiv ℝ W x (V x) i with hC2def
  have i1 : Integrable (fun x => ν * A x) := hAint.const_mul ν
  have i2 : Integrable (fun x => ν * A x - B x) := i1.sub hBint
  have i3 : Integrable (fun x => ν * A x - B x - C1 x) := i2.sub hC1int
  rw [hfun]
  rw [integral_sub i3 hC2int, integral_sub i2 hC1int, integral_sub i1 hBint,
    integral_const_mul, hBval, hC2val]
  have hC1ge : -(3 * K * ∫ x, ∑ i : Fin 3, W x i ^ 2) ≤
      ∫ x, ∑ i : Fin 3, W x i * fderiv ℝ U x (W x) i := by
    rw [← integral_const_mul, ← integral_neg]
    exact integral_mono ((hsq.const_mul _).neg) hC1int
      (fun x => by
        have h1 := hC1b x
        have h2 := neg_abs_le (∑ i : Fin 3, W x i * fderiv ℝ U x (W x) i)
        simp only [Pi.neg_apply]
        linarith)
  have hνA : ν * ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, W x i * fderiv ℝ (pd W j i) x (basisVector j)
      ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hν hAle
  have hWsq : (∫ x, ∑ i : Fin 3, W x i ^ 2) = ∫ x, ∑ i : Fin 3, (U x i - V x i) ^ 2 := rfl
  rw [← hWsq]
  linarith

end Navier.Analysis.RegularUniqueness
set_option pp.fullNames true in
#print axioms Navier.Analysis.RegularUniqueness.slice_energy
