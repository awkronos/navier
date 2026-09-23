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

open Navier.Analysis.ClassDecomposition Navier.Analysis.CriticalControlDecomposition

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

/-! ## The iterated Gronwall lemma -/

/-- **Integral Gronwall with zero start**: a bounded nonnegative function with
`f s ≤ C ∫₀ˢ f` vanishes. -/
theorem gronwall_zero {f : ℝ → ℝ} {C B T : ℝ} (hC : 0 ≤ C)
    (hf0 : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ f s) (hfB : ∀ s ∈ Icc (0 : ℝ) T, f s ≤ B)
    (hint : IntegrableOn f (Icc (0 : ℝ) T))
    (hle : ∀ s ∈ Icc (0 : ℝ) T, f s ≤ C * ∫ r in (0 : ℝ)..s, f r) :
    ∀ s ∈ Icc (0 : ℝ) T, f s = 0 := by
  have key : ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) T, f s ≤ B * (C * s) ^ n / n.factorial := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hfB s hs
    | succ n ih =>
      intro s hs
      refine (hle s hs).trans ?_
      have hsub : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right hs.2
      have hmono : ∫ r in (0 : ℝ)..s, f r ≤ ∫ r in (0 : ℝ)..s, B * (C * r) ^ n / n.factorial := by
        refine intervalIntegral.integral_mono_on hs.1
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hs.1).mpr (hint.mono_set hsub)) ?_ ?_
        · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
        · intro r hr; exact ih r (hsub hr)
      have hcalc : ∫ r in (0 : ℝ)..s, B * (C * r) ^ n / n.factorial =
          B * C ^ n * s ^ (n + 1) / ((n + 1) * n.factorial) := by
        have : (fun r : ℝ => B * (C * r) ^ n / n.factorial) =
            fun r => (B * C ^ n / n.factorial) * r ^ n := by
          funext r; rw [mul_pow]; ring
        rw [this, intervalIntegral.integral_const_mul, integral_pow]
        field_simp
        ring
      calc C * ∫ r in (0 : ℝ)..s, f r ≤ C * (B * C ^ n * s ^ (n + 1) / ((n + 1) * n.factorial)) :=
            mul_le_mul_of_nonneg_left (hmono.trans (le_of_eq hcalc)) hC
        _ = B * (C * s) ^ (n + 1) / (n + 1).factorial := by
            rw [Nat.factorial_succ]; push_cast; rw [mul_pow]; field_simp; ring
  intro s hs
  refine le_antisymm ?_ (hf0 s hs)
  have hlim : Tendsto (fun n : ℕ => B * (C * s) ^ n / n.factorial) atTop (𝓝 0) := by
    have := (FloorSemiring.tendsto_pow_div_factorial_atTop (C * s)).const_mul B
    simpa [mul_div_assoc] using this
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => key n s hs)

/-! ## From the solution clauses to the slice data -/

theorem slice_equation {ν T t : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (heq : SatisfiesNavierStokesBefore ν zeroForce T u p) (ht0 : 0 ≤ t) (htT : t < T)
    (x : Space) :
    timeDerivative u t x = ν • lapF (u t) x - gradF (p t) x - fderiv ℝ (u t) x (u t x) := by
  have h := heq t ht0 htT x
  rw [show zeroForce t x = (0 : Space) from rfl, add_zero] at h
  have h' : timeDerivative u t x = ν • laplacian u t x - pressureGradient p t x -
      convection u t x := by rw [← h]; abel
  exact h'

theorem slice_div {T t : ℝ} {u : VelocityEvolution} (hinc : IncompressibleBefore T u)
    (ht0 : 0 ≤ t) (htT : t < T) (x : Space) : ∑ i : Fin 3, pd (u t) i i x = 0 :=
  hinc t ht0 htT x

/-- The difference energy `∫ ∑ᵢ (uᵢ - vᵢ)²` at time `t`. -/
def Ediff (u v : VelocityEvolution) (t : ℝ) : ℝ := ∫ x, ∑ i : Fin 3, (u t x i - v t x i) ^ 2

/-- **The time-slice energy bound**: `∫ 2 W·∂ₜW ≤ 6K ‖W‖²`. -/
theorem time_slice_energy {ν T K t : ℝ} (hν : 0 ≤ ν) {u v : VelocityEvolution}
    {p q : PressureEvolution} (hu : SolvesBefore ν T u p) (hv : SolvesBefore ν T v q)
    (ht0 : 0 ≤ t) (htT : t < T)
    (hRu : RegSlice K (u t) ∧ PresSlice K (p t) ∧ TimeSlice K u t ∧ SupSlice K (u t) ∧
      PresL2 K (p t))
    (hRv : RegSlice K (v t) ∧ PresSlice K (q t) ∧ TimeSlice K v t ∧ SupSlice K (v t) ∧
      PresL2 K (q t)) :
    Integrable (fun x => ∑ i : Fin 3, 2 * (u t x i - v t x i) *
        (timeDerivative u t x i - timeDerivative v t x i)) ∧
      ∫ x, ∑ i : Fin 3, 2 * (u t x i - v t x i) *
        (timeDerivative u t x i - timeDerivative v t x i) ≤ 6 * K * Ediff u v t := by
  have ht : t ∈ Ico (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu.classical
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv.classical
  have h := slice_energy hν (DU := fun x => timeDerivative u t x)
    (DV := fun x => timeDerivative v t x)
    (contDiff_slice hu1 ht) (contDiff_slice hv1 ht) (contDiff_pslice hu2 ht)
    (contDiff_pslice hv2 ht) (hu.finite_energy t ht0 htT) (hv.finite_energy t ht0 htT)
    hRu.1 hRv.1 hRu.2.1 hRv.2.1 hRu.2.2.2.1 hRv.2.2.2.1 hRu.2.2.2.2 hRv.2.2.2.2
    (slice_div hu3 ht0 htT) (slice_div hv3 ht0 htT)
    (slice_equation hu4 ht0 htT) (slice_equation hv4 ht0 htT)
  have hfun : (fun x => ∑ i : Fin 3, 2 * (u t x i - v t x i) *
      (timeDerivative u t x i - timeDerivative v t x i)) = fun x =>
      2 * ∑ i : Fin 3, (u t x i - v t x i) * (timeDerivative u t x i - timeDerivative v t x i) := by
    funext x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun]
  refine ⟨h.1.const_mul 2, ?_⟩
  rw [integral_const_mul]
  unfold Ediff
  linarith [h.2]

/-! ## The energy identity in time -/

theorem hasDerivAt_sqdiff {T r : ℝ} {u v : VelocityEvolution} (hsu : SmoothVelocityBefore T u)
    (hsv : SmoothVelocityBefore T v) (hr : r ∈ Ioo (0 : ℝ) T) (x : Space) :
    HasDerivAt (fun r => ∑ i : Fin 3, (u r x i - v r x i) ^ 2)
      (∑ i : Fin 3, 2 * (u r x i - v r x i) * (tD u r x i - tD v r x i)) r := by
  have hc : ∀ i : Fin 3, HasDerivAt (fun r => u r x i - v r x i) (tD u r x i - tD v r x i) r :=
    fun i => ((hasDerivAt_pi.mp (hasDerivAt_tD hsu hr x)) i).sub
      ((hasDerivAt_pi.mp (hasDerivAt_tD hsv hr x)) i)
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc i).pow 2
  refine h.congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
  push_cast; ring

/-- The joint integrand `2 W·∂ₜW`. -/
def Fint (u v : VelocityEvolution) (z : ℝ × Space) : ℝ :=
  ∑ i : Fin 3, 2 * (u z.1 z.2 i - v z.1 z.2 i) * (tD u z.1 z.2 i - tD v z.1 z.2 i)

theorem continuousOn_Fint {T : ℝ} {u v : VelocityEvolution} (hsu : SmoothVelocityBefore T u)
    (hsv : SmoothVelocityBefore T v) :
    ContinuousOn (Fint u v) (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) := by
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) T ×ˢ univ :=
    prod_mono Ioo_subset_Ico_self subset_rfl
  have hu := (continuousOn_vel hsu).mono hsub
  have hv := (continuousOn_vel hsv).mono hsub
  have htu := continuousOn_tD hsu
  have htv := continuousOn_tD hsv
  unfold Fint
  refine continuousOn_finsetSum _ fun i _ => ?_
  exact (continuousOn_const.mul (((continuous_apply i).comp_continuousOn hu).sub
    ((continuous_apply i).comp_continuousOn hv))).mul
    (((continuous_apply i).comp_continuousOn htu).sub ((continuous_apply i).comp_continuousOn htv))

/-- The five `R` clauses at one time. -/
def Rslice (K : ℝ) (u : VelocityEvolution) (p : PressureEvolution) (t : ℝ) : Prop :=
  RegSlice K (u t) ∧ PresSlice K (p t) ∧ TimeSlice K u t ∧ SupSlice K (u t) ∧ PresL2 K (p t)

theorem Rslice.mono {K K' : ℝ} {u : VelocityEvolution} {p : PressureEvolution} {t : ℝ}
    (h : Rslice K u p t) (hK : K ≤ K') : Rslice K' u p t :=
  ⟨h.1.mono hK, h.2.1.mono hK, h.2.2.1.mono hK, h.2.2.2.1.mono hK, h.2.2.2.2.mono hK⟩

theorem sum_sq_comp_le (a : Space) : ∑ i : Fin 3, a i ^ 2 ≤ 3 * ‖a‖ ^ 2 := by
  calc ∑ i : Fin 3, a i ^ 2 ≤ ∑ _i : Fin 3, ‖a‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => sq_component_le a i
    _ = 3 * ‖a‖ ^ 2 := by simp

theorem integrable_sum_sq {F : Space → Space} (hFc : Continuous F)
    (hF : Integrable (fun x => ‖F x‖ ^ 2)) : Integrable (fun x => ∑ i : Fin 3, F x i ^ 2) :=
  integrable_finsetSum _ fun i _ => integrable_component_sq hFc hF i

/-- **Section bound for the joint integrand.** -/
theorem Fint_section {ν T K r : ℝ} (hν : 0 ≤ ν) {u v : VelocityEvolution}
    {p q : PressureEvolution} (hu : SolvesBefore ν T u p) (hv : SolvesBefore ν T v q)
    (hr : r ∈ Ioo (0 : ℝ) T) (hRu : Rslice K u p r) (hRv : Rslice K v q r) :
    Integrable (fun x => Fint u v (r, x)) ∧
      ∫ x, ‖Fint u v (r, x)‖ ≤ 2 * (kineticEnergy u 0 + kineticEnergy v 0) + 12 * K := by
  have hsu := hu.classical.1
  have hsv := hv.classical.1
  have hrI : r ∈ Ico (0 : ℝ) T := Ioo_subset_Ico_self hr
  have htdu : ∀ x, timeDerivative u r x = tD u r x := timeDerivative_eq_tD hsu hr
  have htdv : ∀ x, timeDerivative v r x = tD v r x := timeDerivative_eq_tD hsv hr
  obtain ⟨hint, -⟩ := time_slice_energy hν hu hv hr.1.le hr.2 hRu hRv
  have hfun : (fun x => Fint u v (r, x)) = fun x => ∑ i : Fin 3, 2 * (u r x i - v r x i) *
      (timeDerivative u r x i - timeDerivative v r x i) := by
    funext x; unfold Fint; simp only [htdu, htdv]
  refine ⟨hfun ▸ hint, ?_⟩
  -- pointwise domination
  have huc : Continuous (u r) := (contDiff_slice hsu hrI).continuous
  have hvc : Continuous (v r) := (contDiff_slice hsv hrI).continuous
  have hdu : Continuous (fun x => timeDerivative u r x) := by
    have : (fun x => timeDerivative u r x) = fun x => tD u r x := funext htdu
    rw [this]
    exact ((continuousOn_tD hsu).comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hr, mem_univ _⟩))
  have hdv : Continuous (fun x => timeDerivative v r x) := by
    have : (fun x => timeDerivative v r x) = fun x => tD v r x := funext htdv
    rw [this]
    exact ((continuousOn_tD hsv).comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hr, mem_univ _⟩))
  set G : Space → ℝ := fun x => 2 * (∑ i : Fin 3, u r x i ^ 2 + ∑ i : Fin 3, v r x i ^ 2) +
    6 * (‖timeDerivative u r x‖ ^ 2 + ‖timeDerivative v r x‖ ^ 2) with hG
  have hGi : Integrable G :=
    (((integrable_sum_sq huc (hu.finite_energy r hr.1.le hr.2)).add
      (integrable_sum_sq hvc (hv.finite_energy r hr.1.le hr.2))).const_mul 2).add
      ((hRu.2.2.1.1.add hRv.2.2.1.1).const_mul 6)
  have hbd : ∀ x, ‖Fint u v (r, x)‖ ≤ G x := by
    intro x
    rw [congrFun hfun x, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hi : ∀ i : Fin 3, |2 * (u r x i - v r x i) * (timeDerivative u r x i -
        timeDerivative v r x i)| ≤ 2 * (u r x i ^ 2 + v r x i ^ 2) +
          2 * (‖timeDerivative u r x‖ ^ 2 + ‖timeDerivative v r x‖ ^ 2) := by
      intro i
      have a1 := sq_component_le (timeDerivative u r x) i
      have a2 := sq_component_le (timeDerivative v r x) i
      set a := u r x i - v r x i
      set b := timeDerivative u r x i - timeDerivative v r x i
      have hab : |2 * a * b| ≤ a ^ 2 + b ^ 2 := by
        rw [abs_mul, abs_mul, abs_two]
        nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
      have ha : a ^ 2 ≤ 2 * (u r x i ^ 2 + v r x i ^ 2) := by
        nlinarith [sq_nonneg (u r x i + v r x i)]
      have hb : b ^ 2 ≤ 2 * (‖timeDerivative u r x‖ ^ 2 + ‖timeDerivative v r x‖ ^ 2) := by
        nlinarith [sq_nonneg (timeDerivative u r x i + timeDerivative v r x i)]
      linarith
    refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
    simp only [hG, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hFn : Integrable (fun x => ‖Fint u v (r, x)‖) := (hfun ▸ hint).norm
  refine (integral_mono hFn hGi hbd).trans ?_
  have iU : Integrable (fun x => ∑ i : Fin 3, u r x i ^ 2) :=
    integrable_sum_sq huc (hu.finite_energy r hr.1.le hr.2)
  have iV : Integrable (fun x => ∑ i : Fin 3, v r x i ^ 2) :=
    integrable_sum_sq hvc (hv.finite_energy r hr.1.le hr.2)
  have iDU : Integrable (fun x => ‖timeDerivative u r x‖ ^ 2) := hRu.2.2.1.1
  have iDV : Integrable (fun x => ‖timeDerivative v r x‖ ^ 2) := hRv.2.2.1.1
  have i1 : Integrable (fun x => 2 * (∑ i : Fin 3, u r x i ^ 2 + ∑ i : Fin 3, v r x i ^ 2)) :=
    (iU.add iV).const_mul 2
  have i2 : Integrable (fun x => 6 * (‖timeDerivative u r x‖ ^ 2 +
      ‖timeDerivative v r x‖ ^ 2)) := (iDU.add iDV).const_mul 6
  show ∫ x, (2 * (∑ i : Fin 3, u r x i ^ 2 + ∑ i : Fin 3, v r x i ^ 2) +
    6 * (‖timeDerivative u r x‖ ^ 2 + ‖timeDerivative v r x‖ ^ 2)) ≤ _
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_add iU iV,
    integral_add iDU iDV]
  have e1 : ∫ x, ∑ i : Fin 3, u r x i ^ 2 ≤ kineticEnergy u 0 := hu.energy_le_initial r hr.1.le hr.2
  have e2 : ∫ x, ∑ i : Fin 3, v r x i ^ 2 ≤ kineticEnergy v 0 := hv.energy_le_initial r hr.1.le hr.2
  have e3 := hRu.2.2.1.2
  have e4 := hRv.2.2.1.2
  linarith

theorem integrable_sum_sq_diff {U V : Space → Space} (hUc : Continuous U) (hVc : Continuous V)
    (hU : Integrable (fun x => ‖U x‖ ^ 2)) (hV : Integrable (fun x => ‖V x‖ ^ 2)) :
    Integrable (fun x => ∑ i : Fin 3, (U x i - V x i) ^ 2) := by
  have h : Integrable (fun x => ‖U x - V x‖ ^ 2) :=
    ((hU.add hV).const_mul 2).mono' ((hUc.sub hVc).norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := norm_sub_le (U x) (V x)
        have h0 := norm_nonneg (U x - V x)
        show ‖U x - V x‖ ^ 2 ≤ 2 * (‖U x‖ ^ 2 + ‖V x‖ ^ 2)
        nlinarith [sq_nonneg (‖U x‖ - ‖V x‖)])
  exact integrable_sum_sq (hUc.sub hVc) h

/-- **The energy identity**: `E(s) - E(0) = ∫₀ˢ ∫ 2 W·∂ₜW`. -/
theorem energy_identity {ν T T' K s : ℝ} (hν : 0 ≤ ν) {u v : VelocityEvolution}
    {p q : PressureEvolution} (hu : SolvesBefore ν T u p) (hv : SolvesBefore ν T v q)
    (hT'T : T' < T) (hs : s ∈ Icc (0 : ℝ) T')
    (hR : ∀ r ∈ Icc (0 : ℝ) T', Rslice K u p r ∧ Rslice K v q r) :
    IntegrableOn (fun r => ∫ x, Fint u v (r, x)) (Ioc 0 s) ∧
      Ediff u v s - Ediff u v 0 = ∫ r in Ioc 0 s, ∫ x, Fint u v (r, x) := by
  have hsu := hu.classical.1
  have hsv := hv.classical.1
  have hsT : s < T := lt_of_le_of_lt hs.2 hT'T
  set μ : Measure ℝ := volume.restrict (Ioc 0 s) with hμ
  have hprod : μ.prod (volume : Measure Space) =
      ((volume : Measure ℝ).prod (volume : Measure Space)).restrict (Ioc 0 s ×ˢ univ) := by
    rw [hμ, ← Measure.prod_restrict, Measure.restrict_univ]
  have hsub : Ioc (0 : ℝ) s ×ˢ (univ : Set Space) ⊆ Ioo (0 : ℝ) T ×ˢ univ :=
    prod_mono (fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hsT⟩) subset_rfl
  have hmeas : AEStronglyMeasurable (Fint u v) (μ.prod volume) := by
    rw [hprod]
    exact ((continuousOn_Fint hsu hsv).mono hsub).aestronglyMeasurable
      (measurableSet_Ioc.prod MeasurableSet.univ)
  set B : ℝ := 2 * (kineticEnergy u 0 + kineticEnergy v 0) + 12 * K
  have hsec : ∀ r ∈ Ioc (0 : ℝ) s, Integrable (fun x => Fint u v (r, x)) ∧
      ∫ x, ‖Fint u v (r, x)‖ ≤ B := fun r hr =>
    Fint_section hν hu hv ⟨hr.1, lt_of_le_of_lt hr.2 hsT⟩ (hR r ⟨hr.1.le, hr.2.trans hs.2⟩).1
      (hR r ⟨hr.1.le, hr.2.trans hs.2⟩).2
  have hInt : Integrable (Fint u v) (μ.prod volume) := by
    refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using (hsec r hr).1
    · refine (integrableOn_const (C := B) (s := Ioc (0 : ℝ) s)
        (hs := measure_Ioc_lt_top.ne)).mono'
        hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      exact (hsec r hr).2
  have hJ : Integrable (fun r => ∫ x, Fint u v (r, x)) μ := hInt.integral_prod_left
  refine ⟨hJ, ?_⟩
  have hswap : ∫ r, (∫ x, Fint u v (r, x)) ∂μ = ∫ x, (∫ r, Fint u v (r, x) ∂μ) :=
    integral_integral_swap (f := fun r x => Fint u v (r, x)) hInt
  rw [hswap]
  -- per-point fundamental theorem of calculus
  have hFTC : ∀ᵐ x ∂(volume : Measure Space), ∫ r, Fint u v (r, x) ∂μ =
      ∑ i : Fin 3, (u s x i - v s x i) ^ 2 - ∑ i : Fin 3, (u 0 x i - v 0 x i) ^ 2 := by
    filter_upwards [hInt.prod_left_ae] with x hx
    have hcont : ContinuousOn (fun r => ∑ i : Fin 3, (u r x i - v r x i) ^ 2) (Icc 0 s) := by
      have hsub' : Icc (0 : ℝ) s ⊆ Ico 0 T := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hsT⟩
      have hcu : ContinuousOn (fun r => u r x) (Icc 0 s) :=
        ((continuousOn_vel hsu).comp (continuous_id.prodMk continuous_const).continuousOn
          (fun r hr => ⟨hsub' hr, mem_univ _⟩))
      have hcv : ContinuousOn (fun r => v r x) (Icc 0 s) :=
        ((continuousOn_vel hsv).comp (continuous_id.prodMk continuous_const).continuousOn
          (fun r hr => ⟨hsub' hr, mem_univ _⟩))
      exact continuousOn_finsetSum _ fun i _ =>
        (((continuous_apply i).comp_continuousOn hcu).sub
          ((continuous_apply i).comp_continuousOn hcv)).pow 2
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 hcont
      (fun r hr => hasDerivAt_sqdiff hsu hsv ⟨hr.1, lt_trans hr.2 hsT⟩ x)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).2 hx)
    rw [intervalIntegral.integral_of_le hs.1] at h
    exact h
  rw [integral_congr_ae hFTC]
  have hs0 : s ∈ Ico (0 : ℝ) T := ⟨hs.1, hsT⟩
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) T := ⟨le_rfl, lt_of_le_of_lt hs.1 hsT⟩
  rw [integral_sub
    (integrable_sum_sq_diff (contDiff_slice hsu hs0).continuous (contDiff_slice hsv hs0).continuous
      (hu.finite_energy s hs.1 hsT) (hv.finite_energy s hs.1 hsT))
    (integrable_sum_sq_diff (contDiff_slice hsu h0).continuous (contDiff_slice hsv h0).continuous
      (hu.finite_energy 0 le_rfl h0.2) (hv.finite_energy 0 le_rfl h0.2))]
  rfl

/-! ## Strong–strong uniqueness -/

theorem Ediff_nonneg (u v : VelocityEvolution) (t : ℝ) : 0 ≤ Ediff u v t :=
  integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _

theorem Ediff_le {ν T t : ℝ} {u v : VelocityEvolution} {p q : PressureEvolution}
    (hu : SolvesBefore ν T u p) (hv : SolvesBefore ν T v q) (ht0 : 0 ≤ t) (htT : t < T) :
    Ediff u v t ≤ 2 * (kineticEnergy u 0 + kineticEnergy v 0) := by
  have ht : t ∈ Ico (0 : ℝ) T := ⟨ht0, htT⟩
  have huc := (contDiff_slice hu.classical.1 ht).continuous
  have hvc := (contDiff_slice hv.classical.1 ht).continuous
  have iU := integrable_sum_sq huc (hu.finite_energy t ht0 htT)
  have iV := integrable_sum_sq hvc (hv.finite_energy t ht0 htT)
  have hmono : Ediff u v t ≤ ∫ x, 2 * (∑ i : Fin 3, u t x i ^ 2 + ∑ i : Fin 3, v t x i ^ 2) := by
    refine integral_mono (integrable_sum_sq_diff huc hvc (hu.finite_energy t ht0 htT)
      (hv.finite_energy t ht0 htT)) ((iU.add iV).const_mul 2) (fun x => ?_)
    show ∑ i : Fin 3, (u t x i - v t x i) ^ 2 ≤ 2 * (∑ i : Fin 3, u t x i ^ 2 + ∑ i : Fin 3, v t x i ^ 2)
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (u t x i + v t x i)]
  have e : ∫ x, 2 * (∑ i : Fin 3, u t x i ^ 2 + ∑ i : Fin 3, v t x i ^ 2) =
      2 * (kineticEnergy u t + kineticEnergy v t) := by
    rw [integral_const_mul, integral_add iU iV]; rfl
  have h1 := hu.energy_le_initial t ht0 htT
  have h2 := hv.energy_le_initial t ht0 htT
  linarith

/-- **Strong–strong uniqueness in `R`.** -/
theorem uniqueness_R {ν T : ℝ} (hν : 0 < ν) {u v : VelocityEvolution} {p q : PressureEvolution}
    (hu : SolvesBefore ν T u p) (hv : SolvesBefore ν T v q)
    (hRu : RegularOnCompacts T u p) (hRv : RegularOnCompacts T v q) (h0 : u 0 = v 0) :
    ∀ t : ℝ, 0 ≤ t → t < T → u t = v t := by
  intro t ht0 htT
  set T' : ℝ := (t + T) / 2 with hT'
  have hT'T : T' < T := by rw [hT']; linarith
  have htT' : t ≤ T' := by rw [hT']; linarith
  obtain ⟨Ku, hKu⟩ := hRu T' hT'T
  obtain ⟨Kv, hKv⟩ := hRv T' hT'T
  set K : ℝ := max Ku Kv
  have hR : ∀ r ∈ Icc (0 : ℝ) T', Rslice K u p r ∧ Rslice K v q r := fun r hr =>
    ⟨Rslice.mono (hKu r hr) (le_max_left _ _), Rslice.mono (hKv r hr) (le_max_right _ _)⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans ((hR 0 ⟨le_rfl, (ht0.trans htT')⟩).1.2.2.2.1.1 0)
  have hsu := hu.classical.1
  have hsv := hv.classical.1
  set E : ℝ → ℝ := Ediff u v
  have hE0 : E 0 = 0 := by
    show ∫ x, ∑ i : Fin 3, (u 0 x i - v 0 x i) ^ 2 = 0
    simp [h0]
  -- measurability and boundedness of `E`
  have hEmeas : AEStronglyMeasurable E (volume.restrict (Icc (0 : ℝ) T')) := by
    have hprod : (volume.restrict (Icc (0 : ℝ) T')).prod (volume : Measure Space) =
        ((volume : Measure ℝ).prod (volume : Measure Space)).restrict (Icc 0 T' ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have hc : ContinuousOn (fun z : ℝ × Space => ∑ i : Fin 3, (u z.1 z.2 i - v z.1 z.2 i) ^ 2)
        (Icc (0 : ℝ) T' ×ˢ univ) := by
      have hsub : Icc (0 : ℝ) T' ×ˢ (univ : Set Space) ⊆ Ico 0 T ×ˢ univ :=
        prod_mono (fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hT'T⟩) subset_rfl
      have hu' := (continuousOn_vel hsu).mono hsub
      have hv' := (continuousOn_vel hsv).mono hsub
      exact continuousOn_finsetSum _ fun i _ =>
        (((continuous_apply i).comp_continuousOn hu').sub
          ((continuous_apply i).comp_continuousOn hv')).pow 2
    have hm : AEStronglyMeasurable (fun z : ℝ × Space =>
        ∑ i : Fin 3, (u z.1 z.2 i - v z.1 z.2 i) ^ 2)
        ((volume.restrict (Icc (0 : ℝ) T')).prod volume) := by
      rw [hprod]
      exact hc.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)
    exact hm.integral_prod_right'
  set Bd : ℝ := 2 * (kineticEnergy u 0 + kineticEnergy v 0)
  have hEB : ∀ r ∈ Icc (0 : ℝ) T', E r ≤ Bd := fun r hr =>
    Ediff_le hu hv hr.1 (lt_of_le_of_lt hr.2 hT'T)
  have hEint : IntegrableOn E (Icc (0 : ℝ) T') := by
    refine (integrableOn_const (C := Bd) (s := Icc (0 : ℝ) T')
      (hs := measure_Icc_lt_top.ne)).mono' hEmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (Ediff_nonneg u v r)]
    exact hEB r hr
  -- the integral inequality
  have hle : ∀ s ∈ Icc (0 : ℝ) T', E s ≤ 6 * K * ∫ r in (0 : ℝ)..s, E r := by
    intro s hs
    obtain ⟨hJ, hid⟩ := energy_identity hν.le hu hv hT'T hs hR
    have hJle : ∀ r ∈ Ioc (0 : ℝ) s, ∫ x, Fint u v (r, x) ≤ 6 * K * E r := by
      intro r hr
      have hrT : r ∈ Ioo (0 : ℝ) T := ⟨hr.1, lt_of_le_of_lt (hr.2.trans hs.2) hT'T⟩
      have hRr := hR r ⟨hr.1.le, hr.2.trans hs.2⟩
      have h := (time_slice_energy hν.le hu hv hrT.1.le hrT.2 hRr.1 hRr.2).2
      have e : ∫ x, Fint u v (r, x) = ∫ x, ∑ i : Fin 3, 2 * (u r x i - v r x i) *
          (timeDerivative u r x i - timeDerivative v r x i) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Fint, timeDerivative_eq_tD hsu hrT, timeDerivative_eq_tD hsv hrT]
      rw [e]; exact h
    have hEIoc : IntegrableOn E (Ioc (0 : ℝ) s) :=
      hEint.mono_set (fun r hr => ⟨hr.1.le, hr.2.trans hs.2⟩)
    have hmono : ∫ r in Ioc (0 : ℝ) s, ∫ x, Fint u v (r, x) ≤ ∫ r in Ioc (0 : ℝ) s, 6 * K * E r :=
      setIntegral_mono_on hJ (hEIoc.const_mul _) measurableSet_Ioc hJle
    rw [integral_const_mul] at hmono
    have hE0' : Ediff u v 0 = 0 := hE0
    rw [hE0', sub_zero] at hid
    show Ediff u v s ≤ _
    rw [hid, intervalIntegral.integral_of_le hs.1]; exact hmono
  have hzero := gronwall_zero (by positivity) (fun r _ => Ediff_nonneg u v r) hEB hEint hle
    t ⟨ht0, htT'⟩
  -- conclude pointwise equality
  have ht : t ∈ Ico (0 : ℝ) T := ⟨ht0, htT⟩
  have huc := (contDiff_slice hsu ht).continuous
  have hvc := (contDiff_slice hsv ht).continuous
  have hgc : Continuous (fun x => ∑ i : Fin 3, (u t x i - v t x i) ^ 2) :=
    continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp huc).sub ((continuous_apply i).comp hvc)).pow 2
  have hgi := integrable_sum_sq_diff huc hvc (hu.finite_energy t ht0 htT)
    (hv.finite_energy t ht0 htT)
  have hae : (fun x => ∑ i : Fin 3, (u t x i - v t x i) ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _) hgi).1
      hzero
  have hall : (fun x => ∑ i : Fin 3, (u t x i - v t x i) ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq volume hgc continuous_const).1 hae
  funext x i
  have hx := congrFun hall x
  simp only [Pi.zero_apply] at hx
  have hi : (u t x i - v t x i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hx i (Finset.mem_univ i)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hi
  linarith

end Navier.Analysis.RegularUniqueness

set_option pp.fullNames true in
#print axioms Navier.Analysis.RegularUniqueness.uniqueness_R
set_option pp.fullNames true in
#print axioms Navier.Analysis.RegularUniqueness.slice_energy
