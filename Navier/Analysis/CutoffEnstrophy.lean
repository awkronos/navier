import Navier.Analysis.LocalEnstrophyBalance

/-!
# The cutoff enstrophy and its time derivative (integral layer, part a)

The cutoff enstrophy `E_χ(t) = ∫ χ(x) |ω(t,x)|² dx` localizes the enstrophy
against a spatial multiplier `χ`.  This file derives its time derivative by
differentiation under the integral
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`):

  `E_χ'(t₀) = ∫ χ · ∂ₜ(|ω|²) = ∫ χ · (2⟨ω, ∂ₜω⟩)`,

and, composing with the established pointwise balance
`local_enstrophy_balance`, the **cutoff enstrophy rate in balance form**

  `E_χ'(t₀) = ∫ χ · (2⟨ω,(ω·∇)u⟩ − (u·∇)|ω|² + νΔ|ω|² − 2ν|∇ω|²)`.

The differentiation is performed under the named Pattern-A hypothesis
`LocallyDominatedEnstrophy` (ladder rung 6, residual (c) input): an `L¹`
majorant `g` dominating `|ω(t,·)|²` and `∂ₜ(|ω(t,·)|²) = 2⟨ω,∂ₜω⟩` uniformly
for `t` in each compact subset of `[0,T)`.  This domination is automatic for
`H^m`/Schwartz-class solutions but is not carried by `IsClassicalSolution`
(Step-0e: without it the Bochner integral can degenerate and the derivative
interchange fails), so it is an explicit hypothesis, never assumed silently.
`locallyDominatedEnstrophy_zero` anchors non-vacuity.

Supporting layer built here and reusable downstream:

* `fderiv_space_slice_apply` / `differentiableWithinAt_spaceDeriv_curve` —
  public joint-smoothness bridges (the `VorticityTransport` versions are
  `private`): the spatial-derivative curve `s ↦ D(u s)(x)eᵢ` is
  differentiable within `Ici 0`.
* `differentiableWithinAt_vorticity_timeCurve`, `vorticity_hasDerivAt_time` —
  the vorticity time curve is differentiable, with the repository's one-sided
  `timeDerivative` as its two-sided derivative at interior times.
* `hasDerivAt_officialNormSq_comp` — `d/dt |v(t)|² = 2⟨v, v'⟩` in the
  official coordinates.
* `continuous_timeDerivative_vorticity` — spatial continuity of `∂ₜω` along a
  classical solution, obtained through the established transport equation
  `∂ₜω = (ω·∇)u + νΔω − (u·∇)ω`.

Residual (ladder rung 6, integral layer): the `R → ∞` interchange — the
`∇χ_R`/`Δχ_R` remainders vanish and `E_{χ_R} → E` under the same domination
hypothesis — feeding `enstrophyDifferentialInequality`.  The integration by
parts converting the transport and viscous terms into `∇χ`/`Δχ` remainders is
`Navier.Analysis.CutoffIntegrationByParts`.

Reference: Majda–Bertozzi, *Vorticity and Incompressible Flow*, §3.3.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open MeasureTheory Set

namespace Navier.Analysis.CutoffEnstrophy

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Enstrophy
open Navier.Analysis.EnstrophyPointwise
open Navier.Analysis.LocalEnstrophyBalance

/-!
## Joint-smoothness bridges (public)
-/

/-- **Space-slice bridge.**  The spatial derivative of a nonnegative-time
slice equals the joint within-derivative along `(0, v)`.  Public counterpart
of the `private` bridge inside `VorticityTransport`. -/
theorem fderiv_space_slice_apply {β : Type*} [NormedAddCommGroup β]
    [NormedSpace ℝ β] {F : ℝ → Space → β}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Space => F z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs : 0 ≤ s) (x v : Space) :
    fderiv ℝ (F s) x v =
      fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) (s, x) (0, v) := by
  have hmem : (s, x) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ :=
    Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hs, Set.mem_univ x⟩
  have hG : HasFDerivWithinAt (fun z : ℝ × Space => F z.1 z.2)
      (fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) (s, x))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) (s, x) :=
    ((hF (s, x) hmem).differentiableWithinAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)).hasFDerivWithinAt
  have hκ : HasFDerivAt (fun y : Space => (s, y))
      (ContinuousLinearMap.inr ℝ ℝ Space) x := hasFDerivAt_prodMk_right s x
  have hmaps : Set.MapsTo (fun y : Space => (s, y)) Set.univ
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun y _ =>
    Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hs, Set.mem_univ y⟩
  have hcomp := HasFDerivWithinAt.comp x hG hκ.hasFDerivWithinAt hmaps
  rw [show ((fun z : ℝ × Space => F z.1 z.2) ∘ (fun y : Space => (s, y))) =
      F s from rfl] at hcomp
  have hAt : HasFDerivAt (F s)
      ((fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) (s, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
    hcomp.hasFDerivAt Filter.univ_mem
  rw [hAt.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- The spatial-derivative curve `s ↦ D(u s)(x) eᵢ` is differentiable within
`Ici 0` at every nonnegative time.  Public counterpart of the `private`
curve lemma inside `VorticityTransport`. -/
theorem differentiableWithinAt_spaceDeriv_curve (u : VelocityEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u) {t : ℝ} (ht : 0 ≤ t) (x : Space)
    (i : Fin 3) :
    DifferentiableWithinAt ℝ (fun s => fderiv ℝ (u s) x (basisVector i))
      (Set.Ici 0) t := by
  set S : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ Set.univ with hSdef
  set G : ℝ × Space → Space := fun z => u z.1 z.2 with hGdef
  have hUD : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hz : (t, x) ∈ S := Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht, Set.mem_univ x⟩
  have hg2 : ContDiffWithinAt ℝ ∞ G S (t, x) := hu (t, x) hz
  have hDg : DifferentiableWithinAt ℝ (fderivWithin ℝ G S) S (t, x) :=
    (hg2.fderivWithin_right hUD (by decide) hz).differentiableWithinAt one_ne_zero
  have hH : DifferentiableWithinAt ℝ
      (fun z' => fderivWithin ℝ G S z' ((0, basisVector i) : ℝ × Space))
      S (t, x) := by
    let T : ((ℝ × Space) →L[ℝ] Space) →L[ℝ] Space :=
      ContinuousLinearMap.apply ℝ Space ((0, basisVector i) : ℝ × Space)
    have hcomp := DifferentiableWithinAt.comp (t, x)
      (T.differentiableAt).differentiableWithinAt hDg (fun z' _ => Set.mem_univ _)
    rw [show (T ∘ (fderivWithin ℝ G S)) =
        (fun z' => fderivWithin ℝ G S z' ((0, basisVector i) : ℝ × Space))
        from rfl] at hcomp
    exact hcomp
  have hmaps : Set.MapsTo (fun s : ℝ => (s, x)) (Set.Ici 0) S := fun s hs =>
    Set.mem_prod.mpr ⟨hs, Set.mem_univ x⟩
  have hcomp := hH.comp t
    (hasFDerivAt_prodMk_left t x).hasFDerivWithinAt.differentiableWithinAt hmaps
  rw [show ((fun z' => fderivWithin ℝ G S z' (0, basisVector i)) ∘
      (fun s : ℝ => (s, x))) =
      (fun s => fderivWithin ℝ G S (s, x) (0, basisVector i)) from rfl] at hcomp
  refine hcomp.congr (fun s hs => ?_) ?_
  · exact fderiv_space_slice_apply hu (Set.mem_Ici.mp hs) x (basisVector i)
  · exact fderiv_space_slice_apply hu ht x (basisVector i)

/-!
## The vorticity time curve
-/

/-- The vorticity time curve `s ↦ ω(s,x)` is differentiable within `Ici 0` at
every nonnegative time: the curl is a fixed linear combination of the
spatial-derivative curves. -/
theorem differentiableWithinAt_vorticity_timeCurve (u : VelocityEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    DifferentiableWithinAt ℝ (fun s => vorticity u s x) (Set.Ici 0) t := by
  have hshape : (fun s => vorticity u s x) =
      (fun s => ∑ i : Fin 3,
        (crossProduct (basisVector i)) (fderiv ℝ (u s) x (basisVector i))) := rfl
  rw [hshape]
  exact DifferentiableWithinAt.fun_sum fun i _ =>
    ((crossProduct (basisVector i)).toContinuousLinearMap.differentiableAt
      ).comp_differentiableWithinAt t
      (differentiableWithinAt_spaceDeriv_curve u hu ht x i)

/-- At interior times the vorticity time curve has the repository's one-sided
`timeDerivative` as a genuine two-sided derivative: `Ici 0` is a neighborhood
of every `t > 0`, so the within-derivative agrees with the full derivative. -/
theorem vorticity_hasDerivAt_time (u : VelocityEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u) {t : ℝ} (ht : 0 < t) (x : Space) :
    HasDerivAt (fun s => vorticity u s x)
      (timeDerivative (fun s => vorticity u s) t x) t := by
  have hnhds : Set.Ici (0 : ℝ) ∈ nhds t := Ici_mem_nhds ht
  have hda : DifferentiableAt ℝ (fun s => vorticity u s x) t :=
    (differentiableWithinAt_vorticity_timeCurve u hu ht.le x).differentiableAt
      hnhds
  have hval : timeDerivative (fun s => vorticity u s) t x =
      fderiv ℝ (fun s => vorticity u s x) t 1 := by
    unfold timeDerivative
    rw [fderivWithin_of_mem_nhds hnhds]
  rw [hval]
  simpa [fderiv_apply_one_eq_deriv] using hda.hasDerivAt

/-- **Time derivative of the squared official norm along a curve**:
`d/dt |v(t)|² = 2⟨v(t), v'(t)⟩`, componentwise Leibniz in the official
coordinates. -/
theorem hasDerivAt_officialNormSq_comp {v : ℝ → Space} {v' : Space} {t : ℝ}
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => officialEuclideanNorm (v s) ^ 2)
      (2 * officialInner (v t) v') t := by
  have hcomp : ∀ j : Fin 3, HasDerivAt (fun s => v s j) (v' j) t := fun j =>
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp_hasDerivAt t hv
  have hsum : HasDerivAt (fun s => ∑ j : Fin 3, v s j * v s j)
      (∑ j : Fin 3, (v' j * v t j + v t j * v' j)) t :=
    HasDerivAt.fun_sum fun j _ => (hcomp j).mul (hcomp j)
  have hshape : (fun s => officialEuclideanNorm (v s) ^ 2) =
      (fun s => ∑ j : Fin 3, v s j * v s j) := by
    funext s
    rw [officialEuclideanNorm_sq_eq_sum]
    exact Finset.sum_congr rfl fun j _ => sq (v s j)
  have hval : 2 * officialInner (v t) v' =
      ∑ j : Fin 3, (v' j * v t j + v t j * v' j) := by
    rw [officialInner_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hshape, hval]
  exact hsum

/-!
## Spatial continuity of the pointwise rate
-/

/-- The official inner product of two continuous fields is continuous. -/
theorem continuous_officialInner_comp {f g : Space → Space}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => officialInner (f x) (g x)) := by
  have hshape : (fun x => officialInner (f x) (g x)) =
      (fun x => ∑ i : Fin 3, f x i * g x i) := by
    funext x
    exact officialInner_eq_sum (f x) (g x)
  rw [hshape]
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)

/-- The squared official norm of a continuous field is continuous. -/
theorem continuous_officialNormSq_comp {f : Space → Space} (hf : Continuous f) :
    Continuous (fun x => officialEuclideanNorm (f x) ^ 2) := by
  have hshape : (fun x => officialEuclideanNorm (f x) ^ 2) =
      (fun x => ∑ i : Fin 3, f x i ^ 2) := by
    funext x
    exact officialEuclideanNorm_sq_eq_sum (f x)
  rw [hshape]
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hf).pow 2

/-- **Spatial continuity of `∂ₜω`** along a classical solution, through the
established transport equation `∂ₜω = (ω·∇)u + νΔω − (u·∇)ω`: each right-hand
term is a continuous spatial-derivative expression of `C^∞` slices. -/
theorem continuous_timeDerivative_vorticity
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (fun x => timeDerivative (fun s => vorticity u s) t x) := by
  have huAll : ContDiff ℝ ∞ (u t) := contDiff_iff_contDiffAt.mpr fun y =>
    VorticityTransport.contDiffAt_spatial_slice hsol.velocity_smooth ht y
  have hωC : ContDiff ℝ ∞ (vorticity u t) := vorticity_contDiff hsol ht
  have heq : (fun x => timeDerivative (fun s => vorticity u s) t x) =
      (fun x => spatialDerivative u t x (vorticity u t x)
        + ν • laplacian (fun s => vorticity u s) t x
        - spatialDerivative (fun s => vorticity u s) t x (u t x)) := by
    funext x
    exact eq_sub_of_add_eq (vorticityTransportEquation hsol t ht x)
  rw [heq]
  have h1 : Continuous (fun x => spatialDerivative u t x (vorticity u t x)) :=
    (huAll.continuous_fderiv (by norm_num)).clm_apply hωC.continuous
  have h2 : Continuous (fun x => laplacian (fun s => vorticity u s) t x) := by
    have hshape : (fun x => laplacian (fun s => vorticity u s) t x) =
        (fun x => ∑ i : Fin 3,
          fderiv ℝ (fun y => fderiv ℝ (vorticity u t) y (basisVector i)) x
            (basisVector i)) := rfl
    rw [hshape]
    refine continuous_finsetSum _ fun i _ => ?_
    have hFi : ContDiff ℝ ∞
        (fun y => fderiv ℝ (vorticity u t) y (basisVector i)) :=
      (hωC.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const
    exact (hFi.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h3 : Continuous
      (fun x => spatialDerivative (fun s => vorticity u s) t x (u t x)) :=
    (hωC.continuous_fderiv (by norm_num)).clm_apply huAll.continuous
  exact (h1.add (continuous_const.smul h2)).sub h3

/-!
## The cutoff enstrophy and the Pattern-A domination hypothesis
-/

/-- The **cutoff enstrophy**: the vorticity `L²` mass weighted by a spatial
multiplier `χ`.  (For a cutoff family `χ = χ_R` this is `E_R`; the `R → ∞`
recovery of the full `enstrophy` is the named residual of the integral
layer.) -/
def cutoffEnstrophy (χ : Space → ℝ) (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * officialEuclideanNorm (vorticity u t x) ^ 2

/-- **Pattern-A domination hypothesis** (ladder rung 6, integral layer):
an `L¹` majorant dominating the enstrophy density `|ω(t,·)|²` and its
pointwise rate `∂ₜ(|ω(t,·)|²) = 2⟨ω, ∂ₜω⟩` (`hasDerivAt_officialNormSq_comp`)
uniformly for `t` in each compact subset of `[0,T)`.  Automatic for
`H^m`/Schwartz-class solutions; NOT carried by `IsClassicalSolution`
(Step-0e), hence explicit. -/
def LocallyDominatedEnstrophy (u : VelocityEvolution) (T : ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ico 0 T →
    ∃ g : Space → ℝ, Integrable g ∧
      (∀ t ∈ K, ∀ x : Space,
        officialEuclideanNorm (vorticity u t x) ^ 2 ≤ g x) ∧
      (∀ t ∈ K, ∀ x : Space,
        |2 * officialInner (vorticity u t x)
          (timeDerivative (fun s => vorticity u s) t x)| ≤ g x)

/-- Non-vacuity anchor: the zero velocity satisfies the domination hypothesis
for every horizon, with the zero majorant. -/
theorem locallyDominatedEnstrophy_zero (T : ℝ) :
    LocallyDominatedEnstrophy (fun _ _ => 0) T := by
  intro K _ _
  refine ⟨fun _ => 0, integrable_zero _ _ _, ?_, ?_⟩
  · intro t _ x
    have hv : vorticity (fun _ _ => 0) t x = 0 := by
      simp [vorticity, staticCurl]
    rw [hv, (officialEuclideanNorm_eq_zero_iff 0).mpr rfl]
    norm_num
  · intro t _ x
    have hv : vorticity (fun _ _ => 0) t x = 0 := by
      simp [vorticity, staticCurl]
    have hzero : officialInner (0 : Space)
        (timeDerivative (fun s => vorticity (fun _ _ => 0) s) t x) = 0 := by
      rw [officialInner_eq_sum]
      simp
    rw [hv, hzero]
    norm_num

/-!
## The cutoff enstrophy rate (differentiation under the integral)
-/

/-- **Cutoff enstrophy rate.**  Along a classical solution satisfying the
Pattern-A domination hypothesis, for every continuous bounded multiplier `χ`
and interior time `t₀ ∈ (0,T)`, the cutoff enstrophy is differentiable with

  `E_χ'(t₀) = ∫ χ · (2⟨ω, ∂ₜω⟩)`.

Differentiation under the integral via
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` over the compact time
window `[t₀−ε, t₀+ε] ⊂ (0,T)`: the domination hypothesis supplies the
uniform `L¹` bound, `vorticity_hasDerivAt_time` +
`hasDerivAt_officialNormSq_comp` the pointwise derivative, and
`continuous_timeDerivative_vorticity` the measurability of the rate. -/
theorem cutoffEnstrophy_hasDerivAt
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    {T : ℝ} (hdom : LocallyDominatedEnstrophy u T)
    {χ : Space → ℝ} (hχc : Continuous χ) {C : ℝ} (hχbd : ∀ x, |χ x| ≤ C)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 T) :
    HasDerivAt (cutoffEnstrophy χ u)
      (∫ x : Space, χ x * (2 * officialInner (vorticity u t₀ x)
        (timeDerivative (fun s => vorticity u s) t₀ x))) t₀ := by
  obtain ⟨ht₀pos, ht₀T⟩ := ht₀
  set ε : ℝ := min (t₀ / 2) ((T - t₀) / 2) with hεdef
  have hε1 : ε ≤ t₀ / 2 := min_le_left _ _
  have hε2 : ε ≤ (T - t₀) / 2 := min_le_right _ _
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hKsub : Set.Icc (t₀ - ε) (t₀ + ε) ⊆ Set.Ico 0 T := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨g, hgInt, hgSq, hgD⟩ :=
    hdom (Set.Icc (t₀ - ε) (t₀ + ε)) isCompact_Icc hKsub
  have hpos : ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε), (0:ℝ) < s := fun s hs => by
    have := hs.1
    linarith
  have ht₀K : t₀ ∈ Set.Icc (t₀ - ε) (t₀ + ε) :=
    Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hs_nhds : Set.Icc (t₀ - ε) (t₀ + ε) ∈ nhds t₀ :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hχbd 0)
  have hF_meas : ∀ᶠ t in nhds t₀, AEStronglyMeasurable
      (fun x : Space => χ x * officialEuclideanNorm (vorticity u t x) ^ 2)
      volume := by
    filter_upwards [hs_nhds] with t htK
    exact (hχc.mul (continuous_officialNormSq_comp
      (vorticity_contDiff hsol (hpos t htK).le).continuous)).aestronglyMeasurable
  have hFmeas₀ : AEStronglyMeasurable
      (fun x : Space => χ x * officialEuclideanNorm (vorticity u t₀ x) ^ 2)
      volume :=
    (hχc.mul (continuous_officialNormSq_comp
      (vorticity_contDiff hsol ht₀pos.le).continuous)).aestronglyMeasurable
  have hF_int : Integrable
      (fun x : Space => χ x * officialEuclideanNorm (vorticity u t₀ x) ^ 2)
      volume := by
    refine (hgInt.const_mul C).mono' hFmeas₀ ?_
    filter_upwards with x
    have h1 : officialEuclideanNorm (vorticity u t₀ x) ^ 2 ≤ g x :=
      hgSq t₀ ht₀K x
    have h2 : (0:ℝ) ≤ officialEuclideanNorm (vorticity u t₀ x) ^ 2 :=
      sq_nonneg _
    calc ‖χ x * officialEuclideanNorm (vorticity u t₀ x) ^ 2‖
        = |χ x| * (officialEuclideanNorm (vorticity u t₀ x) ^ 2) := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h2]
      _ ≤ C * g x := mul_le_mul (hχbd x) h1 h2 hCnn
  have hDcont : Continuous (fun x => 2 * officialInner (vorticity u t₀ x)
      (timeDerivative (fun s => vorticity u s) t₀ x)) :=
    continuous_const.mul (continuous_officialInner_comp
      (vorticity_contDiff hsol ht₀pos.le).continuous
      (continuous_timeDerivative_vorticity hsol ht₀pos.le))
  have hF'_meas : AEStronglyMeasurable
      (fun x : Space => χ x * (2 * officialInner (vorticity u t₀ x)
        (timeDerivative (fun s => vorticity u s) t₀ x))) volume :=
    (hχc.mul hDcont).aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂(volume : Measure Space),
      ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      ‖χ x * (2 * officialInner (vorticity u t x)
        (timeDerivative (fun s => vorticity u s) t x))‖ ≤ C * g x := by
    filter_upwards with x t htK
    calc ‖χ x * (2 * officialInner (vorticity u t x)
          (timeDerivative (fun s => vorticity u s) t x))‖
        = |χ x| * |2 * officialInner (vorticity u t x)
            (timeDerivative (fun s => vorticity u s) t x)| := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ C * g x := mul_le_mul (hχbd x) (hgD t htK x) (abs_nonneg _) hCnn
  have h_diff : ∀ᵐ x ∂(volume : Measure Space),
      ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun t' => χ x * officialEuclideanNorm (vorticity u t' x) ^ 2)
        (χ x * (2 * officialInner (vorticity u t x)
          (timeDerivative (fun s => vorticity u s) t x))) t := by
    filter_upwards with x t htK
    exact (hasDerivAt_officialNormSq_comp
      (vorticity_hasDerivAt_time u hsol.velocity_smooth (hpos t htK) x)
      ).const_mul (χ x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds hF_meas
    hF_int hF'_meas h_bound (hgInt.const_mul C) h_diff).2

/-- **Cutoff enstrophy rate in balance form** (ladder rung 6, integral layer,
part (a)): composing with the established pointwise balance
`local_enstrophy_balance`,

  `E_χ'(t₀) = ∫ χ · (2⟨ω,(ω·∇)u⟩ − (u·∇)|ω|² + νΔ|ω|² − 2ν|∇ω|²)`

— the cutoff integral of the local enstrophy balance right-hand side. -/
theorem cutoffEnstrophy_hasDerivAt_balance
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    {T : ℝ} (hdom : LocallyDominatedEnstrophy u T)
    {χ : Space → ℝ} (hχc : Continuous χ) {C : ℝ} (hχbd : ∀ x, |χ x| ≤ C)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 T) :
    HasDerivAt (cutoffEnstrophy χ u)
      (∫ x : Space, χ x *
        (2 * officialInner (vorticity u t₀ x)
            (spatialDerivative u t₀ x (vorticity u t₀ x))
          - fderiv ℝ (fun y =>
              officialEuclideanNorm (vorticity u t₀ y) ^ 2) x (u t₀ x)
          + ν * (∑ i : Fin 3,
              fderiv ℝ (fun z =>
                fderiv ℝ (fun y =>
                  officialEuclideanNorm (vorticity u t₀ y) ^ 2) z
                  (basisVector i)) x (basisVector i))
          - 2 * ν * (∑ i : Fin 3,
              officialEuclideanNorm
                (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2))) t₀ := by
  have h := cutoffEnstrophy_hasDerivAt hsol hdom hχc hχbd ht₀
  have hfun : (fun x : Space => χ x * (2 * officialInner (vorticity u t₀ x)
      (timeDerivative (fun s => vorticity u s) t₀ x))) =
      (fun x : Space => χ x *
        (2 * officialInner (vorticity u t₀ x)
            (spatialDerivative u t₀ x (vorticity u t₀ x))
          - fderiv ℝ (fun y =>
              officialEuclideanNorm (vorticity u t₀ y) ^ 2) x (u t₀ x)
          + ν * (∑ i : Fin 3,
              fderiv ℝ (fun z =>
                fderiv ℝ (fun y =>
                  officialEuclideanNorm (vorticity u t₀ y) ^ 2) z
                  (basisVector i)) x (basisVector i))
          - 2 * ν * (∑ i : Fin 3,
              officialEuclideanNorm
                (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2))) := by
    funext x
    rw [local_enstrophy_balance hsol ht₀.1.le x]
  have hint : (∫ x : Space, χ x * (2 * officialInner (vorticity u t₀ x)
      (timeDerivative (fun s => vorticity u s) t₀ x))) =
      ∫ x : Space, χ x *
        (2 * officialInner (vorticity u t₀ x)
            (spatialDerivative u t₀ x (vorticity u t₀ x))
          - fderiv ℝ (fun y =>
              officialEuclideanNorm (vorticity u t₀ y) ^ 2) x (u t₀ x)
          + ν * (∑ i : Fin 3,
              fderiv ℝ (fun z =>
                fderiv ℝ (fun y =>
                  officialEuclideanNorm (vorticity u t₀ y) ^ 2) z
                  (basisVector i)) x (basisVector i))
          - 2 * ν * (∑ i : Fin 3,
              officialEuclideanNorm
                (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2)) :=
    congrArg (fun f => ∫ x : Space, f x) hfun
  rw [hint] at h
  exact h

/-- **Full enstrophy rate** (the `χ ≡ 1` instance of the cutoff rate): under
the domination hypothesis the full enstrophy is differentiable at interior
times with

  `E'(t₀) = ∫ 2⟨ω, ∂ₜω⟩`.

The constant multiplier is continuous and bounded by `1`, so no compact
support is needed for the differentiation step; the cutoff family enters only
in the integration-by-parts layer (`CutoffIntegrationByParts`), where the
transport and viscous terms individually need the `∇χ`/`Δχ` remainders. -/
theorem enstrophy_hasDerivAt
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    {T : ℝ} (hdom : LocallyDominatedEnstrophy u T)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 T) :
    HasDerivAt (enstrophy u)
      (∫ x : Space, 2 * officialInner (vorticity u t₀ x)
        (timeDerivative (fun s => vorticity u s) t₀ x)) t₀ := by
  have h := cutoffEnstrophy_hasDerivAt hsol hdom (χ := fun _ => 1)
    continuous_const (C := 1) (fun x => by norm_num) ht₀
  have hEeq : cutoffEnstrophy (fun _ => 1) u = enstrophy u := by
    funext t
    unfold cutoffEnstrophy enstrophy
    congr 1
    funext x
    rw [one_mul]
  have hval : (∫ x : Space, (1:ℝ) * (2 * officialInner (vorticity u t₀ x)
      (timeDerivative (fun s => vorticity u s) t₀ x))) =
      ∫ x : Space, 2 * officialInner (vorticity u t₀ x)
        (timeDerivative (fun s => vorticity u s) t₀ x) := by
    congr 1
    funext x
    rw [one_mul]
  rw [hEeq, hval] at h
  exact h

end Navier.Analysis.CutoffEnstrophy
