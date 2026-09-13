/-
Original work, lane L6b, 2026-09-13. Adapted carriers are imported, not copied.
-/
import Navier.Analysis.BKMForcedBreakdownNecessity
import Navier.Analysis.AprioriCriticalControlQuantifiers
import Navier.Analysis.ConditionalRegularity
import Navier.Construction.R3CompactCandidate

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff BigOperators Matrix Pointwise
open Navier Navier.Analysis.Vorticity Navier.Analysis.OfficialABEncoding
open Navier.Analysis.ConditionalRegularity
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.BKMForcedBreakdownNecessity
open Navier.Construction.ProblemStatement
open Navier.Analysis.AprioriCriticalControlQuantifiers
open Navier.Construction.R3CompactCandidate

/-!
# Vorticity-integral divergence for the selected profile

This module constructs the vorticity sup profile
`V u t = ⨆ x, ‖ω(u,t)(x)‖` in the official Euclidean carrier, proves its
continuity on `Ico 0 1`, assembles the full `BKMControl` hypothesis bundle
from a Grönwall control pair `(Y, Y')`, and derives the divergence statements

* `¬ ∃ B, ∀ t ∈ Ico 0 1, ∫₀ᵗ V u ≤ B`,
* `∫⁻ t in Icc 0 1, ENNReal.ofReal (V u t) = ⊤`,
* `⊤ ≤ bkmVorticityControl 1 (uncurry u)`,

for every `R3CompactCandidate` competitor `u` — in particular the selected
profile, via `selected_candidate_forces_no_BKM_control_in_every_smooth_competitor`.

WHAT THIS MODULE DOES NOT PROVE: it does not construct the Grönwall control
pair `(Y, Y')` — positive continuous `Y` with derivative `Y'` on `Ioo 0 1`
satisfying `Y' ≤ V u · Y` and `‖uncurry u t x‖ ≤ Y t`. That pair is the named
missing primitive (the row's residual); every divergence theorem above is
conditional on it. The carrier equivalences `ofReal (V u t) = vorticityRate`
and the `V`/`Vpi` norm sandwich tie this profile to the estate's existing
critical quantities.
-/

namespace Navier.Analysis.BKMVorticityIntegralDivergence

private abbrev ESpace := Navier.Construction.ProblemStatement.Space
private abbrev EVelocityField := Navier.Construction.ProblemStatement.VelocityField

private def toPiCLM : ESpace →L[ℝ] Navier.Space where
  toFun := fun y => (y : Navier.Space)
  map_add' := by intro a b; rfl
  map_smul' := by intro c x; rfl
  cont := by fun_prop

private def fromPiCLM : Navier.Space →L[ℝ] ESpace where
  toFun := fun x => WithLp.toLp 2 x
  map_add' := by intro a b; rfl
  map_smul' := by intro c x; rfl
  cont := by fun_prop

private theorem fromPiCLM_basis (i : Fin 3) :
    fromPiCLM (basisVector i) = coordinateVector i := rfl

private theorem toPiCLM_apply (y : ESpace) : toPiCLM y = (y : Navier.Space) := rfl

/-! ## 1. Carrier transport. -/

theorem slice_contDiff {u : EVelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun y : ESpace => u (t, y)) :=
  hu.comp_contDiff (contDiff_const.prodMk contDiff_id) fun _ => ⟨ht, trivial⟩

theorem uncurry_slice_contDiff {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ContDiff ℝ ∞ (uncurry u t) := by
  have h1 : ContDiff ℝ ∞ (fun z : ESpace => (u (t, z) : Navier.Space)) :=
    toPiCLM.contDiff.comp (slice_contDiff hu ht)
  have h2 : (fun z : ESpace => (u (t, z) : Navier.Space)) ∘ fromPiCLM =
      uncurry u t := by
    funext x; rfl
  rw [← h2]
  exact h1.comp fromPiCLM.contDiff

theorem fderiv_uncurry_basis {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (x : Navier.Space) (i : Fin 3) :
    (fderiv ℝ (uncurry u t) x (basisVector i)) i =
      (fderiv ℝ (fun y : ESpace => u (t, y)) (WithLp.toLp 2 x) (coordinateVector i)) i := by
  have hd : DifferentiableAt ℝ (fun y : ESpace => u (t, y)) (WithLp.toLp 2 x) :=
    (slice_contDiff hu ht).contDiffAt.differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun y : ESpace => u (t, y))
      (fderiv ℝ (fun y : ESpace => u (t, y)) (WithLp.toLp 2 x)) (WithLp.toLp 2 x) :=
    hd.hasFDerivAt
  have h2 : HasFDerivAt (fun z : Navier.Space => u (t, WithLp.toLp 2 z))
      (fderiv ℝ (fun y : ESpace => u (t, y)) (WithLp.toLp 2 x) ∘L fromPiCLM) x :=
    h1.comp x fromPiCLM.hasFDerivAt
  have h3 : HasFDerivAt (uncurry u t)
      (toPiCLM ∘L (fderiv ℝ (fun y : ESpace => u (t, y)) (WithLp.toLp 2 x) ∘L
        fromPiCLM)) x :=
    toPiCLM.hasFDerivAt.comp x h2
  rw [h3.fderiv]
  simp only [ContinuousLinearMap.comp_apply, fromPiCLM_basis, toPiCLM_apply]

theorem staticDivergence_uncurry_slice {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (x : Navier.Space) :
    staticDivergence (uncurry u t) x = spatialDivergence u t (WithLp.toLp 2 x) := by
  show (∑ i : Fin 3, (fderiv ℝ (uncurry u t) x (basisVector i)) i) =
    (∑ i : Fin 3, (fderiv ℝ (fun y : ESpace => u (t, y)) (WithLp.toLp 2 x)
      (coordinateVector i)) i)
  exact Finset.sum_congr rfl fun i _ => fderiv_uncurry_basis hu ht x i

/-! ## 2. Within-tensor transfer and vorticity expression. -/

theorem xfer {u : EVelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (n : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (y : ESpace) :
    iteratedFDeriv ℝ n (fun z : ESpace => u (t, z)) y =
      (iteratedFDerivWithin ℝ n u preSingularDomain (t, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ ESpace) := by
  classical
  set a : ℝ × ESpace := (t, 0) with hadef
  set σ : Set (ℝ × ESpace) := (fun z : ℝ × ESpace => a + z) ⁻¹' preSingularDomain
    with hσdef
  have hσ : σ = Ico (-t) (1 - t) ×ˢ (univ : Set ESpace) := by
    ext ⟨s, w⟩
    simp only [hσdef, mem_preimage, hadef, Prod.mk_add_mk, preSingularDomain,
      mem_prod, mem_Ico, mem_univ, and_true]
    constructor <;> intro h <;> (try constructor) <;> linarith [ht.1, ht.2]
  have hσuniq : UniqueDiffOn ℝ σ := by
    rw [hσ]
    exact (uniqueDiffOn_Ico _ _).prod uniqueDiffOn_univ
  have hmem : ∀ w : ESpace, ContinuousLinearMap.inr ℝ ℝ ESpace w ∈ σ := by
    intro w
    rw [hσ, ContinuousLinearMap.inr_apply]
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, trivial⟩
  have hpre : (ContinuousLinearMap.inr ℝ ℝ ESpace) ⁻¹' σ = (univ : Set ESpace) :=
    eq_univ_of_forall hmem
  have hpreuniq : UniqueDiffOn ℝ ((ContinuousLinearMap.inr ℝ ℝ ESpace) ⁻¹' σ) := by
    rw [hpre]; exact uniqueDiffOn_univ
  have hmap : ContinuousLinearMap.inr ℝ ℝ ESpace y ∈ σ := hmem y
  have hsmooth : ContDiffOn ℝ ∞ ((fun z : ℝ × ESpace => u z) ∘ fun z => a + z) σ :=
    hu.comp (contDiffOn_const.add contDiffOn_id) (Subset.refl _)
  have hcomp := (ContinuousLinearMap.inr ℝ ℝ ESpace).iteratedFDerivWithin_comp_right
    hsmooth hσuniq hpreuniq hmap (show n ≤ ∞ from mod_cast le_top)
  have hfun : (((fun z : ℝ × ESpace => u z) ∘ fun z => a + z) ∘
      ⇑(ContinuousLinearMap.inr ℝ ℝ ESpace)) = (fun w : ESpace => u (t, w)) := by
    funext w
    simp [Function.comp_apply, hadef, ContinuousLinearMap.inr_apply, Prod.mk_add_mk]
  have hshift : iteratedFDerivWithin ℝ n ((fun z : ℝ × ESpace => u z) ∘ fun z => a + z) σ
      (ContinuousLinearMap.inr ℝ ℝ ESpace y) =
      iteratedFDerivWithin ℝ n (fun z : ℝ × ESpace => u z) (a +ᵥ σ)
        (a + ContinuousLinearMap.inr ℝ ℝ ESpace y) := by
    have h := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ)
      (f := fun z : ℝ × ESpace => u z) (s := σ) n a
      (ContinuousLinearMap.inr ℝ ℝ ESpace y)
    simpa [Function.comp_def] using h
  have hσs : a +ᵥ σ = preSingularDomain := by
    rw [hσdef]
    ext z
    constructor
    · intro hz
      rcases Set.mem_vadd_set.mp hz with ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      apply Set.mem_vadd_set.mpr
      exact ⟨z - a, by simpa using hz, by simp [vadd_eq_add]⟩
  have hpoint : a + ContinuousLinearMap.inr ℝ ℝ ESpace y = (t, y) := by
    rw [hadef, ContinuousLinearMap.inr_apply, Prod.mk_add_mk]
    simp
  rw [hpre, iteratedFDerivWithin_univ, hfun, hshift, hσs, hpoint] at hcomp
  convert hcomp using 3

theorem fderiv_uncurry_eq {u : EVelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x : Navier.Space) :
    fderiv ℝ (uncurry u t) x =
      toPiCLM ∘L (fderiv ℝ (fun y : ESpace => u (t, y)) (⇑fromPiCLM x)) ∘L fromPiCLM := by
  have hd : DifferentiableAt ℝ (fun y : ESpace => u (t, y)) (⇑fromPiCLM x) :=
    (slice_contDiff hu ht).contDiffAt.differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun y : ESpace => u (t, y))
      (fderiv ℝ (fun y : ESpace => u (t, y)) (⇑fromPiCLM x)) (⇑fromPiCLM x) :=
    hd.hasFDerivAt
  have h2 : HasFDerivAt (fun z : Navier.Space => u (t, ⇑fromPiCLM z))
      (fderiv ℝ (fun y : ESpace => u (t, y)) (⇑fromPiCLM x) ∘L fromPiCLM) x :=
    h1.comp x fromPiCLM.hasFDerivAt
  have h3 : HasFDerivAt (uncurry u t)
      (toPiCLM ∘L (fderiv ℝ (fun y : ESpace => u (t, y)) (⇑fromPiCLM x) ∘L fromPiCLM)) x :=
    toPiCLM.hasFDerivAt.comp x h2
  exact h3.fderiv

theorem fderiv_slice_eq_within {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (y : ESpace) (w : ESpace) :
    fderiv ℝ (fun z : ESpace => u (t, z)) y w =
      (iteratedFDerivWithin ℝ 1 u preSingularDomain (t, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ ESpace) (fun _ : Fin 1 => w) := by
  have h := DFunLike.congr_fun (xfer hu 1 ht y) (fun _ : Fin 1 => w)
  simpa using h

theorem vorticity_eq_expr {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (x : Navier.Space) :
    vorticity (uncurry u) t x =
      ∑ i : Fin 3, basisVector i ⨯₃
        (toPiCLM ((iteratedFDerivWithin ℝ 1 u preSingularDomain
          (t, ⇑fromPiCLM x)).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inr ℝ ℝ ESpace)
            (fun _ : Fin 1 => coordinateVector i))) := by
  simp only [vorticity, staticCurl]
  refine Finset.sum_congr rfl fun i _ => ?_
  show basisVector i ⨯₃ fderiv ℝ (uncurry u t) x (basisVector i) = _
  rw [fderiv_uncurry_eq hu ht x, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, fromPiCLM_basis,
    ← fderiv_slice_eq_within hu ht (⇑fromPiCLM x) (coordinateVector i)]

theorem expr_continuousOn {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) :
    ContinuousOn (fun p : ℝ × Navier.Space =>
        (iteratedFDerivWithin ℝ 1 u preSingularDomain
          (p.1, ⇑fromPiCLM p.2)).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inr ℝ ℝ ESpace))
      (Ico (0 : ℝ) 1 ×ˢ univ) := by
  have h0 : ContinuousOn (iteratedFDerivWithin ℝ 1 u preSingularDomain)
      preSingularDomain :=
    hu.continuousOn_iteratedFDerivWithin
      (show (1 : ℕ) ≤ ∞ from mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
      ((uniqueDiffOn_Ico _ _).prod uniqueDiffOn_univ)
  have h1 : ContinuousOn (fun z : ℝ × ESpace =>
      (iteratedFDerivWithin ℝ 1 u preSingularDomain z).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ ESpace)) preSingularDomain :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => ContinuousLinearMap.inr ℝ ℝ ESpace)).continuous.comp_continuousOn h0
  refine h1.comp
    (ContinuousOn.prodMk (f := fun p : ℝ × Navier.Space => p.1)
      (g := fun p : ℝ × Navier.Space => ⇑fromPiCLM p.2)
      continuous_fst.continuousOn
      (fromPiCLM.continuous.comp continuous_snd).continuousOn)
    fun p hp => ⟨hp.1, trivial⟩

/-! ## 3. The vorticity sup profile `V`. -/

/-- The peak vorticity profile of the problem-carrier field: the spatial
supremum of the official Euclidean vorticity norm. This is the exact
pointwise quantity the `BKMControl.rate_dominates_vorticity` field consumes. -/
def V (u : EVelocityField) (t : ℝ) : ℝ :=
  ⨆ x : Navier.Space, officialEuclideanNorm (vorticity (uncurry u) t x)

theorem vort_zero_outside_support {u : EVelocityField} {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) {x : Navier.Space}
    (hx : x ∉ ⇑toPiCLM '' K) : vorticity (uncurry u) t x = 0 := by
  classical
  have hxK : ⇑fromPiCLM x ∉ K := by
    intro hK'
    exact hx ⟨_, hK', rfl⟩
  have heq : uncurry u t =ᶠ[𝓝 x] (fun _ : Navier.Space => (0 : Navier.Space)) := by
    have hopen : {x : Navier.Space | ⇑fromPiCLM x ∉ K} ∈ 𝓝 x :=
      ((hK.isClosed.preimage fromPiCLM.continuous).isOpen_compl.mem_nhds hxK)
    filter_upwards [hopen] with y hy
    exact congrArg (fun v : ESpace => (v : Navier.Space)) (hsupp t ht _ hy)
  have hhas :
      HasFDerivAt (uncurry u t) (0 : Navier.Space →L[ℝ] Navier.Space) x :=
    (hasFDerivAt_const (0 : Navier.Space) x).congr_of_eventuallyEq heq
  have hf : fderiv ℝ (uncurry u t) x = 0 := hhas.fderiv
  simp only [vorticity, staticCurl]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hf]
  simp

theorem omega_zero_outside {u : EVelocityField} {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) {x : Navier.Space}
    (hx : x ∉ ⇑toPiCLM '' K) :
    officialEuclideanNorm (vorticity (uncurry u) t x) = 0 := by
  rw [vort_zero_outside_support hK hsupp ht hx]
  exact officialEuclideanNorm_zero

theorem omega_continuousOn {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) :
    ContinuousOn (fun p : ℝ × Navier.Space => vorticity (uncurry u) p.1 p.2)
      (Ico (0 : ℝ) 1 ×ˢ univ) := by
  refine ContinuousOn.congr ?_ fun p hp => vorticity_eq_expr hu hp.1 p.2
  refine continuousOn_finsetSum (f := fun i : Fin 3 => fun p : ℝ × Navier.Space =>
      basisVector i ⨯₃ (toPiCLM ((iteratedFDerivWithin ℝ 1 u preSingularDomain
        (p.1, ⇑fromPiCLM p.2)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ ESpace)
          (fun _ : Fin 1 => coordinateVector i)))) Finset.univ fun i _ => ?_
  have hslot : ContinuousOn (fun p : ℝ × Navier.Space =>
      (iteratedFDerivWithin ℝ 1 u preSingularDomain
        (p.1, ⇑fromPiCLM p.2)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ ESpace)
          (fun _ : Fin 1 => coordinateVector i)) (Ico (0 : ℝ) 1 ×ˢ univ) :=
    ContinuousOn.comp'
      (g := fun q : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => ESpace) ESpace =>
        q (fun _ : Fin 1 => coordinateVector i))
      (f := fun p : ℝ × Navier.Space => (iteratedFDerivWithin ℝ 1 u preSingularDomain
        (p.1, ⇑fromPiCLM p.2)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ ESpace))
      (show ContinuousOn
          (fun q : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => ESpace) ESpace =>
            q (fun _ : Fin 1 => coordinateVector i))
          (univ : Set (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => ESpace) ESpace)) from
        (ContinuousMultilinearMap.uniformContinuous_eval_const
          (x := (fun _ : Fin 1 => coordinateVector i))).continuous.continuousOn)
      (expr_continuousOn hu) fun _ _ => trivial
  have h2 : ContinuousOn (fun p : ℝ × Navier.Space =>
      toPiCLM ((iteratedFDerivWithin ℝ 1 u preSingularDomain
        (p.1, ⇑fromPiCLM p.2)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ ESpace)
          (fun _ : Fin 1 => coordinateVector i)))
      (Ico (0 : ℝ) 1 ×ˢ univ) :=
    ContinuousOn.comp' (g := fun q : ESpace => toPiCLM q)
      (show ContinuousOn (fun q : ESpace => toPiCLM q) (univ : Set ESpace) from
        toPiCLM.continuous.continuousOn)
      hslot fun _ _ => trivial
  refine ContinuousOn.comp' (g := fun v : Navier.Space => basisVector i ⨯₃ v)
    (show ContinuousOn (fun v : Navier.Space => basisVector i ⨯₃ v)
        (univ : Set Navier.Space) from
      (crossProduct (basisVector i)).toContinuousLinearMap.continuous.continuousOn)
    h2 fun _ _ => trivial

theorem omega_norm_continuousOn {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) :
    ContinuousOn (fun p : ℝ × Navier.Space =>
        officialEuclideanNorm (vorticity (uncurry u) p.1 p.2))
      (Ico (0 : ℝ) 1 ×ˢ univ) := by
  have hnorm : Continuous officialEuclideanNorm :=
    continuous_norm.comp (show Continuous officialEuclideanPoint from fromPiCLM.continuous)
  exact ContinuousOn.comp' (g := fun p : Navier.Space => officialEuclideanNorm p)
    (show ContinuousOn (fun p : Navier.Space => officialEuclideanNorm p)
      (univ : Set Navier.Space) from hnorm.continuousOn)
    (omega_continuousOn hu) fun _ _ => trivial

theorem vort_norm_bddAbove {u : EVelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    BddAbove (Set.range fun x : Navier.Space =>
      officialEuclideanNorm (vorticity (uncurry u) t x)) := by
  have hc : ContinuousOn (fun x : Navier.Space =>
      officialEuclideanNorm (vorticity (uncurry u) t x)) (⇑toPiCLM '' K) :=
    (ContinuousOn.comp' (g := fun p : ℝ × Navier.Space =>
        officialEuclideanNorm (vorticity (uncurry u) p.1 p.2))
      (f := fun x : Navier.Space => (t, x)) (omega_norm_continuousOn hu)
      (show ContinuousOn (fun x : Navier.Space => (t, x)) (univ : Set Navier.Space) from
        (continuous_const.prodMk continuous_id).continuousOn)
      fun _ _ => ⟨ht, trivial⟩)
      |>.mono (Set.subset_univ _)
  obtain ⟨M, hM⟩ := (hK.image toPiCLM.continuous).exists_bound_of_continuousOn hc
  exact ⟨max M 0, fun y hy => by
    rcases hy with ⟨x, rfl⟩
    show officialEuclideanNorm (vorticity (uncurry u) t x) ≤ max M 0
    by_cases hx : x ∈ ⇑toPiCLM '' K
    · exact (le_trans (le_abs_self _) (hM x hx)).trans (le_max_left _ _)
    · rw [omega_zero_outside hK hsupp ht hx]
      exact le_max_right _ _⟩

theorem V_nonneg {u : EVelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : 0 ≤ V u t :=
  le_trans (officialEuclideanNorm_nonneg _)
    (le_ciSup (vort_norm_bddAbove hu hK hsupp ht) (0 : Navier.Space))

theorem vort_le_V {u : EVelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x : Navier.Space) :
    officialEuclideanNorm (vorticity (uncurry u) t x) ≤ V u t :=
  le_ciSup (vort_norm_bddAbove hu hK hsupp ht) x

theorem V_continuousOn {u : EVelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0) :
    ContinuousOn (V u) (Ico (0 : ℝ) 1) := by
  classical
  have hL : IsCompact (⇑toPiCLM '' K) := hK.image toPiCLM.continuous
  have hF := omega_norm_continuousOn hu
  by_cases hLe : (⇑toPiCLM '' K) = ∅
  · refine ContinuousOn.congr (continuousOn_const (c := (0 : ℝ))) fun t ht => ?_
    refine le_antisymm (ciSup_le fun x => ?_) (V_nonneg hu hK hsupp ht)
    rw [omega_zero_outside hK hsupp ht (by rw [hLe]; exact fun h => h)]
  · refine fun t₀ ht₀ => ?_
    show Tendsto (V u) (𝓝[Ico (0 : ℝ) 1] t₀) (𝓝 (V u t₀))
    refine Metric.tendsto_nhdsWithin_nhds.mpr ?_
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    set b := (t₀ + 1) / 2 with hb
    have hb₀ : t₀ ≤ b := by rw [hb]; linarith [ht₀.2]
    have hb₁ : b < 1 := by rw [hb]; linarith [ht₀.2]
    have hG : ContinuousOn (fun p : ℝ × Navier.Space =>
        officialEuclideanNorm (vorticity (uncurry u) p.1 p.2))
        ((Icc (0 : ℝ) b) ×ˢ (⇑toPiCLM '' K)) := by
      refine hF.mono ?_
      rintro ⟨s, x⟩ ⟨⟨hs0, hsb⟩, hx⟩
      exact ⟨⟨hs0, lt_of_le_of_lt hsb hb₁⟩, trivial⟩
    obtain ⟨δ', hδ'0, hδ'⟩ := (Metric.uniformContinuousOn_iff).mp
      ((isCompact_Icc.prod hL).uniformContinuousOn_of_continuous hG) (ε / 2) hε2
    refine ⟨min δ' (b - t₀), lt_min hδ'0 (by rw [hb]; linarith [ht₀.2]),
      fun t ht hdt => ?_⟩
    have hdist : dist t t₀ < δ' := lt_of_lt_of_le hdt (min_le_left _ _)
    have hdt' : |t - t₀| < min δ' (b - t₀) := by rw [← Real.dist_eq]; exact hdt
    obtain ⟨_, upper⟩ := abs_lt.mp hdt'
    have hmin : min δ' (b - t₀) ≤ b - t₀ := min_le_right δ' (b - t₀)
    have htIcc : t ∈ Icc (0 : ℝ) b := ⟨ht.1, by linarith [upper, hmin]⟩
    have hVA : V u t ≤ V u t₀ + ε / 2 := by
      refine ciSup_le fun x => ?_
      by_cases hx : x ∈ ⇑toPiCLM '' K
      · have hlt := hδ' (t, x) ⟨htIcc, hx⟩ (t₀, x) ⟨⟨ht₀.1, hb₀⟩, hx⟩
          (by rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hdist)
        dsimp only at hlt
        rw [Real.dist_eq] at hlt
        obtain ⟨p2, _⟩ := abs_lt.mp hlt
        linarith [p2, vort_le_V hu hK hsupp ht₀ x]
      · rw [omega_zero_outside hK hsupp ht hx]
        linarith [V_nonneg hu hK hsupp ht₀]
    have hVB : V u t₀ ≤ V u t + ε / 2 := by
      refine ciSup_le fun x => ?_
      by_cases hx : x ∈ ⇑toPiCLM '' K
      · have hlt := hδ' (t₀, x) ⟨⟨ht₀.1, hb₀⟩, hx⟩ (t, x) ⟨htIcc, hx⟩
          (by rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_comm]; exact hdist)
        dsimp only at hlt
        rw [Real.dist_eq] at hlt
        obtain ⟨p2, _⟩ := abs_lt.mp hlt
        linarith [p2, vort_le_V hu hK hsupp ht x]
      · rw [omega_zero_outside hK hsupp ht₀ hx]
        linarith [V_nonneg hu hK hsupp ht]
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

/-! ## 4. The crown. -/

/-- Every positive `C¹` Sobolev–Grönwall control pair dominating the selected
profile's velocity and vorticity yields a full `BKMControl` structure. This is
the exact hypothesis bundle the BKM criterion consumes; constructing `Y` and
`Y'` is the named missing primitive. -/
private theorem bkmControl_of_control {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : ESpace, spatialDivergence u t x = 0)
    {Y Y' : ℝ → ℝ}
    (hYcont : ContinuousOn Y (Ico (0 : ℝ) 1))
    (hYder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Y (Y' t) t)
    (hYpos : ∀ t ∈ Ico (0 : ℝ) 1, 0 < Y t)
    (hYgron : ∀ t ∈ Ioo (0 : ℝ) 1, Y' t ≤ V u t * Y t)
    (hYdom : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Navier.Space, ‖uncurry u t x‖ ≤ Y t)
    (B : ℝ) (hB : ∀ t ∈ Ico (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, V u s ≤ B) :
    Nonempty (BKMControl (uncurry u) 1) :=
  ⟨{ control := Y, controlDeriv := Y', rate := V u,
     rate_continuousOn := V_continuousOn hu hK hsupp,
     control_continuousOn := hYcont,
     control_hasDerivAt := hYder,
     control_pos := hYpos,
     gronwall_inequality := hYgron,
     velocity_differentiable :=
       fun t ht => (uncurry_slice_contDiff hu ht).differentiable (by norm_num),
     incompressible := fun t ht x => by
       rw [staticDivergence_uncurry_slice hu ht x]; exact hdiv t ht _,
     rate_dominates_vorticity := fun t ht x => vort_le_V hu hK hsupp ht x,
     control_dominates_velocity := hYdom,
     finite_vorticity_integral := ⟨B, hB⟩ }⟩

/-- Residual primitive consumed here: a positive continuous control `Y`
with derivative `Y'` satisfying the Grönwall differential inequality
`Y' ≤ V · Y` and dominating the velocity pointwise. The anchor
`selected_candidate_forces_no_BKM_control_in_every_smooth_competitor` forces
every smooth competitor of the selected profile to be speed-unbounded at time
one, and `not_bkmControl_of_speedUnboundedAtOne` refutes the control bundle.
Hence the vorticity integral `∫₀¹ V u` admits no finite bound. -/
theorem vorticity_integral_divergence {u p f : _} (h : Properties u p f)
    {Y Y' : ℝ → ℝ}
    (hYcont : ContinuousOn Y (Ico (0 : ℝ) 1))
    (hYder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Y (Y' t) t)
    (hYpos : ∀ t ∈ Ico (0 : ℝ) 1, 0 < Y t)
    (hYgron : ∀ t ∈ Ioo (0 : ℝ) 1, Y' t ≤ V u t * Y t)
    (hYdom : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Navier.Space, ‖uncurry u t x‖ ≤ Y t) :
    ¬ ∃ B : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, V u s ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  exact not_bkmControl_of_speedUnboundedAtOne h.speed_unbounded
    (bkmControl_of_control h.velocity_smooth hK hsupp
      (fun t ht => h.divergence_free t ht)
      hYcont hYder hYpos hYgron hYdom B hB)

/-- The constructed vorticity-integral divergence: for the selected profile,
with the Grönwall control pair supplied, `∫⁻ t in Icc 0 1, ofReal (V u t) = ⊤`,
i.e. `∫₀¹ ‖ω(t)‖∞ dt = ∞` in the repo's official-carrier formulation. -/
theorem lintegral_vorticity_integral_divergence {u p f : _} (h : Properties u p f)
    {Y Y' : ℝ → ℝ}
    (hYcont : ContinuousOn Y (Ico (0 : ℝ) 1))
    (hYder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Y (Y' t) t)
    (hYpos : ∀ t ∈ Ico (0 : ℝ) 1, 0 < Y t)
    (hYgron : ∀ t ∈ Ioo (0 : ℝ) 1, Y' t ≤ V u t * Y t)
    (hYdom : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Navier.Space, ‖uncurry u t x‖ ≤ Y t) :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (V u t) = ⊤ := by
  by_contra hne
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  have hV := V_continuousOn h.velocity_smooth hK hsupp
  set L := ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (V u t)
  have hltL : L < ENNReal.ofReal (L.toReal + 1) := by
    have h1 : ENNReal.ofReal L.toReal < ENNReal.ofReal (L.toReal + 1) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr
        (lt_add_one L.toReal)
    rwa [ENNReal.ofReal_toReal hne] at h1
  refine vorticity_integral_divergence h hYcont hYder hYpos hYgron hYdom
    ⟨L.toReal + 1, fun t ht => ?_⟩
  refine le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (intervalIntegral.integral_nonneg ht.1 (fun s hs =>
        V_nonneg h.velocity_smooth hK hsupp
          ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩))).mp ?_)
  have hVsub : ContinuousOn (V u) (Icc (0 : ℝ) t) :=
    hV.mono (fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩)
  calc ENNReal.ofReal (∫ s in (0 : ℝ)..t, V u s)
      = ENNReal.ofReal (∫ s in Ioc (0 : ℝ) t, V u s) := by
          rw [intervalIntegral.integral_of_le ht.1]
    _ = ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (V u s) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp
              (ContinuousOn.intervalIntegrable_of_Icc ht.1 hVsub))
            (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs; exact V_nonneg h.velocity_smooth hK hsupp ⟨hs.1.le, lt_of_le_of_lt hs.2 ht.2⟩)
    _ ≤ L := MeasureTheory.lintegral_mono_set
          (fun _ hs => ⟨hs.1.le, (lt_of_le_of_lt hs.2 ht.2).le⟩)
    _ < ENNReal.ofReal (L.toReal + 1) := hltL

/-- The pointwise tie between the profile `V` and the estate's own critical
quantity `vorticityRate` (Apriori). The sup is attained on the compact support
slice, so `ENNReal.ofReal` commutes with it. -/
theorem ofReal_V_eq_vorticityRate {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ENNReal.ofReal (V u t) = vorticityRate (uncurry u) t := by
  classical
  by_cases hLe : (⇑toPiCLM '' K) = ∅
  · have hz : V u t = 0 :=
      le_antisymm (ciSup_le fun x => by
        rw [omega_zero_outside hK hsupp ht (by rw [hLe]; exact fun h => h)])
        (V_nonneg hu hK hsupp ht)
    have hzr : vorticityRate (uncurry u) t = 0 :=
      le_antisymm (iSup_le fun x => by
        rw [vort_zero_outside_support hK hsupp ht
            (by rw [hLe]; exact fun h => h),
          officialEuclideanNorm_zero, ENNReal.ofReal_zero])
        bot_le
    rw [hz, ENNReal.ofReal_zero, hzr]
  · have hL : IsCompact (⇑toPiCLM '' K) := hK.image toPiCLM.continuous
    have hc : ContinuousOn (fun x : Navier.Space =>
        officialEuclideanNorm (vorticity (uncurry u) t x)) (⇑toPiCLM '' K) :=
      (ContinuousOn.comp' (g := fun p : ℝ × Navier.Space =>
          officialEuclideanNorm (vorticity (uncurry u) p.1 p.2))
        (f := fun x : Navier.Space => (t, x)) (omega_norm_continuousOn hu)
        (show ContinuousOn (fun x : Navier.Space => (t, x)) (univ : Set Navier.Space) from
          (continuous_const.prodMk continuous_id).continuousOn)
        fun _ _ => ⟨ht, trivial⟩)
        |>.mono (Set.subset_univ _)
    obtain ⟨z, _, hmax⟩ := hL.exists_isMaxOn (Set.nonempty_iff_ne_empty.mpr hLe) hc
    have hbdd := vort_norm_bddAbove hu hK hsupp ht
    have hVz : V u t = officialEuclideanNorm (vorticity (uncurry u) t z) := by
      refine le_antisymm (ciSup_le fun x => ?_) (le_ciSup hbdd z)
      by_cases hx : x ∈ ⇑toPiCLM '' K
      · exact isMaxOn_iff.mp hmax x hx
      · rw [omega_zero_outside hK hsupp ht hx]
        exact officialEuclideanNorm_nonneg _
    refine (congrArg ENNReal.ofReal hVz).trans ?_
    refine le_antisymm
      (le_iSup (f := fun x => ENNReal.ofReal (officialEuclideanNorm
          (vorticity (uncurry u) t x))) z) ?_
    refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    rw [← hVz]
    exact vort_le_V hu hK hsupp ht x

/-- The BKM-critical-quantity divergence of the selected profile:
`⊤ ≤ bkmVorticityControl 1 (uncurry u)`. A finite value of the BKM vorticity
control would bound every truncated vorticity integral, contradicting the
crown theorem applied to the speed-unbounded competitor. -/
theorem bkmVorticityControl_eq_top {u p f : _} (h : Properties u p f)
    {Y Y' : ℝ → ℝ}
    (hYcont : ContinuousOn Y (Ico (0 : ℝ) 1))
    (hYder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Y (Y' t) t)
    (hYpos : ∀ t ∈ Ico (0 : ℝ) 1, 0 < Y t)
    (hYgron : ∀ t ∈ Ioo (0 : ℝ) 1, Y' t ≤ V u t * Y t)
    (hYdom : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Navier.Space, ‖uncurry u t x‖ ≤ Y t) :
    ⊤ ≤ bkmVorticityControl 1 (uncurry u) := by
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  set C : ENNReal := bkmVorticityControl 1 (uncurry u) with hCdef
  by_cases hbt : C = ⊤
  · exact hbt.symm.le
  · refine absurd (Exists.intro (C.toReal + 1) fun t ht => ?_)
      (vorticity_integral_divergence h hYcont hYder hYpos hYgron hYdom)
    refine le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (intervalIntegral.integral_nonneg ht.1 (fun s hs =>
          V_nonneg h.velocity_smooth hK hsupp
            ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩))).mp ?_)
    have hVsub : ContinuousOn (V u) (Icc (0 : ℝ) t) :=
      (V_continuousOn h.velocity_smooth hK hsupp).mono
        (fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩)
    calc ENNReal.ofReal (∫ s in (0 : ℝ)..t, V u s)
        = ENNReal.ofReal (∫ s in Ioc (0 : ℝ) t, V u s) := by
            rw [intervalIntegral.integral_of_le ht.1]
      _ = ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (V u s) :=
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp
                (ContinuousOn.intervalIntegrable_of_Icc ht.1 hVsub))
              (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs; exact V_nonneg h.velocity_smooth hK hsupp ⟨hs.1.le, lt_of_le_of_lt hs.2 ht.2⟩)
      _ = ∫⁻ s in Ioc (0 : ℝ) t, vorticityRate (uncurry u) s :=
            MeasureTheory.lintegral_congr_ae (Set.EqOn.aeEq_restrict
              (fun s hs => ofReal_V_eq_vorticityRate h.velocity_smooth hK hsupp
                ⟨hs.1.le, lt_of_le_of_lt hs.2 ht.2⟩)
              measurableSet_Ioc)
      _ ≤ ∫⁻ s in Icc (0 : ℝ) t, vorticityRate (uncurry u) s :=
            MeasureTheory.lintegral_mono_set (fun _ hs => ⟨hs.1.le, hs.2⟩)
      _ ≤ C := by
            rw [show C = ⨆ s ∈ Ico (0 : ℝ) 1,
                ∫⁻ t in Icc (0 : ℝ) s, vorticityRate (uncurry u) t from hCdef]
            exact le_iSup₂ (f := fun s _ => ∫⁻ t in Icc (0 : ℝ) s,
              vorticityRate (uncurry u) t) t ht
      _ = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hbt).symm
      _ < ENNReal.ofReal (C.toReal + 1) :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr
              (lt_add_one C.toReal)

/-! ## 5. Sandwich against the problem-carrier sup norm (row wording `‖ω(t)‖∞`). -/

/-- The vorticity sup profile in the problem-carrier norm itself. -/
def Vpi (u : EVelocityField) (t : ℝ) : ℝ :=
  ⨆ x : Navier.Space, ‖vorticity (uncurry u) t x‖

theorem Vpi_le_V {u : EVelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : Vpi u t ≤ V u t :=
  ciSup_le fun x => le_trans (norm_le_officialEuclideanNorm (vorticity (uncurry u) t x))
    (vort_le_V hu hK hsupp ht x)

theorem V_le_sqrt3_Vpi {u : EVelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : V u t ≤ Real.sqrt 3 * Vpi u t := by
  have hb : BddAbove (Set.range fun x : Navier.Space => ‖vorticity (uncurry u) t x‖) :=
    ⟨V u t, fun y hy => by
      rcases hy with ⟨x, rfl⟩
      exact le_trans (norm_le_officialEuclideanNorm (vorticity (uncurry u) t x))
        (vort_le_V hu hK hsupp ht x)⟩
  refine ciSup_le fun x => le_trans
    (officialEuclideanNorm_le (vorticity (uncurry u) t x))
    (mul_le_mul_of_nonneg_left (le_ciSup hb x) (Real.sqrt_nonneg 3))

end Navier.Analysis.BKMVorticityIntegralDivergence

#check @Navier.Analysis.BKMVorticityIntegralDivergence.slice_contDiff
#check @Navier.Analysis.BKMVorticityIntegralDivergence.uncurry_slice_contDiff
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.uncurry_slice_contDiff
#check @Navier.Analysis.BKMVorticityIntegralDivergence.fderiv_uncurry_basis
#check @Navier.Analysis.BKMVorticityIntegralDivergence.staticDivergence_uncurry_slice
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.staticDivergence_uncurry_slice
#check @Navier.Analysis.BKMVorticityIntegralDivergence.xfer
#check @Navier.Analysis.BKMVorticityIntegralDivergence.fderiv_uncurry_eq
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.fderiv_uncurry_eq
#check @Navier.Analysis.BKMVorticityIntegralDivergence.fderiv_slice_eq_within
#check @Navier.Analysis.BKMVorticityIntegralDivergence.vorticity_eq_expr
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.vorticity_eq_expr
#check @Navier.Analysis.BKMVorticityIntegralDivergence.expr_continuousOn
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.expr_continuousOn
#check @Navier.Analysis.BKMVorticityIntegralDivergence.omega_zero_outside
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.omega_zero_outside
#check @Navier.Analysis.BKMVorticityIntegralDivergence.omega_norm_continuousOn
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.omega_norm_continuousOn
#check @Navier.Analysis.BKMVorticityIntegralDivergence.V_nonneg
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.V_nonneg
#check @Navier.Analysis.BKMVorticityIntegralDivergence.vort_le_V
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.vort_le_V

#check @Navier.Analysis.BKMVorticityIntegralDivergence.V
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.V
#check @Navier.Analysis.BKMVorticityIntegralDivergence.vort_zero_outside_support
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.vort_zero_outside_support
#check @Navier.Analysis.BKMVorticityIntegralDivergence.omega_continuousOn
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.omega_continuousOn
#check @Navier.Analysis.BKMVorticityIntegralDivergence.vort_norm_bddAbove
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.vort_norm_bddAbove
#check @Navier.Analysis.BKMVorticityIntegralDivergence.V_continuousOn
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.V_continuousOn
#check @Navier.Analysis.BKMVorticityIntegralDivergence.vorticity_integral_divergence
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.vorticity_integral_divergence
#check @Navier.Analysis.BKMVorticityIntegralDivergence.lintegral_vorticity_integral_divergence
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.lintegral_vorticity_integral_divergence
#check @Navier.Analysis.BKMVorticityIntegralDivergence.ofReal_V_eq_vorticityRate
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.ofReal_V_eq_vorticityRate
#check @Navier.Analysis.BKMVorticityIntegralDivergence.bkmVorticityControl_eq_top
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.bkmVorticityControl_eq_top
#check @Navier.Analysis.BKMVorticityIntegralDivergence.Vpi
#check @Navier.Analysis.BKMVorticityIntegralDivergence.Vpi_le_V
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.Vpi_le_V
#check @Navier.Analysis.BKMVorticityIntegralDivergence.V_le_sqrt3_Vpi
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.V_le_sqrt3_Vpi
