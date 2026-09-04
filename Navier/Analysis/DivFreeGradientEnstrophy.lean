import Navier.Analysis.CurlIdentities
import Navier.Analysis.EnergyNormBridge
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The divergence-free gradient–enstrophy identity (Plancherel route)

For a Schwartz velocity field `u : SchwartzVelocity` on `Space = ℝ³`,

```
∑ i, ∫ x, ‖∂ᵢu(x)‖²  =  ∫ x, ‖curl u(x)‖²  +  ∫ x, (div u(x))²
```

with every norm the official Euclidean (`ℓ²`) norm on coordinates.  For a
**divergence-free** field the last term vanishes and the full Dirichlet
energy equals the enstrophy.  This is the bridge the Galerkin compactness
assembly needs: the banked `UniformEnstrophyBound` budgets the curl, while
`LerayWeak.spaceEquicontinuous_of_dissipation_bound` consumes a bound on the
full Fréchet derivative.

## Proof route (Fourier side)

On the complexified Euclidean model `v = euclModel u` (banked in
`BKMLogBootstrap`), Plancherel plus the symbol of a line derivative
(`SchwartzMap.fourier_lineDerivOp_eq`) turn both sides into weighted `L²`
integrals of the Fourier transform:

* `∑ i ∫ ‖∂_{eᵢ} v‖² = 4π² ∫ ‖ξ‖² ‖û‖²`,
* each curl component `∂ᵢuⱼ − ∂ⱼuᵢ` has symbol `2πi (ξᵢ ûⱼ − ξⱼ ûᵢ)`, and the
  three of them sum, by the Lagrange identity, to
  `4π² (‖ξ‖² ‖û‖² − |Σᵢ ξᵢ ûᵢ|²)`,
* the divergence has symbol `2πi Σᵢ ξᵢ ûᵢ`.

So the identity is exactly `|ξ × û|² = ‖ξ‖²‖û‖² − |ξ·û|²` integrated against
`4π² dξ`.  The Fourier/Plancherel plumbing lemmas are re-derived here from
mathlib (they exist as `private` lemmas inside `BKMLogBootstrap`, whose
ownership sits with another lane; duplicating ~80 lines keeps this file
collision-free).

## Contents

* `norm_realToCx`, `euclCoords_single` — norm/coordinate bridges between
  `Space` and the Euclidean model.
* `euclModel_lineDeriv_apply` — the model line derivative is the
  complexified Fréchet derivative in a coordinate direction.
* `divModel`, `curlComponent` — the divergence and the three curl components
  as genuine Schwartz maps, with pointwise and Fourier-symbol lemmas.
* `lagrange_sq` — the complex Lagrange identity
  `Σ |ξᵢwⱼ − ξⱼwᵢ|² = ‖ξ‖²‖w‖² − |Σ ξᵢwᵢ|²`.
* `sum_integral_fderiv_sq_eq_curl_sq_add_div_sq` — the master identity.
* `integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree` — the
  `‖fderiv‖² ≤ 3·Σ‖∂ᵢ‖²` operator-norm bound chained with the master
  identity, the exact form `spaceEquicontinuous_of_dissipation_bound`
  consumes through the enstrophy budget.

## Axiom policy

Everything is proved from mathlib Plancherel (`SchwartzMap.integral_norm_sq_fourier`)
and the banked model bridges; the audit target is
`{propext, Classical.choice, Quot.sound}` only.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped FourierTransform LineDeriv

namespace Navier.Analysis.DivFreeGradientEnstrophy

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.EnergyNormBridge

/-!
## The Euclidean/complex model bridges (self-contained copies)

These are the bridge definitions that this file previously consumed from
`BKMLogBootstrap` (`BealeKatoMajda.EuclSpace`/`euclModel`/...).  They are
inlined here verbatim to decouple this file's build from that module; the
copies are definitionally identical to the banked ones.
-/

/-- The Euclidean (ℓ²) model of `Space`, on the same carrier `Fin 3 → ℝ`. -/
abbrev EuclSpace := EuclideanSpace ℝ (Fin 3)

/-- The complex Euclidean codomain, needed because Mathlib's Fourier transform
takes values in a `ℂ`-normed space. -/
abbrev CxSpace := EuclideanSpace ℂ (Fin 3)

/-- The coordinate identification `EuclideanSpace ℝ (Fin 3) ≃L[ℝ] Space`.  It is the
identity on carriers and changes only the norm. -/
def euclCoords : EuclSpace ≃L[ℝ] Space := EuclideanSpace.equiv (Fin 3) ℝ

/-- Componentwise inclusion `ℝ³ ↪ ℂ³`, landing in the complex Euclidean space. -/
def realToCx : Space →L[ℝ] CxSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => (WithLp.toLp 2 (fun i => ((a i : ℂ))) : CxSpace)
      map_add' := by intro a b; ext i; simp
      map_smul' := by intro c a; ext i; simp }

@[simp] theorem realToCx_apply (a : Space) (i : Fin 3) : realToCx a i = (a i : ℂ) := by
  simp [realToCx]

/-- The Euclidean/complex model of a Schwartz velocity field: precompose with the
coordinate identification (`compCLMOfContinuousLinearEquiv`) and postcompose with the
componentwise complexification (`postcompCLM`). -/
def euclModel (u : SchwartzVelocity) : SchwartzMap EuclSpace CxSpace :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) realToCx
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ euclCoords u)

@[simp] theorem euclModel_apply (u : SchwartzVelocity) (y : EuclSpace) :
    euclModel u y = realToCx (u (euclCoords y)) := rfl

/-- **Volume transport between the two models.**  `Space` and `EuclSpace`
share a carrier and the coordinate map is volume preserving
(`PiLp.volume_preserving_ofLp`), so every Lebesgue integral transports
verbatim. -/
theorem integral_space_eq_euclSpace (f : Space → ℝ) :
    ∫ ξ : Space, f ξ = ∫ y : EuclSpace, f (euclCoords y) := by
  have hmp : MeasureTheory.MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ))
      (volume : Measure EuclSpace) (volume : Measure Space) :=
    PiLp.volume_preserving_ofLp (Fin 3)
  rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding]
  rfl

/-- Local alias for the complex-valued Schwartz maps on the Euclidean model. -/
private abbrev SV := SchwartzMap EuclSpace CxSpace

/-- The real standard basis vector of the Euclidean model. -/
private def e3 (i : Fin 3) : EuclSpace := EuclideanSpace.single i (1 : ℝ)

@[simp] private theorem norm_e3 (i : Fin 3) : ‖e3 i‖ = 1 := by
  simp [e3]

@[simp] private theorem inner_e3 (ξ : EuclSpace) (i : Fin 3) :
    (inner ℝ ξ (e3 i) : ℝ) = ξ i := by
  simp [e3, EuclideanSpace.inner_single_right]

private theorem sum_inner_e3_sq (ξ : EuclSpace) :
    ∑ i : Fin 3, (inner ℝ ξ (e3 i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := by
  simp only [inner_e3]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [sq_abs]

/-- The coordinate map sends the model basis to the `Space` basis. -/
theorem euclCoords_single (i : Fin 3) : euclCoords (e3 i) = basisVector i := by
  ext j
  show (e3 i : Fin 3 → ℝ) j = basisVector i j
  simp [e3, basisVector, Pi.single, Function.update]

/-- The complexification is norm-preserving onto the official Euclidean norm. -/
theorem norm_realToCx (a : Space) : ‖realToCx a‖ = officialEuclideanNorm a := by
  rw [officialEuclideanNorm, officialEuclideanPoint, EuclideanSpace.norm_eq,
    EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [realToCx_apply]
  simp [sq_abs]

@[simp] theorem norm_realToCx_sq (a : Space) :
    ‖realToCx a‖ ^ 2 = officialEuclideanNorm a ^ 2 := by
  rw [norm_realToCx]

/-- The model line derivative in a coordinate direction is the complexified
Fréchet derivative in the corresponding `Space` basis direction. -/
theorem euclModel_lineDeriv_apply (u : SchwartzVelocity) (i : Fin 3) (y : EuclSpace) :
    (∂_{e3 i} (euclModel u)) y = realToCx (fderiv ℝ u (euclCoords y) (basisVector i)) := by
  have hu : Differentiable ℝ (⇑u) := (u.smooth 1).differentiable (by norm_num)
  have hfun : (⇑(euclModel u) : EuclSpace → CxSpace) =
      fun z => realToCx (u (euclCoords z)) := funext fun z => euclModel_apply u z
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun]
  have h1 : HasFDerivAt (fun z => u (euclCoords z))
      ((fderiv ℝ u (euclCoords y)).comp
        ((euclCoords : EuclSpace ≃L[ℝ] Space) : EuclSpace →L[ℝ] Space)) y :=
    (hu (euclCoords y)).hasFDerivAt.comp y euclCoords.hasFDerivAt
  have h2 : HasFDerivAt (fun z => realToCx (u (euclCoords z)))
      (realToCx.comp ((fderiv ℝ u (euclCoords y)).comp
        ((euclCoords : EuclSpace ≃L[ℝ] Space) : EuclSpace →L[ℝ] Space))) y :=
    realToCx.hasFDerivAt.comp y h1
  rw [h2.fderiv]
  simp [euclCoords_single]

section IntegrabilityCopies

/-- Copied from `BKMLogBootstrap` (private there): polynomial-weight times
squared norm of a Schwartz map is integrable. -/
private theorem integrable_pow_mul_normSq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap EuclSpace F) (k : ℕ) :
    Integrable (fun ξ : EuclSpace => ‖ξ‖ ^ k * ‖f ξ‖ ^ 2) := by
  have hM : ∀ x, ‖f x‖ ≤ (SchwartzMap.seminorm ℝ 0 0) f := fun x => f.norm_le_seminorm ℝ x
  have hM0 : (0:ℝ) ≤ (SchwartzMap.seminorm ℝ 0 0) f := le_trans (norm_nonneg _) (hM 0)
  refine ((f.integrable_pow_mul volume k).const_mul ((SchwartzMap.seminorm ℝ 0 0) f)).mono'
    ((by fun_prop : Continuous fun ξ : EuclSpace => ‖ξ‖ ^ k * ‖f ξ‖ ^ 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : ‖ξ‖ ^ k * ‖f ξ‖ ^ 2 = (‖ξ‖ ^ k * ‖f ξ‖) * ‖f ξ‖ := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (hM ξ) (by positivity) |>.trans_eq (by ring)

/-- Copied from `BKMLogBootstrap` (private there): any continuous weight
dominated by `‖ξ‖ ^ k` times `‖f‖²` is integrable. -/
private theorem integrable_weight_mul_normSq (f : SV) (k : ℕ) (g : EuclSpace → ℝ)
    (hg : Continuous g) (hgb : ∀ ξ, |g ξ| ≤ ‖ξ‖ ^ k) :
    Integrable (fun ξ : EuclSpace => g ξ * ‖f ξ‖ ^ 2) := by
  refine (integrable_pow_mul_normSq f k).mono'
    ((by fun_prop : Continuous fun ξ : EuclSpace => g ξ * ‖f ξ‖ ^ 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖f ξ‖ ^ 2)]
  exact mul_le_mul_of_nonneg_right (hgb ξ) (by positivity)

/-- The squared norm of a Schwartz map is integrable. -/
private theorem integrable_normSq (f : SV) : Integrable (fun ξ => ‖f ξ‖ ^ 2) := by
  have h := integrable_pow_mul_normSq f 0
  simpa using h

/-- Scalar-ℂ Schwartz maps have integrable squared norm. -/
private theorem integrable_normSq_scalar (f : SchwartzMap EuclSpace ℂ) :
    Integrable (fun ξ => ‖f ξ‖ ^ 2) := by
  have h := integrable_pow_mul_normSq f 0
  simpa using h

/-- Copied from `BKMLogBootstrap` (private there): the symbol of a line
derivative has norm `2π |⟪ξ, m⟫| ‖û‖`. -/
private theorem norm_fourier_lineDeriv (v : SV) (m ξ : EuclSpace) :
    ‖𝓕 (∂_{m} v) ξ‖ = 2 * Real.pi * |inner ℝ ξ m| * ‖𝓕 v ξ‖ := by
  have h : (inner ℝ · m : EuclSpace → ℝ).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp [h, norm_smul, abs_of_pos Real.pi_pos]
  ring

/-- Copied from `BKMLogBootstrap` (private there): weighted Plancherel for one
line derivative. -/
private theorem integral_lineDeriv_sq (v : SV) (m : EuclSpace) :
    ∫ x : EuclSpace, ‖(∂_{m} v) x‖ ^ 2
      = 4 * Real.pi ^ 2 * ∫ ξ : EuclSpace, (inner ℝ ξ m : ℝ) ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  rw [← SchwartzMap.integral_norm_sq_fourier (∂_{m} v), ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖𝓕 (∂_{m} v) ξ‖ ^ 2 = 4 * Real.pi ^ 2 * ((inner ℝ ξ m : ℝ) ^ 2 * ‖𝓕 v ξ‖ ^ 2)
  rw [norm_fourier_lineDeriv]
  rw [mul_pow, mul_pow, mul_pow, sq_abs]
  ring

private theorem integrable_inner_sq (v : SV) (m : EuclSpace) (hm : ‖m‖ ≤ 1) :
    Integrable (fun ξ : EuclSpace => (inner ℝ ξ m : ℝ) ^ 2 * ‖𝓕 v ξ‖ ^ 2) := by
  refine integrable_weight_mul_normSq (𝓕 v) 2 _ (by fun_prop) fun ξ => ?_
  rw [abs_of_nonneg (by positivity)]
  have h := abs_real_inner_le_norm ξ m
  calc (inner ℝ ξ m : ℝ) ^ 2 = |(inner ℝ ξ m : ℝ)| ^ 2 := by rw [sq_abs]
    _ ≤ (‖ξ‖ * ‖m‖) ^ 2 := by gcongr
    _ = ‖ξ‖ ^ 2 * ‖m‖ ^ 2 := by ring
    _ ≤ ‖ξ‖ ^ 2 * 1 ^ 2 := by gcongr
    _ = ‖ξ‖ ^ 2 := by ring

/-- Copied from `BKMLogBootstrap` (private there): the full Dirichlet energy
of the model is `4π²` times the `‖ξ‖²`-weighted Fourier mass. -/
private theorem sum_integral_lineDeriv_sq (v : SV) :
    ∑ i : Fin 3, ∫ x : EuclSpace, ‖(∂_{e3 i} v) x‖ ^ 2
      = 4 * Real.pi ^ 2 * ∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  simp_rw [integral_lineDeriv_sq]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => integrable_inner_sq v (e3 i) (by simp))]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show (∑ i : Fin 3, (inner ℝ ξ (e3 i) : ℝ) ^ 2 * ‖𝓕 v ξ‖ ^ 2) = ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2
  rw [← Finset.sum_mul, sum_inner_e3_sq]

/-- The `‖ξ‖²`-weighted Fourier mass is integrable. -/
private theorem integrable_norm_sq_weight (v : SV) :
    Integrable (fun ξ : EuclSpace => ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) :=
  integrable_weight_mul_normSq (𝓕 v) 2 _ (by fun_prop) fun ξ => by
    rw [abs_of_nonneg (by positivity)]

end IntegrabilityCopies

section FourierSymbols

/-- Fourier transform commutes with postcomposition by a `ℂ`-linear map.
Pointwise form, proved from the Bochner-integral definition of `𝓕`. -/
theorem fourier_postcompCLM_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (L : F →L[ℂ] G) (g : SchwartzMap EuclSpace F) (ξ : EuclSpace) :
    (𝓕 (SchwartzMap.postcompCLM (𝕜 := ℂ) L g)) ξ = L ((𝓕 g) ξ) := by
  have hint : Integrable (fun v : EuclSpace => 𝐞 (-inner ℝ v ξ) • (g v : F)) volume := by
    have c : Continuous fun v : EuclSpace => 𝐞 (-inner ℝ v ξ) := by fun_prop
    simp_rw [← integrable_norm_iff (c.aestronglyMeasurable.smul g.integrable.aestronglyMeasurable),
      Circle.norm_smul]
    exact g.integrable.norm
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq]
  simp only [SchwartzMap.postcompCLM_apply]
  rw [← L.integral_comp_comm hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show 𝐞 (-inner ℝ v ξ) • L (g v) = L (𝐞 (-inner ℝ v ξ) • g v)
  rw [Circle.smul_def, Circle.smul_def, L.map_smul]

/-- The divergence of the Euclidean model, as a scalar-`ℂ` Schwartz map. -/
private def divModel (u : SchwartzVelocity) : SchwartzMap EuclSpace ℂ :=
  ∑ i : Fin 3,
    SchwartzMap.postcompCLM (𝕜 := ℂ) (EuclideanSpace.proj i) (∂_{e3 i} (euclModel u))

private theorem divModel_apply (u : SchwartzVelocity) (y : EuclSpace) :
    divModel u y = (staticDivergence u (euclCoords y) : ℂ) := by
  have hcomp : ∀ i : Fin 3,
      (SchwartzMap.postcompCLM (𝕜 := ℂ) (EuclideanSpace.proj i) (∂_{e3 i} (euclModel u))) y
        = ((fderiv ℝ u (euclCoords y) (basisVector i)) i : ℂ) := by
    intro i
    rw [SchwartzMap.postcompCLM_apply, euclModel_lineDeriv_apply]
    rfl
  rw [divModel]
  simp only [sum_apply, hcomp]
  rw [staticDivergence, Complex.ofReal_sum]

/-- The Fourier symbol of the divergence: `𝓕(div v) ξ = 2πi Σᵢ ξᵢ ûᵢ(ξ)`. -/
private theorem fourier_divModel (u : SchwartzVelocity) (ξ : EuclSpace) :
    (𝓕 (divModel u)) ξ =
      2 * Real.pi * Complex.I * ∑ i : Fin 3, (ξ i : ℂ) * ((𝓕 (euclModel u)) ξ) i := by
  rw [divModel, ← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ), map_sum,
    sum_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ), fourier_postcompCLM_apply,
    SchwartzMap.fourier_lineDerivOp_eq]
  have htemp : (inner ℝ · (e3 i) : EuclSpace → ℝ).HasTemperateGrowth := by fun_prop
  simp only [SchwartzMap.smulLeftCLM_apply_apply htemp, smul_apply]
  rw [inner_e3]
  show EuclideanSpace.proj i
      ((2 * (Real.pi : ℂ) * Complex.I) • ((ξ i : ℂ) • ((𝓕 (euclModel u)) ξ))) = _
  rw [← mul_smul, map_smul]
  show (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) • (((𝓕 (euclModel u)) ξ) i) = _
  rw [smul_eq_mul]
  ring

/-- The `(i,j)` curl component `∂ᵢuⱼ − ∂ⱼuᵢ` of the model, as a scalar-`ℂ`
Schwartz map. -/
private def curlComp (u : SchwartzVelocity) (i j : Fin 3) : SchwartzMap EuclSpace ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℂ) (EuclideanSpace.proj j) (∂_{e3 i} (euclModel u)) -
  SchwartzMap.postcompCLM (𝕜 := ℂ) (EuclideanSpace.proj i) (∂_{e3 j} (euclModel u))

private theorem curlComp_apply (u : SchwartzVelocity) (i j : Fin 3) (y : EuclSpace) :
    curlComp u i j y =
      ((fderiv ℝ u (euclCoords y) (basisVector i)) j -
        (fderiv ℝ u (euclCoords y) (basisVector j)) i : ℂ) := by
  simp only [curlComp, sub_apply, SchwartzMap.postcompCLM_apply,
    euclModel_lineDeriv_apply]
  rfl

/-- The Fourier symbol of a curl component:
`𝓕(curlComp i j) ξ = 2πi (ξᵢ ûⱼ(ξ) − ξⱼ ûᵢ(ξ))`. -/
private theorem fourier_curlComp (u : SchwartzVelocity) (i j : Fin 3) (ξ : EuclSpace) :
    (𝓕 (curlComp u i j)) ξ =
      2 * Real.pi * Complex.I *
        ((ξ i : ℂ) * ((𝓕 (euclModel u)) ξ) j - (ξ j : ℂ) * ((𝓕 (euclModel u)) ξ) i) := by
  rw [curlComp, ← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ), map_sub,
    sub_apply]
  rw [SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ),
    SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ)]
  rw [fourier_postcompCLM_apply, fourier_postcompCLM_apply,
    SchwartzMap.fourier_lineDerivOp_eq, SchwartzMap.fourier_lineDerivOp_eq]
  have htemp : ∀ m : EuclSpace, (inner ℝ · m : EuclSpace → ℝ).HasTemperateGrowth := by
    intro m; fun_prop
  simp only [SchwartzMap.smulLeftCLM_apply_apply (htemp _), smul_apply]
  rw [inner_e3, inner_e3]
  show EuclideanSpace.proj j
      ((2 * (Real.pi : ℂ) * Complex.I) • ((ξ i : ℂ) • ((𝓕 (euclModel u)) ξ))) -
    EuclideanSpace.proj i
      ((2 * (Real.pi : ℂ) * Complex.I) • ((ξ j : ℂ) • ((𝓕 (euclModel u)) ξ))) = _
  rw [← mul_smul, ← mul_smul, map_smul, map_smul]
  show (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) • (((𝓕 (euclModel u)) ξ) j) -
    (2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) • (((𝓕 (euclModel u)) ξ) i) = _
  rw [smul_eq_mul, smul_eq_mul]
  ring

end FourierSymbols

section LagrangeAssembly

private theorem complex_norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring

private theorem euclid_norm_sq (ξ : EuclSpace) : ‖ξ‖ ^ 2 = ∑ i : Fin 3, (ξ i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => by simp [sq_abs]

private theorem cx_norm_sq (w : CxSpace) : ‖w‖ ^ 2 = ∑ i : Fin 3, ‖w i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-- **Complex Lagrange identity.**  For real `ξ` and complex `w`, the three
cross-difference norms sum to `‖ξ‖²‖w‖² − |Σ ξᵢwᵢ|²` — the integrated form of
`|ξ × û|² = ‖ξ‖²‖û‖² − |ξ·û|²`. -/
private theorem lagrange_sq (ξ : EuclSpace) (w : CxSpace) :
    ‖(ξ 1 : ℂ) * w 2 - (ξ 2 : ℂ) * w 1‖ ^ 2 +
      ‖(ξ 2 : ℂ) * w 0 - (ξ 0 : ℂ) * w 2‖ ^ 2 +
      ‖(ξ 0 : ℂ) * w 1 - (ξ 1 : ℂ) * w 0‖ ^ 2
    = ‖ξ‖ ^ 2 * ‖w‖ ^ 2 - ‖∑ i : Fin 3, (ξ i : ℂ) * w i‖ ^ 2 := by
  rw [euclid_norm_sq ξ, cx_norm_sq w]
  simp only [Fin.sum_univ_three, complex_norm_sq, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The `2πi` symbol factor has norm `2π`. -/
private theorem norm_two_pi_i : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
  rw [norm_mul, norm_mul]
  simp [abs_of_nonneg Real.pi_nonneg]

/-- Component of a model vector is norm-dominated by the vector. -/
private theorem norm_component_le (w : CxSpace) (i : Fin 3) : ‖w i‖ ≤ ‖w‖ :=
  PiLp.norm_apply_le w i

/-- The divergence symbol is dominated by the gradient weight, from the
Lagrange identity (the curl sum is nonnegative). -/
private theorem div_symbol_norm_sq_le (ξ : EuclSpace) (w : CxSpace) :
    ‖∑ i : Fin 3, (ξ i : ℂ) * w i‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖w‖ ^ 2 := by
  have h := lagrange_sq ξ w
  have hnn : 0 ≤ ‖(ξ 1 : ℂ) * w 2 - (ξ 2 : ℂ) * w 1‖ ^ 2 +
      ‖(ξ 2 : ℂ) * w 0 - (ξ 0 : ℂ) * w 2‖ ^ 2 +
      ‖(ξ 0 : ℂ) * w 1 - (ξ 1 : ℂ) * w 0‖ ^ 2 := by positivity
  linarith

/-- **Model assembly.**  The Dirichlet energy of the Euclidean model splits
into the three curl-component energies plus the divergence energy; everything
is a weighted Fourier `L²` identity. -/
private theorem grad_sq_eq_curl_add_div_model (u : SchwartzVelocity) :
    ∑ i : Fin 3, ∫ y : EuclSpace, ‖(∂_{e3 i} (euclModel u)) y‖ ^ 2
    = (∫ y : EuclSpace, ‖curlComp u 1 2 y‖ ^ 2) +
      (∫ y : EuclSpace, ‖curlComp u 2 0 y‖ ^ 2) +
      (∫ y : EuclSpace, ‖curlComp u 0 1 y‖ ^ 2) +
      ∫ y : EuclSpace, ‖divModel u y‖ ^ 2 := by
  set û := 𝓕 (euclModel u) with hû
  have hA : Integrable (fun ξ : EuclSpace => ‖ξ‖ ^ 2 * ‖û ξ‖ ^ 2) :=
    integrable_norm_sq_weight _
  have hB : Integrable
      (fun ξ : EuclSpace => ‖∑ i : Fin 3, (ξ i : ℂ) * û ξ i‖ ^ 2) := by
    refine hA.mono' (by fun_prop) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact div_symbol_norm_sq_le ξ (û ξ)
  -- per-component Plancherel to the symbol side
  have hcurl : ∀ i j : Fin 3, ∫ y : EuclSpace, ‖curlComp u i j y‖ ^ 2
      = 4 * Real.pi ^ 2 * ∫ ξ : EuclSpace,
          ‖(ξ i : ℂ) * û ξ j - (ξ j : ℂ) * û ξ i‖ ^ 2 := by
    intro i j
    rw [← SchwartzMap.integral_norm_sq_fourier (curlComp u i j),
      ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show ‖(𝓕 (curlComp u i j)) ξ‖ ^ 2 =
      4 * Real.pi ^ 2 * ‖(ξ i : ℂ) * û ξ j - (ξ j : ℂ) * û ξ i‖ ^ 2
    rw [fourier_curlComp, norm_mul, norm_two_pi_i]
    ring
  have hdiv : ∫ y : EuclSpace, ‖divModel u y‖ ^ 2
      = 4 * Real.pi ^ 2 * ∫ ξ : EuclSpace, ‖∑ i : Fin 3, (ξ i : ℂ) * û ξ i‖ ^ 2 := by
    rw [← SchwartzMap.integral_norm_sq_fourier (divModel u),
      ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show ‖(𝓕 (divModel u)) ξ‖ ^ 2 =
      4 * Real.pi ^ 2 * ‖∑ i : Fin 3, (ξ i : ℂ) * û ξ i‖ ^ 2
    rw [fourier_divModel, norm_mul, norm_two_pi_i]
    ring
  -- sum the three curl-symbol integrals into one
  have hCi : ∀ i j : Fin 3, Integrable
      (fun ξ : EuclSpace => ‖(ξ i : ℂ) * û ξ j - (ξ j : ℂ) * û ξ i‖ ^ 2) := by
    intro i j
    have h4 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
    have h := (integrable_normSq_scalar (𝓕 (curlComp u i j))).const_mul (4 * Real.pi ^ 2)⁻¹
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    show (4 * Real.pi ^ 2)⁻¹ * ‖(𝓕 (curlComp u i j)) ξ‖ ^ 2 =
      ‖(ξ i : ℂ) * û ξ j - (ξ j : ℂ) * û ξ i‖ ^ 2
    rw [fourier_curlComp, norm_mul, norm_two_pi_i]
    field_simp
    ring
  have hsum2 : (∫ ξ : EuclSpace, ‖(ξ 1 : ℂ) * û ξ 2 - (ξ 2 : ℂ) * û ξ 1‖ ^ 2) +
      (∫ ξ : EuclSpace, ‖(ξ 2 : ℂ) * û ξ 0 - (ξ 0 : ℂ) * û ξ 2‖ ^ 2) +
      (∫ ξ : EuclSpace, ‖(ξ 0 : ℂ) * û ξ 1 - (ξ 1 : ℂ) * û ξ 0‖ ^ 2)
      = (∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖û ξ‖ ^ 2) -
        (∫ ξ : EuclSpace, ‖∑ i : Fin 3, (ξ i : ℂ) * û ξ i‖ ^ 2) := by
    have hC1220 : Integrable (fun a : EuclSpace =>
        ‖(a 1 : ℂ) * û a 2 - (a 2 : ℂ) * û a 1‖ ^ 2 +
        ‖(a 2 : ℂ) * û a 0 - (a 0 : ℂ) * û a 2‖ ^ 2) := (hCi 1 2).add (hCi 2 0)
    rw [← integral_add (hCi 1 2) (hCi 2 0), ← integral_add hC1220 (hCi 0 1),
      ← integral_sub hA hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show ‖(ξ 1 : ℂ) * û ξ 2 - (ξ 2 : ℂ) * û ξ 1‖ ^ 2 +
        ‖(ξ 2 : ℂ) * û ξ 0 - (ξ 0 : ℂ) * û ξ 2‖ ^ 2 +
        ‖(ξ 0 : ℂ) * û ξ 1 - (ξ 1 : ℂ) * û ξ 0‖ ^ 2
      = ‖ξ‖ ^ 2 * ‖û ξ‖ ^ 2 - ‖∑ i : Fin 3, (ξ i : ℂ) * û ξ i‖ ^ 2
    exact lagrange_sq ξ (û ξ)
  rw [sum_integral_lineDeriv_sq, hcurl 1 2, hcurl 2 0, hcurl 0 1, hdiv]
  linear_combination (4 * Real.pi ^ 2) * hsum2.symm

end LagrangeAssembly

section SpaceTransport

/-- The `0`-component of the coordinate curl. -/
private theorem staticCurl_apply_zero (u : SchwartzVelocity) (x : Space) :
    staticCurl u x 0 =
      (fderiv ℝ u x (basisVector 1)) 2 - (fderiv ℝ u x (basisVector 2)) 1 := by
  simp only [staticCurl, Fin.sum_univ_three, Finset.sum_apply]
  simp [basisVector, cross_apply]
  ring

/-- The `1`-component of the coordinate curl. -/
private theorem staticCurl_apply_one (u : SchwartzVelocity) (x : Space) :
    staticCurl u x 1 =
      (fderiv ℝ u x (basisVector 2)) 0 - (fderiv ℝ u x (basisVector 0)) 2 := by
  simp only [staticCurl, Fin.sum_univ_three, Finset.sum_apply]
  simp [basisVector, cross_apply]
  ring

/-- The `2`-component of the coordinate curl. -/
private theorem staticCurl_apply_two (u : SchwartzVelocity) (x : Space) :
    staticCurl u x 2 =
      (fderiv ℝ u x (basisVector 0)) 1 - (fderiv ℝ u x (basisVector 1)) 0 := by
  simp only [staticCurl, Fin.sum_univ_three, Finset.sum_apply]
  simp [basisVector, cross_apply]
  ring

/-- The curl energy on `Space` transports to the three curl-component
energies of the Euclidean model. -/
private theorem curl_energy_transport (u : SchwartzVelocity) :
    ∫ x : Space, officialEuclideanNorm (staticCurl u x) ^ 2
    = (∫ y : EuclSpace, ‖curlComp u 1 2 y‖ ^ 2) +
      (∫ y : EuclSpace, ‖curlComp u 2 0 y‖ ^ 2) +
      (∫ y : EuclSpace, ‖curlComp u 0 1 y‖ ^ 2) := by
  have hpt : ∀ y : EuclSpace,
      officialEuclideanNorm (staticCurl u (euclCoords y)) ^ 2
      = ‖curlComp u 1 2 y‖ ^ 2 + ‖curlComp u 2 0 y‖ ^ 2 + ‖curlComp u 0 1 y‖ ^ 2 := by
    intro y
    rw [officialEuclideanNorm_sq_eq_sum_sq, Fin.sum_univ_three]
    rw [staticCurl_apply_zero, staticCurl_apply_one, staticCurl_apply_two]
    rw [curlComp_apply, curlComp_apply, curlComp_apply]
    norm_cast
    simp only [Real.norm_eq_abs, sq_abs]
  have hI : ∀ i j : Fin 3,
      Integrable (fun y : EuclSpace => ‖curlComp u i j y‖ ^ 2) :=
    fun i j => integrable_normSq_scalar _
  have hI1220 : Integrable (fun y : EuclSpace =>
      ‖curlComp u 1 2 y‖ ^ 2 + ‖curlComp u 2 0 y‖ ^ 2) := (hI 1 2).add (hI 2 0)
  rw [integral_space_eq_euclSpace]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_add hI1220 (hI 0 1), integral_add (hI 1 2) (hI 2 0)]

/-- The divergence energy on `Space` transports to the model divergence
energy. -/
private theorem div_energy_transport (u : SchwartzVelocity) :
    ∫ x : Space, (staticDivergence u x) ^ 2
    = ∫ y : EuclSpace, ‖divModel u y‖ ^ 2 := by
  rw [integral_space_eq_euclSpace]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (staticDivergence u (euclCoords y)) ^ 2 = ‖divModel u y‖ ^ 2
  rw [divModel_apply]
  norm_cast
  simp only [Real.norm_eq_abs, sq_abs]

/-- One gradient-direction energy on `Space` transports to the model line
derivative energy. -/
private theorem grad_energy_transport (u : SchwartzVelocity) (i : Fin 3) :
    ∫ x : Space, officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2
    = ∫ y : EuclSpace, ‖(∂_{e3 i} (euclModel u)) y‖ ^ 2 := by
  rw [integral_space_eq_euclSpace]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show officialEuclideanNorm (fderiv ℝ u (euclCoords y) (basisVector i)) ^ 2 =
    ‖(∂_{e3 i} (euclModel u)) y‖ ^ 2
  rw [euclModel_lineDeriv_apply, norm_realToCx_sq]

/-- **The master identity.**  For a Schwartz velocity field on `Space = ℝ³`,
the Dirichlet energy splits into curl energy plus divergence energy:
`∫ Σᵢ‖∂ᵢu‖² = ∫‖curl u‖² + ∫(div u)²` (all norms the official Euclidean
coordinate norm). -/
theorem sum_integral_fderiv_sq_eq_curl_sq_add_div_sq (u : SchwartzVelocity) :
    (∑ i : Fin 3, ∫ x : Space, officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2)
    = (∫ x : Space, officialEuclideanNorm (staticCurl u x) ^ 2) +
      ∫ x : Space, (staticDivergence u x) ^ 2 := by
  rw [Finset.sum_congr rfl (fun i _ => grad_energy_transport u i)]
  rw [grad_sq_eq_curl_add_div_model u, curl_energy_transport u, div_energy_transport u]

end SpaceTransport

section OperatorNormBound

/-- A vector is the sum of its basis components. -/
private theorem eq_sum_smul_basis (v : Space) :
    v = ∑ i : Fin 3, v i • basisVector i := by
  ext j
  simp [Finset.sum_apply, basisVector, Pi.single, Function.update]

/-- The Fréchet-derivative operator norm is bounded by the sum of the
coordinate-direction norms (sup-norm domain estimate). -/
theorem opNorm_le_sum (T : Space →L[ℝ] Space) :
    ‖T‖ ≤ ∑ i : Fin 3, ‖T (basisVector i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => norm_nonneg _)
      (fun v => ?_)
  calc ‖T v‖ = ‖T (∑ i : Fin 3, v i • basisVector i)‖ :=
        congrArg (fun X => ‖T X‖) (eq_sum_smul_basis v)
    _ = ‖∑ i : Fin 3, v i • T (basisVector i)‖ := by rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • T (basisVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖T (basisVector i)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖T (basisVector i)‖) * ‖v‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `(Σ aᵢ)² ≤ 3 Σ aᵢ²` for three terms. -/
private theorem sum_sq_le_three_mul (a : Fin 3 → ℝ) :
    (∑ i : Fin 3, a i) ^ 2 ≤ 3 * ∑ i : Fin 3, a i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) a (fun _ => 1)
  simp only [Fin.sum_univ_three, one_pow, mul_one] at h
  simp only [Fin.sum_univ_three]
  nlinarith [h]

/-- The squared operator norm of the derivative is bounded by `3` times the
sum of the squared coordinate-direction Euclidean norms. -/
private theorem opNorm_sq_le_three_mul_sum (u : SchwartzVelocity) (x : Space) :
    ‖fderiv ℝ u x‖ ^ 2 ≤
      3 * ∑ i : Fin 3, officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2 := by
  have h1 : ‖fderiv ℝ u x‖ ^ 2 ≤ (∑ i : Fin 3, ‖fderiv ℝ u x (basisVector i)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (opNorm_le_sum _) _
  have h2 : (∑ i : Fin 3, ‖fderiv ℝ u x (basisVector i)‖) ^ 2
      ≤ 3 * ∑ i : Fin 3, ‖fderiv ℝ u x (basisVector i)‖ ^ 2 :=
    sum_sq_le_three_mul _
  have h3 : ∀ i : Fin 3, ‖fderiv ℝ u x (basisVector i)‖ ^ 2
      ≤ officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2 :=
    fun i => norm_sq_le_officialEuclideanNorm_sq _
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => h3 i) (by positivity)))

end OperatorNormBound

section Corollaries

/-- Space-domain copy of the polynomial-weight integrability helper. -/
private theorem integrable_pow_mul_normSq_space {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : SchwartzMap Space F) (k : ℕ) :
    Integrable (fun x : Space => ‖x‖ ^ k * ‖f x‖ ^ 2) := by
  have hM : ∀ x, ‖f x‖ ≤ (SchwartzMap.seminorm ℝ 0 0) f := fun x => f.norm_le_seminorm ℝ x
  refine ((f.integrable_pow_mul volume k).const_mul ((SchwartzMap.seminorm ℝ 0 0) f)).mono'
    ((by fun_prop : Continuous fun x : Space => ‖x‖ ^ k * ‖f x‖ ^ 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : ‖x‖ ^ k * ‖f x‖ ^ 2 = (‖x‖ ^ k * ‖f x‖) * ‖f x‖ := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (hM x) (by positivity) |>.trans_eq (by ring)

/-- Integrability of one coordinate-direction Euclidean energy. -/
private theorem integrable_directional_energy (u : SchwartzVelocity) (i : Fin 3) :
    Integrable (fun x : Space =>
      officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2) := by
  have hbase : Integrable (fun x : Space => ‖(∂_{basisVector i} u) x‖ ^ 2) := by
    have h' := integrable_pow_mul_normSq_space (∂_{basisVector i} u) 0
    simpa using h'
  have hmeas : AEStronglyMeasurable (fun x : Space =>
      officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2) volume := by
    have hc : Continuous fun x : Space => fderiv ℝ u x :=
      (u.smooth 1).continuous_fderiv (by norm_num)
    exact ((continuous_officialEuclideanNorm.comp
      (hc.clm_apply continuous_const)).pow 2).aestronglyMeasurable
  refine (hbase.const_mul 3).mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  show officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2 ≤
    3 * ‖(∂_{basisVector i} u) x‖ ^ 2
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact officialEuclideanNorm_sq_le_three_mul_norm_sq _

/-- **Divergence-free fields: Dirichlet energy = enstrophy.**  The divergence
term of the master identity vanishes identically. -/
theorem sum_integral_fderiv_sq_eq_curl_sq_of_divFree (u : SchwartzVelocity)
    (hu : DivergenceFreeInitial u) :
    (∑ i : Fin 3, ∫ x : Space, officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2)
    = ∫ x : Space, officialEuclideanNorm (staticCurl u x) ^ 2 := by
  have hzero : ∀ x : Space, staticDivergence u x = 0 := fun x => hu x
  rw [sum_integral_fderiv_sq_eq_curl_sq_add_div_sq u]
  simp [hzero]

/-- The actual curl energy of a divergence-free velocity is the weighted
Fourier mass of its Euclidean complexification. This exposes the comparison
needed by frequency-band Galerkin projections. -/
theorem curl_sq_eq_fourierWeight_of_divFree (u : SchwartzVelocity)
    (hu : DivergenceFreeInitial u) :
    (∫ x : Space, officialEuclideanNorm (staticCurl u x) ^ 2) =
      4 * Real.pi ^ 2 * ∫ ξ : EuclSpace,
        ‖ξ‖ ^ 2 * ‖(𝓕 (euclModel u)) ξ‖ ^ 2 := by
  rw [← sum_integral_fderiv_sq_eq_curl_sq_of_divFree u hu]
  rw [Finset.sum_congr rfl (fun i _ => grad_energy_transport u i)]
  exact sum_integral_lineDeriv_sq (euclModel u)

/-- **The dissipation bridge.**  For a divergence-free Schwartz field, the
`L²` energy of the full Fréchet derivative (operator norm) is bounded by
three times the enstrophy.  This is the exact estimate that turns the Galerkin
enstrophy budget into the `hdiss` hypothesis of
`LerayWeak.spaceEquicontinuous_of_dissipation_bound`. -/
theorem integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree (u : SchwartzVelocity)
    (hu : DivergenceFreeInitial u) :
    ∫ x : Space, ‖fderiv ℝ u x‖ ^ 2
      ≤ 3 * ∫ x : Space, officialEuclideanNorm (staticCurl u x) ^ 2 := by
  have hint_dir : ∀ i : Fin 3, i ∈ Finset.univ → Integrable (fun x : Space =>
      officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2) :=
    fun i _ => integrable_directional_energy u i
  have hint_sum : Integrable (fun x : Space =>
      3 * ∑ i : Fin 3, officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2) :=
    (integrable_finsetSum Finset.univ hint_dir).const_mul 3
  have hint_op : Integrable (fun x : Space => ‖fderiv ℝ u x‖ ^ 2) := by
    have hmeas : AEStronglyMeasurable (fun x : Space => ‖fderiv ℝ u x‖ ^ 2) volume :=
      (((u.smooth 1).continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
    refine hint_sum.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact opNorm_sq_le_three_mul_sum u x
  calc ∫ x : Space, ‖fderiv ℝ u x‖ ^ 2
      ≤ ∫ x : Space,
          3 * ∑ i : Fin 3, officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2 :=
        integral_mono hint_op hint_sum (fun x => opNorm_sq_le_three_mul_sum u x)
    _ = 3 * ∑ i : Fin 3,
          ∫ x : Space, officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum Finset.univ hint_dir]
    _ = 3 * ∫ x : Space, officialEuclideanNorm (staticCurl u x) ^ 2 := by
        rw [sum_integral_fderiv_sq_eq_curl_sq_of_divFree u hu]

end Corollaries

end Navier.Analysis.DivFreeGradientEnstrophy

end
