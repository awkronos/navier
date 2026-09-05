import Navier.Analysis.BealeKatoMajda
import Navier.Analysis.BKMLogLeaves
import Navier.Analysis.UniformDecayDominated
import Navier.Analysis.BiotSavartKernel
import Navier.Analysis.BiotSavartCore
import Navier.Analysis.BiotSavartNearBounds
import Navier.Analysis.CZNearField
import Navier.Analysis.EnergyNormBridge
import Navier.Analysis.CurlDerivativeBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Morrey--Agmon estimate for Schwartz velocities

This upstream file contains the Euclidean Fourier model, weighted Plancherel
comparison, frequency split, and the resulting `H²` to `C^{0,1/4}` estimate.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral

namespace Navier.Analysis.BealeKatoMajda

open Navier
open Navier.Analysis.BKMLogLeaves
open Navier.Analysis.UniformDecayDominated
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.CZNearField
open Navier.Analysis.EnergyNormBridge

/-- The squared inhomogeneous `H³(ℝ³)` Sobolev norm of a Schwartz velocity
field: `∑_{n ≤ 3} ‖D^n u‖²_{L²}`.  Schwartz decay makes every summand a
genuine (finite) integral. -/
def sobolevH3NormSq (u : SchwartzVelocity) : ℝ :=
  ∑ n ∈ Finset.range 4, ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2

/-- The squared `H³` norm is nonnegative (each summand is an integral of a
square). -/
theorem sobolevH3NormSq_nonneg (u : SchwartzVelocity) :
    0 ≤ sobolevH3NormSq u := by
  apply Finset.sum_nonneg
  intro n _
  exact integral_nonneg (fun x => by positivity)

/-- The squared inhomogeneous `H²(ℝ³)` Sobolev norm of a Schwartz velocity
field: `∑_{n ≤ 2} ‖D^n u‖²_{L²}`.  `H²` is already *strictly* above the
critical order `3/2` in three dimensions, so it is the sharp order at which the
sup-norm embedding used by the BKM assembly holds. -/
def sobolevH2NormSq (u : SchwartzVelocity) : ℝ :=
  ∑ n ∈ Finset.range 3, ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2

/-- **`H³ ⊆ H²` at the level of norms (certified, no sorry).**  The `H²` sum runs
over `Finset.range 3 ⊆ Finset.range 4` and the omitted `n = 3` summand is an
integral of a square, hence nonnegative. -/
theorem sobolevH2NormSq_le_sobolevH3NormSq (u : SchwartzVelocity) :
    sobolevH2NormSq u ≤ sobolevH3NormSq u := by
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))) ?_
  intro n _ _
  exact integral_nonneg (fun x => by positivity)

/-- **Per-order domination by the `H³` norm (certified, no sorry).**  For each
derivative order `n < 4`, the order-`n` energy `∫ ‖Dⁿu‖²` is one summand of
`sobolevH3NormSq u`, and the omitted summands are integrals of squares.  This
is the step that converts a Kato–Ponce commutator bound stated against
`‖Dⁿu‖_{L²}` into the `‖u‖²_{H³}` shape that
`exists_sobolevOrderEnergyEstimate` and the Grönwall consumer use. -/
theorem sobolevOrderNormSq_le_sobolevH3NormSq (u : SchwartzVelocity) {n : ℕ}
    (hn : n < 4) :
    (∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2) ≤ sobolevH3NormSq u :=
  Finset.single_le_sum
    (f := fun m => ∫ x : Space, ‖iteratedFDeriv ℝ m (⇑u) x‖ ^ 2)
    (fun m _ => integral_nonneg (fun x => by positivity))
    (Finset.mem_range.mpr hn)

/-- The squared `H²` norm is nonnegative (each summand is an integral of a
square). -/
theorem sobolevH2NormSq_nonneg (u : SchwartzVelocity) :
    0 ≤ sobolevH2NormSq u := by
  apply Finset.sum_nonneg
  intro n _
  exact integral_nonneg (fun x => by positivity)

/-!
### The Bessel weight `(1 + |ξ|²)⁻²` on `ℝ³` (certified, no sorry)

The part of the Agmon embedding `H²(ℝ³) ↪ L^∞` that is *specific to three
dimensions* is the finiteness of `∫_{ℝ³} (1 + |ξ|²)^{-2} dξ`: on the Euclidean
model this is the radial integral `∫₀^∞ 4πr²/(1+r²)² dr = π²`, finite precisely
because the decay exponent `4` strictly exceeds the dimension `3`.  The `H¹`
analogue `∫_{ℝ³} (1 + |ξ|²)^{-1} dξ` **diverges** (`∫₀^R 4πr²/(1+r²) dr ∼ 4πR`),
which is why the `H²` order in `exists_agmonSupBound` is load-bearing and not
decoration.  Everything below is dimension-generic Lean; `ℝ³` enters through
the single arithmetic fact `Module.finrank ℝ Space = 3 < 4`.

Reference: E. M. Stein, *Singular Integrals and Differentiability Properties of
Functions*, Princeton University Press 1970, Ch. V §3 (Bessel potentials);
S. Agmon, *Lectures on Elliptic Boundary Value Problems*, Van Nostrand 1965.
-/

/-- The reciprocal Bessel weight `ξ ↦ (1 + ‖ξ‖²)⁻¹` is continuous (the
denominator is bounded below by `1`). -/
theorem continuous_inv_one_add_normSq :
    Continuous (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro ξ; positivity

/-- **Bessel-weight integrability in three dimensions (certified, no sorry).**
`ξ ↦ (1 + ‖ξ‖²)⁻²` is `volume`-integrable on `Space = ℝ³`, because the decay
exponent `4` strictly exceeds `Module.finrank ℝ Space = 3`.

This is the sole dimension-dependent input to the Agmon embedding: with the
exponent `2` in place of `4` (the `H¹` weight) the integral diverges, so this
lemma is exactly the reason `H²` — and not `H¹` — embeds into `L^∞` on `ℝ³`.

Reference: Stein, *Singular Integrals and Differentiability Properties of
Functions*, Princeton 1970, Ch. V §3. -/
theorem integrable_inv_one_add_normSq_sq :
    Integrable (fun ξ : Space => (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) := by
  have hr : (Module.finrank ℝ Space : ℝ) < 4 := by
    have h3 : Module.finrank ℝ Space = 3 := by simp
    rw [h3]; norm_num
  refine (integrable_rpow_neg_one_add_norm_sq (E := Space) (μ := volume)
    (r := 4) hr).congr ?_
  filter_upwards with ξ
  rw [show (-4 : ℝ) / 2 = -(2 : ℕ) by norm_num, Real.rpow_neg (by positivity),
    Real.rpow_natCast]

/-- **Sharpness of the `H²` order (certified, no sorry).**  The `H¹` Bessel
weight `ξ ↦ (1 + ‖ξ‖²)⁻¹` is **not** integrable on `ℝ³`: its decay exponent `2`
does not exceed `Module.finrank ℝ Space = 3`.

This is the exact counterpart of `integrable_inv_one_add_normSq_sq`, and it is
what makes the `H²` hypothesis in `exists_agmonSupBound` load-bearing rather
than decorative: the same Fourier/Cauchy–Schwarz route run at order `1` has no
finite weight to pair against, so it yields no `L^∞` bound.  (Indeed
`H¹(ℝ³) ↪ L^∞` is false.)

Proof: on `ball 0 R` with `R ≥ 1` the integrand is `≥ (2R²)⁻¹`, while
`volume (ball 0 R) = R³ · volume (ball 0 1)` by `Measure.addHaar_ball`, so the
lower Lebesgue integral is at least `(R/2)·volume (ball 0 1) → ∞`.

Reference: Stein, *Singular Integrals and Differentiability Properties of
Functions*, Princeton 1970, Ch. V §3 (the Bessel potential `G_s` is in `L²`
iff `2s > n`). -/
theorem not_integrable_inv_one_add_normSq :
    ¬ Integrable (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) := by
  intro hint
  set M : ENNReal := ∫⁻ ξ : Space, ‖((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹‖ₑ with hM
  have hMlt : M < ⊤ := hint.2
  set v : ENNReal := (volume : Measure Space) (Metric.ball (0 : Space) 1) with hv
  have hvpos : 0 < v := Metric.measure_ball_pos _ _ one_pos
  have hvne : v ≠ ⊤ := measure_ball_lt_top.ne
  have key : ∀ R : ℝ, 1 ≤ R →
      ENNReal.ofReal ((2 * R ^ 2)⁻¹) *
        (volume : Measure Space) (Metric.ball (0 : Space) R) ≤ M := by
    intro R hR
    have hms : MeasurableSet (Metric.ball (0 : Space) R) := measurableSet_ball
    rw [← lintegral_indicator_const hms]
    refine lintegral_mono fun ξ => ?_
    by_cases hξ : ξ ∈ Metric.ball (0 : Space) R
    · rw [Set.indicator_of_mem hξ]
      have hlt : ‖ξ‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hξ
      have hnn : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg _
      have hb : (1 : ℝ) + ‖ξ‖ ^ 2 ≤ 2 * R ^ 2 := by nlinarith
      have hpos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
      have hinv : ((2 * R ^ 2 : ℝ))⁻¹ ≤ ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ := inv_anti₀ hpos hb
      calc ENNReal.ofReal ((2 * R ^ 2)⁻¹)
          ≤ ENNReal.ofReal (((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) := ENNReal.ofReal_le_ofReal hinv
        _ = ‖((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹‖ₑ := by rw [Real.enorm_eq_ofReal (by positivity)]
    · rw [Set.indicator_of_notMem hξ]; exact zero_le
  have hball : ∀ R : ℝ, 0 ≤ R →
      (volume : Measure Space) (Metric.ball (0 : Space) R)
        = ENNReal.ofReal (R ^ 3) * v := by
    intro R hR
    rw [Measure.addHaar_ball _ _ hR]
    congr 2
    simp
  have final : ∀ R : ℝ, 1 ≤ R → R / 2 * v.toReal ≤ M.toReal := by
    intro R hR
    have h0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
    have h := key R hR
    rw [hball R h0, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at h
    have heq : (2 * R ^ 2)⁻¹ * R ^ 3 = R / 2 := by
      have hR0 : R ≠ 0 := by positivity
      field_simp
    rw [heq] at h
    have h2 := ENNReal.toReal_mono hMlt.ne h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  have hvr : 0 < v.toReal := ENNReal.toReal_pos hvpos.ne' hvne
  obtain ⟨R, hR1, hRbig⟩ : ∃ R : ℝ, 1 ≤ R ∧ M.toReal < R / 2 * v.toReal := by
    refine ⟨max 1 (2 * (M.toReal + 1) / v.toReal), le_max_left _ _, ?_⟩
    have h2 : 2 * (M.toReal + 1) / v.toReal ≤ max 1 (2 * (M.toReal + 1) / v.toReal) :=
      le_max_right _ _
    have h3 : 2 * (M.toReal + 1) / v.toReal * v.toReal = 2 * (M.toReal + 1) := by
      field_simp
    nlinarith [h3, h2, hvr]
  linarith [final R hR1]

/-- The `L¹(ℝ³)` mass `∫ (1 + ‖ξ‖²)⁻² dξ` of the Bessel weight.  Finite by
`integrable_inv_one_add_normSq_sq`; on the Euclidean model of `ℝ³` its value is
`π²`, but only finiteness is used below. -/
def besselWeightMass : ℝ := ∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹

/-- **Weighted Cauchy–Schwarz against the Bessel weight (certified, no sorry).**
For nonnegative `h : ℝ³ → ℝ` whose Bessel-weighted version `(1 + ‖ξ‖²)·h` is
square integrable,

  `∫ h ≤ √(∫ (1+‖ξ‖²)⁻²) · √(∫ ((1+‖ξ‖²)·h)²)`.

Proof: write `h = (1+‖ξ‖²)⁻¹ · ((1+‖ξ‖²)·h)` and apply Hölder with the
conjugate pair `(2,2)`; the first factor lies in `L²(ℝ³)` by
`integrable_inv_one_add_normSq_sq`.  Applied with `h = ‖û‖` this is precisely
the Cauchy–Schwarz step of the Agmon/Sobolev embedding (Stein, *Singular
Integrals*, Princeton 1970, Ch. V §3). -/
theorem integral_le_besselWeightMass_mul_sqrt
    {h : Space → ℝ} (hnn : ∀ ξ : Space, 0 ≤ h ξ)
    (hmem : MemLp (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) 2) :
    ∫ ξ : Space, h ξ ≤
      Real.sqrt besselWeightMass *
        Real.sqrt (∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) ^ 2) := by
  have hpq : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hfsq : Integrable (fun ξ : Space => (((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) ^ 2) := by
    simpa [inv_pow] using integrable_inv_one_add_normSq_sq
  have hf : MemLp (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) 2 :=
    (memLp_two_iff_integrable_sq continuous_inv_one_add_normSq.aestronglyMeasurable).mpr hfsq
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure Space)) hpq
    (f := fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹)
    (g := fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ)
    (Filter.Eventually.of_forall fun ξ => by positivity)
    (Filter.Eventually.of_forall fun ξ => by have := hnn ξ; positivity)
    (by simpa using hf) (by simpa using hmem)
  have hprod : ∀ ξ : Space,
      ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ * (((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) = h ξ := by
    intro ξ; field_simp
  simp only [hprod] at key
  have hrw : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
    intro y; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hrw] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [besselWeightMass, inv_pow] using key

open scoped FourierTransform LineDeriv

/-!
### Euclidean/complex model transport for the Fourier majorant (certified, no sorry)

`Space = Fin 3 → ℝ` carries the Pi (sup) norm, so it has **no** `InnerProductSpace ℝ`
instance and no `NormedSpace ℂ` instance — both verified against the compiler:
`example : InnerProductSpace ℝ Space := by infer_instance` and
`example : NormedSpace ℂ Space := by infer_instance` each fail with
`failed to synthesize instance`.  Mathlib's Schwartz Fourier transform
(`SchwartzMap.instFourierTransform` in
`Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`) requires
`[InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]`
on the domain and `[NormedSpace ℂ E]` on the codomain, so it does not apply to
`𝓢(Space, Space)` on the nose.  The transport built here is the fix: the domain
moves to `EuclideanSpace ℝ (Fin 3)` (definitionally `PiLp 2 fun _ : Fin 3 => ℝ`,
same carrier, ℓ² norm, volume-preserving by `PiLp.volume_preserving_ofLp`) and the
codomain to `EuclideanSpace ℂ (Fin 3)`, via Mathlib's
`SchwartzMap.compCLMOfContinuousLinearEquiv` and `SchwartzMap.postcompCLM`.
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

/-- The Pi (sup) norm of `ℝ³` is dominated by the ℓ² norm of its complex image.
This is the direction the majorant bound needs: it lets the sup-norm conclusion
`‖u x‖ ≤ ∫ h` be read off from the Euclidean model. -/
theorem norm_le_norm_realToCx (a : Space) : ‖a‖ ≤ ‖realToCx a‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  have h1 : ‖(realToCx a) i‖ ≤ ‖realToCx a‖ := by
    rw [EuclideanSpace.norm_eq]
    refine (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr ?_
    exact Finset.single_le_sum (f := fun j => ‖(realToCx a) j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  rw [realToCx_apply] at h1
  simpa using h1

/-- The Euclidean/complex model of a Schwartz velocity field: precompose with the
coordinate identification (`compCLMOfContinuousLinearEquiv`) and postcompose with the
componentwise complexification (`postcompCLM`).  Both are Mathlib's own Schwartz-space
operations, so the result is a genuine `SchwartzMap EuclSpace CxSpace` and Mathlib's Fourier
transform applies to it. -/
def euclModel (u : SchwartzVelocity) : SchwartzMap EuclSpace CxSpace :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) realToCx
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ euclCoords u)

@[simp] theorem euclModel_apply (u : SchwartzVelocity) (y : EuclSpace) :
    euclModel u y = realToCx (u (euclCoords y)) := rfl

/-- **Fourier-inversion majorant on the Euclidean model (certified, no sorry).**
For a Schwartz map into a complex Hilbert space, the sup norm is dominated by the
`L¹` mass of its Fourier transform: `‖v y‖ = ‖𝓕⁻(𝓕 v) y‖ ≤ ∫ ‖𝓕 v‖`.  This is the
inversion half of `exists_besselFourierMajorant`; the Schwartz-level inversion pair
is Mathlib's `FourierPair.fourierInv_fourier_eq`
(Hörmander, *The Analysis of Linear PDO I*, 2nd ed. Springer 1990, Thm 7.1.5). -/
theorem norm_le_integral_norm_fourier (v : SchwartzMap EuclSpace CxSpace) (y : EuclSpace) :
    ‖v y‖ ≤ ∫ ξ : EuclSpace, ‖(𝓕 v) ξ‖ := by
  have hinv : (𝓕⁻ (𝓕 v) : SchwartzMap EuclSpace CxSpace) = v := FourierPair.fourierInv_fourier_eq v
  have h1 : v y = 𝓕⁻ ((𝓕 v : SchwartzMap EuclSpace CxSpace) : EuclSpace → CxSpace) y := by
    conv_lhs => rw [← hinv]
    rw [SchwartzMap.fourierInv_coe]
  rw [h1, Real.fourierInv_eq_fourier_neg]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- **Volume transport between the two models (certified, no sorry).**  `Space` and
`EuclSpace` share a carrier and the coordinate map is volume preserving
(`PiLp.volume_preserving_ofLp`), so every Lebesgue integral transports verbatim. -/
theorem integral_space_eq_euclSpace (f : Space → ℝ) :
    ∫ ξ : Space, f ξ = ∫ y : EuclSpace, f (euclCoords y) := by
  have hmp : MeasureTheory.MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ))
      (volume : Measure EuclSpace) (volume : Measure Space) :=
    PiLp.volume_preserving_ofLp (Fin 3)
  rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding]
  rfl

/-!
### Leaf 1: weighted Plancherel on the Euclidean model (certified, no sorry)

The coordinate-derivative route.  Mathlib's Plancherel for Schwartz maps
(`SchwartzMap.integral_norm_sq_fourier`) needs an inner-product codomain, which
`iteratedFDeriv` does not have (it lands in a space of multilinear maps).  So the
symbol identity is run on **line derivatives** `∂_{eᵢ}` instead
(`SchwartzMap.fourier_lineDerivOp_eq`: `𝓕(∂_m f) = (2πi)⟪·,m⟫ · 𝓕 f`), whose
codomain is still `CxSpace`.  Summing over the orthonormal basis turns the symbol
product into a power of `‖ξ‖` because `∑_{i₁…i_n} ⟪ξ,e_{i₁}⟫²⋯⟪ξ,e_{i_n}⟫² =
(∑_i ξ_i²)^n = ‖ξ‖^{2n}`, and the passage back to the `iteratedFDeriv` operator
norm is one application of `ContinuousMultilinearMap.le_opNorm` at unit vectors.
Stein, *Singular Integrals*, Princeton 1970, Ch. V §3.
-/

private abbrev SV := SchwartzMap EuclSpace CxSpace

private theorem norm_fourier_lineDeriv (v : SV) (m ξ : EuclSpace) :
    ‖𝓕 (∂_{m} v) ξ‖ = 2 * Real.pi * |inner ℝ ξ m| * ‖𝓕 v ξ‖ := by
  have h : (inner ℝ · m : EuclSpace → ℝ).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp [h, norm_smul, abs_of_pos Real.pi_pos]
  ring

private noncomputable def eucBasis (i : Fin 3) : EuclSpace := EuclideanSpace.single i (1:ℝ)

@[simp] private theorem norm_eucBasis (i : Fin 3) : ‖eucBasis i‖ = 1 := by
  simp [eucBasis]

@[simp] private theorem inner_eucBasis (ξ : EuclSpace) (i : Fin 3) :
    (inner ℝ ξ (eucBasis i) : ℝ) = ξ i := by
  simp [eucBasis, EuclideanSpace.inner_single_right]

private theorem sum_inner_eucBasis_sq (ξ : EuclSpace) :
    ∑ i : Fin 3, (inner ℝ ξ (eucBasis i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := by
  simp only [inner_eucBasis]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [sq_abs]

private theorem integrable_pow_mul_normSq (f : SV) (k : ℕ) :
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

private theorem integrable_weight_mul_normSq (f : SV) (k : ℕ) (g : EuclSpace → ℝ)
    (hg : Continuous g) (hgb : ∀ ξ, |g ξ| ≤ ‖ξ‖ ^ k) :
    Integrable (fun ξ : EuclSpace => g ξ * ‖f ξ‖ ^ 2) := by
  refine (integrable_pow_mul_normSq f k).mono'
    ((by fun_prop : Continuous fun ξ : EuclSpace => g ξ * ‖f ξ‖ ^ 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖f ξ‖ ^ 2)]
  exact mul_le_mul_of_nonneg_right (hgb ξ) (by positivity)

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

private theorem sum_integral_lineDeriv_sq (v : SV) :
    ∑ i : Fin 3, ∫ x : EuclSpace, ‖(∂_{eucBasis i} v) x‖ ^ 2
      = 4 * Real.pi ^ 2 * ∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  simp_rw [integral_lineDeriv_sq]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => integrable_inner_sq v (eucBasis i) (by simp))]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show (∑ i : Fin 3, (inner ℝ ξ (eucBasis i) : ℝ) ^ 2 * ‖𝓕 v ξ‖ ^ 2) = ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2
  rw [← Finset.sum_mul, sum_inner_eucBasis_sq]

private theorem integrable_normSq_iteratedFDeriv (v : SV) (n : ℕ) :
    Integrable (fun x : EuclSpace => ‖iteratedFDeriv ℝ n (⇑v) x‖ ^ 2) := by
  have hM : ∀ x, ‖iteratedFDeriv ℝ n (⇑v) x‖ ≤ (SchwartzMap.seminorm ℝ 0 n) v :=
    fun x => v.norm_iteratedFDeriv_le_seminorm ℝ n x
  have hM0 : (0:ℝ) ≤ (SchwartzMap.seminorm ℝ 0 n) v := le_trans (norm_nonneg _) (hM 0)
  have hcont : Continuous fun x : EuclSpace => ‖iteratedFDeriv ℝ n (⇑v) x‖ ^ 2 :=
    ((ContDiff.continuous_iteratedFDeriv (m := n) (hf := v.smooth ⊤)
      (by exact_mod_cast le_top)).norm).pow 2
  refine ((SchwartzMap.integrable_pow_mul_iteratedFDeriv volume v 0 n).const_mul
    ((SchwartzMap.seminorm ℝ 0 n) v)).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : ‖iteratedFDeriv ℝ n (⇑v) x‖ ^ 2
      = ‖iteratedFDeriv ℝ n (⇑v) x‖ * ‖iteratedFDeriv ℝ n (⇑v) x‖ := by ring
  rw [this]
  calc ‖iteratedFDeriv ℝ n (⇑v) x‖ * ‖iteratedFDeriv ℝ n (⇑v) x‖
      ≤ (SchwartzMap.seminorm ℝ 0 n) v * (‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n (⇑v) x‖) := by
        simp only [pow_zero, one_mul]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    _ = _ := rfl

private theorem integrable_quartic_weight (v : SV) (j : Fin 3) :
    Integrable (fun ξ : EuclSpace =>
      (‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2) * ‖𝓕 v ξ‖ ^ 2) := by
  refine integrable_weight_mul_normSq (𝓕 v) 4 _ (by fun_prop) fun ξ => ?_
  rw [abs_of_nonneg (by positivity)]
  have h := abs_real_inner_le_norm ξ (eucBasis j)
  have h2 : (inner ℝ ξ (eucBasis j) : ℝ) ^ 2 ≤ ‖ξ‖ ^ 2 := by
    calc (inner ℝ ξ (eucBasis j) : ℝ) ^ 2 = |(inner ℝ ξ (eucBasis j) : ℝ)| ^ 2 := by rw [sq_abs]
      _ ≤ (‖ξ‖ * ‖eucBasis j‖) ^ 2 := by gcongr
      _ = ‖ξ‖ ^ 2 := by simp
  calc ‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2 ≤ ‖ξ‖ ^ 2 * ‖ξ‖ ^ 2 := by gcongr
    _ = ‖ξ‖ ^ 4 := by ring

private theorem sum_integral_lineDeriv2_sq (v : SV) :
    ∑ j : Fin 3, ∑ i : Fin 3,
        ∫ x : EuclSpace, ‖(∂_{eucBasis i} (∂_{eucBasis j} v)) x‖ ^ 2
      = 16 * Real.pi ^ 4 * ∫ ξ : EuclSpace, ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2 := by
  have step : ∀ j : Fin 3,
      (∑ i : Fin 3, ∫ x : EuclSpace, ‖(∂_{eucBasis i} (∂_{eucBasis j} v)) x‖ ^ 2)
        = 16 * Real.pi ^ 4 * ∫ ξ : EuclSpace,
            (‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2) * ‖𝓕 v ξ‖ ^ 2 := by
    intro j
    have hpt : ∀ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 (∂_{eucBasis j} v) ξ‖ ^ 2
        = 4 * Real.pi ^ 2 * ((‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2) * ‖𝓕 v ξ‖ ^ 2) := by
      intro ξ
      rw [norm_fourier_lineDeriv, mul_pow, mul_pow, mul_pow, sq_abs]
      ring
    rw [sum_integral_lineDeriv_sq (∂_{eucBasis j} v),
      integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul]
    ring
  rw [Finset.sum_congr rfl (fun j _ => step j), ← Finset.mul_sum,
    ← integral_finsetSum _ (fun j _ => integrable_quartic_weight v j)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show (∑ j : Fin 3, (‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2) * ‖𝓕 v ξ‖ ^ 2)
      = ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2
  rw [← Finset.sum_mul]
  have : (∑ j : Fin 3, ‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2) = ‖ξ‖ ^ 4 := by
    rw [← Finset.mul_sum, sum_inner_eucBasis_sq]; ring
  rw [this]

private theorem norm_lineDeriv_le (v : SV) (m x : EuclSpace) :
    ‖(∂_{m} v) x‖ ≤ ‖iteratedFDeriv ℝ 1 (⇑v) x‖ * ‖m‖ := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, norm_iteratedFDeriv_one]
  exact (fderiv ℝ (⇑v) x).le_opNorm m

private theorem lineDeriv2_eq (v : SV) (m m' x : EuclSpace) :
    (∂_{m} (∂_{m'} v)) x = iteratedFDeriv ℝ 2 (⇑v) x ![m, m'] := by
  have hdiff : Differentiable ℝ (fderiv ℝ (⇑v)) :=
    (ContDiff.fderiv_right (m := (1 : ℕ∞)) (v.smooth 2) (by norm_num)).differentiable (by norm_num)
  have hfun : ((∂_{m'} v : SV) : EuclSpace → CxSpace)
      = fun y : EuclSpace => (fderiv ℝ (⇑v) y) m' := by
    funext y; exact SchwartzMap.lineDerivOp_apply_eq_fderiv m' v y
  rw [iteratedFDeriv_two_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun,
    fderiv_clm_apply (hdiff x) (differentiableAt_const m')]
  simp

private theorem norm_lineDeriv2_le (v : SV) (m m' x : EuclSpace) :
    ‖(∂_{m} (∂_{m'} v)) x‖ ≤ ‖iteratedFDeriv ℝ 2 (⇑v) x‖ * (‖m‖ * ‖m'‖) := by
  rw [lineDeriv2_eq]
  refine le_trans ((iteratedFDeriv ℝ 2 (⇑v) x).le_opNorm ![m, m']) ?_
  simp [Fin.prod_univ_two]

private theorem sum3_const (c : ℝ) : (∑ _i : Fin 3, c) = 3 * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

private theorem sum33_const (c : ℝ) : (∑ _j : Fin 3, ∑ _i : Fin 3, c) = 9 * c := by
  rw [sum3_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

private theorem weight_sq_expand (v : SV) (ξ : EuclSpace) :
    (((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖) ^ 2
      = ‖ξ‖ ^ 0 * ‖𝓕 v ξ‖ ^ 2 + (2 * (‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) + ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2) := by
  simp only [pow_zero, one_mul]
  ring

private theorem integrable_weight_sq (v : SV) :
    Integrable (fun ξ : EuclSpace => (((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖) ^ 2) := by
  have h0 := integrable_pow_mul_normSq (𝓕 v) 0
  have h2 := integrable_pow_mul_normSq (𝓕 v) 2
  have h4 := integrable_pow_mul_normSq (𝓕 v) 4
  have h24 : Integrable (fun ξ : EuclSpace =>
      2 * (‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) + ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2) := (h2.const_mul 2).add h4
  have hall : Integrable (fun ξ : EuclSpace =>
      ‖ξ‖ ^ 0 * ‖𝓕 v ξ‖ ^ 2 + (2 * (‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) + ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2)) := h0.add h24
  exact hall.congr (Filter.Eventually.of_forall fun ξ => (weight_sq_expand v ξ).symm)

theorem memLp_weight_fourier (v : SV) :
    MemLp (fun ξ : EuclSpace => ((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖) 2 volume := by
  refine (memLp_two_iff_integrable_sq ?_).mpr (integrable_weight_sq v)
  exact ((by fun_prop : Continuous fun ξ : EuclSpace =>
    ((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖)).aestronglyMeasurable

set_option maxHeartbeats 1000000 in
theorem exists_weighted_plancherel :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SV,
      (∫ ξ : EuclSpace, (((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖) ^ 2)
        ≤ C * ∑ n ∈ Finset.range 3, ∫ y : EuclSpace, ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2 := by
  refine ⟨3, by norm_num, fun v => ?_⟩
  have hA0nn : (0:ℝ) ≤ ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 0 (⇑v) y‖ ^ 2 :=
    integral_nonneg fun y => by positivity
  have hA1nn : (0:ℝ) ≤ ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2 :=
    integral_nonneg fun y => by positivity
  have hA2nn : (0:ℝ) ≤ ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2 :=
    integral_nonneg fun y => by positivity
  have h0 := integrable_pow_mul_normSq (𝓕 v) 0
  have h2 := integrable_pow_mul_normSq (𝓕 v) 2
  have h4 := integrable_pow_mul_normSq (𝓕 v) 4
  have hsplit : (∫ ξ : EuclSpace, (((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖) ^ 2)
      = (∫ ξ : EuclSpace, ‖𝓕 v ξ‖ ^ 2)
        + (2 * (∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2)
          + ∫ ξ : EuclSpace, ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2) := by
    have h24 : Integrable (fun ξ : EuclSpace =>
        2 * (‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) + ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2) := (h2.const_mul 2).add h4
    have h2c : Integrable (fun ξ : EuclSpace => 2 * (‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2)) := h2.const_mul 2
    rw [integral_congr_ae (Filter.Eventually.of_forall (weight_sq_expand v)),
      integral_add h0 h24, integral_add h2c h4, MeasureTheory.integral_const_mul]
    simp
  have hA : (∫ ξ : EuclSpace, ‖𝓕 v ξ‖ ^ 2)
      = ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 0 (⇑v) y‖ ^ 2 := by
    rw [SchwartzMap.integral_norm_sq_fourier]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ‖v y‖ ^ 2 = ‖iteratedFDeriv ℝ 0 (⇑v) y‖ ^ 2
    rw [norm_iteratedFDeriv_zero]
  have hle1 : ∀ i : Fin 3, (∫ x : EuclSpace, ‖(∂_{eucBasis i} v) x‖ ^ 2)
      ≤ ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2 := by
    intro i
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      (integrable_normSq_iteratedFDeriv v 1) (Filter.Eventually.of_forall fun x => ?_)
    have hb := norm_lineDeriv_le v (eucBasis i) x
    simp only [norm_eucBasis, mul_one] at hb
    have h0' := norm_nonneg ((∂_{eucBasis i} v) x)
    nlinarith
  have hS1 : 4 * Real.pi ^ 2 * (∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2)
      ≤ 3 * ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2 := by
    rw [← sum_integral_lineDeriv_sq v, ← sum3_const (∫ y : EuclSpace,
      ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2)]
    exact Finset.sum_le_sum fun i _ => hle1 i
  have hle2 : ∀ i j : Fin 3,
      (∫ x : EuclSpace, ‖(∂_{eucBasis i} (∂_{eucBasis j} v)) x‖ ^ 2)
        ≤ ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2 := by
    intro i j
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      (integrable_normSq_iteratedFDeriv v 2) (Filter.Eventually.of_forall fun x => ?_)
    have hb := norm_lineDeriv2_le v (eucBasis i) (eucBasis j) x
    simp only [norm_eucBasis, mul_one] at hb
    have h0' := norm_nonneg ((∂_{eucBasis i} (∂_{eucBasis j} v)) x)
    nlinarith
  have hS2 : 16 * Real.pi ^ 4 * (∫ ξ : EuclSpace, ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2)
      ≤ 9 * ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2 := by
    rw [← sum_integral_lineDeriv2_sq v, ← sum33_const (∫ y : EuclSpace,
      ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2)]
    exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hle2 i j
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hBnn : (0:ℝ) ≤ ∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 :=
    integral_nonneg fun ξ => by positivity
  have hDnn : (0:ℝ) ≤ ∫ ξ : EuclSpace, ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2 :=
    integral_nonneg fun ξ => by positivity
  have hpi2 : (9:ℝ) < Real.pi ^ 2 := by nlinarith
  have hpi4 : (81:ℝ) < Real.pi ^ 4 := by nlinarith
  have hB' : 2 * (∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2)
      ≤ 3 * ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2 := by nlinarith
  have hD' : (∫ ξ : EuclSpace, ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2)
      ≤ 3 * ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2 := by nlinarith
  have hsum : (∑ n ∈ Finset.range 3, ∫ y : EuclSpace, ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2)
      = (∫ y : EuclSpace, ‖iteratedFDeriv ℝ 0 (⇑v) y‖ ^ 2)
        + (∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2)
        + ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2 := by
    simp [Finset.sum_range_succ]
  rw [hsplit, hA, hsum]
  linarith

/-!
### Leaf 2: model comparison, and the assembly (certified, no sorry)

`euclModel u = realToCx ∘ u ∘ euclCoords` is a composition with two continuous
linear maps, so `ContinuousLinearMap.iteratedFDeriv_comp_left` and
`ContinuousLinearMap.iteratedFDeriv_comp_right` give
`‖D^n (euclModel u) y‖ ≤ ‖realToCx‖ · ‖euclCoords‖^n · ‖D^n u (euclCoords y)‖`.
Since `n < 3` the operator-norm powers are absorbed into a single constant, and
`integral_space_eq_euclSpace` transports the resulting integrals back to `Space`.
Only finite-dimensional norm equivalence is used; no analysis.
-/

private theorem norm_le_norm_toEucl (ξ : Space) : ‖ξ‖ ≤ ‖euclCoords.symm ξ‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  have h1 : ‖(euclCoords.symm ξ) i‖ ≤ ‖euclCoords.symm ξ‖ := by
    rw [EuclideanSpace.norm_eq]
    refine (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr ?_
    exact Finset.single_le_sum (f := fun j => ‖(euclCoords.symm ξ) j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : (euclCoords.symm ξ) i = ξ i := rfl
  rw [h2] at h1
  exact h1

private theorem iteratedFDeriv_euclModel_le (u : SchwartzVelocity) (n : ℕ) (y : EuclSpace) :
    ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖
      ≤ ‖realToCx‖ * (‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖
          * ∏ _i : Fin n, ‖(euclCoords : EuclSpace →L[ℝ] Space)‖) := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (⇑u) := u.smooth ⊤
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) ((⇑u) ∘ (euclCoords : EuclSpace →L[ℝ] Space)) :=
    hu.comp (euclCoords : EuclSpace →L[ℝ] Space).contDiff
  have heq : (⇑(euclModel u)) = (⇑realToCx) ∘ ((⇑u) ∘ (euclCoords : EuclSpace →L[ℝ] Space)) := by
    funext z; simp [euclModel_apply]
  rw [heq]
  calc ‖iteratedFDeriv ℝ n ((⇑realToCx) ∘ ((⇑u) ∘ (euclCoords : EuclSpace →L[ℝ] Space))) y‖
      = ‖realToCx.compContinuousMultilinearMap
          (iteratedFDeriv ℝ n ((⇑u) ∘ (euclCoords : EuclSpace →L[ℝ] Space)) y)‖ := by
        rw [ContinuousLinearMap.iteratedFDeriv_comp_left realToCx hcomp.contDiffAt
          (by exact_mod_cast le_top)]
    _ ≤ ‖realToCx‖ * ‖iteratedFDeriv ℝ n ((⇑u) ∘ (euclCoords : EuclSpace →L[ℝ] Space)) y‖ :=
        realToCx.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖realToCx‖ * (‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖
          * ∏ _i : Fin n, ‖(euclCoords : EuclSpace →L[ℝ] Space)‖) := by
        gcongr
        rw [ContinuousLinearMap.iteratedFDeriv_comp_right
          (euclCoords : EuclSpace →L[ℝ] Space) hu y (by exact_mod_cast le_top)]
        exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
theorem integrable_normSq_iteratedFDeriv_space (u : SchwartzVelocity) (n : ℕ) :
    Integrable (fun x : Space => ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2) := by
  have hM : ∀ x, ‖iteratedFDeriv ℝ n (⇑u) x‖ ≤ (SchwartzMap.seminorm ℝ 0 n) u :=
    fun x => u.norm_iteratedFDeriv_le_seminorm ℝ n x
  have hM0 : (0:ℝ) ≤ (SchwartzMap.seminorm ℝ 0 n) u := le_trans (norm_nonneg _) (hM 0)
  have hcont : Continuous fun x : Space => ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 :=
    ((ContDiff.continuous_iteratedFDeriv (m := n) (hf := u.smooth ⊤)
      (by exact_mod_cast le_top)).norm).pow 2
  refine ((SchwartzMap.integrable_pow_mul_iteratedFDeriv volume u 0 n).const_mul
    ((SchwartzMap.seminorm ℝ 0 n) u)).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsq : ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2
      = ‖iteratedFDeriv ℝ n (⇑u) x‖ * ‖iteratedFDeriv ℝ n (⇑u) x‖ := by ring
  rw [hsq]
  calc ‖iteratedFDeriv ℝ n (⇑u) x‖ * ‖iteratedFDeriv ℝ n (⇑u) x‖
      ≤ (SchwartzMap.seminorm ℝ 0 n) u * (‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n (⇑u) x‖) := by
        simp only [pow_zero, one_mul]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    _ = _ := rfl

theorem exists_euclModel_h2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SchwartzVelocity,
      (∑ n ∈ Finset.range 3, ∫ y : EuclSpace, ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖ ^ 2)
        ≤ C * sobolevH2NormSq u := by
  set k := ‖realToCx‖ with hk
  set e := ‖(euclCoords : EuclSpace →L[ℝ] Space)‖ with he
  have hk0 : 0 ≤ k := norm_nonneg _
  have he0 : 0 ≤ e := norm_nonneg _
  set M := k * (1 + e) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M ^ 2 + 1, by positivity, fun u => ?_⟩
  have hmp : MeasureTheory.MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ))
      (volume : Measure EuclSpace) (volume : Measure Space) :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have key : ∀ n : ℕ, n ≤ 2 →
      (∫ y : EuclSpace, ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖ ^ 2)
        ≤ M ^ 2 * ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 := by
    intro n hn
    have hint : Integrable
        (fun y : EuclSpace => M ^ 2 * ‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ ^ 2) :=
      (hmp.integrable_comp_of_integrable (integrable_normSq_iteratedFDeriv_space u n)).const_mul (M ^ 2)
    have htrans : (∫ y : EuclSpace, M ^ 2 * ‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ ^ 2)
        = M ^ 2 * ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 := by
      rw [MeasureTheory.integral_const_mul,
        integral_space_eq_euclSpace (fun x : Space => ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2)]
    rw [← htrans]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity) hint
      (Filter.Eventually.of_forall fun y => ?_)
    have hb := iteratedFDeriv_euclModel_le u n y
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hk, ← he] at hb
    have hen : e ^ n ≤ (1 + e) ^ 2 := by
      interval_cases n <;> nlinarith
    have hb2 : ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖
        ≤ M * ‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ := by
      refine hb.trans ?_
      rw [hM]
      calc k * (‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ * e ^ n)
          ≤ k * (‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ * (1 + e) ^ 2) := by gcongr
        _ = k * (1 + e) ^ 2 * ‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ := by ring
    have h0 := norm_nonneg (iteratedFDeriv ℝ n (⇑(euclModel u)) y)
    have h1 := norm_nonneg (iteratedFDeriv ℝ n (⇑u) (euclCoords y))
    nlinarith
  have hnn : ∀ n : ℕ, (0:ℝ) ≤ ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 :=
    fun n => integral_nonneg fun x => by positivity
  have hsum : sobolevH2NormSq u
      = (∫ x : Space, ‖iteratedFDeriv ℝ 0 (⇑u) x‖ ^ 2)
        + (∫ x : Space, ‖iteratedFDeriv ℝ 1 (⇑u) x‖ ^ 2)
        + ∫ x : Space, ‖iteratedFDeriv ℝ 2 (⇑u) x‖ ^ 2 := by
    simp [sobolevH2NormSq, Finset.sum_range_succ]
  rw [show (∑ n ∈ Finset.range 3, ∫ y : EuclSpace, ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖ ^ 2)
      = (∫ y : EuclSpace, ‖iteratedFDeriv ℝ 0 (⇑(euclModel u)) y‖ ^ 2)
        + (∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑(euclModel u)) y‖ ^ 2)
        + ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑(euclModel u)) y‖ ^ 2 from by
      simp [Finset.sum_range_succ], hsum]
  have k0 := key 0 (by norm_num)
  have k1 := key 1 (by norm_num)
  have k2 := key 2 (by norm_num)
  nlinarith [hnn 0, hnn 1, hnn 2, hM0]

private theorem euclCoords_symm_coe : (⇑euclCoords.symm : Space → EuclSpace)
    = (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclSpace) := rfl

/-- **[CERTIFIED — Fourier inversion + Plancherel + Bessel-symbol bookkeeping
for `SchwartzMap Space Space`; Stein, *Singular Integrals and Differentiability
Properties of Functions*, Princeton 1970, Ch. V §3; L. Hörmander, *The Analysis
of Linear Partial Differential Operators I*, 2nd ed. Springer 1990, §7.1 and
§7.9.]**

Every Schwartz velocity field admits a nonnegative **Fourier majorant density**
`h` — classically `h = ‖û‖` in the convention `u(x) = ∫ e^{2πi⟨x,ξ⟩} û(ξ) dξ` —
which dominates the sup norm through inversion, `‖u(x)‖ ≤ ∫ ‖û‖`, and whose
Bessel-weighted `L²` mass is controlled by the *physical* `H²` norm,
`∫ (1+|ξ|²)²‖û‖² ≤ C·‖u‖²_{H²}`: expand `(1+|ξ|²)² = 1 + 2|ξ|² + |ξ|⁴` and match
the three terms against `n = 0, 1, 2` via Plancherel and `ℱ(D^n u) =
(2πiξ)^{⊗n} û`.

**Why this is strictly lower than `exists_agmonSupBound`.**  It contains no
sup-norm/Sobolev inequality and no dimensional hypothesis.  The dimensional
content — that `(1+|ξ|²)⁻²` is integrable on `ℝ³` exactly because `4 > 3`, and
the Cauchy–Schwarz that turns that into the embedding — is discharged above by
`integrable_inv_one_add_normSq_sq` and `integral_le_besselWeightMass_mul_sqrt`.
What remains here is pure Fourier bookkeeping, provable without any reference
to `exists_agmonSupBound`.

**The obstruction, verified against the compiler.**  `Space = Fin 3 → ℝ` carries
the Pi (sup) norm, so both
`example : InnerProductSpace ℝ Space := by infer_instance` and
`example : NormedSpace ℂ Space := by infer_instance` fail with
`failed to synthesize instance`.  Mathlib's Schwartz Fourier transform
(`SchwartzMap.instFourierTransform`) needs `[InnerProductSpace ℝ V]
[FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]` on the domain and
`[NormedSpace ℂ E]` on the codomain, so it does not apply to `𝓢(Space, Space)`
on the nose.  That is the whole of the obstruction: it is an instance mismatch,
not a missing theorem.

**What is now built (certified above, no sorry).**  The transport is in place —
`euclCoords`, `realToCx`, `norm_le_norm_realToCx`, `euclModel`,
`integral_space_eq_euclSpace` — and so is the inversion half,
`norm_le_integral_norm_fourier`.  The correction to the earlier dependency list:
Fourier inversion and Plancherel are **not** Mathlib-absent.  Inversion for
Schwartz maps is `FourierPair.fourierInv_fourier_eq`, and Plancherel is
`SchwartzMap.integral_norm_sq_fourier : ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2`
(`Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`).  The transport API
is `SchwartzMap.compCLMOfContinuousLinearEquiv` and `SchwartzMap.postcompCLM`.

**The two leaves, both certified above.**

* `exists_weighted_plancherel` — *weighted Plancherel on the Euclidean model*
  [Stein Ch. V §3]:
  `∃ C > 0, ∀ v : 𝓢(EuclSpace, CxSpace),
   ∫ y, ((1 + ‖y‖²)·‖𝓕 v y‖)² ≤ C · ∑_{n < 3} ∫ y, ‖iteratedFDeriv ℝ n v y‖²`,
  together with `MemLp ((1 + ‖·‖²)·‖𝓕 v ·‖) 2`.  Route: expand
  `(1 + r²)² = 1 + 2r² + r⁴`, and get each `∫ ‖y‖^{2n}‖𝓕 v y‖²` from
  `SchwartzMap.integral_norm_sq_fourier` applied to the coordinate derivatives
  `∂_{i₁}…∂_{i_n} v` — summing over `(i₁,…,i_n)` turns the symbol product into
  `‖y‖^{2n}` because `∑_{i₁…i_n} y_{i₁}²⋯y_{i_n}² = (∑_i y_i²)^n`.  Working with
  coordinate derivatives rather than `iteratedFDeriv` directly is what keeps the
  codomain an inner-product space, which Plancherel requires; the passage back to
  the `iteratedFDeriv` operator norm is the finite-dimensional multilinear-norm
  comparison and carries the constant.
* `exists_euclModel_h2_bound` — *model comparison* [finite-dimensional norm
  equivalence]:
  `∃ C > 0, ∀ u, ∑_{n < 3} ∫ y, ‖iteratedFDeriv ℝ n (euclModel u) y‖² ≤
   C · sobolevH2NormSq u`.  Only norm equivalence on `Fin 3 → ℝ` and on the
  spaces of `n`-linear maps out of it, plus `integral_space_eq_euclSpace`.

The assembly below takes `h ξ = ‖𝓕 (euclModel u) (euclCoords.symm ξ)‖`, with
`norm_le_norm_realToCx` and `norm_le_integral_norm_fourier` supplying
`‖u x‖ ≤ ∫ h`, `norm_le_norm_toEucl` (Pi sup norm ≤ ℓ² norm) making the weight
transport monotone in the right direction, and `integral_space_eq_euclSpace`
moving the integrals between the two models. -/
theorem exists_besselFourierMajorant :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : SchwartzVelocity, ∃ h : Space → ℝ,
        (∀ ξ : Space, 0 ≤ h ξ) ∧
        MemLp (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) 2 ∧
        (∀ x : Space, ‖(⇑u) x‖ ≤ ∫ ξ : Space, h ξ) ∧
        (∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) ^ 2) ≤ C * sobolevH2NormSq u := by
  obtain ⟨C₁, hC₁, hplan⟩ := exists_weighted_plancherel
  obtain ⟨C₂, hC₂, hmod⟩ := exists_euclModel_h2_bound
  refine ⟨C₁ * C₂, by positivity, fun u => ?_⟩
  set v : SchwartzMap EuclSpace CxSpace := euclModel u with hv
  have hmpT : MeasureTheory.MeasurePreserving
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclSpace) (volume : Measure Space)
      (volume : Measure EuclSpace) := PiLp.volume_preserving_toLp (Fin 3)
  have hcontF : Continuous fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖ := by
    fun_prop
  refine ⟨fun ξ => ‖𝓕 v (euclCoords.symm ξ)‖, fun ξ => norm_nonneg _, ?_, ?_, ?_⟩
  · have hG : MemLp (fun ξ : Space =>
        ((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) 2 volume := by
      rw [euclCoords_symm_coe]
      exact (memLp_weight_fourier v).comp_measurePreserving hmpT
    refine hG.of_le hcontF.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    have hle := norm_le_norm_toEucl ξ
    have h1 : (0:ℝ) ≤ ‖𝓕 v (euclCoords.symm ξ)‖ := norm_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    have h2 : ‖ξ‖ ^ 2 ≤ ‖euclCoords.symm ξ‖ ^ 2 := by
      have := norm_nonneg ξ; nlinarith
    nlinarith
  · intro x
    have h1 : ‖(⇑u) x‖ ≤ ‖v (euclCoords.symm x)‖ := by
      rw [hv, euclModel_apply]
      simp only [ContinuousLinearEquiv.apply_symm_apply]
      exact norm_le_norm_realToCx (u x)
    have h2 : ‖v (euclCoords.symm x)‖ ≤ ∫ ξ : EuclSpace, ‖𝓕 v ξ‖ :=
      norm_le_integral_norm_fourier v _
    have h3 : (∫ ξ : Space, ‖𝓕 v (euclCoords.symm ξ)‖) = ∫ ξ : EuclSpace, ‖𝓕 v ξ‖ := by
      rw [integral_space_eq_euclSpace (fun ξ : Space => ‖𝓕 v (euclCoords.symm ξ)‖)]
      simp
    rw [h3]; linarith
  · have hintE : Integrable
        (fun y : EuclSpace => (((1 : ℝ) + ‖y‖ ^ 2) * ‖𝓕 v y‖) ^ 2) := by
      refine (memLp_two_iff_integrable_sq ?_).mp (memLp_weight_fourier v)
      exact ((by fun_prop : Continuous fun y : EuclSpace =>
        ((1 : ℝ) + ‖y‖ ^ 2) * ‖𝓕 v y‖)).aestronglyMeasurable
    have hint : Integrable (fun ξ : Space =>
        (((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2) := by
      rw [euclCoords_symm_coe]
      exact hmpT.integrable_comp_of_integrable hintE
    have hstep1 : (∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2)
        ≤ ∫ ξ : Space,
            (((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2 := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity) hint
        (Filter.Eventually.of_forall fun ξ => ?_)
      show (((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2
          ≤ (((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2
      have hle := norm_le_norm_toEucl ξ
      have h1 : (0:ℝ) ≤ ‖𝓕 v (euclCoords.symm ξ)‖ := norm_nonneg _
      have h2 : ‖ξ‖ ^ 2 ≤ ‖euclCoords.symm ξ‖ ^ 2 := by
        have := norm_nonneg ξ; nlinarith
      have hmul : ((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖
          ≤ ((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖ := by gcongr
      have hnn : (0:ℝ) ≤ ((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖ := by positivity
      nlinarith
    have hstep2 : (∫ ξ : Space,
          (((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2)
        = ∫ y : EuclSpace, (((1 : ℝ) + ‖y‖ ^ 2) * ‖𝓕 v y‖) ^ 2 := by
      rw [integral_space_eq_euclSpace (fun ξ : Space =>
        (((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2)]
      simp
    have hS : (0:ℝ) ≤ sobolevH2NormSq u := sobolevH2NormSq_nonneg u
    calc (∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2)
        ≤ ∫ y : EuclSpace, (((1 : ℝ) + ‖y‖ ^ 2) * ‖𝓕 v y‖) ^ 2 := hstep1.trans_eq hstep2
      _ ≤ C₁ * ∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
            ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2 := hplan v
      _ ≤ C₁ * (C₂ * sobolevH2NormSq u) := by
          have hh := hmod u
          rw [← hv] at hh
          nlinarith
      _ = C₁ * C₂ * sobolevH2NormSq u := by ring

/-- Concrete non-vacuous base case for the Fourier-majorant interface: the
zero Schwartz velocity is represented by the zero Fourier majorant.  Retained as
a Step-0e non-vacuity anchor for the majorant interface; the universal statement
above is now certified, so this is no longer the only inhabitant. -/
theorem besselFourierMajorant_zero :
    ∃ h : Space → ℝ,
      (∀ ξ : Space, 0 ≤ h ξ) ∧
      MemLp (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) 2 ∧
      (∀ x : Space, ‖((0 : SchwartzVelocity) : Space → Space) x‖ ≤
        ∫ ξ : Space, h ξ) ∧
      (∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) ^ 2) ≤
        sobolevH2NormSq (0 : SchwartzVelocity) := by
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro ξ
    exact le_rfl
  · simpa using (MemLp.zero (μ := volume) (p := (2 : ENNReal)))
  · intro x
    simp
  · simpa using sobolevH2NormSq_nonneg (0 : SchwartzVelocity)

/-- **[DERIVED from `exists_besselFourierMajorant`.]**  Agmon / Sobolev
embedding `H²(ℝ³) ↪ L^∞` (`s = 2 > 3/2 = n/2`); Majda–Bertozzi Lemma 3.2;
Agmon, *Lectures on Elliptic Boundary Value Problems*, Van Nostrand 1965;
Stein, *Singular Integrals*, Princeton 1970, Ch. V.  The sup norm of a Schwartz
field is dominated by the square root of its `H²` norm:
`‖u‖_∞ ≤ C·‖u‖_{H²}`.  This is the **sharp** derivative order for the embedding
used by the BKM assembly, one order below the `H³` control the criterion
actually carries.

The derivation is the classical two-line Fourier argument, now assembled from
certified parts: take the Fourier majorant density `h` supplied by
`exists_besselFourierMajorant`, bound `‖u(x)‖ ≤ ∫ h` by inversion, split
`h = (1+|ξ|²)⁻¹·((1+|ξ|²)h)` and apply
`integral_le_besselWeightMass_mul_sqrt`, whose weight has finite mass by
`integrable_inv_one_add_normSq_sq` — the `4 > 3` step that fails for `H¹`. -/
theorem exists_agmonSupBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (x : Space),
        ‖(⇑u) x‖ ≤ C * Real.sqrt (sobolevH2NormSq u) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_besselFourierMajorant
  refine ⟨Real.sqrt besselWeightMass * Real.sqrt C₀ + 1, by positivity, ?_⟩
  intro u x
  obtain ⟨h, hnn, hmem, hsup, hplan⟩ := hC₀ u
  have hS : (0 : ℝ) ≤ Real.sqrt (sobolevH2NormSq u) := Real.sqrt_nonneg _
  have hstep : ∫ ξ : Space, h ξ ≤
      Real.sqrt besselWeightMass * Real.sqrt (C₀ * sobolevH2NormSq u) :=
    le_trans (integral_le_besselWeightMass_mul_sqrt hnn hmem)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hplan) (Real.sqrt_nonneg _))
  calc ‖(⇑u) x‖
      ≤ ∫ ξ : Space, h ξ := hsup x
    _ ≤ Real.sqrt besselWeightMass * Real.sqrt (C₀ * sobolevH2NormSq u) := hstep
    _ = (Real.sqrt besselWeightMass * Real.sqrt C₀) *
          Real.sqrt (sobolevH2NormSq u) := by
        rw [Real.sqrt_mul hC₀pos.le]; ring
    _ ≤ (Real.sqrt besselWeightMass * Real.sqrt C₀ + 1) *
          Real.sqrt (sobolevH2NormSq u) :=
        mul_le_mul_of_nonneg_right (by linarith) hS

/-- **[DERIVED from `exists_agmonSupBound`.]**  Agmon/Sobolev embedding, s = 3 > 3/2;
Majda–Bertozzi Lemma 3.2; est ~250 LOC.]**  The sup norm of a Schwartz field is
dominated by (the square root of) its `H³` norm: `‖u‖_∞ ≤ C·√Ms` for any
majorant `Ms ≥ ‖u‖²_{H³}`.  Closure route: Fourier inversion +
Cauchy–Schwarz against `(1+|ξ|²)^{-s}` (integrable for `s > 3/2`); needs the
Schwartz Fourier–Plancherel API, present in Mathlib, plus derivative-to-symbol
bookkeeping. -/
theorem sobolevEmbeddingDomination :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (Ms : ℝ), sobolevH3NormSq u ≤ Ms →
        ∀ x : Space, ‖(⇑u) x‖ ≤ C * Real.sqrt Ms := by
  obtain ⟨C, hCpos, hC⟩ := exists_agmonSupBound
  refine ⟨C, hCpos, ?_⟩
  intro u Ms hMs x
  exact le_mul_sqrt_of_le_majorant (le_of_lt hCpos) (hC u x)
    (le_trans (sobolevH2NormSq_le_sobolevH3NormSq u) hMs)

/-!
### The Morrey–Agmon Hölder seminorm bound (certified, no sorry)

`exists_agmonSupBound` controls the *size* of a Schwartz field by its `H²`
norm; the Biot–Savart near field in `exists_biotSavartLogTextbook` consumes
the *difference* version — a Hölder modulus of continuity at the same `H²`
order.  The derivative count is the point: bounding the near-field
cancellation `|ω(x-z) - ω(x)|` by `‖∇ω‖∞·‖z‖` costs a full extra derivative
of the vorticity and would push the log inequality onto `H⁴`, while a Hölder
bound at any exponent `s < 1/2` is available at exactly `H²` of `ω`, hence at
the `H³` of `u` that the BKM statement carries.  The exponent certified here
is `s = 1/4`: the frequency-side bound is the single global pointwise
inequality `min(2, 2π|ξ|h)² ≤ 4·√(2π|ξ|h)`, so the only dimensional input is
the weighted moment `∫ (1+‖ξ‖²)⁻²·√‖ξ‖ dξ < ∞` (radially
`∫₀^∞ r^{5/2}/(1+r²)² dr`, tail `∫^∞ r^{-3/2} dr`), discharged by the same
Japanese-bracket integrability that powers the Agmon chain, at exponent
`7/2 > 3`.

References: S. Agmon, *Lectures on Elliptic Boundary Value Problems*, Van
Nostrand 1965; Stein, *Singular Integrals and Differentiability Properties of
Functions*, Princeton 1970, Ch. V §3 (Bessel potentials) and Ch. II §4.
-/

/-- The Fourier character is `4π`-Lipschitz in its argument below the trivial
bound: `‖𝐞 a - 𝐞 b‖ ≤ min 2 (4π|a - b|)`.  The cap `2` handles the
large-phase regime; on `2π|a-b| ≤ 1` the linear bound is
`Complex.norm_exp_sub_one_le`. -/
private theorem norm_fourierChar_coe_sub_le (a b : ℝ) :
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖
      ≤ min 2 (4 * Real.pi * |a - b|) := by
  have hnorm1 : ∀ θ : ℝ, ‖(Real.fourierChar θ : ℂ)‖ = 1 := by
    intro θ
    exact mem_sphere_zero_iff_norm.mp (Real.fourierChar θ).property
  have hfactor : (Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)
      = (Real.fourierChar b : ℂ) * ((Real.fourierChar (a - b) : ℂ) - 1) := by
    have h1 : (Real.fourierChar a : ℂ)
        = (Real.fourierChar b : ℂ) * (Real.fourierChar (a - b) : ℂ) := by
      rw [← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul,
        show b + (a - b) = a from by ring]
    rw [h1]; ring
  rw [hfactor, norm_mul, hnorm1 b, one_mul]
  have htriv : ‖(Real.fourierChar (a - b) : ℂ) - 1‖ ≤ 2 := by
    calc ‖(Real.fourierChar (a - b) : ℂ) - 1‖
        ≤ ‖(Real.fourierChar (a - b) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm1 (a - b), norm_one]; norm_num
  have hlin : 2 * Real.pi * |a - b| ≤ 1 →
      ‖(Real.fourierChar (a - b) : ℂ) - 1‖ ≤ 4 * Real.pi * |a - b| := by
    intro hz
    have harg : ‖(↑(2 * Real.pi * (a - b)) : ℂ) * Complex.I‖ = 2 * Real.pi * |a - b| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [Real.fourierChar_apply]
    calc ‖Complex.exp (↑(2 * Real.pi * (a - b)) * Complex.I) - 1‖
        ≤ 2 * ‖(↑(2 * Real.pi * (a - b)) : ℂ) * Complex.I‖ :=
          Complex.norm_exp_sub_one_le (harg ▸ hz)
      _ = 4 * Real.pi * |a - b| := by rw [harg]; ring
  by_cases hc : 2 * Real.pi * |a - b| ≤ 1
  · exact le_min htriv (hlin hc)
  · have h2 : (2 : ℝ) ≤ 4 * Real.pi * |a - b| := by
      have hc' := not_le.mp hc
      nlinarith [Real.pi_pos, abs_nonneg (a - b)]
    rw [min_eq_left h2]
    exact htriv

/-- The squared minimum bound underlying the Hölder exponent `1/4`:
`(min 2 (2t))² ≤ 4√t` for `t ≥ 0`.  This one inequality replaces the
frequency split at `|ξ| ~ h⁻¹`: the near-field uses `min(2, 2t) ≤ 2t` and the
far field `min ≤ 2`, and `t² ≤ √t` on `[0,1]` interpolates between them at
the price of the sub-endpoint exponent. -/
private theorem min_two_two_mul_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (min 2 (2 * t)) ^ 2 ≤ 4 * Real.sqrt t := by
  have h1 : min 2 (2 * t) ≤ 2 * min 1 t := by
    by_cases hc : t ≤ 1
    · rw [min_eq_right (by nlinarith : 2 * t ≤ 2), min_eq_right hc]
    · rw [not_le] at hc
      rw [min_eq_left (by nlinarith : (2 : ℝ) ≤ 2 * t), min_eq_left (le_of_lt hc)]
      norm_num
  have h2 : (min 1 t) ^ 2 ≤ Real.sqrt t := by
    by_cases hc : t ≤ 1
    · rw [min_eq_right hc]
      have ht4 : t ^ 4 ≤ t := by
        have h3 : t ^ 3 ≤ 1 := pow_le_one₀ ht hc
        calc t ^ 4 = t * t ^ 3 := by ring
          _ ≤ t * 1 := mul_le_mul_of_nonneg_left h3 ht
          _ = t := mul_one t
      rw [show t ^ 2 = Real.sqrt ((t ^ 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      refine Real.sqrt_le_sqrt ?_
      rw [show (t ^ 2) ^ 2 = t ^ 4 from by ring]
      exact ht4
    · rw [not_le] at hc
      rw [min_eq_left (le_of_lt hc)]
      calc (1 : ℝ) ^ 2 = 1 := by ring
        _ = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt t := Real.sqrt_le_sqrt (le_of_lt hc)
  have hnn : (0 : ℝ) ≤ min 2 (2 * t) := le_min (by norm_num) (by nlinarith)
  calc (min 2 (2 * t)) ^ 2 ≤ (2 * min 1 t) ^ 2 := pow_le_pow_left₀ hnn h1 2
    _ = 4 * (min 1 t) ^ 2 := by ring
    _ ≤ 4 * Real.sqrt t := mul_le_mul_of_nonneg_left h2 (by norm_num)

/-- The quartic Bessel weight on the Euclidean model (the `EuclSpace`
counterpart of `integrable_inv_one_add_normSq_sq`). -/
private theorem integrable_bessel_sq_inv_eucl :
    Integrable (fun ξ : EuclSpace => (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) volume := by
  have hfr : (Module.finrank ℝ EuclSpace : ℝ) < 4 := by
    have h3 : Module.finrank ℝ EuclSpace = 3 := by simp
    rw [h3]; norm_num
  have h := integrable_rpow_neg_one_add_norm_sq (E := EuclSpace) (μ := volume)
    (r := 4) hfr
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  show ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2) = ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹
  rw [show (-(4 : ℝ)) / 2 = -(2 : ℕ) by norm_num, Real.rpow_neg (by positivity),
    Real.rpow_natCast]

/-- The Bessel-weighted half-moment is finite on `ℝ³`:
`ξ ↦ √‖ξ‖·(1+‖ξ‖²)⁻²` is integrable (radially `∫₀^∞ r^{5/2}(1+r²)⁻² dr`,
tail `∫^∞ r^{-3/2} dr`).  This is the only dimensional input to the Morrey
bound; it comes from the same Japanese-bracket integrability as the Agmon
weight, at exponent `7/2 > 3`. -/
private theorem integrable_sqrt_norm_mul_bessel_sq_inv :
    Integrable (fun ξ : EuclSpace => Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹)
      volume := by
  have hfr : (Module.finrank ℝ EuclSpace : ℝ) < 7 / 2 := by
    have h3 : Module.finrank ℝ EuclSpace = 3 := by simp
    rw [h3]; norm_num
  have h := integrable_rpow_neg_one_add_norm_sq (E := EuclSpace) (μ := volume)
    (r := 7 / 2) hfr
  have hcont : Continuous fun ξ : EuclSpace =>
      Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by
    refine (Real.continuous_sqrt.comp continuous_norm).mul ?_
    apply Continuous.inv₀
    · fun_prop
    · intro ξ; positivity
  refine h.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹‖
    ≤ (1 + ‖ξ‖ ^ 2) ^ (-(7 / 2 : ℝ) / 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hx : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have hw1 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  have hs1 : ‖ξ‖ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := by
    conv_lhs => rw [show ‖ξ‖ = Real.sqrt (‖ξ‖ ^ 2) from (Real.sqrt_sq hx).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖ξ‖])
  have hsqrt : Real.sqrt ‖ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (1 / 4 : ℝ) := by
    calc Real.sqrt ‖ξ‖ ≤ Real.sqrt (Real.sqrt (1 + ‖ξ‖ ^ 2)) := Real.sqrt_le_sqrt hs1
      _ = (1 + ‖ξ‖ ^ 2) ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hw1.le]
        congr 1
        norm_num
  calc Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹
      = Real.sqrt ‖ξ‖ * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℕ) : ℝ) := by
        rw [Real.rpow_neg hw1.le, Real.rpow_natCast]
    _ ≤ (1 + ‖ξ‖ ^ 2) ^ (1 / 4 : ℝ) * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hw1.le _)
    _ = (1 + ‖ξ‖ ^ 2) ^ (-(7 / 2) / 2 : ℝ) := by
        rw [← Real.rpow_add hw1, show ((1 : ℝ) / 4 + -(2 : ℕ)) = -(7 / 2) / 2 by norm_num]

/-- The quartic Bessel weight times the square of a continuous factor bounded
by `2` is integrable (dominated by `4` times the weight). -/
private theorem integrable_bessel_mul_sq {φ : EuclSpace → ℝ} (hφcont : Continuous φ)
    (hφnn : ∀ ξ, 0 ≤ φ ξ) (hφ2 : ∀ ξ, φ ξ ≤ 2) :
    Integrable (fun ξ : EuclSpace => (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2)
      volume := by
  have hcont : Continuous fun ξ : EuclSpace => (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2 := by
    refine (Continuous.inv₀ (by fun_prop) (fun ξ => by positivity)).mul (hφcont.pow 2)
  refine (integrable_bessel_sq_inv_eucl.const_mul 4).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖(((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2‖ ≤ 4 * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hφsq : (φ ξ) ^ 2 ≤ 4 := by
    have := pow_le_pow_left₀ (hφnn ξ) (hφ2 ξ) 2
    nlinarith
  calc (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2 ≤ (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * 4 :=
        mul_le_mul_of_nonneg_left hφsq (by positivity)
    _ = 4 * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by ring

/-- Cauchy–Schwarz against the Bessel weight with an extra bounded factor
kept in the weight term: for continuous `0 ≤ φ ≤ 2` and nonneg `ψ` with
`(1+‖ξ‖²)·ψ` in `L²`,

  `∫ φ·ψ ≤ √(∫ (1+‖ξ‖²)⁻²·φ²) · √(∫ ((1+‖ξ‖²)·ψ)²)`.

This is `integral_le_besselWeightMass_mul_sqrt` with the phase factor
retained in the first factor — the `L²` pairing is unchanged; only the first
factor is sharpened from the full weight mass to the phase-weighted one. -/
private theorem integral_phase_mul_le_sqrt_weighted
    {φ : EuclSpace → ℝ} (hφcont : Continuous φ) (hφnn : ∀ ξ, 0 ≤ φ ξ)
    (hφ2 : ∀ ξ, φ ξ ≤ 2)
    {ψ : EuclSpace → ℝ} (hψnn : ∀ ξ, 0 ≤ ψ ξ)
    (hψmem : MemLp (fun ξ : EuclSpace => ((1 : ℝ) + ‖ξ‖ ^ 2) * ψ ξ) 2 volume) :
    ∫ ξ : EuclSpace, φ ξ * ψ ξ ≤
      Real.sqrt (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2) *
        Real.sqrt (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) * ψ ξ) ^ 2) := by
  have hpq : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hfmem : MemLp (fun ξ : EuclSpace => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ * φ ξ) 2 volume := by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact ((Continuous.inv₀ (by fun_prop) (fun ξ => by positivity)).mul
        hφcont).aestronglyMeasurable
    · refine (integrable_bessel_mul_sq hφcont hφnn hφ2).congr
        (Filter.Eventually.of_forall fun ξ => ?_)
      show (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2
        = (((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ * φ ξ) ^ 2
      rw [mul_pow, inv_pow]
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hpq
    (f := fun ξ : EuclSpace => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ * φ ξ)
    (g := fun ξ : EuclSpace => ((1 : ℝ) + ‖ξ‖ ^ 2) * ψ ξ)
    (Filter.Eventually.of_forall fun ξ => mul_nonneg (by positivity) (hφnn ξ))
    (Filter.Eventually.of_forall fun ξ => mul_nonneg (by positivity) (hψnn ξ))
    (by simpa using hfmem) (by simpa using hψmem)
  have hprod : ∀ ξ : EuclSpace,
      ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ * φ ξ * (((1 : ℝ) + ‖ξ‖ ^ 2) * ψ ξ) = φ ξ * ψ ξ := by
    intro ξ
    field_simp
  simp only [hprod] at key
  have hrw : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
    intro y
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hrw] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [mul_pow, inv_pow] using key

/-- The phase-weighted Bessel mass is `O(√h)`: with `w = (1+‖ξ‖²)⁻²`,
`∫ w·min(2, 4π‖ξ‖h)² ≤ 4√(2πh)·∫ w·√‖ξ‖`.  This is the whole frequency
localization of the Morrey argument in one global pointwise step. -/
private theorem integral_weighted_min_sq_le {h : ℝ} (hh : 0 ≤ h) :
    ∫ ξ : EuclSpace,
        (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (min 2 (4 * Real.pi * ‖ξ‖ * h)) ^ 2
      ≤ 4 * Real.sqrt (2 * Real.pi * h) *
          ∫ ξ : EuclSpace, Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by
  have hmincont : Continuous fun ξ : EuclSpace => min 2 (4 * Real.pi * ‖ξ‖ * h) := by
    fun_prop
  have hpt : ∀ ξ : EuclSpace,
      (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (min 2 (4 * Real.pi * ‖ξ‖ * h)) ^ 2
        ≤ 4 * Real.sqrt (2 * Real.pi * h) *
            (Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) := by
    intro ξ
    have hsq := min_two_two_mul_sq_le (t := 2 * Real.pi * ‖ξ‖ * h) (by positivity)
    rw [show 2 * (2 * Real.pi * ‖ξ‖ * h) = 4 * Real.pi * ‖ξ‖ * h from by ring] at hsq
    have hsqrt : Real.sqrt (2 * Real.pi * ‖ξ‖ * h)
        = Real.sqrt (2 * Real.pi * h) * Real.sqrt ‖ξ‖ := by
      rw [show 2 * Real.pi * ‖ξ‖ * h = (2 * Real.pi * h) * ‖ξ‖ from by ring]
      exact Real.sqrt_mul (by positivity) _
    rw [hsqrt] at hsq
    calc (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (min 2 (4 * Real.pi * ‖ξ‖ * h)) ^ 2
        ≤ (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ *
            (4 * (Real.sqrt (2 * Real.pi * h) * Real.sqrt ‖ξ‖)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 4 * Real.sqrt (2 * Real.pi * h) *
            (Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) := by ring
  have hintR : Integrable (fun ξ : EuclSpace =>
      4 * Real.sqrt (2 * Real.pi * h) *
        (Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹)) volume :=
    integrable_sqrt_norm_mul_bessel_sq_inv.const_mul _
  calc ∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (min 2 (4 * Real.pi * ‖ξ‖ * h)) ^ 2
      ≤ ∫ ξ : EuclSpace, 4 * Real.sqrt (2 * Real.pi * h) *
          (Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) :=
        integral_mono_ae
          (integrable_bessel_mul_sq hmincont (fun ξ => le_min (by norm_num) (by positivity))
            (fun ξ => min_le_left _ _))
          hintR (Filter.Eventually.of_forall hpt)
    _ = 4 * Real.sqrt (2 * Real.pi * h) *
          ∫ ξ : EuclSpace, Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ :=
        integral_const_mul _ _

/-- The inverse Fourier transform difference, bounded by the phase-twisted
`L¹` mass of the transform: `𝓕⁻g(y₁) - 𝓕⁻g(y₂) = ∫ (𝐞⟪ξ,y₁⟫ - 𝐞⟪ξ,y₂⟫)·g(ξ)
dξ`, then norm of integral ≤ integral of norm. -/
private theorem norm_fourierInv_sub_le {g : EuclSpace → CxSpace}
    (hgcont : Continuous g) (hg : Integrable g volume) (y₁ y₂ : EuclSpace) :
    ‖𝓕⁻ g y₁ - 𝓕⁻ g y₂‖ ≤
      ∫ ξ : EuclSpace,
        ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
          * ‖g ξ‖ := by
  have hφcont : Continuous fun ξ : EuclSpace =>
      ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
        * ‖g ξ‖ := by
    fun_prop
  have hint : ∀ y : EuclSpace,
      Integrable (fun ξ : EuclSpace => Real.fourierChar (inner ℝ ξ y) • g ξ) volume := by
    intro y
    have h := (Real.fourierIntegral_convergent_iff (μ := volume) (f := g) (-y)).mpr hg
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    show Real.fourierChar (-inner ℝ ξ (-y)) • g ξ = Real.fourierChar (inner ℝ ξ y) • g ξ
    rw [inner_neg_right, neg_neg]
  rw [Real.fourierInv_eq, Real.fourierInv_eq, ← integral_sub (hint y₁) (hint y₂)]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine integral_mono_ae ((hint y₁).sub (hint y₂)).norm
    ((hg.norm.const_mul 2).mono' hφcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_))
    (Filter.Eventually.of_forall fun ξ => ?_)
  · have hb : ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ)
        - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖ ≤ 2 :=
      le_trans (norm_fourierChar_coe_sub_le _ _) (min_le_left _ _)
    show ‖‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
        * ‖g ξ‖‖ ≤ 2 * ‖g ξ‖
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · show ‖Real.fourierChar (inner ℝ ξ y₁) • g ξ
        - Real.fourierChar (inner ℝ ξ y₂) • g ξ‖
      ≤ ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
        * ‖g ξ‖
    have heq : Real.fourierChar (inner ℝ ξ y₁) • g ξ
        - Real.fourierChar (inner ℝ ξ y₂) • g ξ
        = ((Real.fourierChar (inner ℝ ξ y₁) : ℂ)
            - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)) • g ξ := by
      rw [Circle.smul_def, Circle.smul_def, ← sub_smul]
    rw [heq, norm_smul]

/-- **Morrey–Agmon on the Euclidean model (certified, no sorry).**  For a
Schwartz map `v : 𝓢(EuclSpace, CxSpace)` the Hölder seminorm at exponent
`1/4` is controlled by the `H²` energy: the inversion difference is
phase-twisted (`norm_fourierInv_sub_le`), the phase is `min(2, 4π‖ξ‖h)`
(`norm_fourierChar_coe_sub_le` with `abs_real_inner_le_norm`), Cauchy–Schwarz
against the Bessel weight splits off `√(∫ w·min²) = O(h^{1/4})`
(`integral_weighted_min_sq_le`), and the surviving weighted `L²` mass of
`𝓕 v` is weighted Plancherel (`exists_weighted_plancherel`). -/
private theorem exists_morrey_euclModel :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (v : SV) (y₁ y₂ : EuclSpace),
      ‖v y₁ - v y₂‖ ≤
        C₁ * Real.sqrt (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
          ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2) * ‖y₁ - y₂‖ ^ (1 / 4 : ℝ) := by
  obtain ⟨Cp, hCppos, hplan⟩ := exists_weighted_plancherel
  set M : ℝ := ∫ ξ : EuclSpace, Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ with hMdef
  have hMnn : 0 ≤ M := integral_nonneg fun ξ => by positivity
  refine ⟨Real.sqrt (4 * Real.sqrt (2 * Real.pi)) * Real.sqrt M * Real.sqrt Cp + 1,
    by positivity, fun v y₁ y₂ => ?_⟩
  have hv : ∀ y : EuclSpace, v y = 𝓕⁻ (⇑(𝓕 v : SV)) y := by
    intro y
    have hinv : (𝓕⁻ (𝓕 v : SV) : SchwartzMap EuclSpace CxSpace) = v :=
      FourierPair.fourierInv_fourier_eq v
    conv_lhs => rw [← hinv]
    rw [SchwartzMap.fourierInv_coe]
  have hgint : Integrable (⇑(𝓕 v : SV)) volume := (𝓕 v : SV).integrable
  rw [hv y₁, hv y₂]
  set h : ℝ := ‖y₁ - y₂‖ with hhdef
  have hhnn : 0 ≤ h := norm_nonneg _
  have hφcont : Continuous fun ξ : EuclSpace =>
      ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖ := by
    fun_prop
  have hφmin : ∀ ξ : EuclSpace,
      ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
        ≤ min 2 (4 * Real.pi * ‖ξ‖ * h) := by
    intro ξ
    refine le_trans (norm_fourierChar_coe_sub_le _ _) (min_le_min le_rfl ?_)
    have hinner : |inner ℝ ξ y₁ - inner ℝ ξ y₂| ≤ ‖ξ‖ * h := by
      rw [← inner_sub_right]
      exact abs_real_inner_le_norm _ _
    calc 4 * Real.pi * |inner ℝ ξ y₁ - inner ℝ ξ y₂|
        ≤ 4 * Real.pi * (‖ξ‖ * h) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 4 * Real.pi * ‖ξ‖ * h := by ring
  have hcs := integral_phase_mul_le_sqrt_weighted hφcont (fun ξ => norm_nonneg _)
    (fun ξ => le_trans (norm_fourierChar_coe_sub_le _ _) (min_le_left _ _))
    (fun ξ => norm_nonneg _) (memLp_weight_fourier v)
  have hA : (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ *
        ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖ ^ 2)
      ≤ ∫ ξ : EuclSpace,
        (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (min 2 (4 * Real.pi * ‖ξ‖ * h)) ^ 2 :=
    integral_mono_ae
      (integrable_bessel_mul_sq hφcont (fun ξ => norm_nonneg _)
        (fun ξ => le_trans (norm_fourierChar_coe_sub_le _ _) (min_le_left _ _)))
      (integrable_bessel_mul_sq (by fun_prop) (fun ξ => le_min (by norm_num) (by positivity))
        (fun ξ => min_le_left _ _))
      (Filter.Eventually.of_forall fun ξ =>
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hφmin ξ) 2) (by positivity))
  have hfirst := le_trans hA (integral_weighted_min_sq_le hhnn)
  have hsecond : (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) * ‖(𝓕 v : SV) ξ‖) ^ 2)
      ≤ Cp * (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
        ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2) := hplan v
  have hsqrtM : Real.sqrt (4 * Real.sqrt (2 * Real.pi * h) * M)
      = Real.sqrt (4 * Real.sqrt (2 * Real.pi)) * Real.sqrt M * h ^ (1 / 4 : ℝ) := by
    have e1 : Real.sqrt (2 * Real.pi * h) = Real.sqrt (2 * Real.pi) * Real.sqrt h :=
      Real.sqrt_mul (by positivity) _
    rw [e1]
    rw [show (4 : ℝ) * (Real.sqrt (2 * Real.pi) * Real.sqrt h) * M
        = (4 * Real.sqrt (2 * Real.pi) * M) * Real.sqrt h from by ring]
    rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hMnn),
      Real.sqrt_mul (mul_nonneg (by positivity) (Real.sqrt_nonneg _))]
    have e3 : Real.sqrt (Real.sqrt h) = h ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hhnn]
      congr 1
      norm_num
    rw [e3]
  have hsqrtCp : Real.sqrt (Cp * (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
        ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2))
      = Real.sqrt Cp * Real.sqrt (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
        ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2) :=
    Real.sqrt_mul hCppos.le _
  calc ‖𝓕⁻ (⇑(𝓕 v : SV)) y₁ - 𝓕⁻ (⇑(𝓕 v : SV)) y₂‖
      ≤ ∫ ξ : EuclSpace,
          ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
            * ‖(𝓕 v : SV) ξ‖ :=
        norm_fourierInv_sub_le (𝓕 v : SV).continuous hgint y₁ y₂
    _ ≤ Real.sqrt (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ *
            ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ)
              - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖ ^ 2) *
          Real.sqrt (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) * ‖(𝓕 v : SV) ξ‖) ^ 2) := hcs
    _ ≤ Real.sqrt (4 * Real.sqrt (2 * Real.pi * h) * M) *
          Real.sqrt (Cp * (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
            ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2)) :=
        mul_le_mul (Real.sqrt_le_sqrt hfirst) (Real.sqrt_le_sqrt hsecond)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (4 * Real.sqrt (2 * Real.pi)) * Real.sqrt M * Real.sqrt Cp) *
          Real.sqrt (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
            ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2) * h ^ (1 / 4 : ℝ) := by
        rw [hsqrtM, hsqrtCp]; ring
    _ ≤ (Real.sqrt (4 * Real.sqrt (2 * Real.pi)) * Real.sqrt M * Real.sqrt Cp + 1) *
          Real.sqrt (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
            ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2) * h ^ (1 / 4 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hhnn _)
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/-- **[DERIVED from the certified Fourier chain above.]**  **Morrey–Agmon:
`H²(ℝ³) ↪ C^{0,1/4}` for Schwartz fields (certified, no sorry).**  The
Hölder seminorm at exponent `1/4` is dominated by the `H²` norm:
`‖u x - u y‖ ≤ C·√(sobolevH2NormSq u)·‖x - y‖^{1/4}` — the difference
companion of `exists_agmonSupBound` at the same derivative order.

This is the near-field input the BKM log inequality consumes through the
cancellation `ω(x-z) - ω(x)`: applied to the vorticity components (whose `H²`
energies are bounded by `sobolevH3NormSq u`, one derivative up), it upgrades
the certified near-field layer `integral_norm_mul_bsKernelScalar_ball_le`
from `O(ρ·‖∇ω‖∞)` — which would cost `H⁴` — to `O(ρ^{1/4}·‖u‖_{H³})`, the
order the cutoff optimisation at `ρ ≈ ‖u‖_{H³}^{-4}` turns into the
`log(e + ‖u‖_{H³})` factor.  What remains residual for
`exists_biotSavartLogTextbook` is the Biot–Savart representation
`∇u = PV(∇K ∗ ω)` itself (including its local term). -/
theorem exists_agmonMorreyBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : SchwartzVelocity) (x y : Space),
      ‖(⇑u) x - (⇑u) y‖ ≤
        C * Real.sqrt (sobolevH2NormSq u) * ‖x - y‖ ^ (1 / 4 : ℝ) := by
  obtain ⟨C₁, hC₁pos, hmor⟩ := exists_morrey_euclModel
  obtain ⟨C₂, hC₂pos, hmod⟩ := exists_euclModel_h2_bound
  refine ⟨C₁ * Real.sqrt C₂ * ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ) + 1,
    by positivity, fun u x y => ?_⟩
  have hnorm : ‖(⇑u) x - (⇑u) y‖
      ≤ ‖euclModel u (euclCoords.symm x) - euclModel u (euclCoords.symm y)‖ := by
    have heq : euclModel u (euclCoords.symm x) - euclModel u (euclCoords.symm y)
        = realToCx ((⇑u) x - (⇑u) y) := by
      rw [euclModel_apply, euclModel_apply, ContinuousLinearEquiv.apply_symm_apply,
        ContinuousLinearEquiv.apply_symm_apply]
      exact (map_sub realToCx _ _).symm
    rw [heq]
    exact norm_le_norm_realToCx _
  have hdist : ‖euclCoords.symm x - euclCoords.symm y‖
      ≤ ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ * ‖x - y‖ := by
    have hh := ContinuousLinearMap.le_opNorm
      (euclCoords.symm : Space →L[ℝ] EuclSpace) (x - y)
    rwa [ContinuousLinearEquiv.coe_coe, map_sub] at hh
  have hpow : ‖euclCoords.symm x - euclCoords.symm y‖ ^ (1 / 4 : ℝ)
      ≤ ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ)
          * ‖x - y‖ ^ (1 / 4 : ℝ) := by
    calc ‖euclCoords.symm x - euclCoords.symm y‖ ^ (1 / 4 : ℝ)
        ≤ (‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ * ‖x - y‖) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) hdist (by norm_num)
      _ = ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ)
            * ‖x - y‖ ^ (1 / 4 : ℝ) :=
          Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
  calc ‖(⇑u) x - (⇑u) y‖
      ≤ ‖euclModel u (euclCoords.symm x) - euclModel u (euclCoords.symm y)‖ := hnorm
    _ ≤ C₁ * Real.sqrt (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
            ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖ ^ 2)
          * ‖euclCoords.symm x - euclCoords.symm y‖ ^ (1 / 4 : ℝ) :=
        hmor _ _ _
    _ ≤ C₁ * Real.sqrt (C₂ * sobolevH2NormSq u)
          * (‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ)
            * ‖x - y‖ ^ (1 / 4 : ℝ)) := by
        refine mul_le_mul ?_ hpow (Real.rpow_nonneg (norm_nonneg _) _)
          (mul_nonneg hC₁pos.le (Real.sqrt_nonneg _))
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (hmod u)) hC₁pos.le
    _ = (C₁ * Real.sqrt C₂ * ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ))
          * Real.sqrt (sobolevH2NormSq u) * ‖x - y‖ ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_mul hC₂pos.le]; ring
    _ ≤ (C₁ * Real.sqrt C₂ * ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ) + 1)
          * Real.sqrt (sobolevH2NormSq u) * ‖x - y‖ ^ (1 / 4 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)


end Navier.Analysis.BealeKatoMajda
