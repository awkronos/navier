import Navier.Analysis.WeightIntegrability
import Navier.Analysis.BKMLogBootstrap
import Navier.Analysis.FourierWeightedPlancherel

/-!
# Fourier majorant infrastructure for the `H³(ℝ³) ↪ L^∞` Sobolev embedding

This is the reusable analytic core of the Beale–Kato–Majda Sobolev-embedding
route.  The certified interface `SobolevEmbedding.sobolev_domination_of_intermediate`
turns two analytic bounds on a Fourier-side majorant `Q` into the embedding
`‖u‖_∞ ≤ C·√Ms`.  This file supplies the *first* of those two bounds
kernel-cleanly, and — as of this file's closure of
`exists_scalarFourierSpectralData` — the *second* one as well (Fourier inversion
and weighted Plancherel), so the embedding `fourierMajorant_embedding` is now
proved outright with no `sorry` and no project axiom.

## Certified here (no sorry)

* `weightConst := ∫ (1+|ξ|²)^{-3} dξ`, `weightConst_pos` — the Cauchy–Schwarz
  weight constant, finite/positive by consuming
  `WeightIntegrability.sobWeight_integrable`.
* `fourierSupConst := √weightConst` (the `C₁` of the sup bound), positive.
* `spectralMajorant F := ∫ (F ξ)²·(1+|ξ|²)³ dξ` — the `Q`-functional written on a
  spectral density `F` (classically `F ξ = ‖û(ξ)‖`); nonnegative.
* `cauchySchwarz_supMajorant` — **the analytic engine**: for any nonnegative
  spectral density `F` whose weighted `L²` mass is finite,
  `∫ F ≤ fourierSupConst·√(spectralMajorant F)`.  This is Cauchy–Schwarz against
  the integrable weight `(1+|ξ|²)^{-3}`; it is exactly the `∫‖û‖ ≤ C₁·√(Q u)` step
  of the classical embedding, minus Fourier inversion.
* `supBound_of_spectralData` — packages the sup bound `‖u x‖ ≤ C₁·√(Q u)` from a
  spectral density that dominates `u` pointwise (Fourier inversion `|u(x)| ≤ ∫‖û‖`).
* `memLp_sqrt_sobWeight`, `integrable_spectralMajorant_integrand`,
  `integrable_of_memLp_weighted`, `memLp_weighted_sum` — the weighted-`L²`
  calculus: the single hypothesis `F·(sobWeight)^{-1/2} ∈ L²` yields both `F ∈ L¹`
  (Hölder against the weight) and `F²·(sobWeight)^{-1} ∈ L¹`, and is stable under
  finite sums.  These make `spectralMajorant F` and `∫ F` genuine finite integrals
  rather than junk values.
* `spectralMajorant_const_mul` (`Q(a·F) = a²·Q F`, unconditional),
  `spectralMajorant_add_le` (`Q(F+G) ≤ 2(Q F + Q G)`, constant sharp) and
  `spectralMajorant_sum_three_le` (`Q(∑_{i<3}Fᵢ) ≤ 3∑ᵢ Q Fᵢ`) — the majorant's
  algebra.
* `componentCLM`, `spaceProj` — the two norm-`≤ 1` contractions (coordinate
  projection `ℝ³ → ℝ ↪ ℂ` for the Pi sup norm; the Euclidean-to-sup comparison).
* `scalarComponent`, `euclidComponent` — the real component of `u` as a `ℂ`-valued
  Schwartz map on `Space`, then on the Euclidean model, via Mathlib's
  `SchwartzMap.postcompCLM` and `toEuclid`.
* `integrable_normSq_iteratedFDeriv` — every order-`n` derivative energy of a
  Schwartz map is a genuine finite integral.
* `norm_iteratedFDeriv_euclidComponent_le`, `integral_spaceProj`,
  `integral_normSq_iteratedFDeriv_euclidComponent_le` — the derivative comparison
  and its measure transport back to `Space`.
* `norm_iteratedLineDeriv_le`, `norm_pd_le`, `norm_pd2_le`, `norm_pd3_le` — iterated
  coordinate line derivatives are dominated by the full order-`n` derivative, via
  `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`.
* `componentDensity`, `abs_component_le_integral_componentDensity` — the spectral
  density `‖𝓕(uᵢ)‖` and its Fourier-inversion domination.
* `spectralMajorant_componentDensity_eq` — the binomial fold
  `(1+|ξ|²)³ = 1+3|ξ|²+3|ξ|⁴+|ξ|⁶` against the four weighted Plancherel rungs.
* `spectralMajorant_componentDensity_le` — the `H³` bound with constant `27`.
* `exists_scalarFourierSpectralData`, `exists_fourierSpectralData`,
  `exists_fourierMajorant_intermediate`, `fourierMajorant_embedding` — the
  embedding chain, kernel-clean.
* `exists_spectralData_of_components` — **the componentwise reduction**: three
  scalar densities, one per real component of `u`, assemble into a single vector
  density with majorant `9·B`.  `Space = Fin 3 → ℝ` is sup-normed, so componentwise
  domination is sup-norm domination.  This is what reduces
  `exists_fourierSpectralData` to the *scalar* residual
  `exists_scalarFourierSpectralData`.

Weight convention: the sibling `sobWeight ξ = (1+|ξ|²)^{-3}` uses `(1+|ξ|²)`, not
the `(1+4π²|ξ|²)` of the raw Fourier statement.  The two differ by a constant
absorbed into the Plancherel constant `C₂` (project convention, cf.
`BKMLogBootstrap` norm-comparison note).  We keep `(1+|ξ|²)` throughout so the
Cauchy–Schwarz constant is *exactly* `√(∫ sobWeight)`.

Reference: Agmon; Stein, *Singular Integrals* III.2; Majda–Bertozzi Lemma 3.2.
Axiom set: `⊆ {propext, Classical.choice, Quot.sound}` for certified decls.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory SchwartzMap LineDeriv
open scoped BigOperators FourierTransform SchwartzMap

namespace Navier.Analysis.FourierMajorant

open Navier
open Navier.Analysis.WeightIntegrability
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.FourierWeightedPlancherel

/-!
## The Cauchy–Schwarz weight constant
-/

/-- The Sobolev weight `(1+|ξ|²)^{-3}` is continuous on `ℝ³` (denominator `≥ 1`). -/
theorem sobWeight_continuous : Continuous sobWeight := by
  have hd : Continuous (fun ξ : Space => 1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) := by fun_prop
  exact (hd.inv₀ (fun ξ => by positivity)).pow 3

/-- **The Cauchy–Schwarz weight constant** `C₁² = ∫_{ℝ³} (1+|ξ|²)^{-3} dξ`, finite
by `WeightIntegrability.sobWeight_integrable`. -/
def weightConst : ℝ := ∫ ξ : Space, sobWeight ξ

/-- The weight constant is nonnegative. -/
theorem weightConst_nonneg : 0 ≤ weightConst :=
  integral_nonneg (fun ξ => sobWeight_nonneg ξ)

/-- **The weight constant is strictly positive.**  The integrand is continuous,
integrable, nonnegative, and positive at `ξ = 0`, so the integral is positive over
the open-positive Lebesgue measure on `ℝ³`. -/
theorem weightConst_pos : 0 < weightConst :=
  integral_pos_of_integrable_nonneg_nonzero (x := (0 : Space))
    sobWeight_continuous sobWeight_integrable
    (fun ξ => sobWeight_nonneg ξ) (ne_of_gt (sobWeight_pos 0))

/-- **The sup-bound constant** `C₁ = √(∫ (1+|ξ|²)^{-3} dξ)`. -/
def fourierSupConst : ℝ := Real.sqrt weightConst

/-- The sup-bound constant is strictly positive. -/
theorem fourierSupConst_pos : 0 < fourierSupConst :=
  Real.sqrt_pos.mpr weightConst_pos

/-!
## The spectral majorant functional
-/

/-- **The Fourier-side majorant functional on a spectral density** `F`
(classically `F ξ = ‖û(ξ)‖`):
`Q F = ∫ (F ξ)²·(1+|ξ|²)³ dξ = ∫ (F ξ)²·(sobWeight ξ)⁻¹ dξ`.  This is the
Bessel-potential `H³` majorant; the weight is the reciprocal of the integrable
Cauchy–Schwarz weight. -/
def spectralMajorant (F : Space → ℝ) : ℝ :=
  ∫ ξ : Space, (F ξ) ^ 2 * (sobWeight ξ)⁻¹

/-- The spectral majorant is nonnegative. -/
theorem spectralMajorant_nonneg (F : Space → ℝ) : 0 ≤ spectralMajorant F :=
  integral_nonneg fun ξ =>
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (sobWeight_nonneg ξ))


/-- **The reciprocal Sobolev weight is the degree-3 Bessel polynomial:**
`(sobWeight ξ)⁻¹ = (1+|ξ|²)³` with `|ξ|² = ξ₀²+ξ₁²+ξ₂²`.  Lets a consumer see the
majorant weight as a polynomial in the frequency variable. -/
theorem sobWeightInv_eq (ξ : Space) :
    (sobWeight ξ)⁻¹ = (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) ^ 3 := by
  rw [sobWeight, inv_pow, inv_inv]

/-!
## Weighted-`L²` calculus: integrability and the majorant's algebra

The spectral density hypothesis carried through the whole route is
`MemLp (F·(sobWeight)^{-1/2}) 2`.  These leaves turn that single hypothesis into
the two integrability facts every assembly step needs (`F ∈ L¹` and
`F²·(sobWeight)^{-1} ∈ L¹`) and record how `spectralMajorant` behaves under
scaling and finite sums — the exact algebra consumed when the three real
components of a velocity field are recombined into one density.
-/

/-- **The square root of the Sobolev weight lies in `L²`.**  `(√(sobWeight ξ))² =
sobWeight ξ` and `sobWeight ∈ L¹`, so the Hölder partner of a weighted density is
itself square-integrable.  (Extracted from the Cauchy–Schwarz engine so downstream
Hölder arguments reuse it rather than re-deriving it.) -/
theorem memLp_sqrt_sobWeight :
    MemLp (fun ξ : Space => Real.sqrt (sobWeight ξ)) 2 volume := by
  have hcont : Continuous (fun ξ : Space => Real.sqrt (sobWeight ξ)) :=
    Real.continuous_sqrt.comp sobWeight_continuous
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  have hsq : (fun ξ : Space => (Real.sqrt (sobWeight ξ)) ^ 2) = sobWeight := by
    funext ξ; exact Real.sq_sqrt (sobWeight_nonneg ξ)
  rw [hsq]; exact sobWeight_integrable

/-- **The `spectralMajorant` integrand of a weighted-`L²` density is integrable.**
`(F·√(sobWeight)^{-1})² = F²·(sobWeight)^{-1}` pointwise, so the `L²` hypothesis
is exactly integrability of the majorant integrand.  This makes
`spectralMajorant F` a genuine (finite) integral rather than a junk value. -/
theorem integrable_spectralMajorant_integrand {F : Space → ℝ}
    (hmem : MemLp (fun ξ => F ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume) :
    Integrable (fun ξ : Space => (F ξ) ^ 2 * (sobWeight ξ)⁻¹) volume := by
  refine ((memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem).congr ?_
  filter_upwards with ξ
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr (sobWeight_nonneg ξ))]

/-- **A weighted-`L²` spectral density is itself integrable.**  Hölder against
`memLp_sqrt_sobWeight`: `F = (F·√(sobWeight)^{-1})·√(sobWeight)` is a product of two
`L²` functions, hence `L¹`.  This is what makes `∫ F` finite and lets the
componentwise assembly compare component integrals. -/
theorem integrable_of_memLp_weighted {F : Space → ℝ}
    (hmem : MemLp (fun ξ => F ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume) :
    Integrable F volume := by
  refine (hmem.integrable_mul memLp_sqrt_sobWeight).congr ?_
  filter_upwards with ξ
  simp only [Pi.mul_apply]
  rw [mul_assoc, ← Real.sqrt_mul (inv_nonneg.mpr (sobWeight_nonneg ξ)),
      inv_mul_cancel₀ (ne_of_gt (sobWeight_pos ξ)), Real.sqrt_one, mul_one]

/-- **Scaling of the spectral majorant**: `Q(a·F) = a²·Q(F)`.  Unconditional — the
Bochner integral is `ℝ`-homogeneous whether or not the integrand is integrable. -/
theorem spectralMajorant_const_mul (a : ℝ) (F : Space → ℝ) :
    spectralMajorant (fun ξ => a * F ξ) = a ^ 2 * spectralMajorant F := by
  simp only [spectralMajorant]
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)

/-- **Weighted-`L²` membership is closed under finite sums.** -/
theorem memLp_weighted_sum {n : ℕ} (F : Fin n → Space → ℝ)
    (hF : ∀ i, MemLp (fun ξ => F i ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume) :
    MemLp (fun ξ => (∑ i, F i ξ) * Real.sqrt (sobWeight ξ)⁻¹) 2 volume := by
  refine MemLp.ae_eq ?_
    (memLp_finsetSum (Finset.univ : Finset (Fin n))
      (f := fun i ξ => F i ξ * Real.sqrt (sobWeight ξ)⁻¹) (fun i _ => hF i))
  filter_upwards with ξ
  rw [Finset.sum_mul]

/-- **Subadditivity of the spectral majorant with the sharp constant `2`:**
`Q(F+G) ≤ 2·(Q F + Q G)`.  Pointwise `(x+y)² ≤ 2x²+2y²` (equivalently
`0 ≤ (x-y)²`); the constant `2` is sharp and cannot be lowered to `1`
(`F = G` gives equality). -/
theorem spectralMajorant_add_le {F G : Space → ℝ}
    (hF : MemLp (fun ξ => F ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume)
    (hG : MemLp (fun ξ => G ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume) :
    spectralMajorant (fun ξ => F ξ + G ξ)
      ≤ 2 * (spectralMajorant F + spectralMajorant G) := by
  have hFi := integrable_spectralMajorant_integrand hF
  have hGi := integrable_spectralMajorant_integrand hG
  have hsum : MemLp (fun ξ => (F ξ + G ξ) * Real.sqrt (sobWeight ξ)⁻¹) 2 volume := by
    refine MemLp.ae_eq ?_ (hF.add hG)
    filter_upwards with ξ
    simp only [Pi.add_apply]
    ring
  have hSi := integrable_spectralMajorant_integrand hsum
  have hle : (fun ξ : Space => (F ξ + G ξ) ^ 2 * (sobWeight ξ)⁻¹)
      ≤ fun ξ : Space =>
          2 * ((F ξ) ^ 2 * (sobWeight ξ)⁻¹) + 2 * ((G ξ) ^ 2 * (sobWeight ξ)⁻¹) := by
    intro ξ
    have hw : (0 : ℝ) ≤ (sobWeight ξ)⁻¹ := inv_nonneg.mpr (sobWeight_nonneg ξ)
    nlinarith [mul_nonneg hw (sq_nonneg (F ξ - G ξ))]
  calc spectralMajorant (fun ξ => F ξ + G ξ)
      ≤ ∫ ξ : Space, (2 * ((F ξ) ^ 2 * (sobWeight ξ)⁻¹)
            + 2 * ((G ξ) ^ 2 * (sobWeight ξ)⁻¹)) :=
        integral_mono hSi ((hFi.const_mul 2).add (hGi.const_mul 2)) hle
    _ = 2 * (spectralMajorant F + spectralMajorant G) := by
        rw [integral_add (hFi.const_mul 2) (hGi.const_mul 2), integral_const_mul,
            integral_const_mul]
        simp only [spectralMajorant]
        ring

/-- **Three-term subadditivity of the spectral majorant:**
`Q(∑_{i<3} Fᵢ) ≤ 3·∑_{i<3} Q(Fᵢ)`.  Pointwise Cauchy–Schwarz
`(a+b+c)² ≤ 3(a²+b²+c²)`, sharp at `a = b = c`.  This is the exact algebra
consumed when the three real components of a velocity field are recombined
into a single spectral density. -/
theorem spectralMajorant_sum_three_le (F : Fin 3 → Space → ℝ)
    (hF : ∀ i, MemLp (fun ξ => F i ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume) :
    spectralMajorant (fun ξ => ∑ i, F i ξ) ≤ 3 * ∑ i, spectralMajorant (F i) := by
  have hi : ∀ i : Fin 3,
      Integrable (fun ξ : Space => (F i ξ) ^ 2 * (sobWeight ξ)⁻¹) volume :=
    fun i => integrable_spectralMajorant_integrand (hF i)
  have hSi := integrable_spectralMajorant_integrand (memLp_weighted_sum F hF)
  have hle : (fun ξ : Space => (∑ i, F i ξ) ^ 2 * (sobWeight ξ)⁻¹)
      ≤ fun ξ : Space => ∑ i : Fin 3, 3 * ((F i ξ) ^ 2 * (sobWeight ξ)⁻¹) := by
    intro ξ
    have hw : (0 : ℝ) ≤ (sobWeight ξ)⁻¹ := inv_nonneg.mpr (sobWeight_nonneg ξ)
    simp only [Fin.sum_univ_three]
    nlinarith [mul_nonneg hw (sq_nonneg (F 0 ξ - F 1 ξ)),
      mul_nonneg hw (sq_nonneg (F 1 ξ - F 2 ξ)),
      mul_nonneg hw (sq_nonneg (F 0 ξ - F 2 ξ))]
  calc spectralMajorant (fun ξ => ∑ i, F i ξ)
      ≤ ∫ ξ : Space, ∑ i : Fin 3, 3 * ((F i ξ) ^ 2 * (sobWeight ξ)⁻¹) :=
        integral_mono hSi
          (integrable_finsetSum _ fun i _ => (hi i).const_mul 3) hle
    _ = ∑ i : Fin 3, ∫ ξ : Space, 3 * ((F i ξ) ^ 2 * (sobWeight ξ)⁻¹) :=
        integral_finsetSum _ fun i _ => (hi i).const_mul 3
    _ = 3 * ∑ i : Fin 3, spectralMajorant (F i) := by
        simp only [spectralMajorant, integral_const_mul, ← Finset.mul_sum]

/-!
## The Cauchy–Schwarz sup-majorant (the analytic engine)
-/

/-- **The analytic engine of the Sobolev embedding.**  For a nonnegative spectral
density `F` whose weighted `L²` mass is finite (`F·(sobWeight)^{-1/2} ∈ L²`),
Cauchy–Schwarz against the integrable weight `(1+|ξ|²)^{-3}` gives

  `∫ F ≤ fourierSupConst · √(spectralMajorant F)`.

Classically `F ξ = ‖û(ξ)‖`, and this is the `∫‖û‖ ≤ √(∫weight)·√(Q u)` step of the
`H³(ℝ³) ↪ L^∞` embedding.  Kernel-clean; consumes `sobWeight_integrable`.

Citation: Cauchy–Schwarz / Hölder for Bochner integrals
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`, `p = q = 2`); Stein,
*Singular Integrals* III.2. -/
theorem cauchySchwarz_supMajorant {F : Space → ℝ} (hF : ∀ ξ, 0 ≤ F ξ)
    (hmem : MemLp (fun ξ => F ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume) :
    (∫ ξ : Space, F ξ) ≤ fourierSupConst * Real.sqrt (spectralMajorant F) := by
  set f : Space → ℝ := fun ξ => F ξ * Real.sqrt (sobWeight ξ)⁻¹ with hf_def
  set g : Space → ℝ := fun ξ => Real.sqrt (sobWeight ξ) with hg_def
  -- `g = √∘sobWeight` is continuous, hence a.e.-strongly-measurable.
  have hg_cont : Continuous g := Real.continuous_sqrt.comp sobWeight_continuous
  -- `g ∈ L²`: `(g ξ)² = sobWeight ξ` and `sobWeight` is integrable.
  have hg_mem : MemLp g 2 volume := by
    rw [memLp_two_iff_integrable_sq hg_cont.aestronglyMeasurable]
    have hsq : (fun ξ => (g ξ) ^ 2) = sobWeight := by
      funext ξ; simp only [hg_def]; exact Real.sq_sqrt (sobWeight_nonneg ξ)
    rw [hsq]; exact sobWeight_integrable
  -- Pointwise `f ξ · g ξ = F ξ`.
  have hfg : (fun ξ => f ξ * g ξ) = F := by
    funext ξ
    simp only [hf_def, hg_def]
    rw [mul_assoc, ← Real.sqrt_mul (inv_nonneg.mpr (sobWeight_nonneg ξ)),
        inv_mul_cancel₀ (ne_of_gt (sobWeight_pos ξ)), Real.sqrt_one, mul_one]
  -- Pointwise `f ξ ^ (2:ℝ) = (F ξ)² · (sobWeight ξ)⁻¹`.
  have hf2 : (fun ξ => f ξ ^ (2 : ℝ)) = (fun ξ => (F ξ) ^ 2 * (sobWeight ξ)⁻¹) := by
    funext ξ
    simp only [hf_def]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow,
        Real.sq_sqrt (inv_nonneg.mpr (sobWeight_nonneg ξ))]
  -- Pointwise `g ξ ^ (2:ℝ) = sobWeight ξ`.
  have hg2 : (fun ξ => g ξ ^ (2 : ℝ)) = sobWeight := by
    funext ξ
    simp only [hg_def]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Real.sq_sqrt (sobWeight_nonneg ξ)
  -- Cauchy–Schwarz (Hölder `p = q = 2`).
  have hpq : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have hp2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hf_mem' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by rw [hp2]; exact hmem
  have hg_mem' : MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by rw [hp2]; exact hg_mem
  have hfnn : 0 ≤ᵐ[volume] f :=
    ae_of_all _ (fun ξ => by simp only [hf_def]; exact mul_nonneg (hF ξ) (Real.sqrt_nonneg _))
  have hgnn : 0 ≤ᵐ[volume] g := ae_of_all _ (fun ξ => Real.sqrt_nonneg _)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hfnn hgnn hf_mem' hg_mem'
  -- Rewrite the three integrals.
  rw [hfg, hf2, hg2] at hCS
  -- `(spectralMajorant F)^(1/2) = √(spectralMajorant F)`, likewise for `weightConst`.
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  -- `hCS : ∫ F ≤ √(spectralMajorant F) * √(weightConst)`.
  calc (∫ ξ : Space, F ξ)
      ≤ Real.sqrt (spectralMajorant F) * Real.sqrt weightConst := hCS
    _ = fourierSupConst * Real.sqrt (spectralMajorant F) := by
        rw [fourierSupConst]; ring


/-!
## Packaging the sup bound from a spectral density
-/

/-- **The sup bound `‖u x‖ ≤ C₁·√(Q u)` from a dominating spectral density.**  If a
nonnegative density `F` with finite weighted `L²` mass dominates `u` pointwise
(`‖u x‖ ≤ ∫ F`, the Fourier-inversion bound `|u(x)| ≤ ∫‖û‖`), then the Cauchy–Schwarz
engine yields `‖u x‖ ≤ fourierSupConst·√(spectralMajorant F)`.  Kernel-clean;
this is the `‖u‖_∞ ≤ C₁·√(Q u)` half of the intermediate majorant assembly. -/
theorem supBound_of_spectralData {u : SchwartzVelocity} {F : Space → ℝ}
    (hF : ∀ ξ, 0 ≤ F ξ)
    (hmem : MemLp (fun ξ => F ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume)
    (hdom : ∀ x, ‖(⇑u) x‖ ≤ ∫ ξ : Space, F ξ) :
    ∀ x : Space, ‖(⇑u) x‖ ≤ fourierSupConst * Real.sqrt (spectralMajorant F) :=
  fun x => le_trans (hdom x) (cauchySchwarz_supMajorant hF hmem)


/-!
## The componentwise reduction: three scalar densities give one vector density
-/

/-- **The vector-valued spectral data is assembled from three scalar densities.**
`Space = Fin 3 → ℝ` carries the *sup* norm, so a bound on every real component
`|u(x)ᵢ|` is a bound on `‖u(x)‖`.  Given, for each component `i`, a nonnegative
weighted-`L²` density `Fᵢ` dominating that component (`|u(x)ᵢ| ≤ ∫ Fᵢ`) with
majorant `spectralMajorant Fᵢ ≤ B`, the *sum* `G = ∑ᵢ Fᵢ` is a single density
satisfying all three requirements of `exists_fourierSpectralData` with majorant
`9·B`.

The constant `9 = 3·3` is the product of the two Cauchy–Schwarz factors: `3` from
`spectralMajorant_sum_three_le` (`(a+b+c)² ≤ 3(a²+b²+c²)`) and `3` from summing the
three per-component majorant bounds.  Kernel-clean; this is the leaf that turns the
*vector-valued* Fourier–Plancherel bundle into a *scalar* one.

Consumes: `memLp_weighted_sum`, `integrable_of_memLp_weighted`,
`spectralMajorant_sum_three_le`. -/
theorem exists_spectralData_of_components {u : SchwartzVelocity} {B : ℝ}
    (F : Fin 3 → Space → ℝ)
    (hFnn : ∀ (i : Fin 3) (ξ : Space), 0 ≤ F i ξ)
    (hFmem : ∀ i, MemLp (fun ξ => F i ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume)
    (hdom : ∀ (i : Fin 3) (x : Space), |(⇑u) x i| ≤ ∫ ξ : Space, F i ξ)
    (hmaj : ∀ i, spectralMajorant (F i) ≤ B) :
    ∃ G : Space → ℝ, (∀ ξ, 0 ≤ G ξ) ∧
      MemLp (fun ξ => G ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume ∧
      (∀ x : Space, ‖(⇑u) x‖ ≤ ∫ ξ : Space, G ξ) ∧
      spectralMajorant G ≤ 9 * B := by
  have hGnn : ∀ ξ : Space, 0 ≤ ∑ i, F i ξ :=
    fun ξ => Finset.sum_nonneg fun i _ => hFnn i ξ
  have hFint : ∀ i, Integrable (F i) volume :=
    fun i => integrable_of_memLp_weighted (hFmem i)
  have hGint : Integrable (fun ξ : Space => ∑ i, F i ξ) volume :=
    integrable_finsetSum _ fun i _ => hFint i
  refine ⟨fun ξ => ∑ i, F i ξ, hGnn, memLp_weighted_sum F hFmem, ?_, ?_⟩
  · -- sup-norm domination: every component is dominated by the summed density
    intro x
    rw [pi_norm_le_iff_of_nonneg (integral_nonneg hGnn)]
    intro i
    rw [Real.norm_eq_abs]
    refine le_trans (hdom i x) (integral_mono (hFint i) hGint fun ξ => ?_)
    exact Finset.single_le_sum (f := fun j => F j ξ)
      (fun j _ => hFnn j ξ) (Finset.mem_univ i)
  · -- majorant: two Cauchy–Schwarz factors of 3
    have h3 : ∑ i : Fin 3, spectralMajorant (F i) ≤ 3 * B := by
      rw [Fin.sum_univ_three]
      linarith [hmaj 0, hmaj 1, hmaj 2]
    linarith [spectralMajorant_sum_three_le F hFmem]

/-!
## Plancherel on the sup-normed domain `Space = Fin 3 → ℝ` (substeps 1–2)

Mathlib's Fourier/Plancherel API (`SchwartzMap.integral_norm_sq_fourier`) needs an
*inner-product* domain, but `Space = Fin 3 → ℝ` carries the sup norm.  The transport
below reinterprets a Schwartz map over the L²-normed `EuclideanSpace ℝ (Fin 3)` via
the CLE `EuclideanSpace.equiv`, so Plancherel becomes available for this project's
domain — the exact "Mathlib-absent for the sup-normed domain" blocker of the residual.
-/

/-- **Transport a scalar Schwartz map to the inner-product (Euclidean) domain.**
Precomposition with the CLE `EuclideanSpace ℝ (Fin 3) ≃L[ℝ] (Fin 3 → ℝ)` via
`SchwartzMap.compCLMOfContinuousLinearEquiv`; the underlying function is unchanged
(`EuclideanSpace.equiv` is the identity on the shared carrier). -/
noncomputable def toEuclid (f : SchwartzMap Space ℂ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (EuclideanSpace.equiv (Fin 3) ℝ) f

/-- **Plancherel `∫‖𝓕f‖² = ∫‖f‖²` on the sup-normed `Space` domain** (substeps 1–2 of
the residual).  For a scalar `ℂ`-valued Schwartz map on `Space`, the `L²` mass of its
Fourier transform (taken on the Euclidean model) equals the `L²` mass of `f` over
`Space`.  Kernel-clean; consumes Mathlib's `SchwartzMap.integral_norm_sq_fourier`
Plancherel and the measure-preserving `PiLp.volume_preserving_toLp` transfer.

Citation: Mathlib `SchwartzMap.integral_norm_sq_fourier`; Stein III.2 (Plancherel). -/
theorem spacePlancherel (f : SchwartzMap Space ℂ) :
    ∫ x : EuclideanSpace ℝ (Fin 3), ‖(FourierTransform.fourier (toEuclid f)) x‖ ^ 2
      = ∫ ξ : Space, ‖f ξ‖ ^ 2 := by
  rw [SchwartzMap.integral_norm_sq_fourier (toEuclid f),
      ← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with x
  rw [toEuclid, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rfl

/-!
## The Fourier residual and the intermediate-majorant assembly
-/

/-! ## The scalar Fourier–Plancherel bundle (certified)

The residual `exists_scalarFourierSpectralData` is discharged below.  The route
is: transport the real component `x ↦ u(x)ᵢ` to a `ℂ`-valued Schwartz map on the
Euclidean model `ES` (`euclidComponent`, via Mathlib's `SchwartzMap.postcompCLM`
and `toEuclid`); take `F ξ = ‖𝓕(uᵢ)(ξ)‖` (`componentDensity`); get the pointwise
domination from Fourier inversion; and evaluate `spectralMajorant F` by the
binomial `(1+|ξ|²)³ = 1 + 3|ξ|² + 3|ξ|⁴ + |ξ|⁶` against the four weighted
Plancherel rungs of `Navier.Analysis.FourierWeightedPlancherel`.  The derivative
comparison uses `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`
(`∂^{m}f x = D^n f x m`) together with the two contractions `componentCLM`
(post-composition, `‖·‖ ≤ 1` for the Pi sup norm) and `spaceProj`
(pre-composition, `‖·‖ ≤ 1` for the Euclidean-to-sup comparison).
-/

/-! ### components -/
def componentCLM (i : Fin 3) : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

theorem norm_componentCLM_le_one (i : Fin 3) : ‖componentCLM i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa [componentCLM] using norm_le_pi_norm x i

def spaceProj : ES →L[ℝ] Space := (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap

theorem norm_spaceProj_le_one : ‖spaceProj‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => ?_
  have hs : ‖x i‖ ^ 2 ≤ ∑ j : Fin 3, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 3 => ‖x j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖x i‖ = Real.sqrt (‖x i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ j : Fin 3, ‖x j‖ ^ 2) := Real.sqrt_le_sqrt hs
    _ = ‖x‖ := (EuclideanSpace.norm_eq x).symm

def scalarComponent (u : SchwartzVelocity) (i : Fin 3) : SchwartzMap Space ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (componentCLM i) u

def euclidComponent (u : SchwartzVelocity) (i : Fin 3) : SchwartzMap ES ℂ :=
  toEuclid (scalarComponent u i)

theorem euclidComponent_apply (u : SchwartzVelocity) (i : Fin 3) (y : ES) :
    euclidComponent u i y = (((⇑u) (spaceProj y) i : ℝ) : ℂ) := rfl

theorem coe_euclidComponent (u : SchwartzVelocity) (i : Fin 3) :
    ⇑(euclidComponent u i) = (⇑(scalarComponent u i)) ∘ ⇑spaceProj := rfl

/-! ### integrability of derivative energies -/
theorem integrable_normSq_iteratedFDeriv {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure D) [μ.HasTemperateGrowth] (f : SchwartzMap D V) (n : ℕ) :
    Integrable (fun x : D => ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2) μ := by
  obtain ⟨C, _, hC⟩ := f.decay 0 n
  have hCnn : ∀ x : D, ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ C := fun x => by simpa using hC x
  refine ((f.integrable_pow_mul_iteratedFDeriv μ 0 n).const_mul C).mono'
    (((f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)).norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2
      = ‖iteratedFDeriv ℝ n (⇑f) x‖ * ‖iteratedFDeriv ℝ n (⇑f) x‖ := sq _
    _ ≤ C * (‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n (⇑f) x‖) := by
        simpa using mul_le_mul_of_nonneg_right (hCnn x) (norm_nonneg _)

/-! ### derivative comparison -/
theorem norm_iteratedFDeriv_euclidComponent_le
    (u : SchwartzVelocity) (i : Fin 3) (n : ℕ) (y : ES) :
    ‖iteratedFDeriv ℝ n (⇑(euclidComponent u i)) y‖
      ≤ ‖iteratedFDeriv ℝ n (⇑u) (spaceProj y)‖ := by
  have hstep1 : ‖iteratedFDeriv ℝ n (⇑(euclidComponent u i)) y‖
      ≤ ‖iteratedFDeriv ℝ n (⇑(scalarComponent u i)) (spaceProj y)‖ := by
    rw [coe_euclidComponent,
      ContinuousLinearMap.iteratedFDeriv_comp_right (g := spaceProj)
        ((scalarComponent u i).smooth ⊤) y (mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hp : ∏ _k : Fin n, ‖spaceProj‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_spaceProj_le_one)
    nlinarith [norm_nonneg (iteratedFDeriv ℝ n (⇑(scalarComponent u i)) (spaceProj y)),
      Finset.prod_nonneg (fun (_ : Fin n) (_ : _ ∈ Finset.univ) => norm_nonneg spaceProj)]
  refine hstep1.trans ?_
  have hcomp : ⇑(scalarComponent u i) = (⇑(componentCLM i)) ∘ (⇑u) := rfl
  have h2 := (componentCLM i).norm_iteratedFDeriv_comp_left
    (f := (⇑u)) (x := spaceProj y) (n := n) ((u.smooth ⊤).contDiffAt) (mod_cast le_top)
  rw [hcomp]
  refine h2.trans ?_
  nlinarith [norm_componentCLM_le_one i, norm_nonneg (iteratedFDeriv ℝ n (⇑u) (spaceProj y))]

/-- Transport an integral over the Euclidean model back to `Space`. -/
theorem integral_spaceProj (ψ : Space → ℝ) : ∫ y : ES, ψ (spaceProj y) = ∫ x : Space, ψ x := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding (fun z : ES => ψ (spaceProj z))]
  rfl

theorem integral_normSq_iteratedFDeriv_euclidComponent_le
    (u : SchwartzVelocity) (i : Fin 3) (n : ℕ) :
    (∫ y : ES, ‖iteratedFDeriv ℝ n (⇑(euclidComponent u i)) y‖ ^ 2)
      ≤ ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 := by
  rw [← integral_spaceProj (fun x => ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2)]
  refine integral_mono (integrable_normSq_iteratedFDeriv volume (euclidComponent u i) n) ?_ ?_
  · have hu : Integrable
        ((fun y : ES => ‖iteratedFDeriv ℝ n (⇑u) (spaceProj y)‖ ^ 2) ∘ (WithLp.toLp 2)) volume :=
      integrable_normSq_iteratedFDeriv volume u n
    exact ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding).mp hu
  · intro y
    have h := norm_iteratedFDeriv_euclidComponent_le u i n y
    nlinarith [norm_nonneg (iteratedFDeriv ℝ n (⇑(euclidComponent u i)) y)]

/-- Iterated coordinate line derivatives are dominated by the full order-`n` derivative. -/
theorem norm_iteratedLineDeriv_le {n : ℕ} (m : Fin n → ES) (hm : ∀ k, ‖m k‖ ≤ 1)
    (f : SchwartzMap ES ℂ) (x : ES) :
    ‖(∂^{m} f) x‖ ≤ ‖iteratedFDeriv ℝ n (⇑f) x‖ := by
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have hp : ∏ k, ‖m k‖ ≤ 1 := Finset.prod_le_one (fun k _ => norm_nonneg _) (fun k _ => hm k)
  nlinarith [norm_nonneg (iteratedFDeriv ℝ n (⇑f) x),
    Finset.prod_nonneg (fun k (_ : k ∈ Finset.univ) => norm_nonneg (m k))]

theorem norm_single_es (j : Fin 3) : ‖(EuclideanSpace.single j (1:ℝ) : ES)‖ = 1 := by simp

theorem norm_pd_le (j : Fin 3) (f : SchwartzMap ES ℂ) (x : ES) :
    ‖(pd j f) x‖ ≤ ‖iteratedFDeriv ℝ 1 (⇑f) x‖ := by
  have h : pd j f = ∂^{![EuclideanSpace.single j (1:ℝ)]} f := by
    rw [LineDeriv.iteratedLineDerivOp_one]; rfl
  rw [h]
  exact norm_iteratedLineDeriv_le _ (by intro k; fin_cases k; simp) f x

theorem norm_pd2_le (i j : Fin 3) (f : SchwartzMap ES ℂ) (x : ES) :
    ‖(pd i (pd j f)) x‖ ≤ ‖iteratedFDeriv ℝ 2 (⇑f) x‖ := by
  have h : pd i (pd j f)
      = ∂^{![EuclideanSpace.single i (1:ℝ), EuclideanSpace.single j (1:ℝ)]} f := by
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    norm_num [LineDeriv.iteratedLineDerivOp_one, pd_def]
  rw [h]
  exact norm_iteratedLineDeriv_le _ (by intro k; fin_cases k <;> simp) f x

theorem norm_pd3_le (i j l : Fin 3) (f : SchwartzMap ES ℂ) (x : ES) :
    ‖(pd i (pd j (pd l f))) x‖ ≤ ‖iteratedFDeriv ℝ 3 (⇑f) x‖ := by
  have h : pd i (pd j (pd l f))
      = ∂^{![EuclideanSpace.single i (1:ℝ), EuclideanSpace.single j (1:ℝ),
             EuclideanSpace.single l (1:ℝ)]} f := by
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left]
    norm_num [LineDeriv.iteratedLineDerivOp_one, pd_def]
  rw [h]
  exact norm_iteratedLineDeriv_le _ (by intro k; fin_cases k <;> simp) f x

/-! ### the component spectral density -/
def componentDensity (u : SchwartzVelocity) (i : Fin 3) (ξ : Space) : ℝ :=
  ‖(𝓕 (euclidComponent u i)) (WithLp.toLp 2 ξ : ES)‖

theorem componentDensity_nonneg (u : SchwartzVelocity) (i : Fin 3) (ξ : Space) :
    0 ≤ componentDensity u i ξ := norm_nonneg _

theorem sobWeightInv_euclid (ξ : Space) :
    (sobWeight ξ)⁻¹ = (1 + ‖(WithLp.toLp 2 ξ : ES)‖ ^ 2) ^ 3 := by
  rw [sobWeight, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three]
  ring

theorem integral_componentDensity_eq (u : SchwartzVelocity) (i : Fin 3) :
    (∫ ξ : Space, componentDensity u i ξ)
      = ∫ η : ES, ‖(𝓕 (euclidComponent u i)) η‖ :=
  (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    (fun η : ES => ‖(𝓕 (euclidComponent u i)) η‖)

theorem abs_component_le_integral_componentDensity
    (u : SchwartzVelocity) (i : Fin 3) (x : Space) :
    |(⇑u) x i| ≤ ∫ ξ : Space, componentDensity u i ξ := by
  rw [integral_componentDensity_eq]
  set g := euclidComponent u i with hg
  have hinv : 𝓕⁻ (𝓕 (⇑g)) = (⇑g) :=
    g.continuous.fourierInv_fourier_eq g.integrable
      (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 g).integrable)
  have h1 : ‖(𝓕⁻ (𝓕 (⇑g))) (WithLp.toLp 2 x : ES)‖ ≤ ∫ η : ES, ‖(𝓕 (⇑g)) η‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [hinv] at h1
  rw [SchwartzMap.fourier_coe]
  refine le_trans (le_of_eq ?_) h1
  rw [hg]
  exact (Complex.norm_real _).symm

/-! ### the binomial fold -/
theorem spectralMajorant_componentDensity_eq (u : SchwartzVelocity) (i : Fin 3) :
    spectralMajorant (componentDensity u i)
      = (∫ η : ES, ‖(𝓕 (euclidComponent u i)) η‖ ^ 2)
        + 3 * (∫ η : ES, ‖η‖ ^ 2 * ‖(𝓕 (euclidComponent u i)) η‖ ^ 2)
        + 3 * (∫ η : ES, ‖η‖ ^ 4 * ‖(𝓕 (euclidComponent u i)) η‖ ^ 2)
        + (∫ η : ES, ‖η‖ ^ 6 * ‖(𝓕 (euclidComponent u i)) η‖ ^ 2) := by
  set g := euclidComponent u i with hg
  have hI : ∀ k : ℕ, Integrable (fun η : ES => ‖η‖ ^ k * ‖(𝓕 g) η‖ ^ 2) volume :=
    fun k => integrable_norm_pow_mul_normSq (𝓕 g) k
  have hI0 : Integrable (fun η : ES => ‖(𝓕 g) η‖ ^ 2) volume := integrable_normSq (𝓕 g)
  have hcomp := (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
      (fun η : ES => ‖(𝓕 g) η‖ ^ 2 + 3 * (‖η‖ ^ 2 * ‖(𝓕 g) η‖ ^ 2)
          + 3 * (‖η‖ ^ 4 * ‖(𝓕 g) η‖ ^ 2) + ‖η‖ ^ 6 * ‖(𝓕 g) η‖ ^ 2)
  have htrans : spectralMajorant (componentDensity u i)
      = ∫ η : ES, (‖(𝓕 g) η‖ ^ 2 + 3 * (‖η‖ ^ 2 * ‖(𝓕 g) η‖ ^ 2)
          + 3 * (‖η‖ ^ 4 * ‖(𝓕 g) η‖ ^ 2) + ‖η‖ ^ 6 * ‖(𝓕 g) η‖ ^ 2) := by
    refine Eq.trans ?_ hcomp
    rw [spectralMajorant]
    refine integral_congr_ae ?_
    filter_upwards with ξ
    rw [componentDensity, sobWeightInv_euclid]
    ring
  have hA : Integrable (fun η : ES =>
      ‖(𝓕 g) η‖ ^ 2 + 3 * (‖η‖ ^ 2 * ‖(𝓕 g) η‖ ^ 2)) volume :=
    hI0.add ((hI 2).const_mul 3)
  have hB : Integrable (fun η : ES =>
      ‖(𝓕 g) η‖ ^ 2 + 3 * (‖η‖ ^ 2 * ‖(𝓕 g) η‖ ^ 2)
        + 3 * (‖η‖ ^ 4 * ‖(𝓕 g) η‖ ^ 2)) volume :=
    hA.add ((hI 4).const_mul 3)
  rw [htrans, integral_add hB (hI 6), integral_add hA ((hI 4).const_mul 3),
      integral_add hI0 ((hI 2).const_mul 3), integral_const_mul, integral_const_mul]

/-! ### the H³ bound -/
theorem sobolevH3NormSq_expand (u : SchwartzVelocity) :
    sobolevH3NormSq u = (∫ x : Space, ‖iteratedFDeriv ℝ 0 (⇑u) x‖ ^ 2)
      + (∫ x : Space, ‖iteratedFDeriv ℝ 1 (⇑u) x‖ ^ 2)
      + (∫ x : Space, ‖iteratedFDeriv ℝ 2 (⇑u) x‖ ^ 2)
      + (∫ x : Space, ‖iteratedFDeriv ℝ 3 (⇑u) x‖ ^ 2) := by
  simp [sobolevH3NormSq, Finset.sum_range_succ]

theorem integral_normSq_pd_le (u : SchwartzVelocity) (i j : Fin 3) :
    (∫ x : ES, ‖(pd j (euclidComponent u i)) x‖ ^ 2)
      ≤ ∫ x : Space, ‖iteratedFDeriv ℝ 1 (⇑u) x‖ ^ 2 := by
  refine le_trans ?_ (integral_normSq_iteratedFDeriv_euclidComponent_le u i 1)
  refine integral_mono (integrable_normSq _)
    (integrable_normSq_iteratedFDeriv volume (euclidComponent u i) 1) fun x => ?_
  nlinarith [norm_pd_le j (euclidComponent u i) x,
    norm_nonneg ((pd j (euclidComponent u i)) x)]

theorem integral_normSq_pd2_le (u : SchwartzVelocity) (i j l : Fin 3) :
    (∫ x : ES, ‖(pd l (pd j (euclidComponent u i))) x‖ ^ 2)
      ≤ ∫ x : Space, ‖iteratedFDeriv ℝ 2 (⇑u) x‖ ^ 2 := by
  refine le_trans ?_ (integral_normSq_iteratedFDeriv_euclidComponent_le u i 2)
  refine integral_mono (integrable_normSq _)
    (integrable_normSq_iteratedFDeriv volume (euclidComponent u i) 2) fun x => ?_
  nlinarith [norm_pd2_le l j (euclidComponent u i) x,
    norm_nonneg ((pd l (pd j (euclidComponent u i))) x)]

theorem integral_normSq_pd3_le (u : SchwartzVelocity) (i j l k : Fin 3) :
    (∫ x : ES, ‖(pd k (pd l (pd j (euclidComponent u i)))) x‖ ^ 2)
      ≤ ∫ x : Space, ‖iteratedFDeriv ℝ 3 (⇑u) x‖ ^ 2 := by
  refine le_trans ?_ (integral_normSq_iteratedFDeriv_euclidComponent_le u i 3)
  refine integral_mono (integrable_normSq _)
    (integrable_normSq_iteratedFDeriv volume (euclidComponent u i) 3) fun x => ?_
  nlinarith [norm_pd3_le k l j (euclidComponent u i) x,
    norm_nonneg ((pd k (pd l (pd j (euclidComponent u i)))) x)]

theorem one_le_two_pi_pow (n : ℕ) : (1 : ℝ) ≤ (2 * Real.pi) ^ n := by
  refine one_le_pow₀ ?_
  nlinarith [Real.pi_gt_three]

theorem spectralMajorant_componentDensity_le (u : SchwartzVelocity) (i : Fin 3) :
    spectralMajorant (componentDensity u i) ≤ 27 * sobolevH3NormSq u := by
  set g := euclidComponent u i with hg
  set E : ℕ → ℝ := fun n => ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 with hE
  have hEnn : ∀ n, 0 ≤ E n := fun n => integral_nonneg fun x => by positivity
  -- the four spectral integrals
  have hI2nn : (0:ℝ) ≤ ∫ η : ES, ‖η‖ ^ 2 * ‖(𝓕 g) η‖ ^ 2 :=
    integral_nonneg fun η => by positivity
  have hI4nn : (0:ℝ) ≤ ∫ η : ES, ‖η‖ ^ 4 * ‖(𝓕 g) η‖ ^ 2 :=
    integral_nonneg fun η => by positivity
  have hI6nn : (0:ℝ) ≤ ∫ η : ES, ‖η‖ ^ 6 * ‖(𝓕 g) η‖ ^ 2 :=
    integral_nonneg fun η => by positivity
  -- n = 0
  have h0 : (∫ η : ES, ‖(𝓕 g) η‖ ^ 2) ≤ E 0 := by
    have hz := integral_normSq_iteratedFDeriv_euclidComponent_le u i 0
    rw [SchwartzMap.integral_norm_sq_fourier g]
    show (∫ y : ES, ‖g y‖ ^ 2) ≤ ∫ x : Space, ‖iteratedFDeriv ℝ 0 (⇑u) x‖ ^ 2
    refine le_trans (le_of_eq ?_) hz
    exact integral_congr_ae (by filter_upwards with y; rw [norm_iteratedFDeriv_zero])
  -- n = 1
  have h1 : (2 * Real.pi) ^ 2 * (∫ η : ES, ‖η‖ ^ 2 * ‖(𝓕 g) η‖ ^ 2) ≤ 3 * E 1 := by
    rw [← sum_integral_normSq_pd_eq g, Fin.sum_univ_three]
    linarith [integral_normSq_pd_le u i 0, integral_normSq_pd_le u i 1,
      integral_normSq_pd_le u i 2]
  have hle1 : (∫ η : ES, ‖η‖ ^ 2 * ‖(𝓕 g) η‖ ^ 2) ≤ 3 * E 1 := by
    nlinarith [one_le_two_pi_pow 2, hI2nn]
  -- n = 2
  have h2 : (2 * Real.pi) ^ 4 * (∫ η : ES, ‖η‖ ^ 4 * ‖(𝓕 g) η‖ ^ 2) ≤ 9 * E 2 := by
    rw [← sum_integral_normSq_pd_two_eq g]
    simp only [Fin.sum_univ_three]
    linarith [integral_normSq_pd2_le u i 0 0, integral_normSq_pd2_le u i 0 1,
      integral_normSq_pd2_le u i 0 2, integral_normSq_pd2_le u i 1 0,
      integral_normSq_pd2_le u i 1 1, integral_normSq_pd2_le u i 1 2,
      integral_normSq_pd2_le u i 2 0, integral_normSq_pd2_le u i 2 1,
      integral_normSq_pd2_le u i 2 2]
  have hle2 : (∫ η : ES, ‖η‖ ^ 4 * ‖(𝓕 g) η‖ ^ 2) ≤ 9 * E 2 := by
    nlinarith [one_le_two_pi_pow 4, hI4nn]
  -- n = 3
  have h3 : (2 * Real.pi) ^ 6 * (∫ η : ES, ‖η‖ ^ 6 * ‖(𝓕 g) η‖ ^ 2) ≤ 27 * E 3 := by
    rw [← sum_integral_normSq_pd_three_eq g]
    simp only [Fin.sum_univ_three]
    linarith [integral_normSq_pd3_le u i 0 0 0, integral_normSq_pd3_le u i 0 0 1,
      integral_normSq_pd3_le u i 0 0 2, integral_normSq_pd3_le u i 0 1 0,
      integral_normSq_pd3_le u i 0 1 1, integral_normSq_pd3_le u i 0 1 2,
      integral_normSq_pd3_le u i 0 2 0, integral_normSq_pd3_le u i 0 2 1,
      integral_normSq_pd3_le u i 0 2 2, integral_normSq_pd3_le u i 1 0 0,
      integral_normSq_pd3_le u i 1 0 1, integral_normSq_pd3_le u i 1 0 2,
      integral_normSq_pd3_le u i 1 1 0, integral_normSq_pd3_le u i 1 1 1,
      integral_normSq_pd3_le u i 1 1 2, integral_normSq_pd3_le u i 1 2 0,
      integral_normSq_pd3_le u i 1 2 1, integral_normSq_pd3_le u i 1 2 2,
      integral_normSq_pd3_le u i 2 0 0, integral_normSq_pd3_le u i 2 0 1,
      integral_normSq_pd3_le u i 2 0 2, integral_normSq_pd3_le u i 2 1 0,
      integral_normSq_pd3_le u i 2 1 1, integral_normSq_pd3_le u i 2 1 2,
      integral_normSq_pd3_le u i 2 2 0, integral_normSq_pd3_le u i 2 2 1,
      integral_normSq_pd3_le u i 2 2 2]
  have hle3 : (∫ η : ES, ‖η‖ ^ 6 * ‖(𝓕 g) η‖ ^ 2) ≤ 27 * E 3 := by
    nlinarith [one_le_two_pi_pow 6, hI6nn]
  rw [spectralMajorant_componentDensity_eq u i, sobolevH3NormSq_expand u]
  simp only [← hg]
  linarith [hEnn 0, hEnn 1, hEnn 2, hEnn 3]

/-! ### MemLp and the closed residual -/
theorem integrable_componentDensity_sq_weighted (u : SchwartzVelocity) (i : Fin 3) :
    Integrable (fun ξ : Space => componentDensity u i ξ ^ 2 * (sobWeight ξ)⁻¹) volume := by
  set g := euclidComponent u i with hg
  have hI : ∀ k : ℕ, Integrable (fun η : ES => ‖η‖ ^ k * ‖(𝓕 g) η‖ ^ 2) volume :=
    fun k => integrable_norm_pow_mul_normSq (𝓕 g) k
  have hI0 : Integrable (fun η : ES => ‖(𝓕 g) η‖ ^ 2) volume := integrable_normSq (𝓕 g)
  have hES : Integrable (fun η : ES => ‖(𝓕 g) η‖ ^ 2 + 3 * (‖η‖ ^ 2 * ‖(𝓕 g) η‖ ^ 2)
      + 3 * (‖η‖ ^ 4 * ‖(𝓕 g) η‖ ^ 2) + ‖η‖ ^ 6 * ‖(𝓕 g) η‖ ^ 2) volume :=
    ((hI0.add ((hI 2).const_mul 3)).add ((hI 4).const_mul 3)).add (hI 6)
  have htr := ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding).mpr hES
  refine htr.congr ?_
  filter_upwards with ξ
  show ‖(𝓕 g) (WithLp.toLp 2 ξ)‖ ^ 2 + 3 * (‖(WithLp.toLp 2 ξ : ES)‖ ^ 2 * ‖(𝓕 g) (WithLp.toLp 2 ξ)‖ ^ 2)
      + 3 * (‖(WithLp.toLp 2 ξ : ES)‖ ^ 4 * ‖(𝓕 g) (WithLp.toLp 2 ξ)‖ ^ 2)
      + ‖(WithLp.toLp 2 ξ : ES)‖ ^ 6 * ‖(𝓕 g) (WithLp.toLp 2 ξ)‖ ^ 2
      = componentDensity u i ξ ^ 2 * (sobWeight ξ)⁻¹
  rw [componentDensity, sobWeightInv_euclid, ← hg]
  ring

theorem continuous_componentDensity_weighted (u : SchwartzVelocity) (i : Fin 3) :
    Continuous (fun ξ : Space => componentDensity u i ξ * Real.sqrt (sobWeight ξ)⁻¹) := by
  refine Continuous.mul ?_ ?_
  · exact ((𝓕 (euclidComponent u i)).continuous.comp
      (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous).norm
  · exact Real.continuous_sqrt.comp
      (sobWeight_continuous.inv₀ (fun ξ => ne_of_gt (sobWeight_pos ξ)))

theorem memLp_componentDensity (u : SchwartzVelocity) (i : Fin 3) :
    MemLp (fun ξ : Space => componentDensity u i ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume := by
  rw [memLp_two_iff_integrable_sq
    (continuous_componentDensity_weighted u i).aestronglyMeasurable]
  refine (integrable_componentDensity_sq_weighted u i).congr ?_
  filter_upwards with ξ
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr (sobWeight_nonneg ξ))]

/-- **The SCALAR Fourier–Plancherel bundle (certified, no sorry).**
For every Schwartz velocity `u` and every coordinate `i`, the real scalar
component `x ↦ u(x)ᵢ` admits a nonnegative spectral density `F` (namely
`F ξ = ‖𝓕(uᵢ)(ξ)‖`, `componentDensity`) with (i) finite weighted `L²` mass,
(ii) Fourier-inversion domination `|u(x)ᵢ| ≤ ∫ F`, and (iii) the Plancherel bound
`spectralMajorant F ≤ 27·‖u‖²_{H³}`, uniformly in `u` and `i`.

The constant `27` is not optimal: it is the crude uniform majorant of the four
binomial coefficients `1, 3·3, 3·9, 27` divided by `(2π)^{0,2,4,6} ≥ 1`
(`one_le_two_pi_pow`), which is all the downstream consumers need.

Reference: Stein, *Singular Integrals* (1970) III.2; Grafakos, *Classical
Fourier Analysis*, 3rd ed. (2014) §2.2 (Plancherel and inversion for Schwartz
functions); Reed–Simon I (1980) §IX.1; Majda–Bertozzi Lemma 3.2. -/
theorem exists_scalarFourierSpectralData :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : SchwartzVelocity) (i : Fin 3),
      ∃ F : Space → ℝ, (∀ ξ, 0 ≤ F ξ) ∧
        MemLp (fun ξ => F ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume ∧
        (∀ x : Space, |(⇑u) x i| ≤ ∫ ξ : Space, F ξ) ∧
        spectralMajorant F ≤ C * sobolevH3NormSq u :=
  ⟨27, by norm_num, fun u i => ⟨componentDensity u i, componentDensity_nonneg u i,
    memLp_componentDensity u i, abs_component_le_integral_componentDensity u i,
    spectralMajorant_componentDensity_le u i⟩⟩

/-- **The vector-valued spectral data (certified, no sorry).**  Derived from the
scalar bundle `exists_scalarFourierSpectralData` by the componentwise assembly
`exists_spectralData_of_components` (constant `C₂ = 9·C`; the two Cauchy–Schwarz
factors of `3`).

For every Schwartz velocity `u` there is a nonnegative spectral density `F`
(namely `F ξ = ∑ᵢ ‖𝓕(uᵢ)(ξ)‖`) with (i) `F·(sobWeight)^{-1/2} ∈ L²`,
(ii) Fourier-inversion domination `‖u x‖ ≤ ∫ F`, and (iii) the Plancherel bound
`spectralMajorant F ≤ C₂·‖u‖²_{H³}` uniformly in `u`.

Reference: Stein, *Singular Integrals* (1970) III.2; Grafakos, *Classical Fourier
Analysis*, 3rd ed. (2014) §2.2; Majda–Bertozzi Lemma 3.2. -/
theorem exists_fourierSpectralData :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ u : SchwartzVelocity,
      ∃ F : Space → ℝ, (∀ ξ, 0 ≤ F ξ) ∧
        MemLp (fun ξ => F ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume ∧
        (∀ x : Space, ‖(⇑u) x‖ ≤ ∫ ξ : Space, F ξ) ∧
        spectralMajorant F ≤ C₂ * sobolevH3NormSq u := by
  obtain ⟨C, hC, hdata⟩ := exists_scalarFourierSpectralData
  refine ⟨9 * C, by linarith, fun u => ?_⟩
  choose F hFnn hFmem hdom hmaj using hdata u
  obtain ⟨G, hGnn, hGmem, hGdom, hGmaj⟩ :=
    exists_spectralData_of_components (u := u) (B := C * sobolevH3NormSq u)
      F hFnn hFmem hdom hmaj
  refine ⟨G, hGnn, hGmem, hGdom, ?_⟩
  calc spectralMajorant G ≤ 9 * (C * sobolevH3NormSq u) := hGmaj
    _ = 9 * C * sobolevH3NormSq u := by ring

/-- **The intermediate-majorant assembly for the Fourier route.**  Packages a
concrete Fourier-side majorant `Q u` with both analytic bounds required by
`SobolevEmbedding.sobolev_domination_of_intermediate`:

* the sup bound `‖u x‖ ≤ C₁·√(Q u)` (Fourier inversion + the kernel-clean
  Cauchy–Schwarz `supBound_of_spectralData`), and
* the physical bound `Q u ≤ C₂·‖u‖²_{H³}` (Plancherel).

This has exactly the type of the `SobolevEmbedding.exists_sobolev_intermediate`
residual, and is now kernel-clean end to end: the Cauchy–Schwarz half by
`cauchySchwarz_supMajorant`, the Fourier inversion and Plancherel half by
`exists_fourierSpectralData`. -/
theorem exists_fourierMajorant_intermediate :
    ∃ (Q : SchwartzVelocity → ℝ) (C₁ C₂ : ℝ),
      0 < C₁ ∧ 0 < C₂ ∧
      (∀ (u : SchwartzVelocity) (x : Space), ‖(⇑u) x‖ ≤ C₁ * Real.sqrt (Q u)) ∧
      (∀ u : SchwartzVelocity, Q u ≤ C₂ * sobolevH3NormSq u) := by
  obtain ⟨C₂, hC₂, hdata⟩ := exists_fourierSpectralData
  refine ⟨fun u => spectralMajorant (Classical.choose (hdata u)),
          fourierSupConst, C₂, fourierSupConst_pos, hC₂, ?_, ?_⟩
  · intro u x
    obtain ⟨hF, hmem, hdom, _⟩ := Classical.choose_spec (hdata u)
    exact supBound_of_spectralData hF hmem hdom x
  · intro u
    obtain ⟨_, _, _, hplanch⟩ := Classical.choose_spec (hdata u)
    exact hplanch


/-- **The `H³(ℝ³) ↪ L^∞` Sobolev embedding (certified, no sorry).**  Composing the
intermediate assembly with monotonicity of `√` yields `‖u x‖ ≤ C·√Ms` for any
`H³`-majorant `Ms ≥ ‖u‖²_{H³}`.  This is the same statement as
`SobolevEmbedding.sobolevEmbeddingDomination_H3`, here proved outright: the
Cauchy–Schwarz half by `cauchySchwarz_supMajorant`, the Fourier inversion and
Plancherel half by `exists_fourierSpectralData`.  Self-contained (√-monotonicity
assembly inlined; no dependence on the SobolevEmbedding olean). -/
theorem fourierMajorant_embedding :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (Ms : ℝ), sobolevH3NormSq u ≤ Ms →
        ∀ x : Space, ‖(⇑u) x‖ ≤ C * Real.sqrt Ms := by
  obtain ⟨Q, C₁, C₂, hC₁, hC₂, h1, h2⟩ := exists_fourierMajorant_intermediate
  refine ⟨C₁ * Real.sqrt C₂, mul_pos hC₁ (Real.sqrt_pos.mpr hC₂), ?_⟩
  intro u Ms hMs x
  have hQMs : Q u ≤ C₂ * Ms :=
    le_trans (h2 u) (mul_le_mul_of_nonneg_left hMs (le_of_lt hC₂))
  calc ‖(⇑u) x‖ ≤ C₁ * Real.sqrt (Q u) := h1 u x
    _ ≤ C₁ * Real.sqrt (C₂ * Ms) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQMs) (le_of_lt hC₁)
    _ = C₁ * Real.sqrt C₂ * Real.sqrt Ms := by
        rw [Real.sqrt_mul (le_of_lt hC₂), mul_assoc]

end Navier.Analysis.FourierMajorant
