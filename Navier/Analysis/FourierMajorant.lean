import Navier.Analysis.WeightIntegrability
import Navier.Analysis.BKMLogBootstrap

/-!
# Fourier majorant infrastructure for the `H³(ℝ³) ↪ L^∞` Sobolev embedding

This is the reusable analytic core of the Beale–Kato–Majda Sobolev-embedding
route.  The certified interface `SobolevEmbedding.sobolev_domination_of_intermediate`
turns two analytic bounds on a Fourier-side majorant `Q` into the embedding
`‖u‖_∞ ≤ C·√Ms`.  This file supplies the *first* of those two bounds
kernel-cleanly (the Cauchy–Schwarz step), together with the weighted-`L²`
calculus and the componentwise (vector → scalar) reduction, leaving a single
named **scalar** Fourier residual (inversion + Plancherel):
`exists_scalarFourierSpectralData`.

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

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Navier.Analysis.FourierMajorant

open Navier
open Navier.Analysis.WeightIntegrability
open Navier.Analysis.BealeKatoMajda

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

/-- **[RESIDUAL — the SCALAR Fourier–Plancherel bundle.  Est ~180–260 LOC.]**
For every Schwartz velocity `u` and every coordinate `i`, the *real scalar*
component `x ↦ u(x)ᵢ` admits a nonnegative spectral density `F` (classically
`F ξ = ‖𝓕(uᵢ)(ξ)‖`) with (i) finite weighted `L²` mass, (ii) Fourier-inversion
domination `|u(x)ᵢ| ≤ ∫ F`, and (iii) the Plancherel bound
`spectralMajorant F ≤ C·‖u‖²_{H³}`, uniformly in `u` and `i`.

This is strictly smaller than the former vector-valued residual: the sup-norm
recombination of the three components, the `L²`-weight algebra, and the two
Cauchy–Schwarz constants are now kernel-clean
(`exists_spectralData_of_components`, `spectralMajorant_sum_three_le`,
`memLp_weighted_sum`, `integrable_of_memLp_weighted`).  What remains is exactly
the scalar Fourier analysis.

Explicit dependency list for the remaining work:

1. **Component transport (~50 LOC).**  Realize `x ↦ u(x)ᵢ` as a
   `SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ`.  Mathlib supplies *pre*-composition
   (`SchwartzMap.compCLMOfContinuousLinearEquiv`, already used by `toEuclid`); the
   missing plumbing is *post*-composition by the coordinate map
   `ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ` followed by `ℝ ↪ ℂ`.
2. **Inversion domination (~50 LOC).**  `SchwartzMap.fourier_inversion` plus
   `norm_integral_le_integral_norm` give `|u(x)ᵢ| ≤ ∫ ‖𝓕(uᵢ)‖`.
3. **Weighted `L²` membership (~30 LOC).**  `MemLp (‖𝓕(uᵢ)‖·(sobWeight)^{-1/2}) 2`
   from Schwartz decay of `𝓕(uᵢ)` (`SchwartzMap.fourierTransformCLE` maps Schwartz
   to Schwartz), in the style of
   `FourierWeightedPlancherel.integrable_norm_pow_mul_normSq`.
4. **Binomial assembly (~40 LOC).**  `sobWeightInv_eq` expands the weight as
   `(1+|ξ|²)³ = 1 + 3|ξ|² + 3|ξ|⁴ + |ξ|⁶`; the four matching weighted-Plancherel
   rungs are **already established** in `Navier.Analysis.FourierWeightedPlancherel`:
   `spacePlancherel` (n = 0), `sum_integral_normSq_pd_eq` (n = 1),
   `sum_integral_normSq_pd_two_eq` (n = 2), `sum_integral_normSq_pd_three_eq`
   (n = 3).
5. **Component/derivative comparison (~60 LOC).**  `‖iteratedFDeriv ℝ n (uᵢ) x‖ ≤
   ‖iteratedFDeriv ℝ n u x‖` via `ContinuousLinearMap.iteratedFDeriv_comp_left`
   with `‖ContinuousLinearMap.proj i‖ ≤ 1`; the iterated-`pd` versus
   `iteratedFDeriv` norm comparison; and the sup-versus-Euclidean norm equivalence
   on `Fin 3 → ℝ`.  Only this step needs new (elementary) infrastructure.

**Structural note (import DAG).**  Step 4's four rungs exist but sit *downstream*:
`Navier/Analysis/FourierWeightedPlancherel.lean` imports this file, so they are not
in scope here.  Inspection of that file shows the import is unused — it needs only
Mathlib and `EuclideanSpace ℝ (Fin 3)`, never `Space`, `sobWeight`, `toEuclid` or
`spacePlancherel`.  Reversing the edge (drop `import Navier.Analysis.FourierMajorant`
there; import `Navier.Analysis.FourierWeightedPlancherel` here) puts all four rungs
in scope for this residual at zero mathematical cost.  That single-edge refactor is
the prerequisite for closing this statement in place.

Reference: Stein, *Singular Integrals* III.2; Agmon; Majda–Bertozzi Lemma 3.2.
TRUE-as-stated for Schwartz `u` (take `F = ‖𝓕(uᵢ)‖`). -/
theorem exists_scalarFourierSpectralData :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : SchwartzVelocity) (i : Fin 3),
      ∃ F : Space → ℝ, (∀ ξ, 0 ≤ F ξ) ∧
        MemLp (fun ξ => F ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume ∧
        (∀ x : Space, |(⇑u) x i| ≤ ∫ ξ : Space, F ξ) ∧
        spectralMajorant F ≤ C * sobolevH3NormSq u := by
  sorry

/-- **The vector-valued spectral data, reduced to the scalar residual.**  Derived
from `exists_scalarFourierSpectralData` by the kernel-clean componentwise assembly
`exists_spectralData_of_components` (constant `C₂ = 9·C`; the two Cauchy–Schwarz
factors of `3`).  The attack map below records the remaining scalar work and the
Mathlib tools verified present for it.

For every Schwartz velocity `u` there is a nonnegative
spectral density `F` (classically `F ξ = ‖û(ξ)‖`) with (i) `F·(sobWeight)^{-1/2} ∈ L²`,
(ii) Fourier-inversion domination `‖u x‖ ≤ ∫ F`, and (iii) the Plancherel bound
`spectralMajorant F ≤ C₂·‖u‖²_{H³}` uniformly in `u`.

Concrete attack map (Mathlib tools verified present, 2026-07-16):

* **[transport, ~60 LOC]** `Space = Fin 3 → ℝ` is sup-normed, but the Fourier /
  Plancherel API needs an inner-product domain.  Transport via the CLE
  `EuclideanSpace ℝ (Fin 3) ≃L[ℝ] (Fin 3 → ℝ)` and
  `SchwartzMap.compCLMOfContinuousLinearEquiv` (`⇑(compCLMOfCLE 𝕜 g f) = ⇑f ∘ ⇑g`),
  reducing `u` to `SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ` componentwise (embed the
  3 real components `ℝ ↪ ℂ`).  Lebesgue `volume` agrees across the equiv.
* **[Plancherel, in Mathlib]** `SchwartzMap.integral_norm_sq_fourier` :
  `∫‖𝓕f‖² = ∫‖f‖²` — the `n=0` (L²) term directly.
* **[weighted Plancherel, ~200 LOC; n = 1 rung ESTABLISHED 2026-07-22]**
  iterate the Schwartz-level multiplier identity
  `SchwartzMap.fourier_lineDerivOp_eq` (`𝓕(∂ₘf) = 2πi⟨ξ,m⟩·𝓕f`) to get
  `∫‖𝓕f‖²|ξ|^{2n} = c·∫‖D^n f‖²` (n ≤ 3).  The n = 1 rung is
  `FourierWeightedPlancherel.sum_integral_normSq_lineDeriv_eq`
  (`∑ⱼ∫‖∂ⱼf‖² = (2π)²∫‖ξ‖²‖𝓕f‖²`, kernel-clean); n = 2, 3 iterate it on
  `∂ⱼf`; then `sobWeightInv_eq`'s binomial
  `(1+|ξ|²)³ = 1+3|ξ|²+3|ξ|⁴+|ξ|⁶` sums the four terms into
  `C₂·sobolevH3NormSq`.  Mathlib recon 2026-07-22: `Distribution/Sobolev.lean`
  (Bessel-potential spaces) now ships `MemSobolev.fourier_memL1` — the
  qualitative `𝓕f ∈ L¹` half for `2s > d` — and `SchwartzMap.memSobolev`;
  the quantitative physical↔spectral bridge remains this ladder.
* **[substep-3 OBSTRUCTION, found 2026-07-16]** the pointwise multiplier norm is
  assembleable — `‖𝗕(fderiv g) ξ‖ = 2π‖ξ‖‖𝗕g ξ‖` from `Real.fourierIntegral_fderiv`
  + `VectorFourier.norm_fourierSMulRight` (`‖fourierSMulRight L f v‖ = 2π‖L v‖‖f v‖`)
  + `innerSL_apply_norm` (`‖innerSL ℝ ξ‖ = ‖ξ‖`).  But `SchwartzMap.integral_norm_sq_fourier`
  needs a `ℂ`-inner-product codomain, and `fderiv g : ES →L[ℝ] ℂ` has none canonically;
  workaround = scalar partials `∂ⱼg : ES→ℂ` (`fderiv g · eⱼ`, `spacePlancherel` per `j`, sum
  over `j` with HS-vs-operator norm equivalence) + `Integrable (fderiv g)` via
  `SchwartzMap.fderivCLM`.  This is the genuine dedicated-session core.
* **[inversion, ~90 LOC]** `SchwartzMap.fourier_inversion` + `norm_integral_le_integral_norm`
  give `‖u x‖ ≤ ∫‖û‖ = ∫ F`; `MemLp` of `F·(sobWeight)^{-1/2}` from Schwartz decay of `û`.

The Cauchy–Schwarz half is already discharged kernel-cleanly by
`cauchySchwarz_supMajorant`; `sobWeightInv_eq` supplies the weight-polynomial for the
weighted-Plancherel step.  TRUE-as-stated for Schwartz `u` (take `F = ‖û‖`). -/
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
residual: the Cauchy–Schwarz half is kernel-clean here, and the only `sorryAx`
enters through `exists_fourierSpectralData` (Fourier inversion + Plancherel). -/
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


/-- **The `H³(ℝ³) ↪ L^∞` embedding conclusion, reduced to the single Fourier
residual.**  Composing the intermediate assembly with monotonicity of `√` yields
`‖u x‖ ≤ C·√Ms` for any `H³`-majorant `Ms ≥ ‖u‖²_{H³}`.  This is the same statement
as `SobolevEmbedding.sobolevEmbeddingDomination_H3`; here the Cauchy–Schwarz half is
kernel-clean and the sole `sorryAx` enters through `exists_fourierSpectralData`
(Fourier inversion + Plancherel).  Self-contained (√-monotonicity assembly inlined;
no dependence on the SobolevEmbedding olean). -/
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
