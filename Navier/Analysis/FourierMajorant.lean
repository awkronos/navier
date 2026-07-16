import Navier.Analysis.WeightIntegrability
import Navier.Analysis.BKMLogBootstrap

/-!
# Fourier majorant infrastructure for the `H³(ℝ³) ↪ L^∞` Sobolev embedding

This is the reusable analytic core of the Beale–Kato–Majda Sobolev-embedding
route.  The certified interface `SobolevEmbedding.sobolev_domination_of_intermediate`
turns two analytic bounds on a Fourier-side majorant `Q` into the embedding
`‖u‖_∞ ≤ C·√Ms`.  This file supplies the *first* of those two bounds
kernel-cleanly (the Cauchy–Schwarz step) and reduces the embedding to a single
named Fourier residual (inversion + Plancherel).

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
## The Fourier residual and the intermediate-majorant assembly
-/

/-- **[RESIDUAL — the Fourier/Plancherel core; Stein *Singular Integrals* III.2
(inversion); Majda–Bertozzi Lemma 3.2 + L² Plancherel (`fourierIntegral`
isometry); est ~250 LOC.]**  For every Schwartz velocity field `u` there is a
nonnegative spectral density `F` (classically `F ξ = ‖û(ξ)‖`) with:

* **finite weighted `L²` mass** — `F·(sobWeight)^{-1/2} ∈ L²`, i.e. the Fourier
  majorant `spectralMajorant F = ∫‖û‖²(1+|ξ|²)³` is finite (Schwartz decay);
* **Fourier-inversion domination** — `‖u x‖ ≤ ∫ F` for all `x`, from
  `u(x) = ∫ û(ξ)·e^{2πi⟨ξ,x⟩} dξ` (`SchwartzMap.fourier_inversion`) and
  `|u(x)| ≤ ∫‖û‖` (`norm_integral_le_integral_norm`);
* **Plancherel bound** — `spectralMajorant F ≤ C₂·‖u‖²_{H³}` uniformly in `u`,
  from `∫‖û‖²|ξ|^{2n} = c·∫‖D^n u‖²` (Plancherel + differentiation-multiplier) and
  the binomial expansion of `(1+|ξ|²)³`.

Mathlib-absent piece: the vector-valued Schwartz Fourier–Plancherel identity for
the sup-normed domain/codomain `Space = Fin 3 → ℝ` (Mathlib's
`SchwartzMap.fourierTransformCLM` needs an inner-product domain; the coordinatewise
`EuclideanSpace`/`fourierIntegral` reduction is the ~250-LOC construction).  The
Cauchy–Schwarz half is already discharged kernel-cleanly by
`cauchySchwarz_supMajorant`, so this is the *sole* remaining analytic content. -/
theorem exists_fourierSpectralData :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ u : SchwartzVelocity,
      ∃ F : Space → ℝ, (∀ ξ, 0 ≤ F ξ) ∧
        MemLp (fun ξ => F ξ * Real.sqrt (sobWeight ξ)⁻¹) 2 volume ∧
        (∀ x : Space, ‖(⇑u) x‖ ≤ ∫ ξ : Space, F ξ) ∧
        spectralMajorant F ≤ C₂ * sobolevH3NormSq u := by
  sorry

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

end Navier.Analysis.FourierMajorant
