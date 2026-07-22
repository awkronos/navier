import Navier.Analysis.FourierMajorant

/-!
# The n = 1 weighted Plancherel rung (Fourier residual, substep 3)

The first multiplier rung of the `exists_fourierSpectralData` attack map:
on the Euclidean model `ES = EuclideanSpace ℝ (Fin 3)`,

  `∑ⱼ ∫ ‖∂ⱼ f‖² = (2π)² ∫ ‖ξ‖² ‖𝓕f(ξ)‖²`

(`sum_integral_normSq_lineDeriv_eq`): Mathlib's Schwartz-level
`fourier_lineDerivOp_eq` multiplier identity (`𝓕(∂ₘf) = 2πi⟨ξ,m⟩·𝓕f`),
Plancherel per direction (`integral_norm_sq_fourier`), and the basis
expansion `∑ⱼ⟨ξ,eⱼ⟩² = ‖ξ‖²`.  With `spacePlancherel` (n = 0) this begins
the ladder `∫(1+‖ξ‖²)ⁿ‖𝓕f‖² ≈ ∑_{k≤n}‖Dᵏf‖²` toward the substep-3 weighted
Plancherel of `exists_fourierSpectralData`; the n = 2, 3 rungs iterate the
same multiplier identity on `∂ⱼf`.

Recon note (2026-07-22): Mathlib now also ships
`Mathlib/Analysis/Distribution/Sobolev.lean` (Bessel-potential Sobolev
spaces) with `MemSobolev.fourier_memL1` — the qualitative `𝓕f ∈ L¹` half of
the embedding for `2s > d` — and `SchwartzMap.memSobolev`.  The remaining
quantitative content of the residual is exactly this ladder (physical
derivative norms vs the spectral weight), plus the inversion-domination
substep.

Supporting: `integrable_normSq` — the square of a Schwartz map is
integrable (decay bound times integrability).

Reference: Stein, *Singular Integrals* III.2; Majda–Bertozzi Lemma 3.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory SchwartzMap LineDeriv
open scoped FourierTransform SchwartzMap

namespace Navier.Analysis.FourierWeightedPlancherel

open Navier

abbrev ES := EuclideanSpace ℝ (Fin 3)

theorem integrable_normSq (g : 𝓢(ES, ℂ)) :
    Integrable (fun x : ES => ‖g x‖ ^ 2) := by
  obtain ⟨C, _, hC⟩ := g.decay 0 0
  have hCnn : ∀ x : ES, ‖g x‖ ≤ C := by
    intro x
    have := hC x
    simpa using this
  refine (g.integrable.norm.const_mul C).mono'
    ((map_continuous g).norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc ‖g x‖ ^ 2 = ‖g x‖ * ‖g x‖ := sq (‖g x‖)
    _ ≤ C * ‖g x‖ := mul_le_mul_of_nonneg_right (hCnn x) (norm_nonneg _)

theorem norm_fourier_lineDerivOp_sq (f : 𝓢(ES, ℂ)) (m : ES) (ξ : ES) :
    ‖(𝓕 (∂_{m} f)) ξ‖ ^ 2 =
      (2 * Real.pi) ^ 2 * (inner ℝ ξ m) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have hg : (fun x : ES => inner ℝ x m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [smul_apply, smulLeftCLM_apply_apply hg]
  rw [norm_smul, norm_smul]
  have h2πi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul]
    simp [Real.pi_nonneg]
  rw [h2πi, Real.norm_eq_abs]
  ring_nf
  rw [sq_abs]
  ring

/-- **The n = 1 weighted Plancherel (multiplier) identity on the Euclidean
model**: the summed derivative L² masses equal `(2π)²` times the
`|ξ|²`-weighted L² mass of the Fourier transform. -/
theorem sum_integral_normSq_lineDeriv_eq (f : 𝓢(ES, ℂ)) :
    ∑ j : Fin 3, ∫ x : ES, ‖(∂_{EuclideanSpace.single j (1:ℝ)} f) x‖ ^ 2
      = (2 * Real.pi) ^ 2 * ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
  have hstep : ∀ j : Fin 3,
      (∫ x : ES, ‖(∂_{EuclideanSpace.single j (1:ℝ)} f) x‖ ^ 2) =
      ∫ ξ : ES, (2 * Real.pi) ^ 2 *
        (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
    intro j
    rw [← SchwartzMap.integral_norm_sq_fourier (∂_{EuclideanSpace.single j (1:ℝ)} f)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ =>
      norm_fourier_lineDerivOp_sq f (EuclideanSpace.single j (1:ℝ)) ξ)
  have hint : ∀ j : Fin 3, Integrable (fun ξ : ES =>
      (2 * Real.pi) ^ 2 * (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
        ‖(𝓕 f) ξ‖ ^ 2) := by
    intro j
    have := integrable_normSq (𝓕 (∂_{EuclideanSpace.single j (1:ℝ)} f))
    refine this.congr ?_
    filter_upwards with ξ
    exact norm_fourier_lineDerivOp_sq f (EuclideanSpace.single j (1:ℝ)) ξ
  calc ∑ j : Fin 3, ∫ x : ES, ‖(∂_{EuclideanSpace.single j (1:ℝ)} f) x‖ ^ 2
      = ∑ j : Fin 3, ∫ ξ : ES, (2 * Real.pi) ^ 2 *
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => hstep j
    _ = ∫ ξ : ES, ∑ j : Fin 3, (2 * Real.pi) ^ 2 *
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 :=
        (integral_finsetSum _ fun j _ => hint j).symm
    _ = ∫ ξ : ES, (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
        apply integral_congr_ae
        filter_upwards with ξ
        have hsum : ∑ j : Fin 3, (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2
            = ‖ξ‖ ^ 2 := by
          have hin : ∀ j : Fin 3,
              (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) = ξ j := by
            intro j
            rw [EuclideanSpace.inner_single_right]
            simp
          rw [Finset.sum_congr rfl fun j _ => by rw [hin j]]
          rw [EuclideanSpace.norm_eq]
          rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
          exact Finset.sum_congr rfl fun j _ => by
            rw [Real.norm_eq_abs, sq_abs]
        calc ∑ j : Fin 3, (2 * Real.pi) ^ 2 *
              (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2
            = ∑ j : Fin 3,
                (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
                  ((2 * Real.pi) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) :=
              Finset.sum_congr rfl fun j _ => by ring
            _ = ‖ξ‖ ^ 2 * ((2 * Real.pi) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
              rw [← Finset.sum_mul, hsum]
            _ = (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
              ring
    _ = (2 * Real.pi) ^ 2 * ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 :=
        integral_const_mul _ _
end Navier.Analysis.FourierWeightedPlancherel
