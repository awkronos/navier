import Navier.Analysis.Vorticity

/-!
# The curl-component bridge: `‖curl u‖ ≤ C‖∇u‖`

`exists_biotSavartKernelSplitting` (`Navier/Analysis/BKMLogBootstrap.lean`)
carries two Mathlib-absent ingredients: the principal-value Biot–Savart
representation `∇u = PV(∇K ∗ ω)` with its local term, and the **curl-component
bridge** that feeds the vorticity of a Schwartz velocity field into the
Morrey–Agmon Hölder input.  This file certifies the bridge, kernel-clean, and
so removes it from that residual.

`staticCurl u x = Σᵢ eᵢ ×₃ (Du x eᵢ)` is a fixed linear function of the first
derivative, so its Euclidean size is controlled by the operator norm of `Du x`
with an explicit dimensional constant.  The only subtlety is that `Space` is
`Fin 3 → ℝ` with the **product (sup) norm** while the vorticity majorants of
the BKM file are stated in `officialEuclideanNorm`; the two comparisons
`norm_le_officialEuclideanNorm` and `officialEuclideanNorm_le` supply the
`√3` that appears in the constant.

Everything here is kernel-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Navier.Analysis.CurlDerivativeBridge

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity
open scoped Matrix BigOperators

/-- The Euclidean point norm is subadditive along a `Finset` sum: it is the
norm of the linear image of `x` in `EuclideanSpace ℝ (Fin 3)`. -/
theorem officialEuclideanNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Space) :
    officialEuclideanNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, officialEuclideanNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [officialEuclideanNorm_eq_sqrt_sum_sq]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine le_trans ?_ (add_le_add_left ih _)
      -- `officialEuclideanNorm` is the norm of an additive map, so it is subadditive.
      have hadd : officialEuclideanPoint (f a + ∑ i ∈ s, f i) =
          officialEuclideanPoint (f a) + officialEuclideanPoint (∑ i ∈ s, f i) := by
        ext i
        simp [officialEuclideanPoint]
      simpa [officialEuclideanNorm, hadd] using
        norm_add_le (officialEuclideanPoint (f a)) (officialEuclideanPoint (∑ i ∈ s, f i))

/-- **Cauchy–Schwarz for the cross product in the Euclidean point norm.**
`‖a ×₃ b‖ ≤ ‖a‖·‖b‖`, with no hypothesis.  (Lagrange's identity: the defect is
`⟪a,b⟫²`.) -/
theorem officialEuclideanNorm_cross_le (a b : Space) :
    officialEuclideanNorm (a ⨯₃ b) ≤
      officialEuclideanNorm a * officialEuclideanNorm b := by
  have hb : 0 ≤ officialEuclideanNorm a * officialEuclideanNorm b :=
    mul_nonneg (officialEuclideanNorm_nonneg _) (officialEuclideanNorm_nonneg _)
  have hsq : ∀ x : Space, officialEuclideanNorm x ^ 2 = ∑ i : Fin 3, |x i| ^ 2 := by
    intro x
    rw [officialEuclideanNorm_eq_sqrt_sum_sq, Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : officialEuclideanNorm (a ⨯₃ b) ^ 2 ≤
      (officialEuclideanNorm a * officialEuclideanNorm b) ^ 2 := by
    rw [mul_pow, hsq, hsq, hsq]
    simp only [cross_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, sq_abs]
    nlinarith [sq_nonneg (a 0 * b 0 + a 1 * b 1 + a 2 * b 2)]
  nlinarith [officialEuclideanNorm_nonneg (a ⨯₃ b), h1, hb]

/-- The coordinate basis vectors are unit vectors for the product norm. -/
theorem norm_basisVector (j : Fin 3) : ‖(basisVector j : Space)‖ = 1 := by
  rw [basisVector, pi_norm_eq_iff (by norm_num : (0:ℝ) < 1)] <;>
    refine ⟨fun i => ?_, ⟨j, ?_⟩⟩
  · by_cases h : i = j <;> simp [Pi.single_apply, h]
  · simp [Pi.single_apply]

/-- The coordinate basis vectors are unit vectors for the Euclidean point norm. -/
theorem officialEuclideanNorm_basisVector (j : Fin 3) :
    officialEuclideanNorm (basisVector j) = 1 := by
  rw [officialEuclideanNorm_eq_sqrt_sum_sq]
  have : (∑ i : Fin 3, |(basisVector j : Space) i| ^ 2) = 1 := by
    fin_cases j <;>
      simp [basisVector, Pi.single_apply, Fin.sum_univ_three]
  rw [this, Real.sqrt_one]

/-- **The curl-component bridge (certified).**  For any velocity field
differentiable at `x`, the Euclidean size of the coordinate curl is at most
`3√3` times the operator norm of the derivative.

This is the `‖Dⁿ(staticCurl u)‖ ≤ C‖D^{n+1}u‖` bookkeeping of the
`exists_biotSavartKernelSplitting` residual at order `n = 0` — the order the
BKM splitting actually consumes, since the vorticity enters there through the
pointwise majorant `Mω` and through `exists_agmonMorreyBound`. -/
theorem officialEuclideanNorm_staticCurl_le (u : VelocityField) (x : Space) :
    officialEuclideanNorm (staticCurl u x) ≤ 3 * Real.sqrt 3 * ‖fderiv ℝ u x‖ := by
  have hterm : ∀ i : Fin 3,
      officialEuclideanNorm (basisVector i ⨯₃ (fderiv ℝ u x (basisVector i))) ≤
        Real.sqrt 3 * ‖fderiv ℝ u x‖ := by
    intro i
    have hcross := officialEuclideanNorm_cross_le (basisVector i)
      (fderiv ℝ u x (basisVector i))
    rw [officialEuclideanNorm_basisVector, one_mul] at hcross
    refine le_trans hcross ?_
    refine le_trans (officialEuclideanNorm_le _) ?_
    have hop : ‖fderiv ℝ u x (basisVector i)‖ ≤ ‖fderiv ℝ u x‖ := by
      have := (fderiv ℝ u x).le_opNorm (basisVector i)
      rwa [norm_basisVector, mul_one] at this
    exact mul_le_mul_of_nonneg_left hop (Real.sqrt_nonneg 3)
  calc officialEuclideanNorm (staticCurl u x)
      = officialEuclideanNorm
          (∑ i : Fin 3, basisVector i ⨯₃ (fderiv ℝ u x (basisVector i))) := by
        rw [staticCurl]
    _ ≤ ∑ i : Fin 3, officialEuclideanNorm
          (basisVector i ⨯₃ (fderiv ℝ u x (basisVector i))) :=
        officialEuclideanNorm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, Real.sqrt 3 * ‖fderiv ℝ u x‖ :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = 3 * Real.sqrt 3 * ‖fderiv ℝ u x‖ := by
        simp [Finset.sum_const]; ring

end Navier.Analysis.CurlDerivativeBridge
