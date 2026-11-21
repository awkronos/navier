import Mathlib

/-!
# X¹-weight heat-kernel smoothing (leaf toward a weaker `SourceL1X1` replacement)

`SourceL1X1` (X¹-weighted source in `L¹_{ξ,t}`) is false for the linked box
(`not_forall_actualLinkedBox_sourceL1X1`). Pointwise,
`‖ξ‖ e^{-ν‖ξ‖²τ} ≤ (e^{-1}/(2ντ))^{1/2}`, so the X¹ Duhamel bound is controlled by
the X⁰-weighted source convolved with `τ^{-1/2}`; a source in `L^p_t(X⁰)`, `p > 2`,
is the natural weaker norm. This file proves the kernel inequality only; the
convolution/Tonelli step is open. No ledger row is closed here.
-/

set_option autoImplicit false

namespace Navier.Analysis.SourceX1HeatKernelBound

/-- `y e^{-y} ≤ e^{-1}` for real `y`. -/
theorem mul_exp_neg_le (y : ℝ) : y * Real.exp (-y) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (y - 1)
  have h2 : y ≤ Real.exp (y - 1) := by linarith
  have e1 : Real.exp (y - 1) = Real.exp y * Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add]; simp
  calc y * Real.exp (-y) ≤ Real.exp (y - 1) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (-1) := by
        rw [e1]; calc Real.exp y * Real.exp (-1) * Real.exp (-y)
            = (Real.exp (-y) * Real.exp y) * Real.exp (-1) := by ring
          _ = Real.exp (-1) := by rw [e2, one_mul]

/-- Heat-kernel smoothing at the `X¹` weight, squared form:
`(‖ξ‖ e^{-c‖ξ‖²})² ≤ e^{-1} / (2c)` for `c > 0`. -/
theorem sq_weight_heat_le (c x : ℝ) (hc : 0 < c) :
    (x * Real.exp (-(c * x ^ 2))) ^ 2 ≤ Real.exp (-1) / (2 * c) := by
  have h := mul_exp_neg_le (2 * c * x ^ 2)
  have e : (x * Real.exp (-(c * x ^ 2))) ^ 2 = x ^ 2 * Real.exp (-(2 * c * x ^ 2)) := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [e, le_div_iff₀ (by positivity)]
  nlinarith [h]

/-- Sqrt form: `|x| e^{-c x²} ≤ (e^{-1}/(2c))^{1/2}`. -/
theorem abs_weight_heat_le (c x : ℝ) (hc : 0 < c) :
    |x| * Real.exp (-(c * x ^ 2)) ≤ Real.sqrt (Real.exp (-1) / (2 * c)) := by
  apply Real.le_sqrt_of_sq_le
  have := sq_weight_heat_le c x hc
  rw [mul_pow, sq_abs, ← mul_pow]; exact this

end Navier.Analysis.SourceX1HeatKernelBound
