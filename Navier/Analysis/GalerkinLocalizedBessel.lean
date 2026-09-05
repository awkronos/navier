import Navier.Analysis.GalerkinSpectralBands

/-!
# Localized Bessel inequality

For orthonormal functions supported in a measurable frequency band, their
coefficients see only the input restricted to that band. The restricted input
is an actual `L²` element, even though a sharp cutoff need not be Schwartz.
-/

noncomputable section
open MeasureTheory

namespace Navier.Analysis.GalerkinLocalizedBessel

variable {α H ι : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype ι]

theorem toLp_norm_sq (f : α → H) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- A support-localized Bessel bound for an actual square-integrable input.
No regularity of the sharp band boundary is required. -/
theorem sum_inner_sq_le_integralOn
    (w : ι → α → H) (hw : ∀ i, MemLp (w i) 2 μ)
    (horth : Orthonormal ℝ (fun i => (hw i).toLp (w i)))
    (f : α → H) (hf : MemLp f 2 μ) {B : Set α} (hB : MeasurableSet B)
    (hsupport : ∀ i, ∀ᵐ x ∂μ, x ∉ B → w i x = 0) :
    (∑ i, ‖inner ℝ ((hw i).toLp (w i)) (hf.toLp f)‖ ^ 2) ≤
      ∫ x in B, ‖f x‖ ^ 2 ∂μ := by
  have hcut : MemLp (B.indicator f) 2 μ := hf.indicator hB
  have hinner : ∀ i,
      inner ℝ ((hw i).toLp (w i)) (hf.toLp f) =
        inner ℝ ((hw i).toLp (w i)) (hcut.toLp (B.indicator f)) := by
    intro i
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hw i).coeFn_toLp, hf.coeFn_toLp,
      hcut.coeFn_toLp, hsupport i] with x hxw hxf hxc hxs
    rw [hxw, hxf, hxc]
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
    · rw [hxs hx]
      simp
  have hbessel := horth.sum_inner_products_le (s := Finset.univ)
    (hcut.toLp (B.indicator f))
  simp_rw [hinner]
  refine hbessel.trans_eq ?_
  rw [toLp_norm_sq]
  rw [← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ B <;> simp [hx]

end Navier.Analysis.GalerkinLocalizedBessel
