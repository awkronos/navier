import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The integer-order Kato–Ponce commutator: Leibniz + Hölder

`Navier/Analysis/BKMLogBootstrap.lean` reduces
`exists_sobolevOrderEnergyEstimate` (Majda–Bertozzi Prop. 3.7) to the
Kato–Ponce commutator bound

  `|⟨Dⁿ(u·∇u), Dⁿu⟩| ≤ C‖∇u‖_∞‖u‖²_{Hⁿ}`,  `n ≤ 3`.

For **integer** order `n` the estimate is not the fractional Kato–Ponce
theorem: it is the Leibniz rule for a bounded bilinear map, followed by
Hölder/Cauchy–Schwarz in `L²` with the low-order factor taken in `L^∞`.  Both
of those steps are certified here, kernel-clean, in the exact shape the
bootstrap consumes.

## Contents

* `norm_iteratedFDeriv_bilinear_le_of_supBound` — Leibniz with a sup majorant
  on the first factor: `‖Dⁿ B(f,g)‖ ≤ ‖B‖ Σᵢ C(n,i)·Aᵢ·‖D^{n−i}g‖`.
* `integral_mul_norm_le_sqrt_mul_sqrt` — the `p = q = 2` Hölder step in the
  square-root-of-energy shape this repository states energies in.
* `integral_norm_iteratedFDeriv_bilinear_mul_le` — the assembly: the
  `L²` pairing of `Dⁿ B(f,g)` against `Dⁿ h` is bounded by
  `‖B‖ Σᵢ C(n,i)·Aᵢ·‖D^{n−i}g‖_{L²}·‖Dⁿh‖_{L²}`.

Everything is kernel-clean (`propext`, `Classical.choice`, `Quot.sound` only)
and Mathlib-generic: no Navier–Stokes structure is used, so the file is a
reusable analytic leaf.

**What this does not do.**  It does not supply the Gagliardo–Nirenberg
interpolation that converts `Σᵢ ‖Dⁱu‖_∞‖D^{n−i+1}u‖_{L²}` into
`‖∇u‖_∞‖u‖_{Hⁿ}`, nor the divergence-free cancellation that kills the top
order term `⟨u·∇Dⁿu, Dⁿu⟩`.  Those two remain the named residual.
-/

namespace Navier.Analysis.KatoPonceLeibniz

open MeasureTheory Finset

section Leibniz

variable {𝕜 : Type*} [RCLike 𝕜]
variable {D E F G : Type*}
variable [NormedAddCommGroup D] [NormedSpace 𝕜 D]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Leibniz with a sup majorant on the first factor.**

If `‖Dⁱf‖` is bounded by `A i` uniformly in space for every `i ≤ n`, the
Mathlib bilinear Leibniz bound
`ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear` collapses to a bound
in which the first factor no longer appears pointwise.  This is the step that
turns the Leibniz expansion into something Hölder can act on. -/
theorem norm_iteratedFDeriv_bilinear_le_of_supBound
    (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : WithTop ℕ∞}
    (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) {n : ℕ} (hn : (n : WithTop ℕ∞) ≤ N)
    {A : ℕ → ℝ} (hA : ∀ i ≤ n, ∀ y : D, ‖iteratedFDeriv 𝕜 i f y‖ ≤ A i)
    (x : D) :
    ‖iteratedFDeriv 𝕜 n (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * A i * ‖iteratedFDeriv 𝕜 (n - i) g x‖ := by
  refine le_trans (B.norm_iteratedFDeriv_le_of_bilinear hf hg x hn) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (norm_nonneg B)
  intro i hi
  have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hchoose : (0 : ℝ) ≤ (n.choose i : ℝ) := by positivity
  have hgx : (0 : ℝ) ≤ ‖iteratedFDeriv 𝕜 (n - i) g x‖ := norm_nonneg _
  have hstep : (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ ≤ (n.choose i : ℝ) * A i :=
    mul_le_mul_of_nonneg_left (hA i hile x) hchoose
  exact mul_le_mul_of_nonneg_right hstep hgx

end Leibniz

section Holder

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedAddCommGroup H₂]

/-- **The `p = q = 2` Hölder step, in the square-root-of-energy shape.**

`∫ ‖P‖·‖Q‖ ≤ √(∫‖P‖²)·√(∫‖Q‖²)`.  This repository writes Sobolev energies as
`∫ ‖Dⁿu‖²` (see `sobolevH3NormSq`), so the square-root form is the one the
energy estimate actually consumes. -/
theorem integral_mul_norm_le_sqrt_mul_sqrt {P : α → H₁} {Q : α → H₂}
    (hP : MemLp P 2 μ) (hQ : MemLp Q 2 μ) :
    ∫ x, ‖P x‖ * ‖Q x‖ ∂μ ≤
      Real.sqrt (∫ x, ‖P x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖Q x‖ ^ 2 ∂μ) := by
  have hpq : Real.HolderConjugate 2 2 := by
    constructor <;> norm_num
  have hP' : MemLp (fun x => ‖P x‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hP.norm
  have hQ' : MemLp (fun x => ‖Q x‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hQ.norm
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hpq hP' hQ'
  simp only [Real.norm_eq_abs, abs_norm] at h
  have hrwP : (∫ x, ‖P x‖ ^ (2 : ℝ) ∂μ) = ∫ x, ‖P x‖ ^ (2 : ℕ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact_mod_cast Real.rpow_natCast ‖P x‖ 2
  have hrwQ : (∫ x, ‖Q x‖ ^ (2 : ℝ) ∂μ) = ∫ x, ‖Q x‖ ^ (2 : ℕ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact_mod_cast Real.rpow_natCast ‖Q x‖ 2
  rw [hrwP, hrwQ] at h
  rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

end Holder


section Assembly

variable {D E F G H : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [MeasurableSpace D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **The integer-order Kato–Ponce energy pairing bound (Leibniz + Hölder).**

For a bounded bilinear `B`, a first factor `f` with sup-controlled derivatives
`‖Dⁱf‖ ≤ A i` (`i ≤ n`), and `L²` control on the derivatives of `g` and on
`Dⁿh`, the `L²` pairing of `Dⁿ B(f,g)` against `Dⁿh` obeys

  `∫ ‖Dⁿ B(f,g)‖·‖Dⁿh‖ ≤ ‖B‖ · Σᵢ C(n,i)·Aᵢ · ‖D^{n−i}g‖_{L²} · ‖Dⁿh‖_{L²}`.

Taking `B` the pointwise contraction `(v, w) ↦ v ⬝ w`, `f = g = h = u` and
`n ≤ 3` this is the Leibniz-plus-Hölder half of Majda–Bertozzi Prop. 3.7;
`|⟨Dⁿ(u·∇u), Dⁿu⟩| ≤ ∫ ‖Dⁿ(u·∇u)‖·‖Dⁿu‖` is Cauchy–Schwarz pointwise. -/
theorem integral_norm_iteratedFDeriv_bilinear_mul_le
    {μ : Measure D} (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F} {h : D → H}
    {N : WithTop ℕ∞} (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g)
    {n : ℕ} (hn : (n : WithTop ℕ∞) ≤ N)
    {A : ℕ → ℝ} (hA : ∀ i ≤ n, ∀ y : D, ‖iteratedFDeriv ℝ i f y‖ ≤ A i)
    (hA0 : ∀ i ≤ n, 0 ≤ A i)
    (hg2 : ∀ j ≤ n, MemLp (fun x => iteratedFDeriv ℝ j g x) 2 μ)
    (hh2 : MemLp (fun x => iteratedFDeriv ℝ n h x) 2 μ)
    (hLHS : Integrable (fun x =>
      ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ * ‖iteratedFDeriv ℝ n h x‖) μ) :
    ∫ x, ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ *
        ‖iteratedFDeriv ℝ n h x‖ ∂μ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i *
        (Real.sqrt (∫ x, ‖iteratedFDeriv ℝ (n - i) g x‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x, ‖iteratedFDeriv ℝ n h x‖ ^ 2 ∂μ)) := by
  classical
  -- the summandwise integrability, from `L²·L² ⊆ L¹`
  have hterm : ∀ i ∈ Finset.range (n + 1), Integrable
      (fun x => (‖B‖ * ((n.choose i : ℝ) * A i)) *
        (‖iteratedFDeriv ℝ (n - i) g x‖ * ‖iteratedFDeriv ℝ n h x‖)) μ := by
    intro i _
    have h1 : MemLp (fun x => ‖iteratedFDeriv ℝ (n - i) g x‖) 2 μ :=
      (hg2 (n - i) (Nat.sub_le n i)).norm
    have h2 : MemLp (fun x => ‖iteratedFDeriv ℝ n h x‖) 2 μ := hh2.norm
    have hmul : MemLp
        (fun x => ‖iteratedFDeriv ℝ (n - i) g x‖ * ‖iteratedFDeriv ℝ n h x‖) 1 μ :=
      h2.mul' h1
    exact (memLp_one_iff_integrable.mp hmul).const_mul _
  have hsumint : Integrable (fun x => ∑ i ∈ Finset.range (n + 1),
      (‖B‖ * ((n.choose i : ℝ) * A i)) *
        (‖iteratedFDeriv ℝ (n - i) g x‖ * ‖iteratedFDeriv ℝ n h x‖)) μ :=
    integrable_finsetSum _ hterm
  -- Step 1: pointwise Leibniz with the sup majorant, times `‖Dⁿh‖ ≥ 0`.
  have hpt : ∀ x : D,
      ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ * ‖iteratedFDeriv ℝ n h x‖ ≤
        ∑ i ∈ Finset.range (n + 1), (‖B‖ * ((n.choose i : ℝ) * A i)) *
          (‖iteratedFDeriv ℝ (n - i) g x‖ * ‖iteratedFDeriv ℝ n h x‖) := by
    intro x
    have hL := norm_iteratedFDeriv_bilinear_le_of_supBound B hf hg hn hA x
    have hstep := mul_le_mul_of_nonneg_right hL (norm_nonneg (iteratedFDeriv ℝ n h x))
    refine le_trans hstep (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hstep1 : ∫ x, ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ *
      ‖iteratedFDeriv ℝ n h x‖ ∂μ ≤
      ∫ x, ∑ i ∈ Finset.range (n + 1), (‖B‖ * ((n.choose i : ℝ) * A i)) *
        (‖iteratedFDeriv ℝ (n - i) g x‖ * ‖iteratedFDeriv ℝ n h x‖) ∂μ :=
    integral_mono hLHS hsumint hpt
  -- Step 2: swap the finite sum with the integral, pull the constants out.
  have hstep2 : ∫ x, ∑ i ∈ Finset.range (n + 1), (‖B‖ * ((n.choose i : ℝ) * A i)) *
      (‖iteratedFDeriv ℝ (n - i) g x‖ * ‖iteratedFDeriv ℝ n h x‖) ∂μ =
      ∑ i ∈ Finset.range (n + 1), (‖B‖ * ((n.choose i : ℝ) * A i)) *
        ∫ x, ‖iteratedFDeriv ℝ (n - i) g x‖ * ‖iteratedFDeriv ℝ n h x‖ ∂μ := by
    rw [integral_finsetSum _ hterm]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  -- Step 3: Hölder on each summand.
  have hstep3 : ∑ i ∈ Finset.range (n + 1), (‖B‖ * ((n.choose i : ℝ) * A i)) *
      ∫ x, ‖iteratedFDeriv ℝ (n - i) g x‖ * ‖iteratedFDeriv ℝ n h x‖ ∂μ ≤
      ∑ i ∈ Finset.range (n + 1), (‖B‖ * ((n.choose i : ℝ) * A i)) *
        (Real.sqrt (∫ x, ‖iteratedFDeriv ℝ (n - i) g x‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x, ‖iteratedFDeriv ℝ n h x‖ ^ 2 ∂μ)) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hc : (0 : ℝ) ≤ ‖B‖ * ((n.choose i : ℝ) * A i) := by
      have := hA0 i hile
      positivity
    exact mul_le_mul_of_nonneg_left
      (integral_mul_norm_le_sqrt_mul_sqrt (hg2 (n - i) (Nat.sub_le n i)) hh2) hc
  have hfinal : ∑ i ∈ Finset.range (n + 1), (‖B‖ * ((n.choose i : ℝ) * A i)) *
      (Real.sqrt (∫ x, ‖iteratedFDeriv ℝ (n - i) g x‖ ^ 2 ∂μ) *
        Real.sqrt (∫ x, ‖iteratedFDeriv ℝ n h x‖ ^ 2 ∂μ)) =
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i *
        (Real.sqrt (∫ x, ‖iteratedFDeriv ℝ (n - i) g x‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x, ‖iteratedFDeriv ℝ n h x‖ ^ 2 ∂μ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc _ ≤ _ := hstep1
    _ = _ := hstep2
    _ ≤ _ := hstep3
    _ = _ := hfinal

end Assembly

end Navier.Analysis.KatoPonceLeibniz
