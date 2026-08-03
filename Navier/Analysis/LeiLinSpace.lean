import Mathlib
import Navier.Analysis.WienerAlgebraConvolution
import Navier.Analysis.LeiLinCriticalMechanism

/-!
# The Lei-Lin critical spaces `𝒳^{-1}`, `𝒳⁰`, `𝒳¹` on a mode lattice

Step 1 of the Lei-Lin assembly.  `LeiLinCriticalMechanism` supplied the two
mechanisms (scale-free dissipation, homogeneous weight) and the finite-sum
interpolation; `WienerAlgebraConvolution` supplied the Banach-algebra bound on
`𝒳⁰`.  This module defines the three norms as genuine `tsum`s over the mode
lattice and upgrades the interpolation to the infinite-sum form.

Setup.  `G` is the mode lattice (an additive commutative group; `ℤ × ℤ × ℤ` is
the intended instance) and `σ : G → ℝ` is the mode size `σ k = |k|`.  For a
coefficient family `f : G → ℝ`:

* `normX0 f     = ∑' k, |f k|`                (the Wiener algebra)
* `normXm1 σ f  = ∑' k, (σ k)⁻¹ * |f k|`      (`𝒳^{-1}`, the critical space)
* `normX1  σ f  = ∑' k, (σ k) * |f k|`        (`𝒳¹`)

The zero mode.  `σ 0 = 0`, and Lean's junk convention `0⁻¹ = 0` makes the
`𝒳^{-1}` weight vanish there.  This is exactly right: the Lei-Lin space is
defined on mean-zero fields, and the zero mode carries no `𝒳^{-1}` mass.  It
also makes `normXm1_deriv_le` below hold with no side condition at `k = 0`.

Scope.  Definitions and the two inequalities used downstream
(`interpolation_tsum`, `normXm1_deriv_le`).  No solution is constructed here and
nothing in this file claims global regularity for large data.

Reference: Z. Lei and F. Lin, "Global mild solutions of Navier-Stokes
equations", Comm. Pure Appl. Math. 64 (2011) 1297-1304.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.LeiLinSpace

open Filter Topology

variable {G : Type*}

/-- The weighted Wiener norm `∑' k, w k * |f k|`. -/
def wNorm (w f : G → ℝ) : ℝ := ∑' k, w k * |f k|

/-- Summability of the weighted family: membership in the weighted space. -/
abbrev InW (w f : G → ℝ) : Prop := Summable fun k => w k * |f k|

/-- The `𝒳⁰` (Wiener algebra) norm. -/
def normX0 (f : G → ℝ) : ℝ := ∑' k, |f k|

/-- The `𝒳^{-1}` norm: weight `|k|⁻¹`.  This is the critical Lei-Lin norm. -/
def normXm1 (σ f : G → ℝ) : ℝ := wNorm (fun k => (σ k)⁻¹) f

/-- The `𝒳¹` norm: weight `|k|`. -/
def normX1 (σ f : G → ℝ) : ℝ := wNorm σ f

theorem normX0_eq_wienerNorm (f : G → ℝ) :
    normX0 f = WienerAlgebraConvolution.wienerNorm f := rfl

theorem wNorm_nonneg {w f : G → ℝ} (hw : ∀ k, 0 ≤ w k) : 0 ≤ wNorm w f :=
  tsum_nonneg fun k => mul_nonneg (hw k) (abs_nonneg _)

theorem normX0_nonneg (f : G → ℝ) : 0 ≤ normX0 f := tsum_nonneg fun _ => abs_nonneg _

theorem normXm1_nonneg {σ : G → ℝ} (hσ : ∀ k, 0 ≤ σ k) (f : G → ℝ) :
    0 ≤ normXm1 σ f :=
  wNorm_nonneg fun k => inv_nonneg.mpr (hσ k)

theorem normX1_nonneg {σ : G → ℝ} (hσ : ∀ k, 0 ≤ σ k) (f : G → ℝ) :
    0 ≤ normX1 σ f := wNorm_nonneg hσ

/-! ## The interpolation inequality at the level of infinite sums -/

/-- **`‖f‖²_{𝒳⁰} ≤ ‖f‖_{𝒳^{-1}} · ‖f‖_{𝒳¹}`.**

The `tsum` form of `LeiLinCriticalMechanism.interpolation_sq_le`, obtained by
passing to the limit along finite subsets.  This is the estimate that converts
the Banach-algebra bound in `𝒳⁰` into a product of the two critical norms, and
it is where the smallness threshold `‖u₀‖_{𝒳^{-1}} < ν` comes from. -/
theorem interpolation_tsum {σ f : G → ℝ} (hσ : ∀ k, 0 < σ k)
    (h0 : Summable fun k => |f k|)
    (hm : InW (fun k => (σ k)⁻¹) f) (hp : InW σ f) :
    normX0 f ^ 2 ≤ normXm1 σ f * normX1 σ f := by
  have hfinite : ∀ s : Finset G,
      (∑ i ∈ s, |f i|) ^ 2 ≤ normXm1 σ f * normX1 σ f := by
    intro s
    refine le_trans (LeiLinCriticalMechanism.interpolation_sq_le s (fun i => |f i|) σ
      (fun i _ => abs_nonneg _) (fun i _ => hσ i)) ?_
    have h1 : (∑ i ∈ s, (σ i)⁻¹ * |f i|) ≤ normXm1 σ f :=
      hm.sum_le_tsum s (fun i _ => mul_nonneg (inv_nonneg.mpr (hσ i).le) (abs_nonneg _))
    have h2 : (∑ i ∈ s, σ i * |f i|) ≤ normX1 σ f :=
      hp.sum_le_tsum s (fun i _ => mul_nonneg (hσ i).le (abs_nonneg _))
    have hn1 : 0 ≤ ∑ i ∈ s, (σ i)⁻¹ * |f i| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.mpr (hσ i).le) (abs_nonneg _)
    have hn2 : 0 ≤ ∑ i ∈ s, σ i * |f i| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hσ i).le (abs_nonneg _)
    exact mul_le_mul h1 h2 hn2 (normXm1_nonneg (fun k => (hσ k).le) f)
  have hbase : Tendsto (fun s : Finset G => ∑ i ∈ s, |f i|) atTop (𝓝 (normX0 f)) :=
    h0.hasSum
  have htend : Tendsto (fun s : Finset G => (∑ i ∈ s, |f i|) ^ 2) atTop
      (𝓝 (normX0 f ^ 2)) := hbase.pow 2
  exact le_of_tendsto htend (Eventually.of_forall hfinite)

/-! ## The derivative cancellation at the level of norms -/

/-- **The homogeneous weight absorbs the derivative.**

If `Df k = σ k * f k` is the Fourier multiplier by `|k|` (the derivative in
`∇·(u ⊗ u)`), then `‖Df‖_{𝒳^{-1}} ≤ ‖f‖_{𝒳⁰}`, because `|k|⁻¹ · |k| ≤ 1`
pointwise, with equality off the zero mode.  This is
`LeiLinCriticalMechanism.homogeneous_weight_cancels_derivative` promoted to the
norms. -/
theorem normXm1_deriv_le {σ f : G → ℝ} (hσ : ∀ k, 0 ≤ σ k)
    (h0 : Summable fun k => |f k|) :
    normXm1 σ (fun k => σ k * f k) ≤ normX0 f := by
  have hle : ∀ k, (σ k)⁻¹ * |σ k * f k| ≤ |f k| := by
    intro k
    rcases eq_or_lt_of_le (hσ k) with h | h
    · simp [← h]
    · rw [abs_mul, abs_of_pos h, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt h), one_mul]
  have hsum : Summable fun k => (σ k)⁻¹ * |σ k * f k| :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (inv_nonneg.mpr (hσ k)) (abs_nonneg _)) hle h0
  exact hsum.tsum_le_tsum hle h0


/-- **Interpolation for mean-zero families.**

The same Cauchy-Schwarz interpolation as `interpolation_tsum`, but with the
weight allowed to vanish, provided the family vanishes wherever the weight does.
This is the form the mode lattice actually needs: on `G = ℤ³` the zero mode has
`σ 0 = 0`, and a mean-zero velocity field has no zero mode, so `hz` holds.
Without `hz` the inequality is false at the zero mode, where the left side sees
`|f 0|` and the right side weights it by `0⁻¹ = 0`. -/
theorem interpolation_tsum_meanZero {σ f : G → ℝ} (hσ : ∀ k, 0 ≤ σ k)
    (hz : ∀ k, σ k = 0 → f k = 0)
    (h0 : Summable fun k => |f k|)
    (hm : InW (fun k => (σ k)⁻¹) f) (hp : InW σ f) :
    normX0 f ^ 2 ≤ normXm1 σ f * normX1 σ f := by
  have hfinite : ∀ s : Finset G,
      (∑ i ∈ s, |f i|) ^ 2 ≤ normXm1 σ f * normX1 σ f := by
    intro s
    classical
    have hsub : s.filter (fun i => σ i ≠ 0) ⊆ s := Finset.filter_subset _ s
    have hzero : ∀ i ∈ s, i ∉ s.filter (fun i => σ i ≠ 0) → |f i| = 0 := by
      intro i hi hni
      have : σ i = 0 := by
        by_contra hne
        exact hni (Finset.mem_filter.mpr ⟨hi, hne⟩)
      rw [hz i this, abs_zero]
    have hsum_eq : (∑ i ∈ s.filter (fun i => σ i ≠ 0), |f i|) = ∑ i ∈ s, |f i| :=
      Finset.sum_subset hsub hzero
    have hpos : ∀ i ∈ s.filter (fun i => σ i ≠ 0), 0 < σ i := by
      intro i hi
      exact lt_of_le_of_ne (hσ i) (Ne.symm (Finset.mem_filter.mp hi).2)
    rw [← hsum_eq]
    refine le_trans (LeiLinCriticalMechanism.interpolation_sq_le
      (s.filter (fun i => σ i ≠ 0)) (fun i => |f i|) σ
      (fun i _ => abs_nonneg _) hpos) ?_
    have h1 : (∑ i ∈ s.filter (fun i => σ i ≠ 0), (σ i)⁻¹ * |f i|) ≤ normXm1 σ f :=
      hm.sum_le_tsum _ (fun i _ => mul_nonneg (inv_nonneg.mpr (hσ i)) (abs_nonneg _))
    have h2 : (∑ i ∈ s.filter (fun i => σ i ≠ 0), σ i * |f i|) ≤ normX1 σ f :=
      hp.sum_le_tsum _ (fun i _ => mul_nonneg (hσ i) (abs_nonneg _))
    have hn2 : 0 ≤ ∑ i ∈ s.filter (fun i => σ i ≠ 0), σ i * |f i| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hσ i) (abs_nonneg _)
    exact mul_le_mul h1 h2 hn2 (normXm1_nonneg hσ f)
  have hbase : Tendsto (fun s : Finset G => ∑ i ∈ s, |f i|) atTop (𝓝 (normX0 f)) :=
    h0.hasSum
  exact le_of_tendsto (hbase.pow 2) (Eventually.of_forall hfinite)

/-- `‖f‖_{𝒳⁰} ≤ (‖f‖_{𝒳^{-1}} ‖f‖_{𝒳¹})^{1/2}`, the square-root form of the
interpolation, which is what the bilinear estimate consumes. -/
theorem normX0_le_sqrt {σ f : G → ℝ} (hσ : ∀ k, 0 ≤ σ k)
    (hz : ∀ k, σ k = 0 → f k = 0)
    (h0 : Summable fun k => |f k|)
    (hm : InW (fun k => (σ k)⁻¹) f) (hp : InW σ f) :
    normX0 f ≤ Real.sqrt (normXm1 σ f * normX1 σ f) := by
  have hsq := interpolation_tsum_meanZero hσ hz h0 hm hp
  have hy : 0 ≤ normXm1 σ f * normX1 σ f :=
    mul_nonneg (normXm1_nonneg hσ f) (normX1_nonneg hσ f)
  exact (Real.le_sqrt (normX0_nonneg f) hy).mpr hsq

end Navier.Analysis.LeiLinSpace

#print axioms Navier.Analysis.LeiLinSpace.interpolation_tsum
#print axioms Navier.Analysis.LeiLinSpace.normXm1_deriv_le
