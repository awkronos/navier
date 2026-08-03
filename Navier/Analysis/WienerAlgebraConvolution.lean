import Mathlib

/-!
# The Wiener algebra estimate for the critical space

`LeiLinCriticalMechanism` supplies the two gains the fixed-radius restart
discards -- the scale-free dissipation integral and the homogeneous weight --
and the Cauchy-Schwarz interpolation joining `𝒳^{-1}` to `𝒳^{1}`.  It named the
convolution estimate as the remaining input.  This module supplies it.

`𝒳⁰` is the Wiener algebra: the space of lattice-mode coefficient families with
`∑ |û(k)| < ∞`.  The Navier-Stokes nonlinearity `u ⊗ u` is a convolution on the
Fourier side, and the whole Lei-Lin argument rests on the fact that this space
is a **Banach algebra**:

  `‖f ⋆ g‖_{𝒳⁰} ≤ ‖f‖_{𝒳⁰} · ‖g‖_{𝒳⁰}`.

The proof is the product-index rearrangement: the double family
`(j, k) ↦ |f j| · |g k|` is summable with total mass
`(∑|f|)·(∑|g|)`, and the convolution at each mode is a sub-sum of it.

Combined with `LeiLinCriticalMechanism.interpolation_sq_le` this is exactly the
bilinear estimate behind the smallness threshold `‖u₀‖_{𝒳^{-1}} < ν`: the
derivative in `∇·(u ⊗ u)` is absorbed by the `|k|⁻¹` weight
(`homogeneous_weight_cancels_derivative`), the convolution is controlled in
`𝒳⁰` by the algebra property here, and `‖u‖²_{𝒳⁰} ≤ ‖u‖_{𝒳^{-1}}‖u‖_{𝒳¹}`
converts that into the product of the two critical norms.

Scope.  This is the convolution half of the bilinear estimate, unconditional
and for an arbitrary index type with a summable structure.  The Duhamel fixed
point in `L^∞_t 𝒳^{-1} ∩ L¹_t 𝒳¹` is not constructed here.

Reference: Z. Lei and F. Lin, "Global mild solutions of Navier-Stokes
equations", Comm. Pure Appl. Math. 64 (2011) 1297-1304, Sec. 2; N. Wiener,
*The Fourier Integral and Certain of its Applications*, CUP 1933, for the
algebra property of absolutely convergent Fourier series.  Mathlib inputs:
`summable_mul_of_summable_norm`, `tsum_mul_tsum_of_summable_norm`,
`Summable.tsum_le_tsum`, `Summable.tsum_comp_injective`.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.WienerAlgebraConvolution

open scoped Topology

variable {G : Type*} [AddCommGroup G]

/-- The Wiener (`𝒳⁰`) norm of a coefficient family: the total absolute mass. -/
def wienerNorm (f : G → ℝ) : ℝ := ∑' k, |f k|

/-- Membership in the Wiener algebra. -/
abbrev InWiener (f : G → ℝ) : Prop := Summable fun k => |f k|

/-- The convolution of two coefficient families on the mode lattice.  This is
the Fourier-side form of the Navier-Stokes nonlinearity. -/
def conv (f g : G → ℝ) (k : G) : ℝ := ∑' j, f j * g (k - j)

/-- **The product family is summable with the product mass.**

`(j, k) ↦ |f j| · |g k|` is summable and `∑ = (∑|f|)(∑|g|)`.  This is the
engine for both statements below. -/
theorem summable_prod_abs {f g : G → ℝ} (hf : InWiener f) (hg : InWiener g) :
    Summable (fun p : G × G => |f p.1| * |g p.2|) := by
  have hf' : Summable fun k => ‖|f k|‖ := by simpa [Real.norm_eq_abs, abs_abs] using hf
  have hg' : Summable fun k => ‖|g k|‖ := by simpa [Real.norm_eq_abs, abs_abs] using hg
  exact summable_mul_of_summable_norm hf' hg'

/-- The total mass of the product family factorises. -/
theorem tsum_prod_abs {f g : G → ℝ} (hf : InWiener f) (hg : InWiener g) :
    (∑' p : G × G, |f p.1| * |g p.2|) = wienerNorm f * wienerNorm g := by
  have hf' : Summable fun k => ‖|f k|‖ := by simpa [Real.norm_eq_abs, abs_abs] using hf
  have hg' : Summable fun k => ‖|g k|‖ := by simpa [Real.norm_eq_abs, abs_abs] using hg
  exact (tsum_mul_tsum_of_summable_norm hf' hg').symm

/-- **The Wiener norm is nonnegative.** -/
theorem wienerNorm_nonneg (f : G → ℝ) : 0 ≤ wienerNorm f :=
  tsum_nonneg fun _ => abs_nonneg _

/-- The mode-indexed family `F (k, j) = |f j| · |g (k - j)|`.  Its outer index
is the convolution mode. -/
def shiftedFamily (f g : G → ℝ) (p : G × G) : ℝ := |f p.2| * |g (p.1 - p.2)|

/-- `(k, j) ↦ (j, k - j)` is a bijection of the product lattice, carrying the
product family to the mode-indexed family. -/
def modeEquiv : G × G ≃ G × G where
  toFun p := (p.2, p.1 - p.2)
  invFun q := (q.1 + q.2, q.1)
  left_inv p := by simp
  right_inv q := by simp

/-- **The mode-indexed family is summable.** -/
theorem summable_shiftedFamily {f g : G → ℝ} (hf : InWiener f) (hg : InWiener g) :
    Summable (shiftedFamily f g) := by
  have h := (summable_prod_abs hf hg).comp_injective
    (modeEquiv (G := G)).injective
  refine h.congr fun p => ?_
  rfl

/-- **Its total mass is the product of the two Wiener norms.** -/
theorem tsum_shiftedFamily {f g : G → ℝ} (hf : InWiener f) (hg : InWiener g) :
    (∑' p : G × G, shiftedFamily f g p) = wienerNorm f * wienerNorm g := by
  rw [← tsum_prod_abs hf hg]
  exact (modeEquiv (G := G)).tsum_eq (fun q : G × G => |f q.1| * |g q.2|)

/-- **Each convolution mode is absolutely summable.** -/
theorem summable_conv_mode {f g : G → ℝ} (hf : InWiener f) (hg : InWiener g) (k : G) :
    Summable (fun j => f j * g (k - j)) := by
  refine Summable.of_abs ?_
  refine ((summable_shiftedFamily hf hg).prod_factor k).congr fun j => ?_
  rw [shiftedFamily, abs_mul]

/-- **The Wiener algebra estimate.**

`‖f ⋆ g‖_{𝒳⁰} ≤ ‖f‖_{𝒳⁰} · ‖g‖_{𝒳⁰}`.

This is the Banach-algebra property of `𝒳⁰` and the convolution half of the
Lei-Lin bilinear estimate.  Its combination with
`LeiLinCriticalMechanism.interpolation_sq_le` and the derivative cancellation
`|k|⁻¹ · |k| = 1` is what produces the smallness threshold
`‖u₀‖_{𝒳^{-1}} < ν`.

Reference: Lei-Lin, CPAM 64 (2011) 1297-1304, Sec. 2; Wiener 1933. -/
theorem wienerNorm_conv_le {f g : G → ℝ} (hf : InWiener f) (hg : InWiener g) :
    (∑' k, |conv f g k|) ≤ wienerNorm f * wienerNorm g := by
  have hF := summable_shiftedFamily hf hg
  have hfib : HasSum (fun k : G => ∑' j, shiftedFamily f g (k, j))
      (∑' p : G × G, shiftedFamily f g p) :=
    hF.hasSum.prod_fiberwise fun k => (hF.prod_factor k).hasSum
  have hbound : ∀ k : G, |conv f g k| ≤ ∑' j, shiftedFamily f g (k, j) := by
    intro k
    have hs : Summable (fun j => shiftedFamily f g (k, j)) := hF.prod_factor k
    have hs' : Summable fun j => ‖f j * g (k - j)‖ := by
      refine hs.congr fun j => ?_
      simp [shiftedFamily, Real.norm_eq_abs, abs_mul]
    refine (norm_tsum_le_tsum_norm hs').trans_eq ?_
    exact tsum_congr fun j => by simp [shiftedFamily, Real.norm_eq_abs, abs_mul]
  have hsum1 : Summable fun k : G => |conv f g k| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hbound hfib.summable
  calc (∑' k, |conv f g k|)
      ≤ ∑' k, ∑' j, shiftedFamily f g (k, j) :=
        Summable.tsum_le_tsum hbound hsum1 hfib.summable
    _ = ∑' p : G × G, shiftedFamily f g p := hfib.tsum_eq
    _ = wienerNorm f * wienerNorm g := tsum_shiftedFamily hf hg


/-- **The convolution is absolutely summable.**

The companion to `wienerNorm_conv_le`: the convolution of two Wiener-algebra
elements is itself in the Wiener algebra, not merely bounded in it.  Consumers
of the bilinear estimate need this to apply weighted-norm monotonicity. -/
theorem summable_abs_conv {f g : G → ℝ} (hf : InWiener f) (hg : InWiener g) :
    Summable fun k => |conv f g k| := by
  have hF := summable_shiftedFamily hf hg
  have hfib : HasSum (fun k : G => ∑' j, shiftedFamily f g (k, j))
      (∑' p : G × G, shiftedFamily f g p) :=
    hF.hasSum.prod_fiberwise fun k => (hF.prod_factor k).hasSum
  have hbound : ∀ k : G, |conv f g k| ≤ ∑' j, shiftedFamily f g (k, j) := by
    intro k
    have hs : Summable (fun j => shiftedFamily f g (k, j)) := hF.prod_factor k
    have hs' : Summable fun j => ‖f j * g (k - j)‖ := by
      refine hs.congr fun j => ?_
      simp [shiftedFamily, Real.norm_eq_abs, abs_mul]
    refine (norm_tsum_le_tsum_norm hs').trans_eq ?_
    exact tsum_congr fun j => by simp [shiftedFamily, Real.norm_eq_abs, abs_mul]
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hbound hfib.summable

end Navier.Analysis.WienerAlgebraConvolution

#print axioms Navier.Analysis.WienerAlgebraConvolution.summable_prod_abs
#print axioms Navier.Analysis.WienerAlgebraConvolution.tsum_prod_abs
#print axioms Navier.Analysis.WienerAlgebraConvolution.summable_shiftedFamily
#print axioms Navier.Analysis.WienerAlgebraConvolution.tsum_shiftedFamily
#print axioms Navier.Analysis.WienerAlgebraConvolution.summable_conv_mode
#print axioms Navier.Analysis.WienerAlgebraConvolution.wienerNorm_conv_le
#print axioms Navier.Analysis.WienerAlgebraConvolution.summable_abs_conv
