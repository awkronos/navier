import Navier.Analysis.LeiLinSpace

/-!
# The Lei-Lin bilinear estimate in the critical norms

Step 3 of the Lei-Lin assembly.  The Navier-Stokes nonlinearity is, on the
Fourier side, a convolution followed by one derivative:
`k ↦ |k| (û ⋆ v̂)(k)`.  Three ingredients already exist and are combined here.

1. `WienerAlgebraConvolution.wienerNorm_conv_le` : `‖u ⋆ v‖_{𝒳⁰} ≤ ‖u‖_{𝒳⁰}‖v‖_{𝒳⁰}`.
2. `LeiLinSpace.normXm1_deriv_le` : the `|k|⁻¹` weight absorbs the derivative
   exactly, so the derivative costs nothing in `𝒳^{-1}`.
3. `LeiLinSpace.normX0_le_sqrt` : `‖u‖_{𝒳⁰} ≤ (‖u‖_{𝒳^{-1}}‖u‖_{𝒳¹})^{1/2}`.

Chaining them gives `‖B(u,v)‖_{𝒳^{-1}} ≤ (‖u‖_{-1}‖u‖_1)^{1/2}(‖v‖_{-1}‖v‖_1)^{1/2}`,
and one application of AM-GM against the mixed norm `‖·‖_{-1} + ν‖·‖_1`
produces the constant `1/(4ν)` -- the constant that makes `‖u₀‖_{𝒳^{-1}} < ν`
the smallness threshold.

Scope.  This is the estimate **at a fixed time**, with the mixed quantity
`‖u‖_{𝒳^{-1}} + ν‖u‖_{𝒳¹}` formed from the two norms of one coefficient family.
Passing to the genuine mixed norm `L^∞_t 𝒳^{-1} ∩ L¹_t 𝒳¹` requires, in
addition, the Cauchy-Schwarz inequality in the time variable applied to
`∫₀^∞ ‖u(t)‖_{𝒳¹}^{1/2}‖v(t)‖_{𝒳¹}^{1/2} dt`; that step and the Duhamel fixed
point are not in this file.  Nothing here claims global regularity.

Reference: Z. Lei and F. Lin, CPAM 64 (2011) 1297-1304, Sec. 2.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.LeiLinBilinear

open LeiLinSpace WienerAlgebraConvolution

variable {G : Type*} [AddCommGroup G]

/-! ## The convolution half, in the critical norm -/

/-- **The nonlinearity is bounded in `𝒳^{-1}` by the product of `𝒳⁰` norms.**

`‖ |k| (u ⋆ v) ‖_{𝒳^{-1}} ≤ ‖u‖_{𝒳⁰} ‖v‖_{𝒳⁰}`.

The derivative is absorbed by the homogeneous weight with no loss, and the
convolution is controlled by the Banach-algebra property of the Wiener
algebra. -/
theorem bilinear_Xm1_le {σ u v : G → ℝ} (hσ : ∀ k, 0 ≤ σ k)
    (hu : InWiener u) (hv : InWiener v) :
    normXm1 σ (fun k => σ k * conv u v k) ≤ normX0 u * normX0 v :=
  (normXm1_deriv_le hσ (summable_abs_conv hu hv)).trans (wienerNorm_conv_le hu hv)

/-! ## The scalar AM-GM producing the constant `1/(4ν)` -/

/-- `√(xy) ≤ (x+y)/2` for nonnegative reals. -/
theorem sqrt_mul_le_add_div_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x * y) ≤ (x + y) / 2 := by
  rw [Real.sqrt_mul hx]
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt hx, Real.sq_sqrt hy,
    Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- **The AM-GM step against the mixed norm.**

`√(AB)·√(CD) ≤ (1/(4ν))·(A + νB)(C + νD)`.

With `A = ‖u‖_{𝒳^{-1}}`, `B = ‖u‖_{𝒳¹}` this is exactly how the viscosity
enters the bilinear constant: the mixed norm weights the `𝒳¹` part by `ν`, and
the geometric mean is dominated by a quarter of the product of the mixed
quantities.  The `4` here and the `ν` are the source of the Lei-Lin threshold. -/
theorem sqrt_mul_sqrt_le_quarter {ν A B C D : ℝ} (hν : 0 < ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    Real.sqrt (A * B) * Real.sqrt (C * D)
      ≤ (1 / (4 * ν)) * ((A + ν * B) * (C + ν * D)) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hsq : Real.sqrt ν * Real.sqrt ν = ν := Real.mul_self_sqrt hν.le
  have h1 : Real.sqrt (A * B) * Real.sqrt ν ≤ (A + ν * B) / 2 := by
    rw [← Real.sqrt_mul (mul_nonneg hA hB)]
    have hre : A * B * ν = A * (ν * B) := by ring
    rw [hre]
    exact sqrt_mul_le_add_div_two hA (mul_nonneg hν.le hB)
  have h2 : Real.sqrt (C * D) * Real.sqrt ν ≤ (C + ν * D) / 2 := by
    rw [← Real.sqrt_mul (mul_nonneg hC hD)]
    have hre : C * D * ν = C * (ν * D) := by ring
    rw [hre]
    exact sqrt_mul_le_add_div_two hC (mul_nonneg hν.le hD)
  have hXY : 0 ≤ Real.sqrt (A * B) * Real.sqrt (C * D) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h3 : (Real.sqrt (A * B) * Real.sqrt ν) * (Real.sqrt (C * D) * Real.sqrt ν)
      ≤ ((A + ν * B) / 2) * ((C + ν * D) / 2) :=
    mul_le_mul h1 h2 (mul_nonneg (Real.sqrt_nonneg _) hs.le) (by positivity)
  have h4 : (Real.sqrt (A * B) * Real.sqrt (C * D)) * ν
      ≤ ((A + ν * B) * (C + ν * D)) / 4 := by nlinarith [h3, hsq]
  have h4ν : (0:ℝ) < 4 * ν := by linarith
  have hgoal : (Real.sqrt (A * B) * Real.sqrt (C * D)) * (4 * ν)
      ≤ (A + ν * B) * (C + ν * D) := by nlinarith [h4]
  rw [show (1 / (4 * ν)) * ((A + ν * B) * (C + ν * D))
      = ((A + ν * B) * (C + ν * D)) / (4 * ν) by ring]
  exact (le_div_iff₀ h4ν).mpr hgoal

/-! ## The Lei-Lin bilinear estimate at a fixed time -/

/-- **The bilinear estimate with the Lei-Lin constant `1/(4ν)`.**

`‖ |k| (u ⋆ v) ‖_{𝒳^{-1}} ≤ (1/(4ν)) (‖u‖_{-1} + ν‖u‖_1)(‖v‖_{-1} + ν‖v‖_1)`.

Every input is the one the paper uses: the Wiener-algebra bound, the exact
derivative cancellation by the homogeneous weight, the Cauchy-Schwarz
interpolation between the two critical norms, and AM-GM against the viscosity.

The mean-zero hypotheses `hzu`, `hzv` say the families vanish at modes of zero
size; on `G = ℤ³` this is exactly the absence of the zero mode, and without it
the interpolation step is false there.

Scope: fixed time.  The `L^∞_t ∩ L¹_t` version needs Cauchy-Schwarz in time as
well; this file does not construct a solution. -/
theorem bilinear_mixed_le {ν : ℝ} {σ u v : G → ℝ} (hν : 0 < ν) (hσ : ∀ k, 0 ≤ σ k)
    (hzu : ∀ k, σ k = 0 → u k = 0) (hzv : ∀ k, σ k = 0 → v k = 0)
    (hu : InWiener u) (hv : InWiener v)
    (hmu : InW (fun k => (σ k)⁻¹) u) (hpu : InW σ u)
    (hmv : InW (fun k => (σ k)⁻¹) v) (hpv : InW σ v) :
    normXm1 σ (fun k => σ k * conv u v k)
      ≤ (1 / (4 * ν)) *
        ((normXm1 σ u + ν * normX1 σ u) * (normXm1 σ v + ν * normX1 σ v)) := by
  have hsu : normX0 u ≤ Real.sqrt (normXm1 σ u * normX1 σ u) :=
    normX0_le_sqrt hσ hzu hu hmu hpu
  have hsv : normX0 v ≤ Real.sqrt (normXm1 σ v * normX1 σ v) :=
    normX0_le_sqrt hσ hzv hv hmv hpv
  have hstep : normX0 u * normX0 v
      ≤ Real.sqrt (normXm1 σ u * normX1 σ u) * Real.sqrt (normXm1 σ v * normX1 σ v) :=
    mul_le_mul hsu hsv (normX0_nonneg v) (Real.sqrt_nonneg _)
  refine le_trans (bilinear_Xm1_le hσ hu hv) (le_trans hstep ?_)
  exact sqrt_mul_sqrt_le_quarter hν (normXm1_nonneg hσ u) (normX1_nonneg hσ u)
    (normXm1_nonneg hσ v) (normX1_nonneg hσ v)

end Navier.Analysis.LeiLinBilinear

#print axioms Navier.Analysis.LeiLinBilinear.bilinear_Xm1_le
#print axioms Navier.Analysis.LeiLinBilinear.sqrt_mul_sqrt_le_quarter
#print axioms Navier.Analysis.LeiLinBilinear.bilinear_mixed_le
