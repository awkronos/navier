import Navier.Problem
import Navier.Analysis.CurlIdentities

/-!
# The scalar Madelung decoder cannot lift rotational whole-space data

`docs/MADELUNG_CORRESPONDENCE.md` records in prose: "For a smooth local phase,
the resulting velocity has zero curl."  This file kernelizes that sentence at
the crown's own data surface and uses it to kernel-falsify the exact transport
proposition the Madelung route would need in order to carry the
ε = ν₀/16 small-data class onto `Navier.Problem`'s
`VelocityEvolution × PressureEvolution` carrier.

The needed transport proposition (Madelung sector of the lift directive): for
every regular divergence-free Schwartz initial datum `u₀` — including the small
ones — there is a `C^∞` scalar wavefunction `ψ`, nonzero at the evaluation
point, whose decoder law (MADELUNG_CORRESPONDENCE.md's
`inner ℝ (u₀ x) d = κ * (Dψ(x) d / ψ x).im`, stated here in the equivalent
component form at the basis directions, since both sides are linear in `d`)
agrees with `u₀`.  `madelung_decoder_mixed_partial_comm` proves that any such
decoded field has commuting mixed partials at the origin: locally the decoded
field is the gradient of the arctangent phase of `ψ`, so the scalar Madelung
route is irrotational-by-construction off the zeros of `ψ`.  The explicit
datum `rotationalDatum lam` is Schwartz, `DivergenceFreeInitial`, componentwise
bounded by `|lam|` (hence present at every small-data scale, in particular below
`rawMildViscosity ν₀ / 16`), and satisfies `∂₀u₁(0) = lam ≠ -lam = ∂₁u₀(0)`.
Therefore `no_scalar_madelung_initial_lift_of_rotational_data` refutes the
transport proposition for every `lam > 0`.

Scope and honesty notes:
* The obstruction is at initial-time agreement only — it needs no PDE
  dynamics.  A lift must decode its own initial datum, so a route that fails
  here cannot carry the class.
* The `lam = 0` datum is zero, already covered by `isClassicalSolution_zero`.
  A full Liouville classification of the decodable (irrotational) data sector
  is not claimed here.
* What this does NOT touch: the analytic lattice → ℝ³ transport route, whose
  missing primitive remains a weight-compatible extension
  `WeightedLatticeBanach` → whole-space carrier preserving the
  `rawMildViscosity ν₀ / 16` threshold.  That residual stays OPEN.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators ContDiff

namespace Navier.Analysis.MadelungDecoderCurlObstruction

open Navier Filter Set Metric Function
open Navier.Analysis.CurlIdentities

private theorem real_smul_eq_mul (r x : ℝ) : r • x = r * x := by simp

/-! ## One-dimensional C^∞ bumps: support in `(-1,1)`, value `1` at `0` -/

private abbrev IsBump (η : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ η 0 = 1 ∧
    range η ⊆ Icc (0 : ℝ) 1 ∧ tsupport η ⊆ ball (0 : ℝ) 1

private theorem exists_bump : ∃ η : ℝ → ℝ, IsBump η := by
  obtain ⟨η, ht, hs, hc, hr, h1⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (s := ball (0 : ℝ) 1)
      (x := (0 : ℝ)) (ball_mem_nhds 0 one_pos)
  exact ⟨η, hc, hs, h1, hr, ht⟩

private noncomputable def bump : ℝ → ℝ := Classical.choose exists_bump

private theorem bump_spec : IsBump bump := Classical.choose_spec exists_bump

private theorem bump_smooth : ContDiff ℝ ∞ bump := bump_spec.1
private theorem bump_hcs : HasCompactSupport bump := bump_spec.2.1
private theorem bump_zero : bump 0 = 1 := bump_spec.2.2.1
private theorem bump_range : range bump ⊆ Icc (0 : ℝ) 1 := bump_spec.2.2.2.1
private theorem bump_tsupport : tsupport bump ⊆ ball (0 : ℝ) 1 := bump_spec.2.2.2.2

/-! ## The rotational envelope `rho` -/

/-- The compactly supported rotational envelope
`ρ(x) = θ(x₀² + x₁²) · θ(x₂)`, where `θ` is a `C^∞` bump equal to `1` at `0`
with support in `(-1,1)`. -/
private def rho (x : Space) : ℝ := bump (x 0 ^ 2 + x 1 ^ 2) * bump (x 2)

private theorem rho_zero : rho 0 = 1 := by simp [rho, bump_zero]

private theorem rho_nonneg (x : Space) : 0 ≤ rho x := by
  have hθ : bump (x 0 ^ 2 + x 1 ^ 2) ∈ Icc (0 : ℝ) 1 := bump_range ⟨_, rfl⟩
  have hβ : bump (x 2) ∈ Icc (0 : ℝ) 1 := bump_range ⟨_, rfl⟩
  exact mul_nonneg hθ.1 hβ.1

private theorem rho_le_one (x : Space) : rho x ≤ 1 := by
  have hθ : bump (x 0 ^ 2 + x 1 ^ 2) ∈ Icc (0 : ℝ) 1 := bump_range ⟨_, rfl⟩
  have hβ : bump (x 2) ∈ Icc (0 : ℝ) 1 := bump_range ⟨_, rfl⟩
  calc rho x = bump (x 0 ^ 2 + x 1 ^ 2) * bump (x 2) := rfl
    _ ≤ 1 * bump (x 2) := mul_le_mul_of_nonneg_right hθ.2 hβ.1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hβ.2 (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ 1 := by norm_num

private theorem abs_sq_lt_one {a : ℝ} (h : a ^ 2 < 1) : |a| < 1 := by
  rw [abs_lt]
  exact ⟨by nlinarith [sq_nonneg (a + 1)], by nlinarith [sq_nonneg (a - 1)]⟩

private theorem rho_ne0_mem_ball {x : Space} (hx : rho x ≠ 0) :
    x ∈ ball (0 : Space) 1 := by
  have hθ : bump (x 0 ^ 2 + x 1 ^ 2) ≠ 0 := by
    intro H
    exact hx (by rw [rho, H, zero_mul])
  have hβ : bump (x 2) ≠ 0 := by
    intro H
    exact hx (by rw [rho, H, mul_zero])
  have hq : x 0 ^ 2 + x 1 ^ 2 < 1 := by
    have hmem : (x 0 ^ 2 + x 1 ^ 2) ∈ ball (0 : ℝ) 1 :=
      bump_tsupport (subset_tsupport _ (mem_support.mpr hθ))
    rw [mem_ball, Real.dist_eq, sub_zero] at hmem
    exact (abs_lt.mp hmem).2
  have h2 : |x 2| < 1 := by
    have hmem : x 2 ∈ ball (0 : ℝ) 1 :=
      bump_tsupport (subset_tsupport _ (mem_support.mpr hβ))
    rw [mem_ball, Real.dist_eq, sub_zero] at hmem
    exact hmem
  have hx0 : |x 0| < 1 := abs_sq_lt_one (by nlinarith [sq_nonneg (x 1)])
  have hx1 : |x 1| < 1 := abs_sq_lt_one (by nlinarith [sq_nonneg (x 0)])
  rw [mem_ball, dist_eq_norm, sub_zero]
  refine (pi_norm_lt_iff (by norm_num)).mpr ?_
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hx0
  · exact hx1
  · exact h2

private theorem rho_contDiff : ContDiff ℝ ∞ rho := by
  have hp0 : ContDiff ℝ ∞ (fun x : Space => x 0) :=
    ((ContinuousLinearMap.proj (i := (0 : Fin 3))) : Space →L[ℝ] ℝ).contDiff
  have hp1 : ContDiff ℝ ∞ (fun x : Space => x 1) :=
    ((ContinuousLinearMap.proj (i := (1 : Fin 3))) : Space →L[ℝ] ℝ).contDiff
  have hp2 : ContDiff ℝ ∞ (fun x : Space => x 2) :=
    ((ContinuousLinearMap.proj (i := (2 : Fin 3))) : Space →L[ℝ] ℝ).contDiff
  have hq : ContDiff ℝ ∞ (fun x : Space => x 0 ^ 2 + x 1 ^ 2) :=
    (hp0.pow 2).add (hp1.pow 2)
  have hA : ContDiff ℝ ∞ (fun x : Space => bump (x 0 ^ 2 + x 1 ^ 2)) :=
    bump_smooth.comp hq
  have hB : ContDiff ℝ ∞ (fun x : Space => bump (x 2)) := bump_smooth.comp hp2
  exact hA.mul hB

private theorem rho_hasCompactSupport : HasCompactSupport rho := by
  rw [hasCompactSupport_def]
  refine (isCompact_closedBall (0 : Space) 1).of_isClosed_subset isClosed_closure ?_
  exact (closure_mono (by
    intro x hx
    exact rho_ne0_mem_ball (mem_support.mp hx))).trans Metric.closure_ball_subset_closedBall

/-! ## The datum -/

private def datumFn (lam : ℝ) (x : Space) : Space :=
  ![-lam * x 1 * rho x, lam * x 0 * rho x, 0]

private theorem datum_contDiff (lam : ℝ) : ContDiff ℝ ∞ (datumFn lam) := by
  have hp1 : ContDiff ℝ ∞ (fun x : Space => x 1) :=
    ((ContinuousLinearMap.proj (i := (1 : Fin 3))) : Space →L[ℝ] ℝ).contDiff
  have hp0 : ContDiff ℝ ∞ (fun x : Space => x 0) :=
    ((ContinuousLinearMap.proj (i := (0 : Fin 3))) : Space →L[ℝ] ℝ).contDiff
  have hd0 : ContDiff ℝ ∞ (fun x : Space => -lam * x 1 * rho x) :=
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : Space => (-lam : ℝ))).mul hp1).mul rho_contDiff
  have hd1 : ContDiff ℝ ∞ (fun x : Space => lam * x 0 * rho x) :=
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : Space => (lam : ℝ))).mul hp0).mul rho_contDiff
  refine contDiff_pi.mpr ?_
  intro j
  fin_cases j
  · exact hd0
  · exact hd1
  · exact contDiff_const

private theorem datum_hasCompactSupport (lam : ℝ) :
    HasCompactSupport (datumFn lam) := by
  have hsub : support (datumFn lam) ⊆ support rho := by
    intro x hx
    refine mem_support.mpr ?_
    by_contra hρ
    have hzero : datumFn lam x = 0 := by
      funext j
      fin_cases j <;> simp [datumFn, hρ]
    exact mem_support.mp hx hzero
  rw [hasCompactSupport_def]
  exact (hasCompactSupport_def.mp rho_hasCompactSupport).of_isClosed_subset
    isClosed_closure (closure_mono hsub)

/-- The small rotational whole-space datum
`u₀(x) = lam · (-x₁ρ(x), x₀ρ(x), 0)`: divergence-free, Schwartz, and
componentwise bounded by `|lam|`. -/
def rotationalDatum (lam : ℝ) : SchwartzVelocity :=
  HasCompactSupport.toSchwartzMap (datum_hasCompactSupport lam) (datum_contDiff lam)

@[simp]
theorem coe_rotationalDatum (lam : ℝ) (x : Space) : ⇑(rotationalDatum lam) x = datumFn lam x :=
  rfl

theorem rotationalDatum_le (lam : ℝ) (x : Space) (i : Fin 3) :
    |(⇑(rotationalDatum lam) x) i| ≤ |lam| := by
  by_cases hρ : rho x = 0
  · have hzero : ⇑(rotationalDatum lam) x = 0 := by
      funext j
      fin_cases j <;> simp [coe_rotationalDatum, datumFn, hρ]
    rw [hzero]
    simp
  · have hnorm : x ∈ ball (0 : Space) 1 := rho_ne0_mem_ball hρ
    rw [mem_ball, dist_eq_norm, sub_zero] at hnorm
    have hn (j : Fin 3) : |x j| < 1 := by
      rw [← Real.norm_eq_abs]
      exact (pi_norm_lt_iff (by norm_num)).mp hnorm j
    have hρ0 : 0 ≤ rho x := rho_nonneg x
    fin_cases i
    · show |-lam * x 1 * rho x| ≤ |lam|
      rw [abs_mul, abs_mul, abs_of_nonneg hρ0, abs_neg]
      have hstep : |x 1| * rho x ≤ 1 :=
        calc |x 1| * rho x ≤ 1 * rho x := mul_le_mul_of_nonneg_right (hn 1).le hρ0
          _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (rho_le_one x) (by norm_num : (0 : ℝ) ≤ 1)
          _ ≤ 1 := by norm_num
      calc |lam| * |x 1| * rho x = |lam| * (|x 1| * rho x) := by ring
        _ ≤ |lam| * 1 := mul_le_mul_of_nonneg_left hstep (abs_nonneg lam)
        _ = |lam| := by ring
    · show |lam * x 0 * rho x| ≤ |lam|
      rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
      have hstep : |x 0| * rho x ≤ 1 :=
        calc |x 0| * rho x ≤ 1 * rho x := mul_le_mul_of_nonneg_right (hn 0).le hρ0
          _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (rho_le_one x) (by norm_num : (0 : ℝ) ≤ 1)
          _ ≤ 1 := by norm_num
      calc |lam| * |x 0| * rho x = |lam| * (|x 0| * rho x) := by ring
        _ ≤ |lam| * 1 := mul_le_mul_of_nonneg_left hstep (abs_nonneg lam)
        _ = |lam| := by ring
    · show |(0 : ℝ)| ≤ |lam|
      simp

/-! ## The derivative of `rho` and the divergence-free certificate -/

private theorem fderiv_rho_apply (x v : Space) :
    fderiv ℝ rho x v =
      deriv bump (x 0 ^ 2 + x 1 ^ 2) * (2 * x 0 * v 0 + 2 * x 1 * v 1) * bump (x 2) +
        bump (x 0 ^ 2 + x 1 ^ 2) * deriv bump (x 2) * v 2 := by
  have h0 : HasFDerivAt (fun y : Space => y 0)
      ((ContinuousLinearMap.proj (i := (0 : Fin 3))) : Space →L[ℝ] ℝ) x :=
    ((ContinuousLinearMap.proj (i := (0 : Fin 3))) : Space →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun y : Space => y 1)
      ((ContinuousLinearMap.proj (i := (1 : Fin 3))) : Space →L[ℝ] ℝ) x :=
    ((ContinuousLinearMap.proj (i := (1 : Fin 3))) : Space →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Space => y 2)
      ((ContinuousLinearMap.proj (i := (2 : Fin 3))) : Space →L[ℝ] ℝ) x :=
    ((ContinuousLinearMap.proj (i := (2 : Fin 3))) : Space →L[ℝ] ℝ).hasFDerivAt
  have hs0 := h0.pow 2
  have hs1 := h1.pow 2
  have hsadd := hs0.add hs1
  have hbq : HasDerivAt bump (deriv bump (x 0 ^ 2 + x 1 ^ 2)) (x 0 ^ 2 + x 1 ^ 2) :=
    ((bump_smooth.differentiable (by norm_num)).differentiableAt
      (x := x 0 ^ 2 + x 1 ^ 2)).hasDerivAt
  have hA := hbq.hasFDerivAt.comp x hsadd
  have hb2 : HasDerivAt bump (deriv bump (x 2)) (x 2) :=
    ((bump_smooth.differentiable (by norm_num)).differentiableAt (x := x 2)).hasDerivAt
  have hB := hb2.hasFDerivAt.comp x h2
  have hρ : HasFDerivAt rho _ x := hA.mul hB
  rw [hρ.fderiv]
  simp
  try ring

theorem divergenceFreeInitial_rotationalDatum (lam : ℝ) :
    DivergenceFreeInitial (rotationalDatum lam) := by
  intro x
  have hsmooth : ∀ (j : Fin 3),
      DifferentiableAt ℝ (fun y : Space => datumFn lam y j) x := by
    intro j
    have hj : ContDiff ℝ ∞ (fun y : Space => datumFn lam y j) :=
      contDiff_pi.mp (datum_contDiff lam) j
    exact hj.differentiable (by norm_num) x
  have hpi : ∀ (h : Space) (j : Fin 3),
      (fderiv ℝ (datumFn lam) x h) j = fderiv ℝ (fun y : Space => datumFn lam y j) x h := by
    intro h j
    have hpi' := fderiv_pi (𝕜 := ℝ) (E := Space) (x := x)
      (φ := fun (j : Fin 3) (y : Space) => datumFn lam y j) hsmooth
    have heqf : (fun x : Space => fun j => datumFn lam x j) = datumFn lam := rfl
    rw [heqf] at hpi'
    rw [hpi']
    simp
  have hrd : HasFDerivAt rho (fderiv ℝ rho x) x :=
    ((rho_contDiff.differentiable (by norm_num)).differentiableAt (x := x)).hasFDerivAt
  -- ∂₀u₀
  have t0 : (fderiv ℝ (datumFn lam) x (basisVector 0)) 0 =
      -lam * x 1 * (deriv bump (x 0 ^ 2 + x 1 ^ 2) * (2 * x 0) * bump (x 2)) := by
    rw [hpi (basisVector 0) 0]
    have hc : HasFDerivAt (fun y : Space => -lam * y 1)
        ((-lam) • ((ContinuousLinearMap.proj (i := (1 : Fin 3))) : Space →L[ℝ] ℝ)) x :=
      (((ContinuousLinearMap.proj (i := (1 : Fin 3))) : Space →L[ℝ] ℝ).hasFDerivAt).const_mul (-lam)
    have hg : HasFDerivAt (fun y : Space => datumFn lam y 0) _ x := hc.mul hrd
    rw [hg.fderiv]
    simp [fderiv_rho_apply, basisVector]
    try ring
  -- ∂₁u₁
  have t1 : (fderiv ℝ (datumFn lam) x (basisVector 1)) 1 =
      lam * x 0 * (deriv bump (x 0 ^ 2 + x 1 ^ 2) * (2 * x 1) * bump (x 2)) := by
    rw [hpi (basisVector 1) 1]
    have hc : HasFDerivAt (fun y : Space => lam * y 0)
        (lam • ((ContinuousLinearMap.proj (i := (0 : Fin 3))) : Space →L[ℝ] ℝ)) x :=
      (((ContinuousLinearMap.proj (i := (0 : Fin 3))) : Space →L[ℝ] ℝ).hasFDerivAt).const_mul lam
    have hg : HasFDerivAt (fun y : Space => datumFn lam y 1) _ x := hc.mul hrd
    rw [hg.fderiv]
    simp [fderiv_rho_apply, basisVector]
    try ring
  -- ∂₂u₂
  have t2 : (fderiv ℝ (datumFn lam) x (basisVector 2)) 2 = 0 := by
    rw [hpi (basisVector 2) 2]
    have hg : HasFDerivAt (fun y : Space => datumFn lam y 2) (0 : Space →L[ℝ] ℝ) x :=
      hasFDerivAt_const (0 : ℝ) x
    rw [hg.fderiv]
    simp
  show staticDivergence (fun y : Space => ⇑(rotationalDatum lam) y) x = 0
  show staticDivergence (datumFn lam) x = 0
  rw [staticDivergence, Fin.sum_univ_three]
  have e0 : (fderiv ℝ (datumFn lam) x (basisVector 0)) 0 =
      -2 * lam * deriv bump (x 0 ^ 2 + x 1 ^ 2) * bump (x 2) * x 0 * x 1 := by
    rw [t0]
    ring
  have e1 : (fderiv ℝ (datumFn lam) x (basisVector 1)) 1 =
      2 * lam * deriv bump (x 0 ^ 2 + x 1 ^ 2) * bump (x 2) * x 0 * x 1 := by
    rw [t1]
    ring
  rw [e0, e1, t2]
  ring

/-! ## The scalar Madelung decoder and the mixed-partial obstruction -/

/-- Component form of the MADELUNG_CORRESPONDENCE.md decoder law
`inner ℝ (u₀ x) d = κ * (Dψ(x) d / ψ x).im` for every direction `d` (both
sides are linear in `d`, and the basis directions determine a linear map). -/
def MadelungInitialDecoder (κ : ℝ) (ψ : Space → ℂ) (u₀ : VelocityField) : Prop :=
  ∀ (x : Space) (i : Fin 3),
    u₀ x i = κ * ((fderiv ℝ ψ x (basisVector i)) / ψ x).im

/-- **Scalar Madelung data has commuting mixed partials at the origin.**
If `u₀` is decoded from a `C^∞` scalar `ψ` with `ψ 0 ≠ 0`, rotate `ψ` by a
constant phase `c₀` so that `c₀ * ψ 0` is a positive real; then on a whole
neighbourhood of the origin the arctangent phase `Θ = arctan ((c₀ψ)ᵢ / (c₀ψ)ᵣ)`
is `C^∞` and `DΘ(y) v = (Dψ(y) v / ψ y).im`, i.e. `κ * DΘ` decodes `u₀`
eventually near `0`.  Hence the two mixed partials of the decoded field agree
at the origin: `∂₀(κ DΘ·e₁)(0)·e₀ = ∂₁(κ DΘ·e₀)(0)·e₁` by symmetry of
second derivatives of `Θ`.  The scalar Madelung route therefore cannot decode
any datum whose mixed partials do not commute — it is irrotational-by-
construction off the zeros of `ψ`, and the decoder requires no zeros at the
evaluation point. -/
theorem madelung_decoder_mixed_partial_comm
    (κ : ℝ) (ψ : Space → ℂ) (hψ : ContDiff ℝ ∞ ψ) (h0 : ψ 0 ≠ 0)
    (u : VelocityField) (hdec : MadelungInitialDecoder κ ψ u) :
    fderiv ℝ (fun y : Space => u y 1) 0 (basisVector 0) =
      fderiv ℝ (fun y : Space => u y 0) 0 (basisVector 1) := by
  -- Rotate ψ by a constant phase so that its value at 0 is a positive real.
  set c0 : ℂ := Complex.exp (-(Complex.I * (ψ 0).arg)) with hc0d
  have hc0 : c0 ≠ 0 := Complex.exp_ne_zero _
  have hpol : ‖ψ 0‖ * Complex.exp (Complex.I * (ψ 0).arg) = ψ 0 := by
    have h := Complex.norm_mul_exp_arg_mul_I (ψ 0)
    rwa [← mul_comm Complex.I ((ψ 0).arg)] at h
  have hkey : c0 * Complex.exp (Complex.I * (ψ 0).arg) = 1 := by
    rw [show c0 = Complex.exp (-(Complex.I * (ψ 0).arg)) from rfl, ← Complex.exp_add,
      neg_add_cancel, Complex.exp_zero]
  have hrot : c0 * ψ 0 = (‖ψ 0‖ : ℂ) := by
    conv_lhs => rw [← hpol]
    rw [mul_left_comm c0, hkey, mul_one]
  set φ : Space → ℂ := fun x => c0 * ψ x with hφdef
  set Θ : Space → ℝ := fun x => Real.arctan ((φ x).im / (φ x).re) with hΘdef
  have hre0 : 0 < (φ 0).re := by
    show 0 < (c0 * ψ 0).re
    rw [hrot, Complex.ofReal_re]
    exact norm_pos_iff.mpr h0
  have hφc : ContDiff ℝ ∞ φ :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => (c0 : ℂ))).mul hψ
  have hΘ : ContDiffAt ℝ ∞ Θ 0 := by
    have hi : ContDiffAt ℝ ∞ (fun z : ℂ => z.im) (φ 0) :=
      (Complex.imCLM : ℂ →L[ℝ] ℝ).contDiff.contDiffAt (x := φ 0)
    have hinv : ContDiffAt ℝ ∞ (fun z : ℂ => (z.re)⁻¹) (φ 0) :=
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).contDiff.contDiffAt (x := φ 0)).inv (ne_of_gt hre0)
    have hratio : ContDiffAt ℝ ∞ (fun z : ℂ => z.im / z.re) (φ 0) := hi.mul hinv
    have hcomp : ContDiffAt ℝ ∞ (fun x : Space => (φ x).im / (φ x).re) (0 : Space) :=
      ContDiffAt.comp (0 : Space) hratio hφc.contDiffAt
    have hmain :
        ContDiffAt ℝ ∞
          ((fun y : ℝ => Real.arctan y) ∘ fun x : Space => (φ x).im / (φ x).re) (0 : Space) :=
      ContDiffAt.comp (0 : Space)
        (Real.contDiff_arctan.contDiffAt :
          ContDiffAt ℝ ∞ (fun y : ℝ => Real.arctan y) ((φ 0).im / (φ 0).re)) hcomp
    exact hmain
  have hreC : ContinuousAt (fun x : Space => (φ x).re) (0 : Space) :=
    ((Complex.reCLM : ℂ →L[ℝ] ℝ).continuous.continuousAt (x := φ 0)).comp
      (hφc.continuous.continuousAt (x := 0))
  have hev : ∀ᶠ y in nhds (0 : Space), (φ y).re ≠ 0 :=
    hreC.tendsto.eventually_ne (ne_of_gt hre0)
  -- Pointwise: the phase's differential is the decoded 1-form.
  have hDphi' (y : Space) : fderiv ℝ φ y = c0 • fderiv ℝ ψ y := by
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
      ((hψ.differentiable (by norm_num)).differentiableAt (x := y)).hasFDerivAt
    have h : HasFDerivAt φ _ y := (hasFDerivAt_const c0 y).mul hψd
    rw [h.fderiv]
    refine ContinuousLinearMap.ext fun w => ?_
    simp
  have hphase (y : Space) (hy : (φ y).re ≠ 0) (v : Space) :
      fderiv ℝ Θ y v = (fderiv ℝ ψ y v / ψ y).im := by
    have hdφ : HasFDerivAt φ (fderiv ℝ φ y) y :=
      ((hφc.differentiable (by norm_num)).differentiableAt (x := y)).hasFDerivAt
    have hi : HasFDerivAt (fun z : ℂ => z.im) (Complex.imCLM : ℂ →L[ℝ] ℝ) (φ y) :=
      (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt
    have hr : HasFDerivAt (fun z : ℂ => z.re) (Complex.reCLM : ℂ →L[ℝ] ℝ) (φ y) :=
      (Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt
    have hinv : HasFDerivAt (fun z : ℂ => (z.re)⁻¹) _ (φ y) :=
      ((hasDerivAt_inv hy).hasFDerivAt).comp (φ y) hr
    have hratio : HasFDerivAt (fun z : ℂ => z.im / z.re) _ (φ y) := hi.mul hinv
    have harct : HasFDerivAt (fun z : ℂ => Real.arctan (z.im / z.re)) _ (φ y) :=
      ((Real.hasDerivAt_arctan _).hasFDerivAt).comp (φ y) hratio
    have hden : (φ y).re * (φ y).re + (φ y).im * (φ y).im ≠ 0 := by
      nlinarith [mul_self_pos.mpr hy]
    have hDΘ : fderiv ℝ Θ y v = (fderiv ℝ φ y v / φ y).im := by
      have h : HasFDerivAt Θ _ y := harct.comp y hdφ
      rw [h.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.toSpanSingleton_apply,
        Complex.reCLM_apply, Complex.imCLM_apply, real_smul_eq_mul, pow_two,
        Complex.div_im, Complex.normSq_apply]
      field_simp [hy, hden]
      ring
    rw [hDΘ]
    have hf : fderiv ℝ φ y v = c0 * fderiv ℝ ψ y v := by
      rw [hDphi' y, ContinuousLinearMap.smul_apply]
      simp only [smul_eq_mul, Algebra.smul_def, id_eq]
    rw [hf, show φ y = c0 * ψ y from rfl,
      mul_div_mul_left (fderiv ℝ ψ y v) (ψ y) hc0]
  have hΘ2 : ContDiffAt ℝ 2 Θ 0 := hΘ.of_le (by simp)
  have hsymm : fderiv ℝ (fun y : Space => fderiv ℝ Θ y (basisVector 1)) 0 (basisVector 0) =
      fderiv ℝ (fun y : Space => fderiv ℝ Θ y (basisVector 0)) 0 (basisVector 1) :=
    hΘ2.hasSymmetricMixedPartialAt 0 1
  have hdif (i : Fin 3) : DifferentiableAt ℝ
      (fun y : Space => fderiv ℝ Θ y (basisVector i)) 0 := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ Θ) 0 := hΘ2.fderiv_right le_rfl
    have hdiff : DifferentiableAt ℝ (fderiv ℝ Θ) 0 :=
      h1.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have : (fun y : Space => fderiv ℝ Θ y (basisVector i)) =
        ((ContinuousLinearMap.apply ℝ ℝ (basisVector i) :
            (Space →L[ℝ] ℝ) →L[ℝ] ℝ) ∘ (fderiv ℝ Θ)) := rfl
    rw [this]
    exact (ContinuousLinearMap.apply ℝ ℝ (basisVector i)).differentiableAt.comp 0 hdiff
  have hpull (i : Fin 3) :
      fderiv ℝ (fun y : Space => κ * fderiv ℝ Θ y (basisVector i)) 0 =
        κ • fderiv ℝ (fun y : Space => fderiv ℝ Θ y (basisVector i)) 0 :=
    ((hdif i).hasFDerivAt.const_mul κ).fderiv
  have heq (i : Fin 3) :
      (fun y : Space => u y i) =ᶠ[nhds 0] fun y : Space => κ * fderiv ℝ Θ y (basisVector i) := by
    refine Filter.Eventually.mono hev ?_
    intro y hy
    show u y i = κ * fderiv ℝ Θ y (basisVector i)
    rw [hdec y i, hphase y hy (basisVector i)]
  have hL : fderiv ℝ (fun y : Space => u y 1) 0 (basisVector 0)
      = κ • fderiv ℝ (fun y : Space => fderiv ℝ Θ y (basisVector 1)) 0 (basisVector 0) := by
    rw [(heq 1).fderiv_eq, hpull 1, ContinuousLinearMap.smul_apply]
  have hR : fderiv ℝ (fun y : Space => u y 0) 0 (basisVector 1)
      = κ • fderiv ℝ (fun y : Space => fderiv ℝ Θ y (basisVector 0)) 0 (basisVector 1) := by
    rw [(heq 0).fderiv_eq, hpull 0, ContinuousLinearMap.smul_apply]
  rw [hL, hR, hsymm]

theorem no_scalar_madelung_initial_lift_of_rotational_data (lam : ℝ) (hlam : 0 < lam) :
    ¬ ∃ (κ : ℝ) (ψ : Space → ℂ), ContDiff ℝ ∞ ψ ∧ ψ 0 ≠ 0 ∧
      MadelungInitialDecoder κ ψ ⇑(rotationalDatum lam) := by
  intro hex
  obtain ⟨κ, ψ, hψ, h0, hdec⟩ := hex
  have h := madelung_decoder_mixed_partial_comm κ ψ hψ h0 (⇑(rotationalDatum lam)) hdec
  have hL : fderiv ℝ (fun y : Space => ⇑(rotationalDatum lam) y 1) 0 (basisVector 0) = lam := by
    have hf : (fun y : Space => ⇑(rotationalDatum lam) y 1) =
        (fun y : Space => lam * y 0 * rho y) := rfl
    rw [hf]
    have h1 : HasFDerivAt (fun y : Space => lam * y 0)
        (lam • ((ContinuousLinearMap.proj (i := (0 : Fin 3))) : Space →L[ℝ] ℝ)) 0 :=
      (((ContinuousLinearMap.proj (i := (0 : Fin 3))) : Space →L[ℝ] ℝ).hasFDerivAt
        (x := (0 : Space))).const_mul lam
    have h2 : HasFDerivAt rho (fderiv ℝ rho 0) 0 :=
      ((rho_contDiff.differentiable (by norm_num)).differentiableAt
        (x := (0 : Space))).hasFDerivAt
    have h : HasFDerivAt (fun y : Space => lam * y 0 * rho y) _ 0 := h1.mul h2
    rw [h.fderiv]
    simp [fderiv_rho_apply, rho_zero, basisVector]
    try ring
  have hR : fderiv ℝ (fun y : Space => ⇑(rotationalDatum lam) y 0) 0 (basisVector 1) = -lam := by
    have hf : (fun y : Space => ⇑(rotationalDatum lam) y 0) =
        (fun y : Space => -lam * y 1 * rho y) := rfl
    rw [hf]
    have h1 : HasFDerivAt (fun y : Space => -lam * y 1)
        ((-lam) • ((ContinuousLinearMap.proj (i := (1 : Fin 3))) : Space →L[ℝ] ℝ)) 0 :=
      (((ContinuousLinearMap.proj (i := (1 : Fin 3))) : Space →L[ℝ] ℝ).hasFDerivAt
        (x := (0 : Space))).const_mul (-lam)
    have h2 : HasFDerivAt rho (fderiv ℝ rho 0) 0 :=
      ((rho_contDiff.differentiable (by norm_num)).differentiableAt
        (x := (0 : Space))).hasFDerivAt
    have h : HasFDerivAt (fun y : Space => -lam * y 1 * rho y) _ 0 := h1.mul h2
    rw [h.fderiv]
    simp [fderiv_rho_apply, rho_zero, basisVector]
    try ring
  rw [hL, hR] at h
  linarith

end Navier.Analysis.MadelungDecoderCurlObstruction

#print axioms Navier.Analysis.MadelungDecoderCurlObstruction.rotationalDatum_le
#print axioms
  Navier.Analysis.MadelungDecoderCurlObstruction.divergenceFreeInitial_rotationalDatum
#print axioms Navier.Analysis.MadelungDecoderCurlObstruction.no_scalar_madelung_initial_lift_of_rotational_data
