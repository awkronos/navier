/-
Sound-field-native representations ("splats"): the acoustic monopole fundamental
solution, its finite-superposition synthesis object, and the proved direction of
the representation theorem — every finite splat field solves the homogeneous
Helmholtz equation on the complement of its sources.

This file owns the REPRESENTATION-THEOREM half of the W34 sound-splat package.
The adjoint/backprop half lives in `Navier.AdjointBackpropagation`.

Conventions:
* `Space = Navier.Construction.ProblemStatement.Space = EuclideanSpace ℝ (Fin 3)`
  and `coordinateVector i = EuclideanSpace.single i 1`, reused verbatim.
* `scalarLaplacian` mirrors the project's `spatialLaplacian` convention
  (`∑ᵢ ∂ᵢ∂ᵢ` as two iterated `fderiv`s on coordinate directions) at the scalar
  `ℂ`-valued layer. The self-adjointness machinery of the fluid operator lives in
  `Navier/Analysis/GalerkinBasis.lean`; this file neither re-proves nor depends
  on it — the Laplacian here is the pointwise Euclidean coordinate Laplacian.
* Everything here is the POINTWISE (classical) equation away from sources.
  The distributional identity `(Δ + k²)Φ_y = -δ_y` (the other half of the
  representation theorem: sources are exactly where the equation fails) is
  OUT OF SCOPE here and is an OPEN construction obligation for this repository
  (Mathlib has no fundamental-solution API; searched shapes in the lane receipt).
* CLAIM TIER: the theorems below are mathematical statements at THEOREM tier
  (kernel-checked, strict axioms) under exactly the hypotheses displayed. They
  make NO device claim: microphone-array reachability of this representation
  (e.g. a 4-mic raw capture) is a separate SIMULATED-VERIFIED tier and is
  firmware-pending — stock G2 hardware is one mixed mono 16 kHz stream;
  KagamiFW 4-channel is not flashed. A kernel proof here does not certify a
  device pipeline.
-/
import Navier.Construction.ProblemStatement
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Topology.Separation.Basic

open scoped BigOperators InnerProductSpace Topology
open Filter ContinuousLinearMap
open Navier.Construction.ProblemStatement

/-- Transport of the Fréchet derivative along an equality of the derivative
`ContinuousLinearMap` itself. Mathlib has `HasDerivAt.congr_deriv` but no
FDeriv-side analogue (measured in this toolchain: the projection
`HasFDerivAtFilter.congr_deriv` does not exist); this is the exact missing
signature, one `▸` deep. -/
private theorem HasFDerivAt.congrCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {g g' : E →L[ℝ] F} {x : E} (h : HasFDerivAt f g x) (he : g = g') :
    HasFDerivAt f g' x := he ▸ h

namespace Navier.Sound

noncomputable section

/-- The **monopole radial profile** `g(t) = e^{ikt} / (4π t)`: the radial factor of
the three-dimensional acoustic fundamental solution. At `t = 0` Lean's
division-by-zero convention gives the junk value `0`; every theorem below
evaluates at `t ≠ 0`. -/
def radialProfile (k : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ↑(k * t)) / ↑(4 * Real.pi * t)

/-- **Acoustic monopole fundamental solution**
`Φ_y(x) = e^{ik‖x−y‖} / (4π‖x−y‖)` for a source `y` at field point `x`.
For `x ≠ y` this is smooth; the value at `x = y` is Lean junk and is never
consumed (every consumer carries `x ≠ y`). -/
def monopole (k : ℝ) (y : Space) (x : Space) : ℂ := radialProfile k ‖x - y‖

/-- **Euclidean Laplacian for scalar complex fields**, `Δu = ∑ᵢ ∂ᵢ∂ᵢu`, in the
repository's `spatialLaplacian` convention (`Navier.Construction.ProblemStatement`):
two iterated `fderiv`s applied to coordinate directions. -/
def scalarLaplacian (u : Space → ℂ) (x : Space) : ℂ :=
  ∑ i : Fin 3,
    fderiv ℝ (fun z : Space => fderiv ℝ u z (coordinateVector i)) x (coordinateVector i)

/-- The **Helmholtz operator** `(Δ + k²)u` evaluated at a point. -/
def helmholtzOperator (k : ℝ) (u : Space → ℂ) (x : Space) : ℂ :=
  scalarLaplacian u x + (↑(k * k) : ℂ) * u x

/-- **Splat synthesis.** A finite superposition of monopoles with prescribed
frequency `k`, source locations `support`, and complex amplitudes `amps`:
`u(x) = Σᵢ aᵢ Φ_{yᵢ}(x)`. This is the "Gaussian-splat-like, but native to
sound fields" representation object; `splatSatisfiesHelmholtz` proves the
synthesis direction rather than assuming it. -/
def splatField (k : ℝ) (amps : Space → ℂ) (support : Finset Space) (x : Space) : ℂ :=
  ∑ y ∈ support, amps y * monopole k y x

/-! ## Small plumbing -/

private lemma hasDerivAt_realCoe (r : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) r := by
  have h : HasFDerivAt (fun t : ℝ => (t : ℂ)) Complex.ofRealCLM r :=
    Complex.ofRealCLM.hasFDerivAt (x := r)
  have hL : Complex.ofRealCLM = toSpanSingleton ℝ (1 : ℂ) := by
    ext x
    simp
  rw [hL] at h
  exact hasDerivAt_iff_hasFDerivAt.mp h

/-- The Euclidean-real inner functional `z ↦ ⟪z − y, w⟫_ℝ` is affine. -/
private lemma hasFDerivAt_realInnerShift (x y w : Space) :
    HasFDerivAt (fun z : Space => ⟪z - y, w⟫_ℝ) (innerSL ℝ w) x := by
  have hz : HasFDerivAt (fun z : Space => z - y) (1 : Space →L[ℝ] Space) x :=
    (hasFDerivAt_id x).sub_const y
  have h := (innerSL ℝ w).hasStrictFDerivAt (x := x - y).hasFDerivAt.comp x hz
  have hem : (fun z : Space => ⟪z - y, w⟫_ℝ) =ᶠ[𝓝 x] fun z => (innerSL ℝ w) (z - y) := by
    filter_upwards [univ_mem] with z _hz
    simp only [innerSL_apply_apply, real_inner_comm]
  refine' (h.congr_of_eventuallyEq hem).congrCLM _
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]

/-- `⟪coordinateVector i, w⟫_ℝ = w i`. -/
private lemma real_inner_coordVector (w : Space) (i : Fin 3) :
    ⟪coordinateVector i, w⟫_ℝ = w i := by
  classical
  have h := EuclideanSpace.inner_single_left i (1 : ℝ) w
  simpa [coordinateVector] using h

/-- `⟪coordinateVector i, coordinateVector i⟫_ℝ = 1`. -/
private lemma real_inner_self_coord (i : Fin 3) :
    ⟪coordinateVector i, coordinateVector i⟫_ℝ = 1 := by
  rw [real_inner_coordVector]
  classical
  simp [coordinateVector, PiLp.single_apply]

/-- `⟪x − y, coordinateVector i⟫_ℝ = ⟪coordinateVector i, x − y⟫_ℝ`. -/
private lemma real_inner_coordShift_comm (x y : Space) (i : Fin 3) :
    ⟪x - y, coordinateVector i⟫_ℝ = ⟪coordinateVector i, x - y⟫_ℝ :=
  real_inner_comm _ _

/-- Convert a one-dimensional derivative into its `toSpanSingleton` CLM form. -/
private lemma toFD {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {c : F} {x : 𝕜}
    (h : HasDerivAt f c x) : HasFDerivAt f (toSpanSingleton 𝕜 c) x :=
  hasDerivAt_iff_hasFDerivAt.mpr h

/-! ## Chain-rule plumbing for the profile (consumed by the radial crowns) -/

/-- `t ↦ i·(kt)` has derivative `ik`. Proved with an `eventuallyEq` transport so
no `convert` ever has to align `HasDerivAt` instances. -/
private lemma hasDerivAt_linExp (k r : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.I * ↑(k * t)) (Complex.I * ↑k) r := by
  have h := (hasDerivAt_const (c := Complex.I) (x := r)).mul
    ((hasDerivAt_const (c := (↑k : ℂ)) (x := r)).mul (hasDerivAt_realCoe r))
  have he : (fun t : ℝ => Complex.I * ↑(k * t)) =ᶠ[𝓝 r]
      (fun _ : ℝ => Complex.I) *
        ((fun _ : ℝ => (↑k : ℂ)) * (fun t : ℝ => (t : ℂ))) := by
    filter_upwards [univ_mem] with t _ht
    simp only [Pi.mul_apply, Complex.ofReal_mul]
  exact (h.congr_of_eventuallyEq he).congr_deriv (by ring)

/-- `t ↦ e^{ikt}` has derivative `ik·e^{ikr}`. -/
private lemma hasDerivAt_exp_iik (k r : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * ↑(k * t)))
      (Complex.exp (Complex.I * ↑(k * r)) * (Complex.I * ↑k)) r :=
    (Complex.hasDerivAt_exp _).comp r (hasDerivAt_linExp k r)

/-- `t ↦ 4πt` (cast to `ℂ`) has derivative `4π`. -/
private lemma hasDerivAt_den1 (r : ℝ) :
    HasDerivAt (fun t : ℝ => (↑(4 * Real.pi * t) : ℂ)) (↑(4 * Real.pi)) r := by
  have h := (hasDerivAt_const (c := (↑(4 * Real.pi) : ℂ)) (x := r)).mul (hasDerivAt_realCoe r)
  have he : (fun t : ℝ => (↑(4 * Real.pi * t) : ℂ)) =ᶠ[𝓝 r]
      (fun _ : ℝ => (↑(4 * Real.pi) : ℂ)) * (fun t : ℝ => (t : ℂ)) := by
    filter_upwards [univ_mem] with t _ht
    simp only [Pi.mul_apply, Complex.ofReal_mul]
  exact (h.congr_of_eventuallyEq he).congr_deriv (by ring)

/-- `t ↦ ik·t − 1` has derivative `ik`. -/
private lemma hasDerivAt_lin (k r : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.I * ↑k * (t : ℂ) - 1) (Complex.I * ↑k) r := by
  have h := (hasDerivAt_const (c := Complex.I * ↑k) (x := r)).mul (hasDerivAt_realCoe r)
  have he : (fun t : ℝ => Complex.I * ↑k * (t : ℂ)) =ᶠ[𝓝 r]
      (fun _ : ℝ => Complex.I * ↑k) * (fun t : ℝ => (t : ℂ)) := by
    filter_upwards [univ_mem] with t _ht
    simp only [Pi.mul_apply]
  have hs := (h.congr_of_eventuallyEq he).sub (hasDerivAt_const (c := (1 : ℂ)) (x := r))
  exact hs.congr_deriv (by ring)

/-- `t ↦ 4π·t·t` has derivative `2·4π·r`. -/
private lemma hasDerivAt_den2 (r : ℝ) :
    HasDerivAt (fun t : ℝ => ↑(4 * Real.pi) * (t : ℂ) * (t : ℂ))
      (2 * ↑(4 * Real.pi) * (r : ℂ)) r := by
  have h := ((hasDerivAt_const (c := (↑(4 * Real.pi) : ℂ)) (x := r)).mul
    (hasDerivAt_realCoe r)).mul (hasDerivAt_realCoe r)
  have he : (fun t : ℝ => ↑(4 * Real.pi) * (t : ℂ) * (t : ℂ)) =ᶠ[𝓝 r]
      ((fun _ : ℝ => (↑(4 * Real.pi) : ℂ)) * (fun t : ℝ => (t : ℂ))) *
        (fun t : ℝ => (t : ℂ)) := by
    filter_upwards [univ_mem] with t _ht
    simp only [Pi.mul_apply]
  exact (h.congr_of_eventuallyEq he).congr_deriv (by simp only [Pi.mul_apply]; ring)

/-- Nonvanishing of the profile denominators, in the exact shape the div-rule
applications consume. -/
private lemma coe_4pi_ne_zero (r : ℝ) (hr : r ≠ 0) :
    (↑(4 * Real.pi * r) : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero) hr

private lemma coe_4pi_mul_r_mul_r_ne_zero (r : ℝ) (hr : r ≠ 0) :
    (↑(4 * Real.pi) * (r : ℂ) * (r : ℂ)) ≠ 0 := by
  have rc : (r : ℂ) ≠ 0 := by simp only [ne_eq, Complex.ofReal_eq_zero]; exact hr
  have p4 : (↑(4 * Real.pi) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero p4 rc) rc

/-! ## Crown support 1: the radial ODE of the Green profile -/

/-- First derivative of the monopole radial profile:
`g'(r) = e^{ikr} (ikr − 1) / (4π r²)`, for `r ≠ 0`. -/
private lemma deriv_radialProfile (k r : ℝ) (hr : r ≠ 0) :
    deriv (radialProfile k) r =
      Complex.exp (Complex.I * ↑(k * r)) * (Complex.I * ↑k * ↑r - 1) /
        (↑(4 * Real.pi) * ↑r * ↑r) := by
  have hne := coe_4pi_ne_zero r hr
  have h1 := (hasDerivAt_exp_iik k r).div (hasDerivAt_den1 r) hne
  have he : (radialProfile k) =ᶠ[𝓝 r] (fun t : ℝ =>
      Complex.exp (Complex.I * ↑(k * t)) / (↑(4 * Real.pi * t) : ℂ)) :=
    eventuallyEq_of_mem univ_mem fun t _ht => rfl
  rw [(h1.congr_of_eventuallyEq he).deriv]
  push_cast
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  have hr' : (r : ℂ) ≠ 0 := by simpa using hr
  field_simp [h4, hpi, hr']

/-- Second derivative of the profile:
`g''(r) = e^{ikr} (−k²r² − 2ikr + 2) / (4π r³)`, for `r ≠ 0`. -/
private lemma deriv_deriv_radialProfile (k r : ℝ) (hr : r ≠ 0) :
    deriv (deriv (radialProfile k)) r =
      Complex.exp (Complex.I * ↑(k * r)) *
        (-(↑(k * k)) * ↑r * ↑r - 2 * Complex.I * ↑k * ↑r + 2) /
        (↑(4 * Real.pi) * ↑r * ↑r * ↑r) := by
  have hEq : ∀ t : ℝ, t ≠ 0 →
      deriv (radialProfile k) t =
        Complex.exp (Complex.I * ↑(k * t)) * (Complex.I * ↑k * ↑t - 1) /
          (↑(4 * Real.pi) * ↑t * ↑t) := fun t ht => deriv_radialProfile k t ht
  have hnum := (hasDerivAt_exp_iik k r).mul (hasDerivAt_lin k r)
  have hden := hasDerivAt_den2 r
  have hne := coe_4pi_mul_r_mul_r_ne_zero r hr
  have h1 := hnum.div hden hne
  have he : (fun t : ℝ => deriv (radialProfile k) t) =ᶠ[𝓝 r] (fun t : ℝ =>
      Complex.exp (Complex.I * ↑(k * t)) * (Complex.I * ↑k * (t : ℂ) - 1) /
        (↑(4 * Real.pi) * (t : ℂ) * (t : ℂ))) := by
    filter_upwards [isOpen_ne (x := (0 : ℝ)).mem_nhds hr] with t ht using hEq t ht
  rw [(h1.congr_of_eventuallyEq he).deriv]
  field_simp [hne]
  ring_nf
  simp only [Pi.mul_apply, Complex.I_sq, Complex.ofReal_mul, mul_neg, neg_mul, neg_neg]
  push_cast
  ring

/-- **Radial Helmholtz ODE** (crown support): the monopole Green profile
satisfies `g'' + (2/r) g' + k² g = 0` for every `r ≠ 0`. -/
theorem radialProfile_helmholtzODE (k r : ℝ) (hr : r ≠ 0) :
    deriv (deriv (radialProfile k)) r +
      (2 : ℂ) / (↑r : ℂ) * deriv (radialProfile k) r +
      ↑(k * k) * radialProfile k r = 0 := by
  rw [deriv_deriv_radialProfile k r hr, deriv_radialProfile k r hr, radialProfile]
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  have hr' : (r : ℂ) ≠ 0 := by simpa using hr
  field_simp [h4, hpi, hr']
  ring_nf
  simp only [Complex.I_sq, Complex.ofReal_mul, mul_neg, neg_mul, neg_neg]
  ring

/-- Reorganization of the radial ODE consumed by the Laplacian crowns:
`g'' + (2/r) g' = -k² g`. -/
private lemma radialProfile_ode_neg (k r : ℝ) (hr : r ≠ 0) :
    deriv (deriv (radialProfile k)) r + (2 : ℂ) / ↑r * deriv (radialProfile k) r =
      -(↑(k * k) : ℂ) * radialProfile k r := by
  have h := radialProfile_helmholtzODE k r hr
  calc deriv (deriv (radialProfile k)) r + (2 : ℂ) / ↑r * deriv (radialProfile k) r
      = deriv (deriv (radialProfile k)) r + (2 : ℂ) / ↑r * deriv (radialProfile k) r +
          ↑(k * k) * radialProfile k r - ↑(k * k) * radialProfile k r := by ring
    _ = 0 - ↑(k * k) * radialProfile k r := by rw [h]
    _ = -(↑(k * k) : ℂ) * radialProfile k r := by ring

/-! ## Crown support 2: the Cartesian complex-exponential ansatz -/

/-- **Plane-wave (complex exponential) ansatz** with wave vector `w`, source
offset `y`: `x ↦ e^{i⟪x − y, w⟫}`. -/
def planeWave (k : ℝ) (w y : Space) (x : Space) : ℂ :=
  Complex.exp (Complex.I * ↑⟪x - y, w⟫_ℝ)

private lemma hasFDerivAt_planeWave (k : ℝ) (w y : Space) (x : Space) :
    HasFDerivAt (planeWave k w y)
      ((Complex.I * planeWave k w y x) • Complex.ofRealCLM.comp (innerSL ℝ w)) x := by
  have hl : HasFDerivAt (fun z : Space => ⟪z - y, w⟫_ℝ) (innerSL ℝ w) x :=
    hasFDerivAt_realInnerShift x y w
  have hcast : HasFDerivAt (fun z : Space => (⟪z - y, w⟫_ℝ : ℂ))
      (Complex.ofRealCLM.comp (innerSL ℝ w)) x := by
    have hcomp :=
      (Complex.ofRealCLM.hasStrictFDerivAt (x := ⟪x - y, w⟫_ℝ)).hasFDerivAt.comp x hl
    refine' hcomp.congr_of_eventuallyEq (eventuallyEq_of_mem univ_mem fun t _ht => ?_)
    simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  have hlin : HasFDerivAt (fun z : Space => Complex.I * (⟪z - y, w⟫_ℝ : ℂ))
      (Complex.I • Complex.ofRealCLM.comp (innerSL ℝ w)) x := by
    have hmul := (hasFDerivAt_const (c := Complex.I) (x := x)).mul hcast
    have hem : (fun z : Space => Complex.I * (⟪z - y, w⟫_ℝ : ℂ)) =ᶠ[𝓝 x]
        (fun _ => Complex.I) * fun z => (⟪z - y, w⟫_ℝ : ℂ) := by
      filter_upwards [univ_mem] with t _ht; rfl
    exact (hmul.congr_of_eventuallyEq hem).congrCLM (by
      ext v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, smul_eq_mul,
        mul_zero, add_zero])
  refine' hlin.cexp.congrCLM _
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  unfold planeWave
  ring

/-- `∑ᵢ ⟪coordinateVector i, w⟫_ℝ² = ‖w‖²` (Parseval on the coordinate basis). -/
private lemma sum_coord_inner_sq (w : Space) :
    ∑ i : Fin 3, ⟪coordinateVector i, w⟫_ℝ ^ 2 = ‖w‖ ^ 2 := by
  simp only [real_inner_coordVector]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [sq]

/-- **Plane-wave crown (Cartesian ansatz).** Every plane wave with `‖w‖ = k`
solves the homogeneous Helmholtz equation at every point. -/
theorem planeWaveSatisfiesHelmholtz (k : ℝ) (w y : Space) (hw : ‖w‖ = k) (x : Space) :
    helmholtzOperator k (planeWave k w y) x = 0 := by
  have hPi (w y : Space) (i : Fin 3) (z : Space) :
      fderiv ℝ (planeWave k w y) z (coordinateVector i) =
        planeWave k w y z * (Complex.I * ↑⟪coordinateVector i, w⟫_ℝ) := by
    rw [(hasFDerivAt_planeWave k w y z).fderiv]
    simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, real_inner_comm]
    ring
  have hinner (w y : Space) (i : Fin 3) :
      (fun z : Space => fderiv ℝ (planeWave k w y) z (coordinateVector i)) =
        fun z : Space => planeWave k w y z * (Complex.I * ↑⟪coordinateVector i, w⟫_ℝ) :=
    funext fun z => hPi w y i z
  have hD2 (w y : Space) (i : Fin 3) :
      fderiv ℝ (fun z : Space => fderiv ℝ (planeWave k w y) z (coordinateVector i)) x
        (coordinateVector i) =
        (Complex.I * ↑⟪coordinateVector i, w⟫_ℝ) ^ 2 * planeWave k w y x := by
    have hmul := (hasFDerivAt_planeWave k w y x).mul
      (hasFDerivAt_const (c := Complex.I * ↑⟪coordinateVector i, w⟫_ℝ) (x := x))
    have hem : (fun z : Space => planeWave k w y z * (Complex.I * ↑⟪coordinateVector i, w⟫_ℝ))
        =ᶠ[𝓝 x] (fun z => planeWave k w y z) *
          fun _ => (Complex.I * ↑⟪coordinateVector i, w⟫_ℝ) := by
      filter_upwards [univ_mem] with t _ht; rfl
    have hc := hmul.congr_of_eventuallyEq hem
    rw [hinner w y i, hc.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, smul_eq_mul,
      Complex.ofRealCLM_apply, innerSL_apply_apply, real_inner_comm]
    ring
  unfold helmholtzOperator scalarLaplacian
  rw [Finset.sum_congr rfl (fun i _ => hD2 w y i), ← Finset.sum_mul]
  have hsum : ∑ i : Fin 3, (Complex.I * (⟪coordinateVector i, w⟫_ℝ : ℂ)) ^ 2
      = -(‖w‖ : ℂ) ^ 2 := by
    have h1 : ∑ i : Fin 3, (Complex.I * (⟪coordinateVector i, w⟫_ℝ : ℂ)) ^ 2
        = -(∑ i : Fin 3, (↑(⟪coordinateVector i, w⟫_ℝ ^ 2) : ℂ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_pow, Complex.I_sq, neg_one_mul, ← Complex.ofReal_pow]
    rw [h1, ← Complex.ofReal_sum, sum_coord_inner_sq, Complex.ofReal_pow]
  rw [hsum]
  have hh : (‖w‖ : ℂ) ^ 2 = (↑(k * k) : ℂ) := by
    rw [← hw, ← Complex.ofReal_pow, sq, Complex.ofReal_mul]
  rw [hh]
  ring

/-! ## Crown support 3: profile derivative as an explicit stand-in -/

/-- The closed form of the profile derivative, used as an explicit stand-in for
`deriv (radialProfile k)` when composing chain rules, so that no `deriv` of an
opaque `deriv` is ever taken. -/
private def profileDerivClosed (k : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ↑(k * t)) * (Complex.I * ↑k * (t : ℂ) - 1) /
    (↑(4 * Real.pi) * (t : ℂ) * (t : ℂ))

private lemma hasDerivAt_profileDerivClosed (k r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (profileDerivClosed k)
      (Complex.exp (Complex.I * ↑(k * r)) *
        (-(↑(k * k)) * ↑r * ↑r - 2 * Complex.I * ↑k * ↑r + 2) /
        (↑(4 * Real.pi) * ↑r * ↑r * ↑r)) r := by
  have hnum := (hasDerivAt_exp_iik k r).mul (hasDerivAt_lin k r)
  have hden := hasDerivAt_den2 r
  have hne := coe_4pi_mul_r_mul_r_ne_zero r hr
  have h1 := hnum.div hden hne
  have he : (profileDerivClosed k) =ᶠ[𝓝 r] (fun t : ℝ =>
      Complex.exp (Complex.I * ↑(k * t)) * (Complex.I * ↑k * (t : ℂ) - 1) /
        (↑(4 * Real.pi) * (t : ℂ) * (t : ℂ))) :=
    eventuallyEq_of_mem univ_mem fun t _ht => rfl
  exact (h1.congr_of_eventuallyEq he).congr_deriv
    (by
      simp only [Pi.mul_apply, Pi.sub_apply]
      field_simp [hne]
      ring_nf
      simp only [Complex.I_sq, Complex.ofReal_mul, mul_neg, neg_mul, neg_neg]
      push_cast
      ring)

/-- `profileDerivClosed k` agrees with `deriv (radialProfile k)` near `r ≠ 0`. -/
private lemma eventuallyEq_deriv_profile (k r : ℝ) (hr : r ≠ 0) :
    (fun t => deriv (radialProfile k) t) =ᶠ[𝓝 r] profileDerivClosed k :=
  eventuallyEq_of_mem (isOpen_ne (x := (0 : ℝ)).mem_nhds hr)
    fun t ht => deriv_radialProfile k t ht

/-- The profile derivative is itself differentiable, in the form consumed by the
chain rule (built via the explicit closed form). -/
private lemma hasDerivAt_deriv_profile (k r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (deriv (radialProfile k)) (deriv (deriv (radialProfile k)) r) r := by
  have hfc : HasDerivAt (profileDerivClosed k) (deriv (profileDerivClosed k) r) r :=
    (hasDerivAt_profileDerivClosed k r hr).differentiableAt.hasDerivAt
  have ev := eventuallyEq_deriv_profile k r hr
  exact (hfc.congr_of_eventuallyEq ev).congr_deriv ev.deriv_eq.symm

private lemma differentiableAt_radialProfile (k r : ℝ) (hr : r ≠ 0) :
    DifferentiableAt ℝ (radialProfile k) r :=
  ((hasDerivAt_exp_iik k r).div (hasDerivAt_den1 r) (coe_4pi_ne_zero r hr)).differentiableAt

/-! ## The monopole is a Helmholtz solution away from its source -/

/-- `z ↦ ‖z − y‖` is differentiable away from `y`, with derivative
`(1/‖x−y‖) • ⟪x−y, ·⟩_ℝ`. -/
private lemma hasFDerivAt_normDist (x y : Space) (hxy : x ≠ y) :
    HasFDerivAt (fun z : Space => ‖z - y‖)
      ((1 / ‖x - y‖ : ℝ) • innerSL ℝ (x - y)) x := by
  have hn : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hz : HasFDerivAt (fun z : Space => z - y) (1 : Space →L[ℝ] Space) x :=
    (hasFDerivAt_id x).sub_const y
  have h1 : HasFDerivAt (fun z : Space => ‖z - y‖ ^ 2) (2 • innerSL ℝ (x - y)) x := by
    refine' ((hasStrictFDerivAt_norm_sq (x - y)).hasFDerivAt.comp x hz).congrCLM _
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, smul_apply]
  have h0 : (fun z : Space => ‖z - y‖ ^ 2) x ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  have hsq : (fun z : Space => ‖z - y‖) =ᶠ[𝓝 x] (fun z : Space => √(‖z - y‖ ^ 2)) := by
    filter_upwards [univ_mem] with z _hz
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  refine' ((h1.sqrt h0).congr_of_eventuallyEq hsq).congrCLM _
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_smul]
  rw [Real.sqrt_sq (norm_nonneg _)]
  field_simp [norm_ne_zero_iff.mpr hn]
  ring

/-- First order at a field point: the monopole's Fréchet derivative is
`g'(r) • (1/r) • ⟪x−y, ·⟩` where `r = ‖x−y‖`. -/
private lemma hasFDerivAt_monopole (k : ℝ) (x y : Space) (hxy : x ≠ y) :
    HasFDerivAt (monopole k y)
      ((toSpanSingleton ℝ (deriv (radialProfile k) ‖x - y‖)).comp
        ((1 / ‖x - y‖ : ℝ) • innerSL ℝ (x - y))) x := by
  have hr : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hnd := hasFDerivAt_normDist x y hxy
  have hcv := (differentiableAt_radialProfile k ‖x - y‖ hr).hasDerivAt
  have hcomp := hcv.hasFDerivAt.comp x hnd
  exact hcomp.congr_of_eventuallyEq (eventuallyEq_of_mem univ_mem fun z _ => rfl)

/-- The per-coordinate partial of the monopole, as an explicit function:
`∂ᵢΦ_y(z) = g'(‖z−y‖) · ⟪z−y, eᵢ⟫ / ‖z−y‖`. -/
private def partialMonopole (k : ℝ) (y : Space) (i : Fin 3) (z : Space) : ℂ :=
  deriv (radialProfile k) ‖z - y‖ * (⟪z - y, coordinateVector i⟫_ℝ / ‖z - y‖ : ℂ)

private lemma hasFDerivAt_coordRatio (y : Space) (i : Fin 3) (x : Space) (hxy : x ≠ y) :
    HasFDerivAt (fun z : Space => ⟪z - y, coordinateVector i⟫_ℝ / ‖z - y‖)
      ((‖x - y‖⁻¹ : ℝ) • innerSL ℝ (coordinateVector i)
        + ⟪x - y, coordinateVector i⟫_ℝ •
            (-((‖x - y‖ : ℝ) ^ 2)⁻¹ • ((1 / ‖x - y‖ : ℝ) • innerSL ℝ (x - y)))) x := by
  have hr : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have h1 : HasDerivAt (fun t : ℝ => t⁻¹) (-((‖x - y‖ : ℝ) ^ 2)⁻¹) ‖x - y‖ :=
    hasDerivAt_inv hr
  have hinv : HasFDerivAt (fun z : Space => ‖z - y‖⁻¹)
      (-((‖x - y‖ : ℝ) ^ 2)⁻¹ • ((1 / ‖x - y‖ : ℝ) • innerSL ℝ (x - y))) x := by
    have hcomp := h1.hasFDerivAt.comp x (hasFDerivAt_normDist x y hxy)
    refine' hcomp.congrCLM _
    ext v
    simp only [ContinuousLinearMap.comp_apply, toSpanSingleton_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    ring
  have hlin := hasFDerivAt_realInnerShift x y (coordinateVector i)
  have hmul := hlin.mul hinv
  have hem : (fun z : Space => ⟪z - y, coordinateVector i⟫_ℝ / ‖z - y‖) =ᶠ[𝓝 x]
      (fun z : Space => ⟪z - y, coordinateVector i⟫_ℝ) * fun z : Space => ‖z - y‖⁻¹ := by
    filter_upwards [univ_mem] with t _ht; rfl
  refine' (hmul.congr_of_eventuallyEq hem).congrCLM _
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    innerSL_apply_apply]
  ring

/-- Second-order plumbing: the Fréchet derivative of the per-coordinate partial
`∂ᵢΦ_y`, in the product-rule normal form `g₁ • L₂ + ratio • L₁`. -/
private lemma hasFDerivAt_partialMonopole (k : ℝ) (y : Space) (i : Fin 3)
    (x : Space) (hxy : x ≠ y) :
    HasFDerivAt (partialMonopole k y i)
      ((deriv (radialProfile k) ‖x - y‖ : ℂ) •
          (Complex.ofRealCLM.comp
            ((‖x - y‖⁻¹ : ℝ) • innerSL ℝ (coordinateVector i)
              + ⟪x - y, coordinateVector i⟫_ℝ •
                  (-((‖x - y‖ : ℝ) ^ 2)⁻¹ • ((1 / ‖x - y‖ : ℝ) • innerSL ℝ (x - y)))))
        + (⟪x - y, coordinateVector i⟫_ℝ / ‖x - y‖ : ℂ) •
            ((toSpanSingleton ℝ (deriv (deriv (radialProfile k)) ‖x - y‖)).comp
              ((1 / ‖x - y‖ : ℝ) • innerSL ℝ (x - y)))) x := by
  have hr : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hnd := hasFDerivAt_normDist x y hxy
  have hA : HasFDerivAt (fun z : Space => deriv (radialProfile k) ‖z - y‖)
      ((toSpanSingleton ℝ (deriv (deriv (radialProfile k)) ‖x - y‖)).comp
        ((1 / ‖x - y‖ : ℝ) • innerSL ℝ (x - y))) x :=
    (HasFDerivAt.comp (g := deriv (radialProfile k))
      (g' := toSpanSingleton ℝ (deriv (deriv (radialProfile k)) ‖x - y‖)) x
      ((hasDerivAt_deriv_profile k ‖x - y‖ hr).hasFDerivAt) hnd)
  have hB : HasFDerivAt (fun z : Space => (⟪z - y, coordinateVector i⟫_ℝ / ‖z - y‖ : ℂ))
      (Complex.ofRealCLM.comp
        ((‖x - y‖⁻¹ : ℝ) • innerSL ℝ (coordinateVector i)
          + ⟪x - y, coordinateVector i⟫_ℝ •
              (-((‖x - y‖ : ℝ) ^ 2)⁻¹ • ((1 / ‖x - y‖ : ℝ) • innerSL ℝ (x - y))))) x := by
    have hratio := hasFDerivAt_coordRatio y i x hxy
    have hcomp := (Complex.ofRealCLM.hasStrictFDerivAt (x := _)).hasFDerivAt.comp x hratio
    refine' hcomp.congr_of_eventuallyEq _
    filter_upwards [univ_mem] with t _ht
    exact (Complex.ofReal_div _ _).symm
  have hmul := hA.mul hB
  have hem : partialMonopole k y i =ᶠ[𝓝 x]
      (fun z : Space => deriv (radialProfile k) ‖z - y‖) *
        (fun z : Space => (⟪z - y, coordinateVector i⟫_ℝ / ‖z - y‖ : ℂ)) := by
    filter_upwards [univ_mem] with t _ht; rfl
  refine' (hmul.congr_of_eventuallyEq hem).congrCLM _
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, toSpanSingleton_apply, smul_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul]

/-- The `i`-th iterated partial of the monopole evaluated at the field point:
`∂ᵢ∂ᵢΦ_y = g''·(ℓᵢ/r)² + g'·(1/r − ℓᵢ²/r³)` in coordinate-free cast form. -/
private lemma fderiv_partialMonopole (k : ℝ) (y : Space) (i : Fin 3)
    (x : Space) (hxy : x ≠ y) :
    fderiv ℝ (partialMonopole k y i) x (coordinateVector i) =
      deriv (deriv (radialProfile k)) ‖x - y‖ *
        (↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑‖x - y‖⁻¹) *
        (↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑‖x - y‖⁻¹) +
      deriv (radialProfile k) ‖x - y‖ *
        (↑‖x - y‖⁻¹ -
          ↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑(⟪x - y, coordinateVector i⟫_ℝ) *
            ↑((‖x - y‖ ^ 2)⁻¹) * ↑‖x - y‖⁻¹) := by
  have hrc : (‖x - y‖ : ℂ) ≠ 0 := by
    simpa using norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hP := hasFDerivAt_partialMonopole k y i x hxy
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, toSpanSingleton_apply, innerSL_apply_apply, smul_eq_mul,
    Complex.ofRealCLM_apply]
  rw [real_inner_self_coord, real_inner_comm (coordinateVector i) (x - y)]
  push_cast
  simp only [div_eq_mul_inv, one_mul, mul_one]
  rw [show (‖x - y‖⁻¹ * ⟪coordinateVector i, x - y⟫_ℝ) •
      deriv (deriv (radialProfile k)) ‖x - y‖ =
      ↑(‖x - y‖⁻¹ * ⟪coordinateVector i, x - y⟫_ℝ) *
        deriv (deriv (radialProfile k)) ‖x - y‖ from rfl]
  push_cast
  ring

/-- The per-coordinate partials telescope to the radial Laplacian:
`∑ᵢ ∂ᵢ(∂ᵢΦ_y)(x) = g''(r) + (2/r)·g'(r)`. The engine is Parseval
(`∑ᵢ ℓᵢ² = r²`) plus the field arithmetic `r⁻²·r² = 1`, `3/r − 1/r = 2/r`. -/
private lemma sum_partialMonopole (k : ℝ) (y : Space) (x : Space) (hxy : x ≠ y) :
    ∑ i : Fin 3,
      (deriv (deriv (radialProfile k)) ‖x - y‖ *
        (↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑‖x - y‖⁻¹) *
        (↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑‖x - y‖⁻¹) +
      deriv (radialProfile k) ‖x - y‖ *
        (↑‖x - y‖⁻¹ -
          ↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑(⟪x - y, coordinateVector i⟫_ℝ) *
            ↑((‖x - y‖ ^ 2)⁻¹) * ↑‖x - y‖⁻¹)) =
      deriv (deriv (radialProfile k)) ‖x - y‖ +
        (2 : ℂ) / ↑‖x - y‖ * deriv (radialProfile k) ‖x - y‖ := by
  classical
  have hr : (‖x - y‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hsumR : ∑ i : Fin 3, ⟪x - y, coordinateVector i⟫_ℝ * ⟪x - y, coordinateVector i⟫_ℝ =
      ‖x - y‖ * ‖x - y‖ := by
    rw [show (fun i : Fin 3 => ⟪x - y, coordinateVector i⟫_ℝ * ⟪x - y, coordinateVector i⟫_ℝ) =
          (fun i : Fin 3 => ⟪coordinateVector i, x - y⟫_ℝ ^ 2) from by
        funext i; rw [real_inner_comm, sq]]
    rw [sum_coord_inner_sq, sq]
  have hR1 : ∑ i : Fin 3, (⟪x - y, coordinateVector i⟫_ℝ * ‖x - y‖⁻¹) *
      (⟪x - y, coordinateVector i⟫_ℝ * ‖x - y‖⁻¹) = (1 : ℝ) := by
    have h1 : (fun i : Fin 3 => (⟪x - y, coordinateVector i⟫_ℝ * ‖x - y‖⁻¹) *
        (⟪x - y, coordinateVector i⟫_ℝ * ‖x - y‖⁻¹)) =
        (fun i : Fin 3 => ‖x - y‖⁻¹ * ‖x - y‖⁻¹ *
          (⟪x - y, coordinateVector i⟫_ℝ * ⟪x - y, coordinateVector i⟫_ℝ)) := by
      funext i; ring
    rw [h1, ← Finset.mul_sum, hsumR]
    field_simp [hr]
  have hR2 : ∑ i : Fin 3, (‖x - y‖⁻¹ - ⟪x - y, coordinateVector i⟫_ℝ *
      ⟪x - y, coordinateVector i⟫_ℝ * ((‖x - y‖ ^ 2)⁻¹) * ‖x - y‖⁻¹) =
      2 * ‖x - y‖⁻¹ := by
    have h2 : (fun i : Fin 3 => ‖x - y‖⁻¹ - ⟪x - y, coordinateVector i⟫_ℝ *
        ⟪x - y, coordinateVector i⟫_ℝ * ((‖x - y‖ ^ 2)⁻¹) * ‖x - y‖⁻¹) =
        (fun i : Fin 3 => ‖x - y‖⁻¹ -
          (((‖x - y‖ ^ 2)⁻¹) * ‖x - y‖⁻¹) *
            (⟪x - y, coordinateVector i⟫_ℝ * ⟪x - y, coordinateVector i⟫_ℝ)) := by
      funext i; ring
    rw [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumR]
    have h3 : ∑ i : Fin 3, (‖x - y‖⁻¹ : ℝ) = 3 * ‖x - y‖⁻¹ := by
      rw [Fin.sum_univ_three]
      ring
    rw [h3]
    field_simp [hr]
    ring
  have hC1 : ∑ i : Fin 3, ((↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑‖x - y‖⁻¹) *
      (↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑‖x - y‖⁻¹) : ℂ) = 1 := by
    have h1 : (fun i : Fin 3 => ((↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑‖x - y‖⁻¹) *
        (↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑‖x - y‖⁻¹) : ℂ)) =
        (fun i : Fin 3 => ↑((⟪x - y, coordinateVector i⟫_ℝ * ‖x - y‖⁻¹) *
          (⟪x - y, coordinateVector i⟫_ℝ * ‖x - y‖⁻¹)) : Fin 3 → ℂ) := by
      funext i; push_cast; ring
    rw [h1, ← Complex.ofReal_sum, hR1, Complex.ofReal_one]
  have hC2 : ∑ i : Fin 3, ((↑‖x - y‖⁻¹ - ↑(⟪x - y, coordinateVector i⟫_ℝ) *
      ↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑((‖x - y‖ ^ 2)⁻¹) * ↑‖x - y‖⁻¹) : ℂ) =
      ↑(2 * ‖x - y‖⁻¹) := by
    have h2 : (fun i : Fin 3 => ((↑‖x - y‖⁻¹ - ↑(⟪x - y, coordinateVector i⟫_ℝ) *
        ↑(⟪x - y, coordinateVector i⟫_ℝ) * ↑((‖x - y‖ ^ 2)⁻¹) * ↑‖x - y‖⁻¹) : ℂ)) =
        (fun i : Fin 3 => ↑(‖x - y‖⁻¹ - ⟪x - y, coordinateVector i⟫_ℝ *
          ⟪x - y, coordinateVector i⟫_ℝ * ((‖x - y‖ ^ 2)⁻¹) * ‖x - y‖⁻¹) : Fin 3 → ℂ) := by
      funext i; push_cast; ring
    rw [h2, ← Complex.ofReal_sum, hR2]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => mul_assoc _ _ _)]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hC1, hC2]
  push_cast
  ring

/-- Summed second coordinate partials of the monopole as an `fderiv` sum. -/
private lemma sum_fderiv_partialMonopole (k : ℝ) (y : Space) (x : Space) (hxy : x ≠ y) :
    ∑ i : Fin 3, fderiv ℝ (partialMonopole k y i) x (coordinateVector i) =
      deriv (deriv (radialProfile k)) ‖x - y‖ +
        (2 : ℂ) / ↑‖x - y‖ * deriv (radialProfile k) ‖x - y‖ := by
  rw [Finset.sum_congr rfl (fun i _ => fderiv_partialMonopole k y i x hxy)]
  exact sum_partialMonopole k y x hxy

/-- On the punctured neighborhood of a field point `x ≠ y`, the abstract
coordinate partial of the monopole agrees with the explicit partial
`partialMonopole k y i`. -/
private lemma eventuallyEq_monopolePartial (k : ℝ) (y : Space) (i : Fin 3)
    (x : Space) (hxy : x ≠ y) :
    (fun z : Space => fderiv ℝ (monopole k y) z (coordinateVector i)) =ᶠ[𝓝 x]
      partialMonopole k y i := by
  refine eventuallyEq_of_mem (isOpen_ne (x := y).mem_nhds hxy) fun z hzy => ?_
  have hP := hasFDerivAt_monopole k z y hzy
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.comp_apply, toSpanSingleton_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  unfold partialMonopole
  rw [real_inner_comm]
  simp only [smul_eq_mul, div_eq_mul_inv, one_mul]
  rw [show (‖z - y‖⁻¹ * ⟪coordinateVector i, z - y⟫_ℝ) •
      deriv (radialProfile k) ‖z - y‖ =
      ↑(‖z - y‖⁻¹ * ⟪coordinateVector i, z - y⟫_ℝ) *
        deriv (radialProfile k) ‖z - y‖ from rfl]
  push_cast
  ring

/-- **Radial Laplacian of the monopole** (the crown's engine):
`scalarLaplacian Φ_y (x) = g''(r) + (2/r)·g'(r)` at `r = ‖x−y‖ ≠ 0`, in the
repository's double-`fderiv` convention. -/
private lemma laplacian_monopole (k : ℝ) (y : Space) (x : Space) (hxy : x ≠ y) :
    scalarLaplacian (monopole k y) x =
      deriv (deriv (radialProfile k)) ‖x - y‖ +
        (2 : ℂ) / ↑‖x - y‖ * deriv (radialProfile k) ‖x - y‖ := by
  classical
  unfold scalarLaplacian
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [(eventuallyEq_monopolePartial k y i x hxy).fderiv_eq (𝕜 := ℝ)])]
  exact sum_fderiv_partialMonopole k y x hxy

/-- **Monopole crown.** For every frequency `k`, every source `y`, and every
field point `x ≠ y`, the acoustic monopole solves the homogeneous Helmholtz
equation pointwise: `(Δ + k²)Φ_y(x) = 0`. -/
theorem monopoleSatisfiesHelmholtz (k : ℝ) (y : Space) (x : Space) (hxy : x ≠ y) :
    helmholtzOperator k (monopole k y) x = 0 := by
  unfold helmholtzOperator
  rw [laplacian_monopole k y x hxy,
    radialProfile_ode_neg k ‖x - y‖ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]
  unfold monopole
  ring

/-! ## The splat crown: finite superpositions solve Helmholtz -/

/-- Set-level transport of openness (Mathlib has no `IsOpen.congr`). -/
private lemma isOpen_congr {s t : Set Space} (h : s = t) (ht : IsOpen t) : IsOpen s := by
  rw [h]; exact ht

/-- The complement of a finite source set is open. -/
private lemma isOpen_punctured (s : Finset Space) :
    IsOpen {x : Space | ∀ y ∈ s, x ≠ y} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact isOpen_congr (Set.eq_univ_of_forall
        fun x y hy => absurd hy (by simp)) isOpen_univ
  | @insert a s hat his =>
      refine isOpen_congr ?_ ((isOpen_ne (x := a)).inter his)
      ext z
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert]
      refine ⟨fun h => ⟨h a (Or.inl rfl), fun y hy => h y (Or.inr hy)⟩,
        fun h y hy => hy.elim (fun e => fun he => h.1 (he.trans e)) (fun m => h.2 y m)⟩

/-- The explicit partial of a single scaled monopole. -/
private lemma fderiv_monopole_coord (k : ℝ) (c : ℂ) (y : Space) (i : Fin 3)
    (z : Space) (hzy : z ≠ y) :
    fderiv ℝ (fun w => c * monopole k y w) z (coordinateVector i) =
      c * partialMonopole k y i z := by
  have hrc : (‖z - y‖ : ℂ) ≠ 0 := by
    simpa using norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzy)
  have h := (hasFDerivAt_monopole k z y hzy).const_mul c
  rw [h.fderiv, partialMonopole]
  simp only [smul_apply, comp_apply, toSpanSingleton_apply, innerSL_apply_apply, smul_eq_mul,
    div_eq_mul_inv, one_mul]
  push_cast
  rw [show (‖z - y‖⁻¹ * ⟪z - y, coordinateVector i⟫_ℝ) •
      deriv (radialProfile k) ‖z - y‖ =
      ↑(‖z - y‖⁻¹ * ⟪z - y, coordinateVector i⟫_ℝ) *
        deriv (radialProfile k) ‖z - y‖ from rfl]
  push_cast
  ring

/-- Pointwise: the coordinate partial of a splat is the sum of the explicit
partials, valid on the complement of the sources. -/
private lemma fderiv_splat_pointwise (k : ℝ) (amps : Space → ℂ) (i : Fin 3)
    (s : Finset Space) (w : Space) (hw : ∀ y ∈ s, w ≠ y) :
    fderiv ℝ (splatField k amps s) w (coordinateVector i) =
      ∑ y ∈ s, amps y * partialMonopole k y i w := by
  classical
  have heq : (splatField k amps s) = (fun v => ∑ y ∈ s, amps y * monopole k y v) := rfl
  have hd : ∀ y ∈ s, DifferentiableAt ℝ (fun v => amps y * monopole k y v) w := by
    intro y hy
    exact ((hasFDerivAt_monopole k w y (hw y hy)).const_mul (amps y)).differentiableAt
  rw [heq, fderiv_fun_sum hd]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun y hy => fderiv_monopole_coord k (amps y) y i w (hw y hy))]

/-- Pulling a scalar amplitude through the iterated coordinate partial. -/
private lemma fderiv_partialMonopole_coord (k : ℝ) (c : ℂ) (y : Space) (i : Fin 3)
    (x : Space) (hxy : x ≠ y) :
    fderiv ℝ (fun w => c * partialMonopole k y i w) x (coordinateVector i) =
      c * fderiv ℝ (partialMonopole k y i) x (coordinateVector i) := by
  have hP := hasFDerivAt_partialMonopole k y i x hxy
  have h := hP.const_mul c
  rw [h.fderiv, ← hP.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- **Splat crown — the representation theorem, synthesis direction.** Any
finite superposition of acoustic monopoles `u(x) = Σᵢ aᵢ Φ_{yᵢ}(x)` solves the
homogeneous Helmholtz equation on the complement of its source set: if
`x ≠ yᵢ` for every source, then `(Δ + k²)u(x) = 0`. The synthesis direction is
PROVED (linearity of `Δ + k²` through the coordinate-partial sums, plus the
radial ODE per source), not assumed. -/
theorem splatSatisfiesHelmholtz (k : ℝ) (amps : Space → ℂ) (s : Finset Space)
    (x : Space) (hx : ∀ y ∈ s, x ≠ y) :
    helmholtzOperator k (splatField k amps s) x = 0 := by
  classical
  unfold helmholtzOperator scalarLaplacian
  have hevf (i : Fin 3) :
      (fun w : Space => fderiv ℝ (splatField k amps s) w (coordinateVector i)) =ᶠ[𝓝 x]
        (fun w : Space => ∑ y ∈ s, amps y * partialMonopole k y i w) := by
    refine eventuallyEq_of_mem
      (IsOpen.mem_nhds (isOpen_punctured s) (by simpa using hx)) fun w hw => ?_
    rw [fderiv_splat_pointwise k amps i s w hw]
  have hd2 (i : Fin 3) :
      ∀ y ∈ s, DifferentiableAt ℝ (fun w => amps y * partialMonopole k y i w) x := by
    intro y hy
    exact ((hasFDerivAt_partialMonopole k y i x (hx y hy)).const_mul (amps y)).differentiableAt
  rw [Finset.sum_congr rfl
    (fun i _ => by rw [(hevf i).fderiv_eq (𝕜 := ℝ)])]
  rw [Finset.sum_congr rfl
    (fun i _ => by rw [fderiv_fun_sum (hd2 i)])]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ =>
    Finset.sum_congr rfl (fun y hy =>
      fderiv_partialMonopole_coord k (amps y) y i x (hx y hy)))]
  rw [Finset.sum_comm]
  have hper (y : Space) (hy : y ∈ s) :
      ∑ i : Fin 3, amps y * fderiv ℝ (partialMonopole k y i) x (coordinateVector i) =
        amps y * (deriv (deriv (radialProfile k)) ‖x - y‖ +
          (2 : ℂ) / ↑‖x - y‖ * deriv (radialProfile k) ‖x - y‖) := by
    rw [← Finset.mul_sum, sum_fderiv_partialMonopole k y x (hx y hy)]
  rw [Finset.sum_congr rfl (fun y hy => hper y hy)]
  rw [Finset.sum_congr rfl (fun y hy => congrArg (fun t : ℂ => amps y * t)
    (radialProfile_ode_neg k ‖x - y‖
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hx y hy)))))]
  have this : (fun y : Space => amps y * (-↑(k * k) * radialProfile k ‖x - y‖)) =
      (fun y : Space => -(↑(k * k)) * (amps y * monopole k y x)) := by
    funext y
    unfold monopole
    ring
  rw [this, ← Finset.mul_sum]
  unfold splatField
  ring

/-! ## CONJECTURE (not closed here): splat-placement design optimality

CONJECTURE (frame-type bounds for optimal splat placement). Fix `k > 0`, a target
sound field `f` on a measurement region `M ⊂ ℝ³`, and a budget `N`. Among all
`splatField k amps s` with `‖s‖ = N`, the claim would be that there is an
placement/amplitude pair minimizing `sup_{x ∈ M} ‖u(x) − f(x)‖` whose value is
comparable (up to an absolute constant independent of `f, M, k, N`) to the best
approximation of `f` by ANY superposition of `N` radiating solutions, and that
the synthesis operator `s ↦ Σᵢ amps(yᵢ) Φ_{yᵢ}` is a frame for its range with
bounds depending only on the source separation and `k`.

This is NOT proved in this file and is NOT faked as a theorem here. The named
missing primitives, as exact types:
1. a completeness/totality statement for the far-field pattern class:
   the map `u ↦ u^∞` from radiating Helmholtz solutions (limiting absorption
   class) to `L²(S²)` — Mathlib has no radiation-condition or far-field API
   at all (searched: no `fundamental solution`, no `Hankel`-based radiation,
   no Helmholtz exterior-problem solver);
2. a density theorem for finite monopole sums in that class with explicit
   separation-dependent constants (the analogue of a frame bound for the
   translates of the Green function on a discrete set);
3. measurability + attainment for the optimization over `Finset Space ×
   (Space → ℂ)` of the sup-error functional — needs a compactness target that
   the repository does not yet define for sound fields.
Until 1–3 exist, the honest status of the package is: the REPRESENTATION
direction (superpositions are solutions) is proved above; the APPROXIMATION
direction (solutions are limits of superpositions, and placements can be
chosen optimally) remains CONJECTURE-strength here. -/

/-! ## Evidence block (compiled with the file; read verbatim from `lake env lean` output) -/

#check @Navier.Sound.radialProfile_helmholtzODE
#print axioms Navier.Sound.radialProfile_helmholtzODE
#check @Navier.Sound.planeWaveSatisfiesHelmholtz
#print axioms Navier.Sound.planeWaveSatisfiesHelmholtz
#check @Navier.Sound.monopoleSatisfiesHelmholtz
#print axioms Navier.Sound.monopoleSatisfiesHelmholtz
#check @Navier.Sound.splatSatisfiesHelmholtz
#print axioms Navier.Sound.splatSatisfiesHelmholtz

end
end Navier.Sound

