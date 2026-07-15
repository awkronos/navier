import Navier.Analysis.Covariance
import Navier.Analysis.OfficialABEncoding
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Coordinate vorticity and critical scaling

This file defines coordinate curl, proves its parabolic scaling law, and
defines unit vorticity direction only on the nonzero-vorticity subtype.  The
Euclidean norm is the one used in Fefferman's official coordinates.

Curl-gradient cancellation, the vorticity PDE, Biot--Savart recovery,
stretching estimates, and dynamically generated direction coherence remain
separate analytic obligations.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

namespace Navier.Analysis.Vorticity

open Navier
open Navier.Analysis.Covariance
open Navier.Analysis.OfficialABEncoding

/-- Coordinate curl of a time-independent three-dimensional velocity field. -/
def staticCurl (u : VelocityField) (x : Space) : Space :=
  ∑ i : Fin 3, basisVector i ⨯₃ (fderiv ℝ u x (basisVector i))

/-- Curl carries the critical velocity dilation with homogeneity two. -/
theorem staticCurl_dilation (c : ℝ) (u : VelocityField) (x : Space) :
    staticCurl (fun y => c • u (c • y)) x =
      c ^ 2 • staticCurl u (c • x) := by
  simp only [staticCurl, fderiv_velocity_dilation,
    smul_apply, map_smul]
  rw [Finset.smul_sum]

/-- Vorticity is the spatial curl of each velocity time-slice. -/
def vorticity (u : VelocityEvolution) (t : ℝ) (x : Space) : Space :=
  staticCurl (u t) x

/-- Exact parabolic scaling law for vorticity. -/
theorem vorticity_scaled (lambda : ℝ) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    vorticity (parabolicScaledVelocity lambda u) t x =
      lambda ^ 2 • vorticity u (lambda ^ 2 * t) (lambda • x) := by
  exact staticCurl_dilation lambda (u (lambda ^ 2 * t)) x

theorem officialEuclideanNorm_eq_zero_iff (x : Space) :
    officialEuclideanNorm x = 0 ↔ x = 0 := by
  rw [officialEuclideanNorm, norm_eq_zero]
  constructor
  · intro h
    ext i
    simpa [officialEuclideanPoint] using
      congrFun (congrArg WithLp.ofLp h) i
  · intro h
    subst x
    rfl

theorem officialEuclideanNorm_smul (c : ℝ) (x : Space) :
    officialEuclideanNorm (c • x) =
      |c| * officialEuclideanNorm x := by
  simp [officialEuclideanNorm, officialEuclideanPoint, norm_smul,
    Real.norm_eq_abs]

/-- Spatial points at which vorticity direction is defined. -/
abbrev NonzeroVorticityPoint (u : VelocityEvolution) (t : ℝ) :=
  {x : Space // vorticity u t x ≠ 0}

/-- Euclidean-unit vorticity direction, deliberately undefined at zeros. -/
def vorticityDirection (u : VelocityEvolution) (t : ℝ)
    (x : NonzeroVorticityPoint u t) : Space :=
  (officialEuclideanNorm (vorticity u t x))⁻¹ • vorticity u t x

/-- The direction field has official Euclidean norm one on its exact domain. -/
theorem vorticityDirection_euclideanNorm (u : VelocityEvolution) (t : ℝ)
    (x : NonzeroVorticityPoint u t) :
    officialEuclideanNorm (vorticityDirection u t x) = 1 := by
  have hnorm : officialEuclideanNorm (vorticity u t x) ≠ 0 := by
    intro h
    exact x.property ((officialEuclideanNorm_eq_zero_iff _).mp h)
  rw [vorticityDirection, officialEuclideanNorm_smul]
  rw [abs_of_nonneg (inv_nonneg.mpr (officialEuclideanNorm_nonneg _))]
  exact inv_mul_cancel₀ hnorm

end Navier.Analysis.Vorticity
