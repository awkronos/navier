import Navier.Analysis.OfficialABEncoding
import Navier.Routes.R7.PhaseSymbol

/-!
# Euclidean frequencywise Leray projection

The real Fourier-side Leray multiplier is the orthogonal projection onto the
plane perpendicular to the frequency.  This file realizes that canonical
Euclidean projection, proves contraction and idempotence, and identifies it
exactly with the finite-dimensional symbol already used by the R7 tests.

This is frequencywise real linear algebra.  It is not yet a complex Fourier
multiplier on a function space, a Helmholtz decomposition, a heat semigroup,
or a Duhamel/local-existence theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.LerayProjection

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Routes.R7

/-- Euclidean three-space with the official point norm. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The plane perpendicular to a Fourier frequency. -/
def frequencyPlane (q : E3) : Submodule ℝ E3 :=
  (ℝ ∙ q)ᗮ

/-- The Euclidean orthogonal projection onto the frequency plane. -/
def euclideanLeray (q : E3) : E3 →L[ℝ] E3 :=
  (frequencyPlane q).starProjection

theorem euclideanLeray_mem (q v : E3) :
    euclideanLeray q v ∈ frequencyPlane q :=
  Submodule.starProjection_apply_mem _ _

/-- The projected vector is transverse to its frequency. -/
theorem inner_euclideanLeray (q v : E3) :
    inner ℝ q (euclideanLeray q v) = 0 :=
  (Submodule.mem_orthogonal_singleton_iff_inner_right).1
    (euclideanLeray_mem q v)

/-- Orthogonal Leray projection contracts the official Euclidean norm. -/
theorem euclideanLeray_norm_le (q v : E3) :
    ‖euclideanLeray q v‖ ≤ ‖v‖ :=
  Submodule.norm_starProjection_apply_le _ _

/-- Frequencywise Leray projection is idempotent. -/
theorem euclideanLeray_idempotent (q v : E3) :
    euclideanLeray q (euclideanLeray q v) = euclideanLeray q v :=
  (Submodule.starProjection_eq_self_iff).2 (euclideanLeray_mem q v)

/-- Exact orthogonal-projection formula, totalized to the identity at zero by
Lean's division convention. -/
theorem euclideanLeray_formula (q v : E3) :
    euclideanLeray q v =
      v - (inner ℝ q v / ‖q‖ ^ 2) • q := by
  change ((ℝ ∙ q)ᗮ).starProjection v = _
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton]
  simp

/-- The official Euclidean inner product is the repository's dot product with
the arguments in Mathlib's real-inner-product order. -/
theorem officialPoint_inner_eq_dotProduct (q v : Space) :
    inner ℝ (officialEuclideanPoint q) (officialEuclideanPoint v) =
      v ⬝ᵥ q := by
  simp [PiLp.inner_apply, officialEuclideanPoint, dotProduct]

/-- The squared official Euclidean norm is the self dot product. -/
theorem officialPoint_norm_sq_eq_dotProduct (q : Space) :
    ‖officialEuclideanPoint q‖ ^ 2 = q ⬝ᵥ q := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [officialEuclideanPoint, dotProduct, Real.norm_eq_abs, pow_two]

/-- The existing normalized R7 symbol is exactly the canonical Euclidean
orthogonal projection after transporting coordinates. -/
theorem officialPoint_normalizedLeray (q v : Space) :
    officialEuclideanPoint (normalizedLeraySymbol q v) =
      euclideanLeray (officialEuclideanPoint q) (officialEuclideanPoint v) := by
  rw [euclideanLeray_formula, officialPoint_inner_eq_dotProduct,
    officialPoint_norm_sq_eq_dotProduct]
  ext i
  rfl

/-- Consequently the normalized R7 symbol contracts Fefferman's Euclidean
point norm, not necessarily the inherited Pi supremum norm. -/
theorem officialEuclideanNorm_normalizedLeray_le (q v : Space) :
    officialEuclideanNorm (normalizedLeraySymbol q v) ≤
      officialEuclideanNorm v := by
  rw [officialEuclideanNorm, officialPoint_normalizedLeray]
  exact euclideanLeray_norm_le _ _

end Navier.Analysis.LerayProjection
