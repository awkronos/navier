import Navier.Analysis.OfficialABEncoding
import Navier.Analysis.LerayProjection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The `Space ↔ EuclideanSpace ℝ (Fin 3)` Fourier bridge

The repository's spatial domain is `Navier.Space = Fin 3 → ℝ`, which inherits
Mathlib's product (supremum) norm and therefore is *not* an `InnerProductSpace`
under that norm: the supremum norm does not satisfy `‖x‖² = ⟪x, x⟫`.

The Fourier / Parseval / orthogonal-projection machinery that the BKM assembly
line consumes (see `Navier.Analysis.LerayProjection`, `ComplexLerayProjection`,
`ComplexFrequencyHeatLeray`) lives on `EuclideanSpace ℝ (Fin 3)`, which is
Mathlib's notation for `PiLp 2 (fun _ : Fin 3 => ℝ)` — the canonical ℓ²
inner-product-space structure on the coordinates of `Space`.

This file builds the canonical linear equivalence and norm/inner-product
transport facts that let frequency-side Fourier lemmas be applied to objects
defined in the repository's `Space` coordinates.  The identification is
*adequately normed* (bi-Lipschitz with sharp constants `1` and `√3`), not a
literal `IsometryEquiv` between the supremum and ℓ² norms — those norms are
genuinely different.  The underlying map is the identity on coordinates.

Concretely the file provides:

* `spaceEuclideanEquiv` : the canonical `Space ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)`,
  equal on points to the existing `officialEuclideanPoint`;
* `spaceEuclideanIso` : the same identification lifted to a genuine
  `LinearIsometryEquiv` between the ℓ²-structured copy `PiLp 2 (fun _ : Fin 3 => ℝ)`
  (which is `EuclideanSpace ℝ (Fin 3)`) and `EuclideanSpace ℝ (Fin 3)` — the
  Fourier-native isometric copy;
* the norm equality `‖spaceEuclideanEquiv x‖ = officialEuclideanNorm x`;
* the two-sided bi-Lipschitz bound `‖x‖ ≤ ‖spaceEuclideanEquiv x‖ ≤ √3 · ‖x‖`;
* the inner-product transport `⟪spaceEuclideanEquiv x, spaceEuclideanEquiv y⟫ = ∑ x i * y i`,
  the Fourier/Parseval enabler;
* corollaries tying the bridge to the repository's existing `euclideanLeray`
  projection, so that frequency-side results compose cleanly with
  coordinate-side vorticity and velocity fields.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Analysis.FourierBridge

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.LerayProjection
open Navier.Routes.R7

/-- The canonical coordinate identity as a bundled `ℝ`-linear equivalence
between the repository's `Space` and the Fourier-native `EuclideanSpace ℝ (Fin 3)`.

The underlying function is `WithLp.toLp 2`, identical on coordinates to the
existing `officialEuclideanPoint`; here it is packaged as a two-sided linear
equivalence so Fourier-side operators can be transported across it without
unbundling. -/
def spaceEuclideanEquiv : Space ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (WithLp.linearEquiv 2 ℝ Space).symm

/-- The bridge acts on points as the existing `officialEuclideanPoint`
coordinate embedding. -/
theorem spaceEuclideanEquiv_apply (x : Space) :
    spaceEuclideanEquiv x = officialEuclideanPoint x := rfl

/-- The inverse of the bridge recovers the underlying `Space` coordinates. -/
theorem spaceEuclideanEquiv_symm_apply (x : EuclideanSpace ℝ (Fin 3)) :
    spaceEuclideanEquiv.symm x = WithLp.ofLp x := rfl

/-- Norm of the bridge image equals Fefferman's official Euclidean point norm. -/
theorem norm_spaceEuclideanEquiv (x : Space) :
    ‖spaceEuclideanEquiv x‖ = officialEuclideanNorm x := rfl

/-- Lower bi-Lipschitz bound: the inherited supremum norm is bounded by the
Euclidean norm of the bridge image. -/
theorem norm_le_norm_spaceEuclideanEquiv (x : Space) :
    ‖x‖ ≤ ‖spaceEuclideanEquiv x‖ := by
  rw [norm_spaceEuclideanEquiv]
  exact norm_le_officialEuclideanNorm x

/-- Upper bi-Lipschitz bound: the Euclidean norm of the bridge image is at most
`√3` times the inherited supremum norm (sharp in dimension three). -/
theorem norm_spaceEuclideanEquiv_le (x : Space) :
    ‖spaceEuclideanEquiv x‖ ≤ Real.sqrt 3 * ‖x‖ := by
  rw [norm_spaceEuclideanEquiv]
  exact officialEuclideanNorm_le x

/-- Inner-product transport: the Euclidean inner product on the bridge image is
the coordinate dot product `∑ x i * y i`.  This is the identity that makes
Parseval / Plancherel frequency-side identities composable with
coordinate-side vorticity and velocity fields. -/
theorem inner_spaceEuclideanEquiv (x y : Space) :
    inner ℝ (spaceEuclideanEquiv x) (spaceEuclideanEquiv y) =
      ∑ i : Fin 3, x i * y i := by
  rw [spaceEuclideanEquiv_apply, spaceEuclideanEquiv_apply,
    officialPoint_inner_eq_dotProduct]
  simp only [dotProduct]
  simp_rw [mul_comm]

/-- The bridge preserves the inner product in the sense that the Euclidean
inner product of two bridge images equals the sum of products of coordinates. -/
theorem inner_spaceEuclideanEquiv_eq_dotProduct (x y : Space) :
    inner ℝ (spaceEuclideanEquiv x) (spaceEuclideanEquiv y) = y ⬝ᵥ x := by
  rw [spaceEuclideanEquiv_apply, spaceEuclideanEquiv_apply]
  exact officialPoint_inner_eq_dotProduct x y

/-- The squared Euclidean norm of the bridge image is the self dot product. -/
theorem norm_sq_spaceEuclideanEquiv (x : Space) :
    ‖spaceEuclideanEquiv x‖ ^ 2 = x ⬝ᵥ x := by
  rw [spaceEuclideanEquiv_apply]
  exact officialPoint_norm_sq_eq_dotProduct x

/-- The canonical Fourier-native isometric identification: a genuine
`LinearIsometryEquiv` between the ℓ²-structured copy `PiLp 2 (fun _ : Fin 3 => ℝ)`
and `EuclideanSpace ℝ (Fin 3)`.  Both sides carry the same ℓ² inner-product and
norm; the map is the identity on underlying functions.  This is the form
required by Mathlib's `InnerProductSpace` Fourier lemmas. -/
def spaceEuclideanIso :
    PiLp 2 (fun _ : Fin 3 => ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearIsometryEquiv.refl ℝ _

/-- The bridge image is unchanged by `spaceEuclideanIso`. -/
@[simp]
theorem spaceEuclideanIso_apply (x : PiLp 2 (fun _ : Fin 3 => ℝ)) :
    spaceEuclideanIso x = x := rfl

/-- Transporting the repository's `euclideanLeray` frequencywise projection
across the bridge: the projection of a bridge image equals the bridge image of
the projection applied to the underlying `Space` coordinates. -/
theorem spaceEuclideanEquiv_euclideanLeray (q v : Space) :
    euclideanLeray (spaceEuclideanEquiv q) (spaceEuclideanEquiv v) =
      spaceEuclideanEquiv (normalizedLeraySymbol q v) := by
  rw [spaceEuclideanEquiv_apply, spaceEuclideanEquiv_apply]
  exact (officialPoint_normalizedLeray q v).symm

end Navier.Analysis.FourierBridge
