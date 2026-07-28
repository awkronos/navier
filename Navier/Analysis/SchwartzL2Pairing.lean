import Navier.Analysis.LerayWeak

/-!
# The `L²` pairing of Schwartz velocity fields (shared prerequisite layer)

`schwartzL2Inner` and its bilinearity toolkit, extracted verbatim from
`Navier.Analysis.GalerkinBasis` so that both that file and
`Navier.Analysis.GalerkinRawFamily` can consume it without an import cycle.

**Why this file exists.**  `GalerkinRawFamily` builds the countable
divergence-free `L²`-independent reservoir
(`exists_countable_independent_divFree_family`) that
`GalerkinBasis.exists_denseIndependentDivFreeFamily_of_reservoir` needs as its
hypothesis.  The reservoir's own statement and proof are phrased in
`schwartzL2Inner`, so `GalerkinRawFamily` used to reach for it by importing
`GalerkinBasis` — putting the reservoir *downstream* of the very theorem that
consumes it, and leaving `exists_denseIndependentDivFreeFamily` unproved when
its only obstruction was import order.

Hoisting the pairing into this module turns the three files into a chain

    LerayWeak → SchwartzL2Pairing → GalerkinRawFamily → GalerkinBasis

so `GalerkinBasis` can name the reservoir and discharge the residual in two
lines.  Same move as the `FourierMajorant`/`FourierWeightedPlancherel`
reversal (`bdf5795`).

**Namespace.**  Declarations stay in `Navier.Analysis.GalerkinBasis`, exactly
as before the move, so every fully-qualified name is unchanged and no
downstream file sees a rename.  `GalerkinRawFamily` already follows this
file-name/namespace split.

Nothing here is new mathematics: every declaration below is byte-identical to
its former home in `GalerkinBasis.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter

namespace Navier.Analysis.GalerkinBasis

open Navier
open Navier.Analysis.Enstrophy
open Navier.Analysis.LerayWeak
open Navier.Analysis.OfficialABEncoding

/-!
## The `L²` pairing of Schwartz velocity fields
-/

/-- The `L²` inner product of two Schwartz velocity fields in the official
Euclidean coordinates: `⟨f, g⟩_{L²} = ∫ ⟨f x, g x⟩ dx`. -/
def schwartzL2Inner (f g : SchwartzVelocity) : ℝ :=
  ∫ x : Space, officialInner (f x) (g x)

/-- Symmetry of the official pointwise inner product. -/
theorem officialInner_comm (x y : Space) : officialInner x y = officialInner y x := by
  simp only [officialInner_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Symmetry of the `L²` pairing. -/
theorem schwartzL2Inner_comm (f g : SchwartzVelocity) :
    schwartzL2Inner f g = schwartzL2Inner g f := by
  unfold schwartzL2Inner
  congr 1; funext x; exact officialInner_comm _ _

/-- The `L²` pairing is positive-semidefinite (a seminorm squared). -/
theorem schwartzL2Inner_self_nonneg (f : SchwartzVelocity) :
    0 ≤ schwartzL2Inner f f :=
  integral_nonneg fun x => by
    rw [officialInner_self]; positivity

/-- **The pairing density of two Schwartz fields is integrable** (Leray weak
theory, Temam III §3).  Pointwise Cauchy–Schwarz `|⟨f x, g x⟩| ≤ ‖f x‖₂·‖g x‖₂`
(`abs_officialInner_le`), the coordinate-norm comparison `‖·‖₂ ≤ √3·‖·‖∞`
(`officialEuclideanNorm_le`), the uniform bound on the Schwartz field `g`, and
`SchwartzMap.integrable` (integrability of `‖f ·‖`) dominate the density by
`(3·Cg)·‖f x‖`.  This upgrades `schwartzL2Inner` from a raw Bochner integral to
a bilinear form (`∫ (a+b)·c = ∫ a·c + ∫ b·c` needs integrability of each part),
unlocking projection self-adjointness and the skew transfer `⟨P_m B u, u⟩ = 0`
on the span. -/
theorem schwartzPairing_integrable (f g : SchwartzVelocity) :
    Integrable (fun x : Space => officialInner (f x) (g x)) := by
  -- Uniform bound `Cg` on `‖g x‖` (Schwartz `k=0,n=0` decay).
  obtain ⟨Cg, hCg0, hCgraw⟩ :=
    (schwartzmap_satisfies_fefferman_euclidean_weight_rapid_decay g) 0 0
  have hCg : ∀ x : Space, ‖g x‖ ≤ Cg := by
    intro x
    have h := hCgraw x
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
    exact h
  -- `x ↦ ‖f x‖` is integrable (`SchwartzMap.integrable`).
  have hfint : Integrable (fun x : Space => ‖f x‖) volume := (SchwartzMap.integrable f).norm
  -- Dominate the pairing density by `(3·Cg)·‖f x‖`.
  refine Integrable.mono' (hfint.const_mul (3 * Cg)) ?_ ?_
  · -- Continuity ⇒ a.e.-strong-measurability (coordinate sum of products).
    apply Continuous.aestronglyMeasurable
    simp only [officialInner_eq_sum]
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp f.continuous).mul ((continuous_apply i).comp g.continuous))
  · -- Pointwise Cauchy–Schwarz + `‖·‖₂ ≤ √3‖·‖∞` + the uniform bound on `g`.
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]
    calc |officialInner (f x) (g x)|
        ≤ officialEuclideanNorm (f x) * officialEuclideanNorm (g x) := abs_officialInner_le _ _
      _ ≤ (Real.sqrt 3 * ‖f x‖) * (Real.sqrt 3 * ‖g x‖) := by
          refine mul_le_mul (officialEuclideanNorm_le _) (officialEuclideanNorm_le _)
            (officialEuclideanNorm_nonneg _) ?_
          positivity
      _ = 3 * (‖f x‖ * ‖g x‖) := by
          rw [show Real.sqrt 3 * ‖f x‖ * (Real.sqrt 3 * ‖g x‖)
                = (Real.sqrt 3 * Real.sqrt 3) * (‖f x‖ * ‖g x‖) by ring,
             Real.mul_self_sqrt (by norm_num)]
      _ ≤ 3 * (‖f x‖ * Cg) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (hCg x) (norm_nonneg _)
      _ = (3 * Cg) * ‖f x‖ := by ring

/-!
## Bilinearity of the `L²` pairing

With `schwartzPairing_integrable` in hand, `schwartzL2Inner` is a genuine
bilinear form: `∫ (a + b)·c = ∫ a·c + ∫ b·c` uses integrability of each part.
This is the algebra behind projection self-adjointness (Temam III §3).
-/

/-- Additivity of the official pointwise inner product in its left argument. -/
theorem officialInner_add_left (x y z : Space) :
    officialInner (x + y) z = officialInner x z + officialInner y z := by
  rw [officialInner_comm, officialInner_add_right, officialInner_comm z x, officialInner_comm z y]

/-- `ℝ`-homogeneity of the official pointwise inner product in its left argument. -/
theorem officialInner_smul_left (c : ℝ) (x y : Space) :
    officialInner (c • x) y = c * officialInner x y := by
  rw [officialInner_comm, officialInner_smul_right, officialInner_comm y x]

/-- The `L²` pairing of the zero field with anything vanishes. -/
theorem schwartzL2Inner_zero_left (g : SchwartzVelocity) : schwartzL2Inner 0 g = 0 := by
  unfold schwartzL2Inner
  have hz : (fun x : Space => officialInner ((0 : SchwartzVelocity) x) (g x)) = fun _ => 0 := by
    funext x; simp [officialInner_zero_left]
  rw [hz, integral_zero]

/-- **Left-additivity of the `L²` pairing** (needs `schwartzPairing_integrable`). -/
theorem schwartzL2Inner_add_left (f g h : SchwartzVelocity) :
    schwartzL2Inner (f + g) h = schwartzL2Inner f h + schwartzL2Inner g h := by
  unfold schwartzL2Inner
  rw [← integral_add (schwartzPairing_integrable f h) (schwartzPairing_integrable g h)]
  congr 1; funext x
  rw [SchwartzMap.add_apply, officialInner_add_left]

/-- **Right-additivity of the `L²` pairing.** -/
theorem schwartzL2Inner_add_right (f g h : SchwartzVelocity) :
    schwartzL2Inner f (g + h) = schwartzL2Inner f g + schwartzL2Inner f h := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_add_left, schwartzL2Inner_comm g f,
    schwartzL2Inner_comm h f]

/-- **Left-homogeneity of the `L²` pairing.** -/
theorem schwartzL2Inner_smul_left (c : ℝ) (f g : SchwartzVelocity) :
    schwartzL2Inner (c • f) g = c * schwartzL2Inner f g := by
  unfold schwartzL2Inner
  rw [← integral_const_mul]
  congr 1; funext x
  rw [SchwartzMap.smul_apply, officialInner_smul_left]

/-- **Right-homogeneity of the `L²` pairing.** -/
theorem schwartzL2Inner_smul_right (c : ℝ) (f g : SchwartzVelocity) :
    schwartzL2Inner f (c • g) = c * schwartzL2Inner f g := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_smul_left, schwartzL2Inner_comm g f]

/-- **Finite-sum left-linearity**: pulls a finite linear combination out of the
left slot (the algebra the projection's self-adjointness rides on). -/
theorem schwartzL2Inner_sum_left (s : Finset ℕ) (F : ℕ → SchwartzVelocity)
    (g : SchwartzVelocity) :
    schwartzL2Inner (∑ j ∈ s, F j) g = ∑ j ∈ s, schwartzL2Inner (F j) g := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, schwartzL2Inner_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, schwartzL2Inner_add_left, ih, Finset.sum_insert ha]

/-- **Finite-sum right-linearity.** -/
theorem schwartzL2Inner_sum_right (s : Finset ℕ) (f : SchwartzVelocity)
    (F : ℕ → SchwartzVelocity) :
    schwartzL2Inner f (∑ j ∈ s, F j) = ∑ j ∈ s, schwartzL2Inner f (F j) := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_sum_left]
  exact Finset.sum_congr rfl (fun j _ => schwartzL2Inner_comm _ _)

/-- **Left-negation of the `L²` pairing.** -/
theorem schwartzL2Inner_neg_left (f g : SchwartzVelocity) :
    schwartzL2Inner (-f) g = - schwartzL2Inner f g := by
  have h : (-f : SchwartzVelocity) = (-1 : ℝ) • f := by rw [neg_one_smul]
  rw [h, schwartzL2Inner_smul_left]; ring

/-- **Left-subtractivity of the `L²` pairing.** -/
theorem schwartzL2Inner_sub_left (f g h : SchwartzVelocity) :
    schwartzL2Inner (f - g) h = schwartzL2Inner f h - schwartzL2Inner g h := by
  rw [sub_eq_add_neg, schwartzL2Inner_add_left, schwartzL2Inner_neg_left, ← sub_eq_add_neg]

/-- **Pythagoras for the `L²` seminorm**: orthogonal parts add in the squared
seminorm, `Q(a+b) = Q a + Q b` when `⟨a,b⟩ = 0`. -/
theorem schwartzL2Inner_self_add_of_orthogonal (a b : SchwartzVelocity)
    (h : schwartzL2Inner a b = 0) :
    schwartzL2Inner (a + b) (a + b) = schwartzL2Inner a a + schwartzL2Inner b b := by
  rw [schwartzL2Inner_add_left, schwartzL2Inner_add_right, schwartzL2Inner_add_right,
      schwartzL2Inner_comm b a, h]; ring

end Navier.Analysis.GalerkinBasis
