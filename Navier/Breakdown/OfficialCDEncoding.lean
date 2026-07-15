import Navier.OfficialProblem

/-!
# Coordinatewise force-decay bridge for the official C/D surfaces

The official whole-space force predicate currently uses the sup norm on
Fin 3 to real functions and the operator norm of a total within-Frechet
derivative. Fefferman's wording instead uses the Euclidean spatial norm and
scalar coordinate derivatives. This file proves the safe forward
representation transport: the two spatial norms are quantitatively equivalent,
and an operator-norm bound controls every mixed unit coordinate direction and
every output component.

For the periodic D surface there is intentionally no spatial weight. The
reverse representation theorem and the identification of within-directional
derivatives with every textual coordinatewise convention remain separate
encoding residuals.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Breakdown.OfficialCDEncoding

open Navier

/-- The Euclidean norm from Fefferman's spatial wording, on the same
underlying coordinates as Navier.Space. -/
def euclideanNorm (x : Space) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖

/-- The current sup norm on Space is bounded by the Euclidean norm. -/
theorem norm_le_euclideanNorm (x : Space) :
    ‖x‖ ≤ euclideanNorm x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpos : 0 < euclideanNorm x + ε :=
    add_pos_of_nonneg_of_pos (norm_nonneg _) hε
  exact ((pi_norm_lt_iff hpos).2 fun i =>
    lt_of_le_of_lt
      (PiLp.norm_apply_le
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) i)
      (lt_add_of_pos_right _ hε)).le

/-- In dimension three, the Euclidean norm is at most sqrt(3) times the current
sup norm on Space. -/
-- Citation: Mathlib EuclideanSpace.real_norm_sq_eq.
theorem euclideanNorm_le_sqrt_three_mul_norm (x : Space) :
    euclideanNorm x ≤ √3 * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [show ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 =
    ∑ i : Fin 3, (x i) ^ 2 by
      simpa using EuclideanSpace.real_norm_sq_eq
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  calc
    ∑ i : Fin 3, (x i) ^ 2 ≤ ∑ _i : Fin 3, ‖x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa [sq_abs] using
        pow_le_pow_left₀ (norm_nonneg (x i)) (norm_le_pi_norm x i) 2
    _ = 3 * ‖x‖ ^ 2 := by simp

private theorem euclidean_decayWeight_le
    (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    1 + euclideanNorm x + t ≤ √3 * (1 + ‖x‖ + t) := by
  have hsqrt_nonneg : 0 ≤ √(3 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : √(3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_one : 1 ≤ √(3 : ℝ) := by
    nlinarith
  have hnorm := euclideanNorm_le_sqrt_three_mul_norm x
  nlinarith [norm_nonneg x]

/-- None is the positive time direction; some i is the ith spatial
coordinate direction. -/
def spacetimeCoordinateDirection : Option (Fin 3) → ℝ × Space
  | none => (1, 0)
  | some i => (0, basisVector i)

@[simp] private theorem norm_spacetimeCoordinateDirection
    (a : Option (Fin 3)) : ‖spacetimeCoordinateDirection a‖ = 1 := by
  cases a with
  | none => simp [spacetimeCoordinateDirection]
  | some i =>
      simp only [spacetimeCoordinateDirection, Prod.norm_def, norm_zero]
      rw [show basisVector i = Pi.single i 1 by rfl, Pi.norm_single]
      norm_num

/-- Evaluation of the total nth within-Frechet derivative on a prescribed
mixed list of unit time/spatial coordinate directions. -/
def coordinateDirectionalForceDerivativeWithin
    (f : ForceField) (n : ℕ) (axes : Fin n → Option (Fin 3))
    (t : ℝ) (x : Space) : Space :=
  (iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
    nonnegativeSpacetime (t, x))
      (fun j => spacetimeCoordinateDirection (axes j))

private theorem norm_coordinateDirectionalForceDerivativeWithin_le
    (f : ForceField) (n : ℕ) (axes : Fin n → Option (Fin 3))
    (t : ℝ) (x : Space) :
    ‖coordinateDirectionalForceDerivativeWithin f n axes t x‖ ≤
      ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
        nonnegativeSpacetime (t, x)‖ := by
  have h :=
    (iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x)).le_opNorm
        (fun j => spacetimeCoordinateDirection (axes j))
  simpa only [coordinateDirectionalForceDerivativeWithin,
    norm_spacetimeCoordinateDirection, Finset.prod_const_one, mul_one] using h

/-- One output component of a mixed coordinate-direction derivative. -/
def coordinateForceDerivativeWithin
    (f : ForceField) (n : ℕ) (axes : Fin n → Option (Fin 3))
    (component : Fin 3) (t : ℝ) (x : Space) : ℝ :=
  coordinateDirectionalForceDerivativeWithin f n axes t x component

/-- Every mixed coordinate direction and output component is controlled by
the total Frechet derivative operator norm. -/
-- Citation: Mathlib ContinuousMultilinearMap.le_opNorm.
theorem abs_coordinateForceDerivativeWithin_le
    (f : ForceField) (n : ℕ) (axes : Fin n → Option (Fin 3))
    (component : Fin 3) (t : ℝ) (x : Space) :
    |coordinateForceDerivativeWithin f n axes component t x| ≤
      ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
        nonnegativeSpacetime (t, x)‖ := by
  calc
    |coordinateForceDerivativeWithin f n axes component t x| =
        ‖coordinateDirectionalForceDerivativeWithin f n axes t x component‖ := by
          simp only [coordinateForceDerivativeWithin, Real.norm_eq_abs]
    _ ≤ ‖coordinateDirectionalForceDerivativeWithin f n axes t x‖ :=
      norm_le_pi_norm _ component
    _ ≤ _ := norm_coordinateDirectionalForceDerivativeWithin_le
      f n axes t x

/-- Coordinatewise version of Fefferman's whole-space force decay clause,
using the Euclidean spatial norm and every mixed unit coordinate direction. -/
def WholeSpaceCoordinatewiseForceDecay (f : ForceField) : Prop :=
  ∀ (n K : ℕ) (axes : Fin n → Option (Fin 3)) (component : Fin 3),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        (1 + euclideanNorm x + t) ^ K *
          |coordinateForceDerivativeWithin f n axes component t x| ≤ C

/-- Coordinatewise version of Fefferman's periodic force decay clause.
There is no spatial weight, exactly as in the official periodic alternative. -/
def PeriodicCoordinatewiseForceDecay (f : ForceField) : Prop :=
  ∀ (n K : ℕ) (axes : Fin n → Option (Fin 3)) (component : Fin 3),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        (1 + t) ^ K *
          |coordinateForceDerivativeWithin f n axes component t x| ≤ C

/-- The force predicate consumed by statement C implies Euclidean-weighted
decay of every mixed coordinate-direction derivative and output component. -/
theorem forcedDataRapidDecay_implies_coordinatewise
    {f : ForceField} (hf : ForcedDataRapidDecay f) :
    WholeSpaceCoordinatewiseForceDecay f := by
  rcases hf with ⟨_, hdecay⟩
  intro n K axes component
  rcases hdecay n K with ⟨C, hC, hbound⟩
  let A : ℝ := √(3 : ℝ) ^ K
  have hA : 0 ≤ A := pow_nonneg (Real.sqrt_nonneg _) K
  refine ⟨A * C, mul_nonneg hA hC, ?_⟩
  intro t ht x
  have hdirection :=
    abs_coordinateForceDerivativeWithin_le f n axes component t x
  have hweight := euclidean_decayWeight_le t ht x
  have hbase : 0 ≤ 1 + euclideanNorm x + t := by
    dsimp only [euclideanNorm]
    positivity
  have hpow :
      (1 + euclideanNorm x + t) ^ K ≤
        (√3 * (1 + ‖x‖ + t)) ^ K :=
    pow_le_pow_left₀ hbase hweight K
  calc
    (1 + euclideanNorm x + t) ^ K *
          |coordinateForceDerivativeWithin f n axes component t x|
        ≤ (1 + euclideanNorm x + t) ^ K *
            ‖iteratedFDerivWithin ℝ n
              (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (t, x)‖ :=
          mul_le_mul_of_nonneg_left hdirection (pow_nonneg hbase K)
    _ ≤ (√3 * (1 + ‖x‖ + t)) ^ K *
            ‖iteratedFDerivWithin ℝ n
              (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (t, x)‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = A * ((1 + ‖x‖ + t) ^ K *
            ‖iteratedFDerivWithin ℝ n
              (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (t, x)‖) := by
          simp only [mul_pow, A]
          ring
    _ ≤ A * C := mul_le_mul_of_nonneg_left (hbound t ht x) hA

/-- The force predicate consumed by statement D implies decay of every mixed
coordinate-direction derivative and output component. -/
theorem periodicForcedDataRapidDecay_implies_coordinatewise
    {f : ForceField} (hf : PeriodicForcedDataRapidDecay f) :
    PeriodicCoordinatewiseForceDecay f := by
  rcases hf with ⟨_, _, hdecay⟩
  intro n K axes component
  rcases hdecay n K with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht x
  have hbase : 0 ≤ 1 + t := by linarith
  calc
    (1 + t) ^ K *
          |coordinateForceDerivativeWithin f n axes component t x|
        ≤ (1 + t) ^ K *
            ‖iteratedFDerivWithin ℝ n
              (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (t, x)‖ :=
          mul_le_mul_of_nonneg_left
            (abs_coordinateForceDerivativeWithin_le
              f n axes component t x)
            (pow_nonneg hbase K)
    _ ≤ C := hbound t ht x

end Navier.Breakdown.OfficialCDEncoding
