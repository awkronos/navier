import Navier.Breakdown.OfficialCDEncoding

/-!
# Coordinate expansion for force derivatives

Fefferman's force clauses are written using the time direction and the three
spatial coordinate directions.  `OfficialCDEncoding` defines the corresponding
evaluations of the total within-Fréchet derivative.  This file supplies the
finite-dimensional algebraic converse: those four directions span every
spacetime slot, hence their iterated evaluations determine the total bundle.

This is only a coordinate-expansion fact.  It neither assumes a terminal norm
bound nor changes the norm used by an existing force predicate.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Analysis.ForceCoordinateBridge

open Navier
open Navier.Breakdown.OfficialCDEncoding

/-- The coefficient of a spacetime vector in one of Fefferman's four
coordinate directions. -/
def spacetimeCoordinateCoefficient (z : ℝ × Space) : Option (Fin 3) → ℝ
  | none => z.1
  | some i => z.2 i

/-- Every time or spatial coordinate coefficient is bounded by the inherited
product norm on spacetime. -/
theorem abs_spacetimeCoordinateCoefficient_le_norm
    (z : ℝ × Space) (a : Option (Fin 3)) :
    |spacetimeCoordinateCoefficient z a| ≤ ‖z‖ := by
  cases a with
  | none =>
      rw [spacetimeCoordinateCoefficient, Prod.norm_def, Real.norm_eq_abs]
      exact le_max_left _ _
  | some i =>
      calc
        |spacetimeCoordinateCoefficient z (some i)| = ‖z.2 i‖ := by
          simp [spacetimeCoordinateCoefficient, Real.norm_eq_abs]
        _ ≤ ‖z.2‖ := norm_le_pi_norm _ _
        _ ≤ ‖z‖ := by
          rw [Prod.norm_def]
          exact le_max_right _ _

/-- A spacetime vector is the sum of its time and spatial coordinate parts. -/
theorem spacetime_eq_sum_coordinateDirections (z : ℝ × Space) :
    z = ∑ a : Option (Fin 3),
      spacetimeCoordinateCoefficient z a • spacetimeCoordinateDirection a := by
  rcases z with ⟨s, x⟩
  have hx : x = ∑ i : Fin 3, x i • basisVector i := by
    simpa only [basisVector] using (pi_eq_sum_univ' x)
  rw [Fintype.sum_option]
  ext
  · simp [spacetimeCoordinateCoefficient, spacetimeCoordinateDirection,
      Prod.fst_sum, Prod.smul_mk]
  · simpa [spacetimeCoordinateCoefficient, spacetimeCoordinateDirection,
      Prod.snd_sum, Prod.smul_mk] using congrFun hx _

/-- A continuous multilinear map on spacetime slots is reconstructed from its
values on the time/spatial coordinate directions. -/
theorem continuousMultilinearMap_apply_eq_sum_coordinateDirections
    (n : ℕ)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Space) Space)
    (v : Fin n → ℝ × Space) :
    L v = ∑ axes : Fin n → Option (Fin 3),
      (∏ j, spacetimeCoordinateCoefficient (v j) (axes j)) •
        L (fun j => spacetimeCoordinateDirection (axes j)) := by
  calc
    L v = L (fun j => ∑ a : Option (Fin 3),
        spacetimeCoordinateCoefficient (v j) a • spacetimeCoordinateDirection a) := by
          congr 1
          funext j
          rw [← spacetime_eq_sum_coordinateDirections]
    _ = ∑ axes : Fin n → Option (Fin 3),
        L (fun j => spacetimeCoordinateCoefficient (v j) (axes j) •
          spacetimeCoordinateDirection (axes j)) := by
          exact L.map_sum (fun j a =>
            spacetimeCoordinateCoefficient (v j) a • spacetimeCoordinateDirection a)
    _ = ∑ axes : Fin n → Option (Fin 3),
        (∏ j, spacetimeCoordinateCoefficient (v j) (axes j)) •
          L (fun j => spacetimeCoordinateDirection (axes j)) := by
          apply Finset.sum_congr rfl
          intro axes _
          rw [L.map_smul_univ]

/-- A uniform scalar bound on the four-coordinate evaluations controls the
operator norm of the whole multilinear bundle.  The explicit finite factor is
the number of mixed coordinate lists, not an auxiliary norm convention. -/
theorem continuousMultilinearMap_opNorm_le_coordinateBound
    (n : ℕ)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Space) Space)
    (C : ℝ) (hC : 0 ≤ C)
    (hcoordinate : ∀ (axes : Fin n → Option (Fin 3)) (component : Fin 3),
      |(L (fun j => spacetimeCoordinateDirection (axes j))) component| ≤ C) :
    ‖L‖ ≤ (Fintype.card (Fin n → Option (Fin 3)) : ℝ) * C := by
  apply L.opNorm_le_bound
  · positivity
  intro v
  calc
    ‖L v‖ = ‖∑ axes : Fin n → Option (Fin 3),
        (∏ j, spacetimeCoordinateCoefficient (v j) (axes j)) •
          L (fun j => spacetimeCoordinateDirection (axes j))‖ := by
            rw [continuousMultilinearMap_apply_eq_sum_coordinateDirections]
    _ ≤ ∑ axes : Fin n → Option (Fin 3),
        ‖(∏ j, spacetimeCoordinateCoefficient (v j) (axes j)) •
          L (fun j => spacetimeCoordinateDirection (axes j))‖ := norm_sum_le _ _
    _ ≤ ∑ _axes : Fin n → Option (Fin 3), (∏ j, ‖v j‖) * C := by
      apply Finset.sum_le_sum
      intro axes _
      rw [norm_smul, Real.norm_eq_abs]
      have hcoeff : |∏ j, spacetimeCoordinateCoefficient (v j) (axes j)| ≤
          ∏ j, ‖v j‖ := by
        simp only [Finset.abs_prod]
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          (fun j _ =>
            abs_spacetimeCoordinateCoefficient_le_norm (v j) (axes j))
      have hvalue : ‖L (fun j => spacetimeCoordinateDirection (axes j))‖ ≤ C := by
        refine (pi_norm_le_iff_of_nonneg hC).mpr fun component => ?_
        simpa only [Real.norm_eq_abs] using hcoordinate axes component
      exact mul_le_mul hcoeff hvalue (norm_nonneg _) (by positivity)
    _ = (Fintype.card (Fin n → Option (Fin 3)) : ℝ) * C * ∏ j, ‖v j‖ := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- Finitely many coordinate/component decay constants can be replaced by one
nonnegative constant.  We use their finite sum rather than hiding a choice of
maximum, so the resulting witness is explicit and monotone. -/
theorem exists_uniform_coordinateForceDerivativeWithin_bound
    (f : ForceField) (n : ℕ) (weight : ℝ → Space → ℝ)
    (hcoordinate : ∀ (axes : Fin n → Option (Fin 3)) (component : Fin 3),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        weight t x * |coordinateForceDerivativeWithin f n axes component t x| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (axes : Fin n → Option (Fin 3)) (component : Fin 3)
      (t : ℝ), 0 ≤ t → ∀ x : Space,
        weight t x * |coordinateForceDerivativeWithin f n axes component t x| ≤ C := by
  let c : (Fin n → Option (Fin 3)) → Fin 3 → ℝ := fun axes component =>
    Classical.choose (hcoordinate axes component)
  have hc : ∀ axes component, 0 ≤ c axes component := fun axes component =>
    (Classical.choose_spec (hcoordinate axes component)).1
  refine ⟨∑ axes : Fin n → Option (Fin 3), ∑ component : Fin 3,
    c axes component, Finset.sum_nonneg fun axes _ =>
      Finset.sum_nonneg fun component _ => hc axes component, ?_⟩
  intro axes component t ht x
  calc
    weight t x * |coordinateForceDerivativeWithin f n axes component t x| ≤
        c axes component := (Classical.choose_spec (hcoordinate axes component)).2 t ht x
    _ ≤ ∑ component : Fin 3, c axes component :=
      Finset.single_le_sum (fun component _ => hc axes component) (Finset.mem_univ _)
    _ ≤ ∑ axes : Fin n → Option (Fin 3), ∑ component : Fin 3,
        c axes component :=
      Finset.single_le_sum (fun axes _ =>
        Finset.sum_nonneg fun component _ => hc axes component) (Finset.mem_univ _)

/-- The aggregated coordinate bound controls the complete force derivative
bundle at each spacetime point. -/
theorem iteratedFDerivWithin_opNorm_le_uniformCoordinateBound
    (f : ForceField) (n : ℕ) (t : ℝ) (x : Space) (C : ℝ) (hC : 0 ≤ C)
    (hcoordinate : ∀ (axes : Fin n → Option (Fin 3)) (component : Fin 3),
      |coordinateForceDerivativeWithin f n axes component t x| ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x)‖ ≤
      (Fintype.card (Fin n → Option (Fin 3)) : ℝ) * C := by
  apply continuousMultilinearMap_opNorm_le_coordinateBound n _ C hC
  intro axes component
  exact hcoordinate axes component

/-- Multiplying all coordinate evaluations by one nonnegative weight commutes
with the finite coordinate reconstruction at the level of an operator-norm
bound. -/
theorem weighted_continuousMultilinearMap_opNorm_le_coordinateBound
    (n : ℕ)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Space) Space)
    (w C : ℝ) (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hcoordinate : ∀ (axes : Fin n → Option (Fin 3)) (component : Fin 3),
      w * |(L (fun j => spacetimeCoordinateDirection (axes j))) component| ≤ C) :
    w * ‖L‖ ≤ (Fintype.card (Fin n → Option (Fin 3)) : ℝ) * C := by
  by_cases hwzero : w = 0
  · simp [hwzero, hC]
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hwzero)
  have hraw : ∀ (axes : Fin n → Option (Fin 3)) (component : Fin 3),
      |(L (fun j => spacetimeCoordinateDirection (axes j))) component| ≤ C / w := by
    intro axes component
    rw [le_div_iff₀ hwpos]
    simpa [mul_comm] using hcoordinate axes component
  have hbound := continuousMultilinearMap_opNorm_le_coordinateBound n L (C / w)
    (div_nonneg hC hw) hraw
  calc
    w * ‖L‖ ≤ w * ((Fintype.card (Fin n → Option (Fin 3)) : ℝ) * (C / w)) :=
      mul_le_mul_of_nonneg_left hbound hw
    _ = (Fintype.card (Fin n → Option (Fin 3)) : ℝ) * C := by
      field_simp

/-- Coordinatewise weighted decay witnesses yield one uniform weighted bound
for the entire iterated within-Fréchet derivative bundle. -/
theorem exists_weighted_iteratedFDerivWithin_opNorm_bound
    (f : ForceField) (n : ℕ) (weight : ℝ → Space → ℝ)
    (hweight : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, 0 ≤ weight t x)
    (hcoordinate : ∀ (axes : Fin n → Option (Fin 3)) (component : Fin 3),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        weight t x * |coordinateForceDerivativeWithin f n axes component t x| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      weight t x * ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
        nonnegativeSpacetime (t, x)‖ ≤
        (Fintype.card (Fin n → Option (Fin 3)) : ℝ) * C := by
  obtain ⟨C, hC, huniform⟩ :=
    exists_uniform_coordinateForceDerivativeWithin_bound f n weight hcoordinate
  refine ⟨C, hC, ?_⟩
  intro t ht x
  apply weighted_continuousMultilinearMap_opNorm_le_coordinateBound n _
    (weight t x) C (hweight t ht x) hC
  intro axes component
  exact huniform axes component t ht x

/-- The value of an iterated within-Fréchet derivative on an arbitrary
spacetime list is an explicit finite combination of Fefferman's mixed
time/spatial coordinate evaluations. -/
theorem iteratedFDerivWithin_apply_eq_sum_coordinateDirections
    (f : ForceField) (n : ℕ) (t : ℝ) (x : Space) (v : Fin n → ℝ × Space) :
    (iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x)) v =
      ∑ axes : Fin n → Option (Fin 3),
        (∏ j, spacetimeCoordinateCoefficient (v j) (axes j)) •
          coordinateDirectionalForceDerivativeWithin f n axes t x := by
  exact continuousMultilinearMap_apply_eq_sum_coordinateDirections n
    (iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x)) v

/-- **Consumer smoke theorem for the force Fréchet/coordinate residual.**
At a fixed nonnegative-spacetime point, all scalar mixed coordinate
evaluations being zero forces the complete iterated within-Fréchet derivative
bundle to be zero.  Thus the coordinate family is genuinely determining; the
remaining residual concerns quantitative decay constants and the comparison
with Fefferman's textual partial-derivative convention. -/
theorem iteratedFDerivWithin_eq_zero_of_coordinateForceDerivativeWithin_eq_zero
    (f : ForceField) (n : ℕ) (t : ℝ) (x : Space)
    (hzero : ∀ (axes : Fin n → Option (Fin 3)) (component : Fin 3),
      coordinateForceDerivativeWithin f n axes component t x = 0) :
    iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x) = 0 := by
  ext v
  rw [iteratedFDerivWithin_apply_eq_sum_coordinateDirections]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro axes _
  rw [show coordinateDirectionalForceDerivativeWithin f n axes t x _ = 0 by
    exact hzero axes _]
  simp

end Navier.Analysis.ForceCoordinateBridge
