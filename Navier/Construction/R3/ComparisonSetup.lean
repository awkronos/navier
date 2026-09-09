/-
Adapted from OpenAI/NavierStokesAndEuler, revision
8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538, under Apache-2.0.
Upstream source: NavierStokes/R3/ComparisonSetup.lean
Changes: native module namespace; further compatibility edits are in Git history.
License: references/licenses/OpenAI-Apache-2.0.txt.
-/
import Navier.Construction.R3.ProblemStatement
import Navier.Construction.PeriodicUniqueness
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Common definitions for whole-space comparison

These are the ordinary volume energies and differential expressions. No
comparison estimate or pressure representation is assumed in this module.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff BigOperators ENNReal InnerProductSpace

namespace Navier.ConstructionR3.Comparison

open ProblemStatement

abbrev slab (a b : ℝ) : Set SpaceTime := Icc a b ×ˢ univ

abbrev partialD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (f : Space → E) (x : Space) : E :=
  Navier.Construction.PeriodicIntegration.spatialPartial i f x

def comparisonLpNorm {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) (f : Space → E) : ℝ :=
  (eLpNorm f p (volume : Measure Space)).toReal

def l2Sq {E : Type*} [NormedAddCommGroup E] (f : Space → E) : ℝ :=
  ∫ x : Space, ‖f x‖ ^ 2

def gradientSq (f : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, ‖partialD i f x‖ ^ 2

def weightedEnergy (χ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * ‖w (t, x)‖ ^ 2

def weightedEnergyRate (χ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * (2 * ⟪w (t, x),
    Navier.Construction.ProblemStatement.temporalDerivative w t x⟫_ℝ)

def weightedDissipation (χ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * gradientSq (fun y => w (t, y)) x

def dissipationRoot (φ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  Real.sqrt (weightedDissipation (fun x => φ x ^ 8) w t)

def cutoffL6 (φ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  comparisonLpNorm 6 (fun x => (φ x ^ 4) • w (t, x))

def tensorDiff (u v : VelocityField) (t : ℝ) (i j : Fin 3) (x : Space) : ℝ :=
  u (t, x) i * u (t, x) j - v (t, x) i * v (t, x) j

end Navier.ConstructionR3.Comparison
