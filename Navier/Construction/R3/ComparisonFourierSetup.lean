/-
Adapted from OpenAI/NavierStokesAndEuler, revision
8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538, under Apache-2.0.
Upstream source: NavierStokes/R3/ComparisonFourierSetup.lean
Changes: native module namespace; further compatibility edits are in Git history.
License: references/licenses/OpenAI-Apache-2.0.txt.
-/
import Navier.Construction.R3.ComparisonSetup
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # Fourier test expressions used in pressure recovery -/


noncomputable section

open MeasureTheory

namespace Navier.ConstructionR3.Comparison

open ProblemStatement

abbrev ComplexTest := SchwartzMap Space ℂ

def rieszSymbol (i j : Fin 3) (ξ : Space) : ℝ :=
  -(ξ i * ξ j) / ‖ξ‖ ^ 2

def rieszTest (i j : Fin 3) (ψ : ComplexTest) : Space → ℂ :=
  FourierTransform.fourierInv (fun ξ : Space =>
    (rieszSymbol i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ)

def pressurePair (i j : Fin 3) (g : Space → ℝ) (ψ : ComplexTest) : ℂ :=
  ∫ x : Space, (g x : ℂ) * rieszTest i j ψ x

def fourierHNormSq (s : ℕ) (ψ : ComplexTest) : ℝ :=
  ∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ s * ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ ^ 2

end Navier.ConstructionR3.Comparison
