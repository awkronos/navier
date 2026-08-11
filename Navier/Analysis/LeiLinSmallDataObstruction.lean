import Navier.Analysis.CriticalMildWeightedBanach

/-!
# The Lei--Lin small-data route cannot cover arbitrary data

The fixed-point theorem in `LeiLinFixedPoint` is a genuine small-data result:
its hypothesis is `‖y‖ < ν/2` after the available linear estimate.  This file
records a concrete kernel-checked obstruction to using that hypothesis as an
all-data continuation argument.  For every positive viscosity there is an
explicit weighted lattice datum outside that ball.

This is not a counterexample to Navier--Stokes regularity.  It prevents a
specific invalid reduction: the small-data Lei--Lin theorem alone cannot
discharge the terminal bound for arbitrary initial data.

The carrier is the repository's discrete periodic Fourier carrier
`ℓ¹(ℤ³; ℂ³)`, not the `R³` Schwartz-data carrier in the Millennium crown.
Consequently even a future all-data theorem here would still require a
separate, mathematically substantive representation bridge before it could
feed `ProblemStatements.WholeSpaceGlobalRegularity`.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.LeiLinSmallDataObstruction

open scoped ENNReal
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildWeightedBanach

/-- A nonzero unit coordinate in the completed complex three-space. -/
private def modeUnit : ComplexE3 :=
  WithLp.toLp 2 (Pi.single (0 : Fin 3) (1 : ℂ))

private theorem modeUnit_ne_zero : modeUnit ≠ 0 := by
  intro h
  have h' : (Pi.single (0 : Fin 3) (1 : ℂ) : Fin 3 → ℂ) = 0 :=
    (WithLp.toLp_eq_zero (p := 2)).mp h
  have hcoord := congrFun h' 0
  simpa using hcoord

/-- A single nonzero lattice mode in the actual completed coefficient carrier. -/
private def seed : WeightedLatticeBanach :=
  lp.single 1 (0 : LatticeMode) modeUnit

private theorem seed_ne_zero : seed ≠ 0 := by
  intro h
  change (lp.single 1 (0 : LatticeMode) modeUnit : WeightedLatticeBanach) = 0 at h
  have hvalue := congrArg (fun z : WeightedLatticeBanach => z (0 : LatticeMode)) h
  rw [lp.single_apply] at hvalue
  simpa [seed, modeUnit] using hvalue

private theorem seed_norm_pos : 0 < ‖seed‖ := norm_pos_iff.mpr seed_ne_zero

/-- For every `ν > 0`, the available Lei--Lin smallness threshold excludes
some concrete datum of the formal lattice carrier.  Thus this small-data
theorem cannot, by itself, prove an arbitrary-data terminal estimate. -/
theorem exists_data_not_leiLin_small (ν : ℝ) (hν : 0 < ν) :
    ∃ a : WeightedLatticeBanach, ¬ (‖a‖ < ν / 2) := by
  let c : ℝ := ν / (2 * ‖seed‖) + 1
  refine ⟨c • seed, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (by dsimp [c]; positivity)]
  intro hsmall
  have hseed : 0 < ‖seed‖ := seed_norm_pos
  have hc : ν / (2 * ‖seed‖) < c := by
    dsimp [c]
    linarith
  have hmul : (ν / (2 * ‖seed‖)) * ‖seed‖ < c * ‖seed‖ :=
    mul_lt_mul_of_pos_right hc hseed
  have hleft : (ν / (2 * ‖seed‖)) * ‖seed‖ = ν / 2 := by
    field_simp
  rw [hleft] at hmul
  linarith

end Navier.Analysis.LeiLinSmallDataObstruction

#print axioms Navier.Analysis.LeiLinSmallDataObstruction.exists_data_not_leiLin_small
