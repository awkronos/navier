import Navier.Analysis.CriticalMildGlobalTrajectoryReality
import Navier.Analysis.MadelungDecoderCurlObstruction

/-!
# The periodic mild realization cannot carry Schwartz whole-space data

The lattice small-data route ends at
`CriticalMildGlobalTrajectoryReality.smallDataGlobal_navierStokesBody_on_positiveTime_of_real`:
for a lattice datum `a` with `‖a‖ ≤ rawMildViscosity ν₀ / 16` the physical
field `physicalMildVelocity (smallDataGlobalDriver …)` satisfies the official
momentum equation at every positive time.  The header of
`MadelungDecoderCurlObstruction` names the missing transport primitive of that
route: an extension `WeightedLatticeBanach → whole-space carrier` preserving
the `ν₀ / 16` threshold, landing on `Navier.Problem`'s
`VelocityEvolution × PressureEvolution` carrier with a Schwartz datum.

This file kernel-falsifies the direct form of that transport — using the
periodic realization `physicalMildVelocity` itself as the whole-space
velocity — at the same initial-time surface as the Madelung obstruction.

* `schwartzVelocity_eq_zero_of_spatiallyPeriodic`: a period-one Schwartz
  field is zero.  Translating along `basisVector 0` by `n` leaves the value
  fixed while the Schwartz weight `‖x‖ * ‖u₀ x‖ ≤ C` forces it to `0`.
* `schwartzVelocity_eq_zero_of_physicalMildVelocity_slice`: every slice of
  `physicalMildVelocity A` is period one
  (`spatiallyPeriodicVelocity_physicalMildVelocity`), so it agrees with a
  Schwartz field only when that field is zero — for every raw path `A`,
  small or not, and every nonnegative time.
* `not_isClassicalSolution_physicalMildVelocity_of_ne_zero`: on the crown
  carrier, no `IsClassicalSolution ν f u₀ (physicalMildVelocity A) p` exists
  for a nonzero Schwartz datum `u₀`, for any viscosity, force, path, or
  pressure.  The `initial_condition` field alone is contradicted; no PDE
  dynamics, energy, or smoothness clause is needed.
* `PeriodicSmallDataLift` states the exact transport proposition the
  lattice route would need in the small class: for the datum `u₀`, some
  lattice datum `a` below the `rawMildViscosity ν₀ / 16` threshold, mean
  free, divergence free and anti-Hermitian (the hypotheses of the reality
  theorem), whose global driver's physical realization attains `u₀` at time
  zero.  `not_periodicSmallDataLift_of_rotational_data` refutes it for the
  divergence-free datum `rotationalDatum lam` at every `lam ≠ 0`, which is
  componentwise bounded by `|lam|` (`rotationalDatum_le`) and hence present
  at every small-data scale.

Scope and honesty notes:
* Only the periodic realization is refuted.  The lattice fixed point, its
  positive-time momentum identity, and the `ν₀ / 16` small-data theorem are
  untouched and remain correct on the periodic carrier.
* The repaired statement is a change of carrier, not of threshold: the
  transport must land on a non-periodic whole-space object.  The named
  replacement primitive is the physical reconstruction of the continuous
  Fourier carrier of `ContinuousLeiLinSpace` (`ES → ℂ` on `ℝ³`) to a
  `VelocityEvolution`, with Schwartz initial agreement through whole-space
  Fourier inversion and finite energy through Plancherel.  Its fixed point
  and budgets are separate open construction work.
* The `lam = 0` datum is zero and is carried by `isClassicalSolution_zero`.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PeriodicRealizationSchwartzObstruction

open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.CriticalMildSmallDataGlobal
open Navier.Analysis.MadelungDecoderCurlObstruction

/-- **A period-one Schwartz field vanishes.**  Fix `y`; translating along
`basisVector 0` by every `n : ℕ` leaves `u₀ y` fixed, while the first Schwartz
weight gives `‖y + n e₀‖ * ‖u₀ y‖ ≤ C` with `‖y + n e₀‖ ≥ n - |y 0|`. -/
theorem schwartzVelocity_eq_zero_of_spatiallyPeriodic (u₀ : SchwartzVelocity)
    (h : SpatiallyPeriodic (⇑u₀)) : u₀ = 0 := by
  ext y i
  suffices hnorm : ‖(⇑u₀) y‖ = 0 by
    have hy : (⇑u₀) y = 0 := norm_eq_zero.mp hnorm
    simp [hy]
  obtain ⟨C, _hC, hdec⟩ := u₀.decay 1 0
  have hshift : ∀ n : ℕ, (⇑u₀) (y + (n : ℝ) • basisVector 0) = (⇑u₀) y := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        have hs : y + ((k + 1 : ℕ) : ℝ) • basisVector 0 =
            (y + (k : ℝ) • basisVector 0) + basisVector 0 := by
          push_cast
          rw [add_smul, one_smul, add_assoc]
        rw [hs, h, ih]
  have hbound : ∀ n : ℕ, ((n : ℝ) - |y 0|) * ‖(⇑u₀) y‖ ≤ C := by
    intro n
    have h1 := hdec (y + (n : ℝ) • basisVector 0)
    rw [norm_iteratedFDeriv_zero, pow_one, hshift n] at h1
    have hcoord : (y + (n : ℝ) • basisVector 0) 0 = y 0 + n := by
      simp [basisVector]
    have h2 : (n : ℝ) - |y 0| ≤ ‖y + (n : ℝ) • basisVector 0‖ := by
      calc (n : ℝ) - |y 0| ≤ y 0 + n := by linarith [neg_abs_le (y 0)]
        _ ≤ |y 0 + n| := le_abs_self _
        _ = ‖(y + (n : ℝ) • basisVector 0) 0‖ := by rw [hcoord, Real.norm_eq_abs]
        _ ≤ ‖y + (n : ℝ) • basisVector 0‖ := norm_le_pi_norm _ 0
    nlinarith [norm_nonneg ((⇑u₀) y)]
  by_contra hne
  have hpos : 0 < ‖(⇑u₀) y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖(⇑u₀) y‖ + |y 0|)
  have hlt : C / ‖(⇑u₀) y‖ < (n : ℝ) - |y 0| := by linarith
  rw [div_lt_iff₀ hpos] at hlt
  linarith [hbound n]

/-- **Initial-surface obstruction for the periodic realization.**  For every
raw lattice path `A` and every nonnegative time, the slice
`physicalMildVelocity A t` agrees with a Schwartz field only when that field
is zero. -/
theorem schwartzVelocity_eq_zero_of_physicalMildVelocity_slice
    (A : ℝ → WeightedLatticeBanach) {t : ℝ} (ht : 0 ≤ t) (u₀ : SchwartzVelocity)
    (h : ∀ x : Space, physicalMildVelocity A t x = u₀ x) : u₀ = 0 := by
  apply schwartzVelocity_eq_zero_of_spatiallyPeriodic
  intro x i
  rw [← h, ← h]
  exact spatiallyPeriodicVelocity_physicalMildVelocity A t ht x i

/-- **Crown-carrier form.**  No classical solution from a nonzero Schwartz
datum has the periodic realization as its velocity — for any viscosity, any
force, any raw path, and any pressure.  Only the `initial_condition` field is
used. -/
theorem not_isClassicalSolution_physicalMildVelocity_of_ne_zero
    (ν : ℝ) (f : ForceField) (u₀ : SchwartzVelocity) (hu₀ : u₀ ≠ 0)
    (A : ℝ → WeightedLatticeBanach) (p : PressureEvolution) :
    ¬ IsClassicalSolution ν f u₀ (physicalMildVelocity A) p :=
  fun hsol => hu₀ (schwartzVelocity_eq_zero_of_physicalMildVelocity_slice A le_rfl u₀
    hsol.initial_condition)

/-- The exact transport proposition the lattice small-data route would need
for a whole-space datum `u₀`: a lattice datum below the
`rawMildViscosity ν₀ / 16` threshold satisfying every hypothesis of
`smallDataGlobal_navierStokesBody_on_positiveTime_of_real`, whose global
driver's physical realization attains `u₀` at time zero. -/
def PeriodicSmallDataLift (ν₀ : ℝ) (hν₀ : 0 < ν₀) (u₀ : SchwartzVelocity) : Prop :=
  ∃ (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ rawMildViscosity ν₀ / 16),
    LatticeDivergenceFree a ∧ LatticeAntiHermitian a ∧
      ∀ x : Space, physicalMildVelocity (smallDataGlobalDriver (rawMildViscosity ν₀)
        (by unfold rawMildViscosity; positivity) a ha ha16) 0 x = u₀ x

/-- **Kernel falsification of the periodic small-data lift** at the
divergence-free rotational datum, for every `lam ≠ 0` and every viscosity.
`rotationalDatum_le` bounds the datum componentwise by `|lam|`, so the witness
lives at every small-data scale. -/
theorem not_periodicSmallDataLift_of_rotational_data
    (ν₀ : ℝ) (hν₀ : 0 < ν₀) (lam : ℝ) (hlam : lam ≠ 0) :
    ¬ PeriodicSmallDataLift ν₀ hν₀ (rotationalDatum lam) := by
  rintro ⟨a, ha, ha16, _hdf, _hreal, hinit⟩
  exact rotationalDatum_ne_zero lam hlam
    (schwartzVelocity_eq_zero_of_physicalMildVelocity_slice _ le_rfl _ hinit)

/-- **Vacuity guard.**  The hypothesis bundle of `PeriodicSmallDataLift` is
satisfiable: the zero lattice datum is mean free, below the threshold,
divergence free and anti-Hermitian.  The refutation above therefore rests on
the initial-agreement clause alone, not on an unsatisfiable antecedent. -/
theorem periodicSmallDataLift_hypotheses_inhabited (ν₀ : ℝ) (hν₀ : 0 < ν₀) :
    ∃ (a : WeightedLatticeBanach), a 0 = 0 ∧ ‖a‖ ≤ rawMildViscosity ν₀ / 16 ∧
      LatticeDivergenceFree a ∧ LatticeAntiHermitian a := by
  refine ⟨0, by simp, ?_, ?_, ?_⟩
  · have : 0 < rawMildViscosity ν₀ := by unfold rawMildViscosity; positivity
    simp only [norm_zero]
    positivity
  · intro m
    simp [weightedLatticeCoefficient, Navier.Analysis.ComplexLerayNorm.complexEuclideanPoint]
  · intro m
    simp only [weightedLatticeCoefficient, lp.coeFn_zero, Pi.zero_apply, smul_zero,
      WithLp.ofLp_zero]
    funext i
    simp [Navier.Analysis.ComplexLerayProjection.complexConjugate]

end Navier.Analysis.PeriodicRealizationSchwartzObstruction

#print axioms Navier.Analysis.PeriodicRealizationSchwartzObstruction.schwartzVelocity_eq_zero_of_spatiallyPeriodic
#print axioms Navier.Analysis.PeriodicRealizationSchwartzObstruction.schwartzVelocity_eq_zero_of_physicalMildVelocity_slice
#print axioms Navier.Analysis.PeriodicRealizationSchwartzObstruction.not_isClassicalSolution_physicalMildVelocity_of_ne_zero
#print axioms Navier.Analysis.PeriodicRealizationSchwartzObstruction.not_periodicSmallDataLift_of_rotational_data
