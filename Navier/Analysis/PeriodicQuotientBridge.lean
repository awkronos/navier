import Navier.OfficialSurfaceSignatures
import Mathlib.Algebra.Ring.Periodic

/-!
# Periodic fields and the spatial torus

The periodic alternatives are stated on lifts to `Space = ℝ³`: a field is
unchanged after adding one in any coordinate.  This file proves that this is
exactly the condition for the field to descend to the quotient by the integer
lattice.  The result is valid for arbitrary codomains, so it applies uniformly
to the initial datum, velocity, pressure, and force consumers.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PeriodicQuotientBridge

open Navier
open scoped ContDiff

/-- The integer lattice `ℤ³` inside `Space = ℝ³`. -/
def integerLattice : AddSubgroup Space :=
  AddSubgroup.pi Set.univ (fun _ => AddSubgroup.zmultiples (1 : ℝ))

/-- The spatial three-torus `ℝ³ / ℤ³`. -/
abbrev SpatialTorus := Space ⧸ integerLattice

/-- The quotient projection from the Euclidean lift to the spatial torus. -/
def torusProjection (x : Space) : SpatialTorus := QuotientAddGroup.mk x

/-- Generator periodicity makes a field invariant under every integer-lattice
translation. -/
theorem invariant_add_integerLattice {X : Type*} {g : Space → X}
    (hg : SpatiallyPeriodic g) {z : Space} (hz : z ∈ integerLattice) (x : Space) :
    g (x + z) = g x := by
  classical
  have hz' : ∀ i : Fin 3, ∃ n : ℤ, n • (1 : ℝ) = z i := by
    intro i
    exact hz i (Set.mem_univ i)
  choose n hn using hz'
  have hperiod (i : Fin 3) : Function.Periodic g (basisVector i) :=
    fun y => hg y i
  have hsum : ∀ s : Finset (Fin 3),
      g (x + ∑ i ∈ s, n i • basisVector i) = g x := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        calc
          g (x + (n i • basisVector i + ∑ j ∈ s, n j • basisVector j)) =
              g ((x + ∑ j ∈ s, n j • basisVector j) + n i • basisVector i) := by
                congr 1
                abel
          _ = g (x + ∑ j ∈ s, n j • basisVector j) :=
            (hperiod i).zsmul (n i) _
          _ = g x := ih
  have hzsum : z = ∑ i : Fin 3, n i • basisVector i := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simpa [basisVector] using (hn j).symm
    · intro i _ hne
      simp [basisVector, hne]
    · simp
  rw [hzsum]
  exact hsum Finset.univ

/-- **Periodic lift/quotient equivalence.**  A field on `ℝ³` is periodic
with period one in each coordinate exactly when it is the pullback of a field
on the spatial torus `ℝ³ / ℤ³`. -/
theorem spatiallyPeriodic_iff_factors_through_torus {X : Type*} (g : Space → X) :
    SpatiallyPeriodic g ↔
      ∃ gBar : SpatialTorus → X, ∀ x : Space, gBar (torusProjection x) = g x := by
  constructor
  · intro hg
    refine ⟨fun q => Quotient.liftOn' q g ?_, fun _ => rfl⟩
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply] at hab
    have h := invariant_add_integerLattice hg hab a
    convert h.symm using 1
    all_goals abel_nf
  · rintro ⟨gBar, hgBar⟩ x i
    rw [← hgBar x, ← hgBar (x + basisVector i)]
    apply congrArg gBar
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have hb : basisVector i ∈ integerLattice := by
      intro j _
      by_cases hji : j = i
      · subst j
        refine ⟨1, ?_⟩
        simp [basisVector]
      · refine ⟨0, ?_⟩
        simp [basisVector, hji]
    simpa using hb

/-- The admissible-data consumer can use a genuine torus field instead of a
generator-periodicity premise on its Euclidean lift. -/
theorem periodicInitialDatum_iff_torus_realization (u₀ : VelocityField) :
    PeriodicInitialDatum u₀ ↔
      ContDiff ℝ ∞ u₀ ∧
        (∀ x : Space, staticDivergence u₀ x = 0) ∧
        ∃ uBar₀ : SpatialTorus → Space,
          ∀ x : Space, uBar₀ (torusProjection x) = u₀ x := by
  simp only [PeriodicInitialDatum, SpatiallyPeriodicDatum,
    spatiallyPeriodic_iff_factors_through_torus]

/-- The force-admissibility consumer likewise replaces lift periodicity by a
torus-valued force at every nonnegative time, without changing its smoothness
or decay clauses. -/
theorem periodicForcedDataRapidDecay_iff_torus_realizations (f : ForceField) :
    PeriodicForcedDataRapidDecay f ↔
      (∀ t : ℝ, 0 ≤ t → ∃ fBar : SpatialTorus → Space,
        ∀ x : Space, fBar (torusProjection x) = f t x) ∧
      SmoothForceOnNonnegativeTime f ∧
      ∀ (n K : ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
          (1 + t) ^ K *
              ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space ↦ f z.1 z.2)
                nonnegativeSpacetime (t, x)‖ ≤ C := by
  simp only [PeriodicForcedDataRapidDecay, SpatiallyPeriodicForce,
    spatiallyPeriodic_iff_factors_through_torus]

/-- The periodic classical-solution consumer is equivalent to one carrying
actual quotient-space realizations of its velocity and pressure at every
nonnegative time. -/
theorem periodicClassicalSolution_iff_torus_realizations
    (nu : ℝ) (f : ForceField) (u₀ : VelocityField)
    (u : VelocityEvolution) (p : PressureEvolution) :
    IsPeriodicClassicalSolution nu f u₀ u p ↔
      SmoothVelocityOnNonnegativeTime u ∧
      SmoothPressureOnNonnegativeTime p ∧
      (∀ x : Space, u 0 x = u₀ x) ∧
      Incompressible u ∧
      SatisfiesNavierStokes nu f u p ∧
      (∀ t : ℝ, 0 ≤ t → ∃ uBar : SpatialTorus → Space,
        ∀ x : Space, uBar (torusProjection x) = u t x) ∧
      (∀ t : ℝ, 0 ≤ t → ∃ pBar : SpatialTorus → ℝ,
        ∀ x : Space, pBar (torusProjection x) = p t x) := by
  rw [Navier.OfficialSurfaceSignatures.periodicClassicalSolution_signature]
  simp only [SpatiallyPeriodicVelocity, SpatiallyPeriodicPressure,
    spatiallyPeriodic_iff_factors_through_torus]

end Navier.Analysis.PeriodicQuotientBridge
