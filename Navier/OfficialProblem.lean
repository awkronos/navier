import Navier.Problem

/-!
# Formal Fefferman alternatives A--D

This module leaves `Navier.ProblemStatements.WholeSpaceGlobalRegularity` unchanged and defines non-inhabited
proposition surfaces for the sibling alternatives B, C, and D.  The definitions
follow Fefferman's clauses (1)--(11), including the pressure-periodicity
erratum.  They do not assert that the chosen Mathlib conventions are equivalent
to the official coordinatewise or quotient-space wording.

In particular, the periodic alternatives use clauses (10) and (11), which do
not include the whole-space bounded-energy clause (7).  No whole-space
Lebesgue integral is imported into B or D.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Navier

/-- The closed nonnegative-time spacetime domain used by the existing problem
encoding and by the force-data predicates below. -/
def nonnegativeSpacetime : Set (ℝ × Space) :=
  (Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set Space)

/-- A spacetime force is `C∞` on the nonnegative-time half-space in the same
Mathlib within-smoothness convention used by `Navier.Problem`. -/
def SmoothForceOnNonnegativeTime (f : ForceField) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Space ↦ f z.1 z.2) nonnegativeSpacetime

/-- A precise Frechet-within encoding of Fefferman's whole-space force clause
(5): all mixed spacetime derivatives decay faster than every polynomial in
space and nonnegative time.

The bridge from total Frechet derivatives and the current norm on `Space` to
Fefferman's coordinatewise multi-index/Euclidean-norm wording remains an
explicit semantic residual; no equivalence is claimed here. -/
def ForcedDataRapidDecay (f : ForceField) : Prop :=
  SmoothForceOnNonnegativeTime f ∧
    ∀ (n K : ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        (1 + ‖x‖ + t) ^ K *
            ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space ↦ f z.1 z.2)
              nonnegativeSpacetime (t, x)‖ ≤ C

/-- Period one in every spatial coordinate. -/
def SpatiallyPeriodic {X : Type*} (g : Space → X) : Prop :=
  ∀ (x : Space) (i : Fin 3), g (x + basisVector i) = g x

/-- Periodicity of the initial velocity in clause (8). -/
def SpatiallyPeriodicDatum (u₀ : VelocityField) : Prop :=
  SpatiallyPeriodic u₀

/-- Periodicity of velocity on all nonnegative times, clause (10). -/
def SpatiallyPeriodicVelocity (u : VelocityEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → SpatiallyPeriodic (u t)

/-- Periodicity of pressure on all nonnegative times, required by Fefferman's
erratum for the periodic alternatives. -/
def SpatiallyPeriodicPressure (p : PressureEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → SpatiallyPeriodic (p t)

/-- Periodicity of force in clause (8). -/
def SpatiallyPeriodicForce (f : ForceField) : Prop :=
  ∀ t : ℝ, 0 ≤ t → SpatiallyPeriodic (f t)

/-- An admissible periodic initial datum: smooth, divergence-free, and period
one in every coordinate.  Unlike whole-space data, it is intentionally not a
`SchwartzMap`. -/
def PeriodicInitialDatum (u₀ : VelocityField) : Prop :=
  ContDiff ℝ ∞ u₀ ∧
    (∀ x : Space, staticDivergence u₀ x = 0) ∧
    SpatiallyPeriodicDatum u₀

/-- Fefferman's periodic force clauses (8) and (9): spatial periodicity,
`C∞` half-space regularity, and rapid decay in nonnegative time uniformly in
space for every mixed derivative order.

As for `ForcedDataRapidDecay`, the total-Frechet versus coordinatewise bridge
is retained as a semantic residual rather than asserted. -/
def PeriodicForcedDataRapidDecay (f : ForceField) : Prop :=
  SpatiallyPeriodicForce f ∧
    SmoothForceOnNonnegativeTime f ∧
    ∀ (n K : ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        (1 + t) ^ K *
            ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space ↦ f z.1 z.2)
              nonnegativeSpacetime (t, x)‖ ≤ C

/-- The periodic classical-solution contract from (1), (2), (3), (10), and
(11), with pressure periodicity added per the official erratum.

There is deliberately no whole-space kinetic-energy field: alternatives B and
D do not invoke clause (7). -/
structure IsPeriodicClassicalSolution (nu : ℝ) (f : ForceField)
    (u₀ : VelocityField) (u : VelocityEvolution)
    (p : PressureEvolution) : Prop where
  velocity_smooth : SmoothVelocityOnNonnegativeTime u
  pressure_smooth : SmoothPressureOnNonnegativeTime p
  initial_condition : ∀ x : Space, u 0 x = u₀ x
  incompressible : Incompressible u
  equation : SatisfiesNavierStokes nu f u p
  velocity_periodic : SpatiallyPeriodicVelocity u
  pressure_periodic : SpatiallyPeriodicPressure p

/-- Representation bridges still needed before identifying these precise
Mathlib surfaces with Fefferman's prose without qualification. -/
inductive OfficialSurfaceEncodingResidual where
  | schwartzDatumCoordinatewiseEquivalence
  | forceFrechetCoordinatewiseEquivalence
  | halfSpaceSmoothnessEquivalence
  | currentSpaceNormEuclideanNormEquivalence
  | problemFrechetCoordinatePDEEquivalence
  | wholeSpaceEnergyClauseEquivalence
  | periodicLiftQuotientEquivalence
  deriving DecidableEq, Repr, Fintype

def officialSurfaceEncodingResiduals : Finset OfficialSurfaceEncodingResidual :=
  Finset.univ

namespace ProblemStatements

/-- Fefferman alternative B: unforced global smooth periodic solutions for
every positive viscosity and every admissible periodic initial datum. -/
def PeriodicGlobalRegularity : Prop :=
  ∀ nu : ℝ, 0 < nu →
    ∀ u₀ : VelocityField, PeriodicInitialDatum u₀ →
      ∃ (u : VelocityEvolution) (p : PressureEvolution),
        IsPeriodicClassicalSolution nu zeroForce u₀ u p

/-- Fefferman alternative C: for every positive viscosity, some admissible
whole-space datum and admissible force admit no global smooth bounded-energy
classical solution pair. -/
def WholeSpaceBreakdown : Prop :=
  ∀ nu : ℝ, 0 < nu →
    ∃ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ ∧
      ∃ f : ForceField, ForcedDataRapidDecay f ∧
        ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
          IsClassicalSolution nu f u₀ u p

/-- Fefferman alternative D: for every positive viscosity, some admissible
periodic datum and periodic time-decaying force admit no global smooth periodic
solution pair.  No whole-space energy condition occurs. -/
def PeriodicBreakdown : Prop :=
  ∀ nu : ℝ, 0 < nu →
    ∃ u₀ : VelocityField, PeriodicInitialDatum u₀ ∧
      ∃ f : ForceField, PeriodicForcedDataRapidDecay f ∧
        ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
          IsPeriodicClassicalSolution nu f u₀ u p

end ProblemStatements

end Navier
