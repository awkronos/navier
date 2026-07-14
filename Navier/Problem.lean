import Mathlib

/-!
# Formal whole-space Navier--Stokes statement-A surface

This file gives a direct `R^3` formulation of the velocity, pressure, spatial
and time derivatives, incompressibility, the Navier--Stokes equation, smooth
nonnegative-time classical solutions, and bounded energy.

The canonical endpoint `Navier.Clay.StatementA` formalizes the quantifiers and
equations in (1)--(7) and statement (A) of Charles Fefferman's official Clay
problem description.  It quantifies over every positive viscosity and every
divergence-free Schwartz initial datum, and it fixes the force to zero.

Scope caveat: `SchwartzMap` is used for Fefferman's coordinatewise rapid-decay
condition (4), while `ContDiffOn` on the closed half-space is used for (6).
The comparison of these Mathlib conventions with the official coordinatewise
wording is deliberately retained in `ProblemEncodingResidual`; no equivalence
between those conventions is asserted here.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff
open MeasureTheory

namespace Navier

/-- The spatial domain `R^3`, represented in standard coordinates. -/
abbrev Space := Fin 3 → ℝ

/-- A time-independent velocity field on `R^3`. -/
abbrev VelocityField := Space → Space

/-- A time-independent scalar pressure field on `R^3`. -/
abbrev PressureField := Space → ℝ

/-- A velocity field depending on real time.  Solution obligations below are
imposed only on the nonnegative-time half-space. -/
abbrev VelocityEvolution := ℝ → VelocityField

/-- A pressure field depending on real time. -/
abbrev PressureEvolution := ℝ → PressureField

/-- A spacetime body force. -/
abbrev ForceField := ℝ → Space → Space

/-- Fefferman initial data, represented by Mathlib's Schwartz maps. -/
abbrev SchwartzVelocity := SchwartzMap Space Space

/-- The `i`th coordinate unit vector of `R^3`. -/
def basisVector (i : Fin 3) : Space := Pi.single i 1

/-- The spatial Frechet derivative of a time-dependent velocity. -/
def spatialDerivative (u : VelocityEvolution) (t : ℝ) (x : Space) :
    Space →L[ℝ] Space :=
  fderiv ℝ (u t) x

/-- The time derivative within `[0,infinity)`, represented by the
one-dimensional Frechet derivative within the half-line and applied to the
unit time direction.  At `t = 0` this uses Mathlib's right-within convention
rather than an arbitrary negative-time extension. -/
def timeDerivative (u : VelocityEvolution) (t : ℝ) (x : Space) : Space :=
  fderivWithin ℝ (fun s : ℝ => u s x) (Set.Ici 0) t 1

/-- Divergence in the standard coordinates on `R^3`. -/
def divergence (u : VelocityEvolution) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, spatialDerivative u t x (basisVector i) i

/-- Divergence of a time-independent velocity field. -/
def staticDivergence (u : VelocityField) (x : Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ u x (basisVector i) i

/-- The nonlinear convective term `(u . grad) u`. -/
def convection (u : VelocityEvolution) (t : ℝ) (x : Space) : Space :=
  spatialDerivative u t x (u t x)

/-- The spatial gradient of pressure in the standard coordinates. -/
def pressureGradient (p : PressureEvolution) (t : ℝ) (x : Space) : Space :=
  fun i => fderiv ℝ (p t) x (basisVector i)

/-- The componentwise spatial Laplacian, formed from second Frechet
derivatives in the three coordinate directions. -/
def laplacian (u : VelocityEvolution) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3,
    fderiv ℝ (fun y : Space => fderiv ℝ (u t) y (basisVector i)) x
      (basisVector i)

/-- The identically zero body force used in Fefferman statement A. -/
def zeroForce : ForceField := fun _ _ => 0

/-- `C^infinity` smoothness on `R^3 x [0,infinity)`, expressed using
Mathlib's within-derivative convention on the closed nonnegative-time
half-space.

The `∞` regularity is the coerced top element of `ℕ∞`.  It is deliberately
not `ω`, the top element of `WithTop ℕ∞`, which Mathlib reserves for analytic
regularity. -/
def SmoothVelocityOnNonnegativeTime (u : VelocityEvolution) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2)
    ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set Space))

/-- `C^infinity` pressure smoothness on the same nonnegative-time
half-space. -/
def SmoothPressureOnNonnegativeTime (p : PressureEvolution) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2)
    ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set Space))

/-- The Lebesgue kinetic-energy integral at time `t`. -/
def kineticEnergy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, ‖u t x‖ ^ 2

/-- A Schwartz initial velocity is divergence-free in the standard
coordinates. -/
def DivergenceFreeInitial (u₀ : SchwartzVelocity) : Prop :=
  ∀ x : Space, staticDivergence (fun y => u₀ y) x = 0

/-- Pointwise incompressibility for every nonnegative time. -/
def Incompressible (u : VelocityEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Space, divergence u t x = 0

/-- The forced incompressible Navier--Stokes momentum equation on `R^3`:
`partial_t u + (u . grad)u = nu Delta u - grad p + f`.

This is a classical pointwise equation.  The derivative operators are the
Frechet derivatives defined above; smoothness is carried separately by
`IsClassicalSolution`. -/
def SatisfiesNavierStokes (ν : ℝ) (f : ForceField)
    (u : VelocityEvolution) (p : PressureEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
    timeDerivative u t x + convection u t x =
      ν • laplacian u t x - pressureGradient p t x + f t x

/-- The complete proof-bearing predicate for a smooth bounded-energy
classical solution emanating from `u₀`.

The explicit `Integrable` field prevents Lean's convention for integrals of
nonintegrable functions from making the energy clause vacuous.  The uniform
strict bound is Fefferman's condition (7). -/
structure IsClassicalSolution (ν : ℝ) (f : ForceField)
    (u₀ : SchwartzVelocity) (u : VelocityEvolution)
    (p : PressureEvolution) : Prop where
  velocity_smooth : SmoothVelocityOnNonnegativeTime u
  pressure_smooth : SmoothPressureOnNonnegativeTime p
  initial_condition : ∀ x : Space, u 0 x = u₀ x
  incompressible : Incompressible u
  equation : SatisfiesNavierStokes ν f u p
  finite_energy :
    ∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)
  uniformly_bounded_energy :
    ∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E

/-- Named representation obligations left open when comparing the present
Mathlib surface with Fefferman's coordinatewise conditions (4) and (6).

These are metamathematical encoding residuals, not hypotheses of
`Clay.StatementA`; consequently they cannot be used to project a proof of the
Clay endpoint. -/
inductive ProblemEncodingResidual where
  | schwartzConventionEquivalence
  | halfSpaceSmoothnessEquivalence
  deriving DecidableEq, Repr, Fintype

/-- Both convention-comparison obligations remain explicitly visible. -/
def problemEncodingResiduals : Finset ProblemEncodingResidual := Finset.univ

namespace Clay

/-- The canonical formal encoding of Fefferman whole-space statement A.

For every `nu > 0` and every divergence-free Schwartz velocity `u0` on `R^3`,
there exist velocity and pressure fields that are smooth on nonnegative time,
solve the actual unforced Navier--Stokes equation pointwise, attain `u0`, remain
incompressible, and have uniformly bounded finite kinetic energy.

This is the repository's scientific-frontier surface.  It is a proposition,
not a theorem and not a conclusion hidden in a payload or proof-program
argument.  The `ProblemEncodingResidual` bridges above must close before this
surface may be identified with the official textual conventions without a
qualification. -/
def StatementA : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∃ (u : VelocityEvolution) (p : PressureEvolution),
        IsClassicalSolution ν zeroForce u₀ u p

end Clay

end Navier
