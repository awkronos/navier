import Mathlib

/-!
# Formal whole-space Navier--Stokes statement-A surface

This file gives a direct `R^3` formulation of the velocity, pressure, spatial
and time derivatives, incompressibility, the Navier--Stokes equation, smooth
nonnegative-time classical solutions, and bounded energy.

The canonical endpoint `Navier.ProblemStatements.WholeSpaceGlobalRegularity` formalizes the quantifiers and
equations in (1)--(7) and statement (A) of Charles Fefferman's official problem-statement
problem description.  It quantifies over every positive viscosity and every
divergence-free Schwartz initial datum, and it fixes the force to zero.

Scope caveat: `SchwartzMap`, `ContDiffOn`, the current norm on `Fin 3 → ℝ`,
Fréchet derivatives, and a Lebesgue integral encode Fefferman's coordinatewise
clauses.  Their comparison with the official derivative, Euclidean-norm, PDE,
and energy wording is deliberately retained in `ProblemEncodingResidual`; no
unproved representation equivalence is asserted here.

`kineticEnergy` uses the Euclidean density `∑ᵢ uᵢ²`, which discharges the
energy-integrand clause of the norm residual.  All five residuals nevertheless
remain listed.  Four of them still name an open clause; the norm residual no
longer does, and is retained on the narrower ground stated in
`currentSpaceNormEuclideanNormEquivalence`.
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

/-- The Lebesgue kinetic-energy integral at time `t`, using the Euclidean
squared norm `∑ᵢ uᵢ²`.  The physical kinetic energy is `½∫|u|²`; this omits the
factor `½`.

Choosing the Euclidean density here discharged *one clause* of the
`currentSpaceNormEuclideanNormEquivalence` residual below — the energy integrand
itself, which previously used the sup norm inherited by `Fin 3 → ℝ`.  It does
**not** close that residual, which remains listed.  `finite_energy` below still
*states* integrability of the inherited sup norm `‖u t x‖²`, and the Schwartz and
force-decay clauses (here and in `Navier.OfficialProblem`) still state their
weights and derivative bundles in the product norm.  Each of those is now
provably equivalent to its Euclidean form, and
`Analysis.ForceNormBridge.wholeSpaceGlobalRegularity_iff_official` shows the
endpoint proposition is unaffected; what is not available is a quantitative
identification, since the two norms provably differ
(`Analysis.EnergyNormBridge.norm_sq_lt_officialEuclideanNorm_sq_witness`) and the
dimension constant relating them is attained. -/
def kineticEnergy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, ∑ i : Fin 3, (u t x i) ^ 2

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
strict bound is Fefferman's condition (7).

Note the deliberate norm mismatch between the two energy fields: `finite_energy`
integrates the *inherited* sup norm `‖u t x‖²`, while `uniformly_bounded_energy`
bounds the *Euclidean* `kineticEnergy`.  The mismatch is not an obstruction:
`Analysis.ForceNormBridge.isClassicalSolution_iff_official` shows this predicate
is the same as the one whose energy clause is Fefferman's throughout, the
smoothness field supplying the slice measurability that transport needs.  What
the mismatch does cost is a constant — the two energies are interderivable only
up to the attained dimension factor three
(`Analysis.EnergyNormBridge.uniformlyBoundedEnergy_iff_sup`) — which is why
`currentSpaceNormEuclideanNormEquivalence` stays on the residual list. -/
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
Mathlib statement-A surface with Fefferman's coordinatewise clauses (1)--(7).

These are metamathematical encoding residuals, not hypotheses of
`ProblemStatements.WholeSpaceGlobalRegularity`; consequently they cannot be used to project a proof of the
problem endpoint. -/
inductive ProblemEncodingResidual where
  /-- Mathlib's `SchwartzMap` seminorm convention versus Fefferman's
  multi-index decay wording for the initial datum. -/
  | schwartzConventionEquivalence
  /-- `ContDiffOn` on `Ici 0 ×ˢ univ` versus the official `C^∞` on
  `R^3 × [0,∞)`. -/
  | halfSpaceSmoothnessEquivalence
  /-- The product sup norm inherited by `Space = Fin 3 → ℝ` versus the
  Euclidean norm on `R^3`.

  **No clause of this surface is open in this residual any more, and neither is
  any statement built from them.**  `WholeSpaceGlobalRegularity` is provably the
  same proposition as its fully Euclidean form
  (`Analysis.ForceNormBridge.wholeSpaceGlobalRegularity_iff_official`, via
  `isClassicalSolution_iff_official`, whose slice measurability comes from
  `velocity_smooth` rather than from a new hypothesis), and so are Fefferman's
  alternatives C and D
  (`Analysis.ForceNormBridge.wholeSpaceBreakdown_iff_official`,
  `Analysis.ForceNormBridge.periodicBreakdown_iff_official`).  Underneath: the
  energy integrand is Euclidean by definition, the energy pair transports by
  `Analysis.EnergyOfficialClause.currentWholeSpaceEnergyClause_iff_official`, the
  Schwartz datum decay clause in all three of its norms by
  `Analysis.EnergyNormBridge.feffermanRapidDecayBound_iff_fullyEuclidean`, and
  the force clauses of `Navier.OfficialProblem` by
  `Analysis.ForceNormBridge.forcedDataRapidDecay_iff_official` and
  `Analysis.ForceNormBridge.periodicForcedDataRapidDecay_iff_official`.

  Two things survive, and they are all that this residual now asserts.  First,
  no *definition* on this surface has been restated in Euclidean form: the
  transports above compare a project definition with an official one, they do
  not replace it, so reading `IsClassicalSolution` still means reading the
  inherited norm.  Second, the identifications are of *classes*: each moves an
  existentially quantified constant through a power of `√3`, and none can be
  made an identity, because the two norms differ at the all-ones point and the
  dimension constant three is attained
  (`Analysis.EnergyNormBridge.norm_sq_lt_officialEuclideanNorm_sq_witness`,
  `Analysis.EnergyNormBridge.officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness`).
  A consumer needing a bound with a named constant still pays that factor. -/
  | currentSpaceNormEuclideanNormEquivalence
  /-- Total Frechet derivatives versus Fefferman's coordinatewise partial
  derivatives in the momentum equation. -/
  | problemFrechetCoordinatePDEEquivalence
  /-- The Bochner-integral reading of clause (7) versus the official
  whole-space energy wording. -/
  | wholeSpaceEnergyClauseEquivalence
  deriving DecidableEq, Repr, Fintype

/-- All five statement-A representation obligations remain explicitly visible.

`currentSpaceNormEuclideanNormEquivalence` is retained even though every clause
it names is transported and every statement built from them is provably
norm-independent.  What remains is that no definition here has been *restated*
in Euclidean form, and that each identification is class-level rather than
quantitative because of the attained factor-`3` loss.  A residual is removed
only when nothing it names is open in any sense, never merely when its clause
list has been worked through. -/
def problemEncodingResiduals : Finset ProblemEncodingResidual := Finset.univ

/-- The statement-A surface currently exposes exactly five representation
bridges, independently of its separate analytic existence frontier. -/
theorem problemEncodingResiduals_card : problemEncodingResiduals.card = 5 := by
  decide

namespace ProblemStatements

/-- The canonical formal encoding of Fefferman whole-space statement A.

For every `nu > 0` and every divergence-free Schwartz velocity `u0` on `R^3`,
there exist velocity and pressure fields that are smooth on nonnegative time,
solve the actual unforced Navier--Stokes equation pointwise, attain `u0`, remain
incompressible, and have uniformly bounded finite kinetic energy.

This is the repository's scientific-frontier surface.  It is a proposition,
not a theorem and not a conclusion hidden in a payload or proof-program
argument.  The five `ProblemEncodingResidual` bridges above must close before
this surface may be identified with the official textual conventions without
qualification. -/
def WholeSpaceGlobalRegularity : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∃ (u : VelocityEvolution) (p : PressureEvolution),
        IsClassicalSolution ν zeroForce u₀ u p

end ProblemStatements

end Navier
