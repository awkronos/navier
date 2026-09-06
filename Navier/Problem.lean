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

`SchwartzMap`, `ContDiffOn`, Fréchet derivatives, and the Lebesgue integral
encode the datum, smoothness, PDE, and energy clauses. Their comparison
theorems live in `Analysis.SchwartzConventionEquivalence`,
`Analysis.HalfSpaceSmoothnessBridge`, `Analysis.CoordinatePDEBridge`, and
`Analysis.EnergyOfficialClause`. Norm transport is in
`Analysis.ForceNormBridge`. These mathematical declarations, rather than a
fixed enumeration of residuals, specify what has been established.
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

Choosing the Euclidean density here discharged *one clause* of the former
`currentSpaceNormEuclideanNormEquivalence` residual — the energy integrand
itself, which previously used the sup norm inherited by `Fin 3 → ℝ`.  The
remaining clauses were then transported one by one. `finite_energy` below still
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
(`Analysis.EnergyNormBridge.uniformlyBoundedEnergy_iff_sup`).  Every consumer
provably transports across the mismatch, so the former
`currentSpaceNormEuclideanNormEquivalence` residual is retired rather than
listed. -/
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

namespace ProblemStatements

/-- The canonical formal encoding of Fefferman whole-space statement A.

For every `nu > 0` and every divergence-free Schwartz velocity `u0` on `R^3`,
there exist velocity and pressure fields that are smooth on nonnegative time,
solve the actual unforced Navier--Stokes equation pointwise, attain `u0`, remain
incompressible, and have uniformly bounded finite kinetic energy.

This definition states the target proposition. Establishing it requires a
proof of this exact type; refuting it requires a proof of its negation. -/
def WholeSpaceGlobalRegularity : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∃ (u : VelocityEvolution) (p : PressureEvolution),
        IsClassicalSolution ν zeroForce u₀ u p

/-! ### Two-pole satisfiability guards for the statement-A surface

A universally quantified endpoint fails soundness at either of two poles, and
both are invisible to the kernel.  If the datum class `{u₀ : DivergenceFreeInitial u₀}`
were empty, `WholeSpaceGlobalRegularity` would be vacuously TRUE and provable
without any analysis.  If the conclusion bundle `IsClassicalSolution` were
uninhabitable — for instance if `finite_energy` and `uniformly_bounded_energy`
could not hold simultaneously with the smoothness and equation fields — the
endpoint would be FALSE as stated for a formalization reason rather than a
fluid-mechanical one, and every `iff` and conditional reduction stated against
it would be about a false proposition.

The three declarations below close both poles at a real point of the quantifier
range.  They are guards, not progress: the zero datum is the one Schwartz datum
whose global smooth solution is elementary, and nothing here bears on any
nonzero datum. -/

/-- **Pole (a): the datum class is nonempty.**  The zero Schwartz velocity is
divergence-free, so the outer `∀` of `WholeSpaceGlobalRegularity` does not range
over an empty class and the endpoint is not vacuously true. -/
theorem divergenceFreeInitial_zero : DivergenceFreeInitial (0 : SchwartzVelocity) := by
  intro x
  simp [staticDivergence]

/-- **Pole (b): the solution contract is inhabitable.**  The zero velocity and
zero pressure satisfy every field of `IsClassicalSolution` simultaneously, at
every viscosity, including the explicit `Integrable` field and the strict
uniform energy bound (`kineticEnergy = 0 < 1`).  The seven clauses are therefore
jointly satisfiable: `IsClassicalSolution` is not an uninhabitable bundle, so no
theorem taking it is vacuously true for that reason. -/
theorem isClassicalSolution_zero (ν : ℝ) :
    IsClassicalSolution ν zeroForce 0 (fun _ _ => 0) (fun _ _ => 0) where
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  initial_condition := by intro x; simp
  incompressible := by
    intro t _ x
    simp [divergence, spatialDerivative]
  equation := by
    intro t _ x
    have hpg : pressureGradient (fun _ _ => (0 : ℝ)) t x = 0 := by
      funext i
      simp [pressureGradient]
    simp [timeDerivative, convection, spatialDerivative, laplacian, zeroForce, hpg]
  finite_energy := by intro t _; simp
  uniformly_bounded_energy := ⟨1, one_pos, by intro t _; simp [kineticEnergy]⟩

/-- The body of `WholeSpaceGlobalRegularity` holds at the zero datum, for every
positive viscosity.  This is the endpoint's own shape evaluated at an admissible
point of its quantifier range; it settles both satisfiability poles at once and
proves nothing about `WholeSpaceGlobalRegularity` itself, whose content is the
nonzero data. -/
theorem wholeSpaceGlobalRegularity_body_at_zero_datum (ν : ℝ) (_hν : 0 < ν) :
    ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution ν zeroForce 0 u p :=
  ⟨fun _ _ => 0, fun _ _ => 0, isClassicalSolution_zero ν⟩

end ProblemStatements

end Navier
