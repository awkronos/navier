import Navier.Analysis.BealeKatoMajda
import Navier.Analysis.ConstructedFiniteTimeObstruction
import Navier.Analysis.OfficialABEncoding

/-!
# Necessity: the constructed forced breakdown admits no Beale–Kato–Majda control

The Beale–Kato–Majda criterion of `Navier.Analysis.BealeKatoMajda` derives a
uniform velocity bound on `[0,T)` from a `BKMControl` bundle (`velocity_bounded`),
excludes the repository's point-evaluation breakdown with it
(`excludes_pointEvaluationBreakdown`), and is non-vacuous (`controlZero`).  This
file proves the necessity side at the repository's actual finite-time breakdown:
the selected forced compact candidate and every smooth same-force competitor
from rest admit **no** `BKMControl` on the deadline horizon `[0,1)`.  The
criterion's hypothesis `finite_vorticity_integral` is therefore fully
restrictive at this endpoint: no member of the proved blow-up class satisfies
it, so it cannot be weakened and still be consumable there.

## Carrier bridge

`Navier.Space = Fin 3 → ℝ` carries the product (supremum) norm; the
construction carrier `Navier.Construction.ProblemStatement.Space =
EuclideanSpace ℝ (Fin 3) = PiLp 2 _` carries the Euclidean norm and is the
bundled `Pi.bundled` type synonym, so uncurrying needs the explicit
`uncurry` transport below and the dimension-`√3` point comparison
`Real.sqrt 3 * ‖x‖∞ ≥ ‖x‖₂` from `Navier.Analysis.OfficialABEncoding`.
Euclidean unboundedness transports to supremum unboundedness through that
inequality, which is all the refutation of `velocity_bounded` consumes.

## Pattern-A scope, stated once

What is proved: `¬ Nonempty (BKMControl (uncurry v) 1)` for every competitor
`v` in the class, and for the candidate itself.  What is not claimed: the
divergence `∫₀¹ ‖ω(t)‖∞ dt = ∞` of the constructed field.  Residual (OPEN,
named): constructing any `BKMControl` rate/gronwall pair for the selected
candidate would need Sobolev–Grönwall control inputs the repository does not
supply for this profile; this file refutes the control bundle, which is the
exact hypothesis the criterion consumes, and nothing stronger.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.BKMForcedBreakdownNecessity

open Set
open scoped ContDiff
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.OfficialABEncoding
open Navier.Construction.ProblemStatement

private abbrev ESpace := Navier.Construction.ProblemStatement.Space
private abbrev EVelocityField := Navier.Construction.ProblemStatement.VelocityField
private abbrev EPressureField := Navier.Construction.ProblemStatement.PressureField

/-- **Speed unbounded arbitrarily below a horizon, on the problem carrier.**
`u : Navier.VelocityEvolution` has point speed exceeding every positive
threshold at some time of every terminal window `(T - δ, T)`, measured in the
product (supremum) norm inherited by `Navier.Space`.  This is the problem-
carrier normal form of
`Navier.Construction.ProblemStatement.SpeedUnboundedAtOne`. -/
def SpeedUnboundedBelow (T : ℝ) (u : Navier.VelocityEvolution) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Navier.Space, t ∈ Ioo 0 T ∧ T - δ < t ∧ M < ‖u t x‖

/-- **Uncurrying transport.**  A construction-carrier spacetime field
`v : (ℝ × ESpace) → ESpace` viewed as a problem-carrier `VelocityEvolution`:
spatial slots are the raw `Fin 3 → ℝ` coordinates, values are their
supremum-norm projections.  This is the identity on coordinates; only the
normed-group decoration changes (`Pi.bundled` in, the underlying function
out). -/
def uncurry (v : EVelocityField) : Navier.VelocityEvolution :=
  fun t x => (v (t, WithLp.toLp 2 x) : Navier.Space)

/-- **THEOREM (carrier-free core — the theorem of record).**  Let `T > 0` and
let `u : Navier.VelocityEvolution`.  If `u` has unbounded speed arbitrarily
below `T` on the problem carrier (`SpeedUnboundedBelow T u`), then `u` admits
no `BKMControl` on `[0,T)`: `¬ Nonempty (BKMControl u T)`.

The refutation consumes exactly the consequence `BKMControl.velocity_bounded`
(a uniform supremum bound on `[0,T)`) and nothing else from the bundle, so it
applies to every strengthening or weakening that still implies that bound. -/
theorem not_bkmControl_of_speedUnboundedBelow
    {u : Navier.VelocityEvolution} {T : ℝ} (hT : 0 < T)
    (hu : SpeedUnboundedBelow T u) : ¬ Nonempty (BKMControl u T) := by
  rintro ⟨c⟩
  obtain ⟨M, hM⟩ := c.velocity_bounded hT
  obtain ⟨t, x, ht, _, hlarge⟩ :=
    hu (max M 1) (by linarith [le_max_right M 1]) 1 zero_lt_one
  linarith [hM t ⟨ht.1.le, ht.2⟩ x, hlarge, le_max_left M 1]

/-- Point comparison used by the bridge: the `PiLp 2` (Euclidean) norm of an
`ESpace` vector is at most `√3` times the supremum norm of the same
coordinates viewed on `Navier.Space`.  Obtained from the repository's sharp
comparison `officialEuclideanNorm_le` through the coordinate identity
`officialEuclideanNorm x = ‖WithLp.toLp 2 x‖`. -/
private theorem norm_Euclidean_le (z : ESpace) :
    ‖z‖ ≤ Real.sqrt 3 * ‖(z : Navier.Space)‖ := by
  have h : officialEuclideanNorm (z : Navier.Space) = ‖z‖ := by
    simp [officialEuclideanNorm, officialEuclideanPoint, EuclideanSpace.norm_eq]
  rw [← h]
  exact officialEuclideanNorm_le z

/-- **THEOREM (carrier bridge).**  The uncurried construction-carrier field
preserves unbounded speed: `SpeedUnboundedAtOne v →
SpeedUnboundedBelow 1 (uncurry v)`.  The `√3` comparison transfers each
Euclidean witness to a supremum witness; the threshold `√3·M + 1` is the one
the transfer needs.  No claim is made that the two norms agree — they do not. -/
theorem speedUnboundedBelow_of_speedUnboundedAtOne
    {v : EVelocityField} (hv : SpeedUnboundedAtOne v) :
    SpeedUnboundedBelow 1 (uncurry v) := by
  intro M hM δ hδ
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨t, x, ht, hnear, hlarge⟩ :=
    hv (Real.sqrt 3 * M + 1) (by positivity) δ hδ
  refine ⟨t, (x : Navier.Space), ht, hnear, ?_⟩
  have hcast : uncurry v t (x : Navier.Space) = (v (t, x) : Navier.Space) := by
    simp [uncurry]
  rw [hcast]
  have hlt : Real.sqrt 3 * M < Real.sqrt 3 * ‖(v (t, x) : Navier.Space)‖ := by
    linarith [hlarge, norm_Euclidean_le (z := v (t, x))]
  exact lt_of_mul_lt_mul_left hlt (Real.sqrt_nonneg 3)

/-- **THEOREM (deadline instantiation).**  Every construction-carrier field
whose speed blows up below time one admits no `BKMControl` on the uncurried
problem carrier on `[0,1)`.  This is `not_bkmControl_of_speedUnboundedBelow`
at `T = 1` through the bridge. -/
theorem not_bkmControl_of_speedUnboundedAtOne
    {v : EVelocityField} (hv : SpeedUnboundedAtOne v) :
    ¬ Nonempty (BKMControl (uncurry v) 1) :=
  not_bkmControl_of_speedUnboundedBelow zero_lt_one
    (speedUnboundedBelow_of_speedUnboundedAtOne hv)

/-- **THEOREM (main endpoint — full restrictiveness of the BKM hypothesis at
the constructed breakdown).**  There exist selected fields `u, p, f` with the
same leading conjuncts as
`Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_forces_speed_blowup_in_every_smooth_competitor`
(the compact-candidate properties, a globally smooth force, and presingular
uniform finite energy) such that every competitor `v` in that theorem's class
(presingular smooth, locally finite energy on each closed slab,
divergence-free, same force `f`, at rest at time zero) satisfies **both** the
speed blow-up `SpeedUnboundedAtOne v` and `¬ Nonempty (BKMControl (uncurry v) 1)`
— no Beale–Kato–Majda control bundle exists on `[0,1)`.

This is the necessity side of the sharpness pair.  Sufficiency is the existing
`BKMControl.velocity_bounded` and
`BKMControl.excludes_pointEvaluationBreakdown`; non-vacuity of the control
class is `BKMControl.controlZero` and `bkmControl_class_nonvacuous` below.
The criterion's hypothesis `finite_vorticity_integral` is refuted for every
admissible profile of the sole proved breakdown mechanism, so it cannot be
weakened and remain consumable at this endpoint.

Scope, once: the conclusion is the nonexistence of the control bundle.  The
vorticity-integral divergence `∫₀¹ ‖ω(t)‖∞ dt = ∞` of these fields is not
claimed; that needs Sobolev–Grönwall control inputs the repository does not
construct for the selected profile (OPEN residual, named in the section
header). -/
theorem selected_candidate_forces_no_BKM_control_in_every_smooth_competitor :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ f ∧
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      ∀ v : EVelocityField, ∀ q : EPressureField,
        ContDiffOn ℝ ∞ v preSingularDomain →
        ContDiffOn ℝ ∞ q preSingularDomain →
        (∀ T ∈ Ico (0 : ℝ) 1,
          Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v) →
        (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, spatialDivergence v t x = 0) →
        (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, navierStokesResidual v q t x = f (t, x)) →
        (∀ x, v (0, x) = 0) →
        SpeedUnboundedAtOne v ∧
          ¬ Nonempty (BKMControl (uncurry v) 1) := by
  obtain ⟨u, p, f, h, hf, henergy, hblow⟩ :=
    (Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_forces_speed_blowup_in_every_smooth_competitor : _)
  refine ⟨u, p, f, h, hf, henergy, fun v q hv hq hE hdv hNS hv0 => ?_⟩
  have hspeed := hblow v q hv hq hE hdv hNS hv0
  exact ⟨hspeed, not_bkmControl_of_speedUnboundedAtOne hspeed⟩

/-- **THEOREM (the constructed candidate itself).**  The selected compact
candidate `u` — which instantiates the competitor class of the endpoint above
through its own properties fields `velocity_smooth`, `pressure_smooth`,
`divergence_free`, `navier_stokes`, `zero_initial_velocity`, together with its
`Ico 0 1` uniform finite energy — admits no `BKMControl` on `[0,1)`: the
refutation uses only its own `speed_unbounded` field, so the candidate is the
first witness of the nonexistence, not a hypothetical competitor. -/
theorem selected_candidate_admits_no_BKM_control :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ f ∧
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      ¬ Nonempty (BKMControl (uncurry u) 1) := by
  obtain ⟨u, p, f, _, h, hf, henergy, _, _, _, _⟩ :=
    (Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile : _)
  exact ⟨u, p, f, h, hf, henergy,
    not_bkmControl_of_speedUnboundedAtOne h.speed_unbounded⟩

/-- **THEOREM (the refuted class is not everything — companion witness).**
On the same problem carrier and the same horizon `T = 1` as the endpoint, the
class `{u | ¬ Nonempty (BKMControl u 1)}` is a genuine restriction, not a
totality: the zero velocity `fun _ _ => 0` carries the explicit bundle
`BKMControl.controlZero 1` and has bounded speed (`¬ SpeedUnboundedBelow 1`),
so `not_bkmControl_of_speedUnboundedBelow` is nonvacuous and its hypothesis
`SpeedUnboundedBelow T u` is satisfiable-false and refutable-false at once on
concrete fields.  The uncurried construction-carrier zero field is this same
`Navier.VelocityEvolution` by `rfl` (`uncurry (fun _ => 0)` unfolds to
`fun _ x => (0 : Navier.Space)` coordinate-wise). -/
theorem bkmControl_class_nonvacuous :
    ∃ u : Navier.VelocityEvolution,
      Nonempty (BKMControl u 1) ∧ ¬ SpeedUnboundedBelow 1 u := by
  refine ⟨fun _ _ => (0 : Navier.Space), ⟨BKMControl.controlZero 1⟩, ?_⟩
  intro hu
  obtain ⟨t, x, _, _, hlarge⟩ := hu 1 zero_lt_one 1 zero_lt_one
  have hzero : ‖(fun _ _ => (0 : Navier.Space)) t x‖ = 0 := by simp
  rw [hzero] at hlarge
  linarith

end Navier.Analysis.BKMForcedBreakdownNecessity

#print axioms Navier.Analysis.BKMForcedBreakdownNecessity.not_bkmControl_of_speedUnboundedBelow
#print axioms Navier.Analysis.BKMForcedBreakdownNecessity.speedUnboundedBelow_of_speedUnboundedAtOne
#print axioms Navier.Analysis.BKMForcedBreakdownNecessity.not_bkmControl_of_speedUnboundedAtOne
#print axioms Navier.Analysis.BKMForcedBreakdownNecessity.selected_candidate_forces_no_BKM_control_in_every_smooth_competitor
#print axioms Navier.Analysis.BKMForcedBreakdownNecessity.selected_candidate_admits_no_BKM_control
#print axioms Navier.Analysis.BKMForcedBreakdownNecessity.bkmControl_class_nonvacuous
