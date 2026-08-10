import Navier.Analysis.EnergyNormBridge

/-!
# Exact transport to Fefferman's Euclidean energy clause

The project type `Space = Fin 3 → ℝ` inherits the product supremum norm, while
Fefferman's kinetic energy is the integral of the squared Euclidean coordinate
norm.  This file packages both the slice-integrability and uniform-bound
clauses and proves their exact equivalence for strongly measurable velocity
slices.  Smooth project solutions supply that measurability automatically.

Consequently every existing `IsClassicalSolution` satisfies the corresponding
official Euclidean energy clause.  This is a representation theorem, not an
energy estimate: the current solution predicate already contains finite and
uniformly bounded energy as hypotheses/fields.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Navier.Analysis.EnergyOfficialClause

open Navier
open Navier.Analysis.EnergyNormBridge
open Navier.Analysis.OfficialABEncoding

/-- The whole-space finite and uniformly bounded kinetic-energy clause exactly as
`Navier.IsClassicalSolution` states it.

**This clause is mixed, and deliberately so: it is a transcription, not a
design.**  Its integrability half is stated in the norm `Space` actually inherits
(the product **sup** norm, `‖u t x‖ ^ 2`), matching
`IsClassicalSolution.finite_energy`, while its uniform-bound half is stated in the
**Euclidean** energy `kineticEnergy = ∫ ∑ᵢ uᵢ²`, matching
`IsClassicalSolution.uniformly_bounded_energy`.  The two halves therefore live in
different norms.  This is why `currentWholeSpaceEnergyClause_iff_official` below
splits into one genuine step (integrability, sup vs Euclidean) and one identity
step (the bound, already Euclidean).  For the clause that is uniformly sup-normed
on both halves, and whose transport to Fefferman's genuinely costs the dimension
factor `3`, see `SupWholeSpaceEnergyClause`. -/
def CurrentWholeSpaceEnergyClause (u : VelocityEvolution) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)) ∧
    ∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E

/-- Fefferman's whole-space finite and uniformly bounded Euclidean kinetic-
energy clause. -/
def OfficialWholeSpaceEnergyClause (u : VelocityEvolution) : Prop :=
  (∀ t : ℝ, 0 ≤ t →
    Integrable (fun x : Space => officialEuclideanNorm (u t x) ^ 2)) ∧
    ∃ E : ℝ, 0 < E ∧
      ∀ t : ℝ, 0 ≤ t → officialKineticEnergy u t < E

/-- The squared official Euclidean norm is literally the sum of the three
coordinate squares appearing in Fefferman's clause (7). -/
theorem officialEuclideanNorm_sq_eq_sum_sq (x : Space) :
    officialEuclideanNorm x ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  rw [officialEuclideanNorm_eq_sqrt_sum_sq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg |x i|)]
  apply Finset.sum_congr rfl
  intro i _
  exact sq_abs (x i)

/-- The literal coordinate-sum kinetic energy from the official statement. -/
def coordinateKineticEnergy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, ∑ i : Fin 3, u t x i ^ 2

theorem officialKineticEnergy_eq_coordinateKineticEnergy
    (u : VelocityEvolution) (t : ℝ) :
    officialKineticEnergy u t = coordinateKineticEnergy u t := by
  simp only [officialKineticEnergy, coordinateKineticEnergy,
    officialEuclideanNorm_sq_eq_sum_sq]

/-- Fefferman's energy clause written literally as a coordinate sum. -/
def CoordinateWholeSpaceEnergyClause (u : VelocityEvolution) : Prop :=
  (∀ t : ℝ, 0 ≤ t →
    Integrable (fun x : Space => ∑ i : Fin 3, u t x i ^ 2)) ∧
    ∃ E : ℝ, 0 < E ∧
      ∀ t : ℝ, 0 ≤ t → coordinateKineticEnergy u t < E

theorem officialWholeSpaceEnergyClause_iff_coordinate
    (u : VelocityEvolution) :
    OfficialWholeSpaceEnergyClause u ↔ CoordinateWholeSpaceEnergyClause u := by
  simp only [OfficialWholeSpaceEnergyClause, CoordinateWholeSpaceEnergyClause,
    officialEuclideanNorm_sq_eq_sum_sq,
    officialKineticEnergy_eq_coordinateKineticEnergy]

/-- The uniform-bound halves of `CurrentWholeSpaceEnergyClause` and
`OfficialWholeSpaceEnergyClause` are **the same proposition**, because
`kineticEnergy` is already the Euclidean energy
(`officialKineticEnergy_eq_kineticEnergy`).

This replaces the former `EnergyNormBridge.uniformlyBoundedEnergy_iff_official`
shim.  Stating the collapse as an equality of propositions, rather than as an
`iff` carrying unused measurability and integrability hypotheses, records
honestly that no analysis happens here.  All the content of
`currentWholeSpaceEnergyClause_iff_official` is in the integrability half. -/
theorem uniformBound_current_eq_official (u : VelocityEvolution) :
    (∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E) =
      (∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, 0 ≤ t → officialKineticEnergy u t < E) := by
  simp only [officialKineticEnergy_eq_kineticEnergy]

/-- Under slice measurability, the current and official whole-space energy
clauses are equivalent.

The only step that does work is the integrability transport between the inherited
sup norm and the Euclidean norm.  The uniform bound needs no transport at all: by
`uniformBound_current_eq_official` the two bound clauses are literally the same
proposition, so it is passed through unchanged. -/
theorem currentWholeSpaceEnergyClause_iff_official
    (u : VelocityEvolution)
    (hmeas : ∀ t : ℝ, 0 ≤ t → AEStronglyMeasurable (u t)) :
    CurrentWholeSpaceEnergyClause u ↔ OfficialWholeSpaceEnergyClause u := by
  simp only [CurrentWholeSpaceEnergyClause, OfficialWholeSpaceEnergyClause,
    officialKineticEnergy_eq_kineticEnergy]
  exact and_congr_left' (forall_congr' fun t => imp_congr_right fun ht =>
    integrable_norm_sq_iff_officialEuclideanNorm_sq (u t) (hmeas t ht))

/-! ### The clause that is sup-normed on both halves

`CurrentWholeSpaceEnergyClause` is mixed, so its transport to Fefferman's clause
is cheap on the bound half.  The clause below is the honest sup-norm alternative:
both halves are stated in the norm `Space` inherits, so `supKineticEnergy`
replaces `kineticEnergy`.  Its transport to Fefferman's clause is where the
dimension factor `3` is actually spent.
-/

/-- The whole-space finite and uniformly bounded kinetic-energy clause stated
**entirely** in the norm `Space` inherits, i.e. with the sup-norm energy
`supKineticEnergy = ∫ ‖u t x‖²` on both halves.

This is the clause a consumer gets from a purely sup-norm bundle such as
`LerayWeak.UniformKineticBound`, as opposed to the Euclidean
`LerayWeak.UniformOfficialKineticBound`. -/
def SupWholeSpaceEnergyClause (u : VelocityEvolution) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)) ∧
    ∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, 0 ≤ t → supKineticEnergy u t < E

/-- **The honestly lossy transport.**  Under slice measurability the fully
sup-normed clause and Fefferman's Euclidean clause are equivalent, but unlike
`currentWholeSpaceEnergyClause_iff_official` neither half of this equivalence is
free: the integrability half is the sup/Euclidean comparison, and the bound half
spends the dimension factor `3` in the sup-to-Euclidean direction
(`uniformlyBoundedEnergy_iff_sup`), a factor that
`EnergyNormBridge.officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness` shows is
attained and hence not removable.

Because the clauses only assert that *some* positive bound exists, the constant
loss is invisible in the statement.  Consumers that need the bound with an exact
constant -- notably `LerayWeak.LerayLimitData.energy_le`, whose right-hand side is
literally the datum energy -- must not route through here; they need the Euclidean
bound carried from the start. -/
theorem supWholeSpaceEnergyClause_iff_official
    (u : VelocityEvolution)
    (hmeas : ∀ t : ℝ, 0 ≤ t → AEStronglyMeasurable (u t)) :
    SupWholeSpaceEnergyClause u ↔ OfficialWholeSpaceEnergyClause u := by
  simp only [SupWholeSpaceEnergyClause, OfficialWholeSpaceEnergyClause,
    officialKineticEnergy_eq_kineticEnergy]
  constructor
  · rintro ⟨hint, hbound⟩
    exact ⟨fun t ht => (integrable_norm_sq_iff_officialEuclideanNorm_sq
        (u t) (hmeas t ht)).1 (hint t ht),
      (uniformlyBoundedEnergy_iff_sup u hmeas hint).1 hbound⟩
  · rintro ⟨hoff, hbound⟩
    have hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2) :=
      fun t ht => (integrable_norm_sq_iff_officialEuclideanNorm_sq
        (u t) (hmeas t ht)).2 (hoff t ht)
    exact ⟨hint, (uniformlyBoundedEnergy_iff_sup u hmeas hint).2 hbound⟩

/-- The mixed clause that `IsClassicalSolution` supplies and the fully sup-normed
clause are equivalent under slice measurability.  Composed of the free bound
identity on one side and the factor-`3` sup-to-Euclidean step on the other, so a
project classical solution does satisfy the uniformly sup-normed energy clause --
just not with the same constant. -/
theorem currentWholeSpaceEnergyClause_iff_sup
    (u : VelocityEvolution)
    (hmeas : ∀ t : ℝ, 0 ≤ t → AEStronglyMeasurable (u t)) :
    CurrentWholeSpaceEnergyClause u ↔ SupWholeSpaceEnergyClause u :=
  (currentWholeSpaceEnergyClause_iff_official u hmeas).trans
    (supWholeSpaceEnergyClause_iff_official u hmeas).symm

/-- A nonnegative-time spatial slice of a project classical solution is
continuous. -/
theorem IsClassicalSolution.velocity_slice_continuous
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (sol : IsClassicalSolution ν f u₀ u p)
    {t : ℝ} (ht : 0 ≤ t) :
    Continuous (u t) := by
  rw [← continuousOn_univ]
  exact sol.velocity_smooth.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (by
      intro x _hx
      exact ⟨ht, Set.mem_univ x⟩)

/-- Smooth classical velocity slices are strongly measurable. -/
theorem IsClassicalSolution.velocity_slice_aestronglyMeasurable
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (sol : IsClassicalSolution ν f u₀ u p)
    {t : ℝ} (ht : 0 ≤ t) :
    AEStronglyMeasurable (u t) volume :=
  Navier.Analysis.EnergyOfficialClause.IsClassicalSolution.velocity_slice_continuous
    sol ht |>.aestronglyMeasurable

/-- Every project classical solution's existing energy fields transport to
the official Euclidean finite/uniform energy clause. -/
theorem IsClassicalSolution.officialWholeSpaceEnergyClause
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (sol : IsClassicalSolution ν f u₀ u p) :
    OfficialWholeSpaceEnergyClause u := by
  apply (currentWholeSpaceEnergyClause_iff_official u
    (fun t ht =>
      Navier.Analysis.EnergyOfficialClause.IsClassicalSolution.velocity_slice_aestronglyMeasurable
        sol ht)).1
  exact ⟨sol.finite_energy, sol.uniformly_bounded_energy⟩

/-- Every project classical solution also satisfies the literal coordinate-
sum formulation of Fefferman's energy clause. -/
theorem IsClassicalSolution.coordinateWholeSpaceEnergyClause
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (sol : IsClassicalSolution ν f u₀ u p) :
    CoordinateWholeSpaceEnergyClause u :=
  (officialWholeSpaceEnergyClause_iff_coordinate u).1
    (Navier.Analysis.EnergyOfficialClause.IsClassicalSolution.officialWholeSpaceEnergyClause
      sol)

/-- Every project classical solution also satisfies the fully sup-normed energy
clause.  Together with `IsClassicalSolution.officialWholeSpaceEnergyClause` this
shows the mixed-norm statement of the solution predicate is not an obstruction in
either direction; only the bound constant is norm-dependent. -/
theorem IsClassicalSolution.supWholeSpaceEnergyClause
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (sol : IsClassicalSolution ν f u₀ u p) :
    SupWholeSpaceEnergyClause u :=
  (supWholeSpaceEnergyClause_iff_official u
    (fun t ht =>
      Navier.Analysis.EnergyOfficialClause.IsClassicalSolution.velocity_slice_aestronglyMeasurable
        sol ht)).2
    (Navier.Analysis.EnergyOfficialClause.IsClassicalSolution.officialWholeSpaceEnergyClause
      sol)

end Navier.Analysis.EnergyOfficialClause
