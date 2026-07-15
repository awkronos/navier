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

/-- The whole-space finite and uniformly bounded kinetic-energy clause in the
norm currently inherited by `Space`. -/
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

/-- Under slice measurability, the current and official whole-space energy
clauses are equivalent. -/
theorem currentWholeSpaceEnergyClause_iff_official
    (u : VelocityEvolution)
    (hmeas : ∀ t : ℝ, 0 ≤ t → AEStronglyMeasurable (u t)) :
    CurrentWholeSpaceEnergyClause u ↔ OfficialWholeSpaceEnergyClause u := by
  constructor
  · rintro ⟨hint, hbound⟩
    have hoff : ∀ t : ℝ, 0 ≤ t →
        Integrable (fun x : Space => officialEuclideanNorm (u t x) ^ 2) :=
      fun t ht =>
        (integrable_norm_sq_iff_officialEuclideanNorm_sq
          (u t) (hmeas t ht)).1 (hint t ht)
    exact ⟨hoff,
      (uniformlyBoundedEnergy_iff_official u hmeas hint).1 hbound⟩
  · rintro ⟨hoff, hbound⟩
    have hint : ∀ t : ℝ, 0 ≤ t →
        Integrable (fun x : Space => ‖u t x‖ ^ 2) :=
      fun t ht =>
        (integrable_norm_sq_iff_officialEuclideanNorm_sq
          (u t) (hmeas t ht)).2 (hoff t ht)
    exact ⟨hint,
      (uniformlyBoundedEnergy_iff_official u hmeas hint).2 hbound⟩

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

end Navier.Analysis.EnergyOfficialClause
