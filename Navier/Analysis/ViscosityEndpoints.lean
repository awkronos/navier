import Navier.Analysis.ViscosityAdmissibility
import Navier.OfficialProblem

/-!
# Viscosity-one reductions for the positive existence alternatives

The unforced whole-space and periodic existence alternatives can be normalized
to viscosity one.  Given datum `u₀` at viscosity `nu`, first scale `u₀`
backwards by `nu⁻¹`, invoke the viscosity-one endpoint, and then transport the
resulting complete solution forwards by `nu`.  Zero force is fixed by this
transport.

The breakdown alternatives C and D require an additional analytic input: their
arbitrary admissible forces must remain rapidly decaying under the same
time/amplitude scaling.  That input is not asserted here.  The two missing
transport families are recorded only as finite planning metadata below, so no
conditional bridge can be mistaken for a proved endpoint reduction.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ViscosityEndpoints

open Navier
open ViscosityTransport
open ViscosityAdmissibility

/-- The exact viscosity-one surface of the whole-space existence alternative
A.  Unlike `Clay.StatementA`, it has no viscosity quantifier. -/
def StatementAAtViscosityOne : Prop :=
  ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution 1 zeroForce u₀ u p

/-- The exact viscosity-one surface of the periodic existence alternative B.
Unlike `Clay.StatementB`, it has no viscosity quantifier. -/
def StatementBAtViscosityOne : Prop :=
  ∀ u₀ : VelocityField, PeriodicInitialDatum u₀ →
    ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsPeriodicClassicalSolution 1 zeroForce u₀ u p

/-- The full all-positive-viscosity statement A is equivalent to its
viscosity-one surface. -/
theorem statementA_iff_atViscosityOne :
    Clay.StatementA ↔ StatementAAtViscosityOne := by
  unfold Clay.StatementA StatementAAtViscosityOne
  constructor
  · intro h u₀ hu₀
    exact h 1 zero_lt_one u₀ hu₀
  · intro h nu hnu u₀ hu₀
    let base := viscosityScaledSchwartzDatum nu⁻¹ u₀
    have hbase : DivergenceFreeInitial base :=
      divergenceFreeInitial_viscosityScaledSchwartzDatum nu⁻¹ u₀ hu₀
    rcases h base hbase with ⟨u, p, hsol⟩
    refine ⟨viscosityScaledVelocity nu u,
      viscosityScaledPressure nu p, ?_⟩
    have htransport :=
      isClassicalSolution_one_to_viscosity
        nu hnu zeroForce base u p hsol
    simpa [base, viscosityScaledSchwartzDatum, smul_smul, hnu.ne'] using
      htransport

/-- The full all-positive-viscosity statement B is equivalent to its
viscosity-one surface. -/
theorem statementB_iff_atViscosityOne :
    Clay.StatementB ↔ StatementBAtViscosityOne := by
  unfold Clay.StatementB StatementBAtViscosityOne
  constructor
  · intro h u₀ hu₀
    exact h 1 zero_lt_one u₀ hu₀
  · intro h nu hnu u₀ hu₀
    let base := viscosityScaledDatum nu⁻¹ u₀
    have hbase : PeriodicInitialDatum base :=
      periodicInitialDatum_viscosityScaled nu⁻¹ u₀ hu₀
    rcases h base hbase with ⟨u, p, hsol⟩
    refine ⟨viscosityScaledVelocity nu u,
      viscosityScaledPressure nu p, ?_⟩
    have htransport :=
      isPeriodicClassicalSolution_one_to_viscosity
        nu hnu zeroForce base u p hsol
    have hdatum :
        viscosityScaledDatum nu (viscosityScaledDatum nu⁻¹ u₀) = u₀ := by
      funext x
      simp [viscosityScaledDatum, smul_smul, hnu.ne']
    rw [show viscosityScaledDatum nu base = u₀ by
      simpa only [base] using hdatum] at htransport
    simpa using htransport

/-- Exact analytic transport families still needed before the breakdown
alternatives C and D can be normalized to viscosity one.  These constructors
are metadata, not assumptions or inhabitants of the missing propositions.

The whole-space item asks for preservation of `ForcedDataRapidDecay` under
positive `viscosityScaledForce`; the periodic item asks for preservation of
`PeriodicForcedDataRapidDecay`.  Quantification over every positive scaling
factor also covers inverse scaling. -/
inductive BreakdownViscosityReductionResidual where
  | wholeSpaceArbitraryForceRapidDecayTransport
  | periodicArbitraryForceRapidDecayTransport
  deriving DecidableEq, Repr, Fintype

/-- Both force-admissibility transport families remain visible as planning
residuals; no implication involving `Clay.StatementC` or `Clay.StatementD` is
declared in this module. -/
def breakdownViscosityReductionResiduals :
    Finset BreakdownViscosityReductionResidual :=
  Finset.univ

/-- There are exactly two distinct breakdown-reduction residual families. -/
theorem breakdownViscosityReductionResiduals_card :
    breakdownViscosityReductionResiduals.card = 2 := by
  decide

end Navier.Analysis.ViscosityEndpoints
