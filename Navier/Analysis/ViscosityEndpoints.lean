import Navier.Analysis.ViscosityAdmissibility
import Navier.OfficialProblem

/-!
# Viscosity-one reductions for the positive existence alternatives

The unforced whole-space and periodic existence alternatives can be normalized
to viscosity one.  Given datum `u₀` at viscosity `nu`, first scale `u₀`
backwards by `nu⁻¹`, invoke the viscosity-one endpoint, and then transport the
resulting complete solution forwards by `nu`.  Zero force is fixed by this
transport.

The full arbitrary-force breakdown alternatives C and D require an additional
analytic input: their admissible forces must remain rapidly decaying under the
same time/amplitude scaling.  That input is not asserted here.  A breakdown at
viscosity one with the particular force `zeroForce` is nevertheless a stronger
sufficient surface for each official breakdown alternative, because zero force
is admissible and is fixed by the transport.  These stronger surfaces remain
uninhabited propositions here.  The two missing arbitrary-force transport
families are retained as finite planning metadata below.
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

/-- A stronger zero-force, viscosity-one sufficient surface for alternative C:
some admissible whole-space datum has no complete unforced classical solution
at viscosity one.

This proposition is not inhabited in this module.  It is stronger than the
viscosity-one instance of `Clay.StatementC`, which may choose an arbitrary
admissible force. -/
def StatementCZeroForceAtViscosityOne : Prop :=
  ∃ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ ∧
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution 1 zeroForce u₀ u p

/-- A stronger zero-force, viscosity-one sufficient surface for alternative D:
some admissible periodic datum has no complete unforced periodic classical
solution at viscosity one.

This proposition is not inhabited in this module.  It is stronger than the
viscosity-one instance of `Clay.StatementD`, which may choose an arbitrary
admissible periodic force. -/
def StatementDZeroForceAtViscosityOne : Prop :=
  ∃ u₀ : VelocityField, PeriodicInitialDatum u₀ ∧
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
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

/-- A zero-force whole-space breakdown witness at viscosity one is sufficient
for the official all-positive-viscosity alternative C.

At viscosity `nu`, the witness datum is its forward amplitude scaling by
`nu`.  Any hypothetical solution for that datum inverse-transports to the
forbidden viscosity-one solution.  The reverse implication is not asserted:
an official C witness may rely essentially on a nonzero force. -/
theorem statementC_of_zeroForceAtViscosityOne
    (h : StatementCZeroForceAtViscosityOne) : Clay.StatementC := by
  rcases h with ⟨u₀, hu₀, hbad⟩
  intro nu hnu
  refine ⟨viscosityScaledSchwartzDatum nu u₀,
    divergenceFreeInitial_viscosityScaledSchwartzDatum nu u₀ hu₀,
    zeroForce, forcedDataRapidDecay_zeroForce, ?_⟩
  intro hsolution
  rcases hsolution with ⟨u, p, hsol⟩
  apply hbad
  refine ⟨viscosityScaledVelocity nu⁻¹ u,
    viscosityScaledPressure nu⁻¹ p, ?_⟩
  have hback :=
    isClassicalSolution_viscosity_to_one
      nu hnu zeroForce (viscosityScaledSchwartzDatum nu u₀) u p hsol
  rw [viscosityScaledSchwartzDatum_inv nu hnu.ne' u₀] at hback
  simpa using hback

/-- A zero-force periodic breakdown witness at viscosity one is sufficient for
the official all-positive-viscosity alternative D.

The datum is forward-scaled to viscosity `nu`; a hypothetical periodic
solution then inverse-transports to the excluded viscosity-one solution.  No
reverse implication is asserted because an official D witness may use a
nonzero admissible periodic force. -/
theorem statementD_of_zeroForceAtViscosityOne
    (h : StatementDZeroForceAtViscosityOne) : Clay.StatementD := by
  rcases h with ⟨u₀, hu₀, hbad⟩
  intro nu hnu
  refine ⟨viscosityScaledDatum nu u₀,
    periodicInitialDatum_viscosityScaled nu u₀ hu₀,
    zeroForce, periodicForcedDataRapidDecay_zeroForce, ?_⟩
  intro hsolution
  rcases hsolution with ⟨u, p, hsol⟩
  apply hbad
  refine ⟨viscosityScaledVelocity nu⁻¹ u,
    viscosityScaledPressure nu⁻¹ p, ?_⟩
  have hback :=
    isPeriodicClassicalSolution_viscosity_to_one
      nu hnu zeroForce (viscosityScaledDatum nu u₀) u p hsol
  rw [viscosityScaledDatum_inv nu hnu.ne' u₀] at hback
  simpa using hback

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

/-- Both arbitrary-force admissibility transport families remain visible as
planning residuals.  The stronger zero-force sufficient implications above do
not discharge either residual, and no arbitrary-force equivalence or reverse
endpoint implication is declared in this module. -/
def breakdownViscosityReductionResiduals :
    Finset BreakdownViscosityReductionResidual :=
  Finset.univ

/-- There are exactly two distinct breakdown-reduction residual families. -/
theorem breakdownViscosityReductionResiduals_card :
    breakdownViscosityReductionResiduals.card = 2 := by
  decide

end Navier.Analysis.ViscosityEndpoints
