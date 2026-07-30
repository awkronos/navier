import Navier.Analysis.ViscosityForceDecay
import Navier.OfficialProblem

/-!
# Viscosity-one reductions for the official alternatives

The unforced whole-space and periodic existence alternatives can be normalized
to viscosity one.  Given datum `u₀` at viscosity `nu`, first scale `u₀`
backwards by `nu⁻¹`, invoke the viscosity-one endpoint, and then transport the
resulting complete solution forwards by `nu`.  Zero force is fixed by this
transport.

The arbitrary-force breakdown alternatives normalize as well.  A
viscosity-one witness is transported forward by scaling both its datum and
force; rapid-decay admissibility is preserved by `ViscosityForceDecay`.  Any
hypothetical solution at the target viscosity inverse-transports to the
forbidden viscosity-one solution.  The former two force-admissibility
transport residuals are therefore replaced here by exact endpoint
equivalences.

A breakdown at viscosity one with the particular force `zeroForce` remains a
stronger sufficient surface for each breakdown alternative, because zero force
is admissible and fixed by the transport.  Every surface in this module is only
a proposition: no existence or breakdown endpoint is inhabited here.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ViscosityEndpoints

open Navier
open ViscosityTransport
open ViscosityAdmissibility
open ViscosityForceDecay

/-- The exact viscosity-one surface of the whole-space existence alternative
A.  Unlike `ProblemStatements.WholeSpaceGlobalRegularity`, it has no viscosity quantifier. -/
def WholeSpaceGlobalRegularityAtViscosityOne : Prop :=
  ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution 1 zeroForce u₀ u p

/-- The exact viscosity-one surface of the periodic existence alternative B.
Unlike `ProblemStatements.PeriodicGlobalRegularity`, it has no viscosity quantifier. -/
def PeriodicGlobalRegularityAtViscosityOne : Prop :=
  ∀ u₀ : VelocityField, PeriodicInitialDatum u₀ →
    ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsPeriodicClassicalSolution 1 zeroForce u₀ u p

/-- The exact viscosity-one surface of the arbitrary-force whole-space
breakdown alternative C. -/
def WholeSpaceBreakdownAtViscosityOne : Prop :=
  ∃ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ ∧
    ∃ f : ForceField, ForcedDataRapidDecay f ∧
      ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
        IsClassicalSolution 1 f u₀ u p

/-- The exact viscosity-one surface of the arbitrary-force periodic breakdown
alternative D. -/
def PeriodicBreakdownAtViscosityOne : Prop :=
  ∃ u₀ : VelocityField, PeriodicInitialDatum u₀ ∧
    ∃ f : ForceField, PeriodicForcedDataRapidDecay f ∧
      ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
        IsPeriodicClassicalSolution 1 f u₀ u p

/-- A stronger zero-force, viscosity-one sufficient surface for alternative C:
some admissible whole-space datum has no complete unforced classical solution
at viscosity one.

This proposition is not inhabited in this module.  It is stronger than the
viscosity-one instance of `ProblemStatements.WholeSpaceBreakdown`, which may choose an arbitrary
admissible force. -/
def WholeSpaceBreakdownZeroForceAtViscosityOne : Prop :=
  ∃ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ ∧
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution 1 zeroForce u₀ u p

/-- A stronger zero-force, viscosity-one sufficient surface for alternative D:
some admissible periodic datum has no complete unforced periodic classical
solution at viscosity one.

This proposition is not inhabited in this module.  It is stronger than the
viscosity-one instance of `ProblemStatements.PeriodicBreakdown`, which may choose an arbitrary
admissible periodic force. -/
def PeriodicBreakdownZeroForceAtViscosityOne : Prop :=
  ∃ u₀ : VelocityField, PeriodicInitialDatum u₀ ∧
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsPeriodicClassicalSolution 1 zeroForce u₀ u p

/-- The full all-positive-viscosity statement A is equivalent to its
viscosity-one surface. -/
theorem wholeSpaceGlobalRegularity_iff_atViscosityOne :
    ProblemStatements.WholeSpaceGlobalRegularity ↔ WholeSpaceGlobalRegularityAtViscosityOne := by
  unfold ProblemStatements.WholeSpaceGlobalRegularity WholeSpaceGlobalRegularityAtViscosityOne
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
theorem periodicGlobalRegularity_iff_atViscosityOne :
    ProblemStatements.PeriodicGlobalRegularity ↔ PeriodicGlobalRegularityAtViscosityOne := by
  unfold ProblemStatements.PeriodicGlobalRegularity PeriodicGlobalRegularityAtViscosityOne
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

/-- The full all-positive-viscosity statement C is equivalent to its exact
arbitrary-force viscosity-one surface.

For the nontrivial direction, both datum and force witnesses are scaled
forward.  A hypothetical solution for the scaled witnesses inverse-transports
to a solution contradicting the viscosity-one witness. -/
theorem wholeSpaceBreakdown_iff_atViscosityOne :
    ProblemStatements.WholeSpaceBreakdown ↔ WholeSpaceBreakdownAtViscosityOne := by
  unfold ProblemStatements.WholeSpaceBreakdown WholeSpaceBreakdownAtViscosityOne
  constructor
  · intro h
    exact h 1 zero_lt_one
  · intro h nu hnu
    rcases h with ⟨u₀, hu₀, f, hf, hbad⟩
    refine ⟨viscosityScaledSchwartzDatum nu u₀,
      divergenceFreeInitial_viscosityScaledSchwartzDatum nu u₀ hu₀,
      viscosityScaledForce nu f,
      forcedDataRapidDecay_viscosityScaled nu hnu f hf, ?_⟩
    intro hsolution
    rcases hsolution with ⟨u, p, hsol⟩
    apply hbad
    refine ⟨viscosityScaledVelocity nu⁻¹ u,
      viscosityScaledPressure nu⁻¹ p, ?_⟩
    have hback :=
      isClassicalSolution_viscosity_to_one
        nu hnu (viscosityScaledForce nu f)
          (viscosityScaledSchwartzDatum nu u₀) u p hsol
    rw [viscosityScaledForce_inv nu hnu.ne' f,
      viscosityScaledSchwartzDatum_inv nu hnu.ne' u₀] at hback
    exact hback

/-- The full all-positive-viscosity statement D is equivalent to its exact
arbitrary-force viscosity-one surface.

The periodic datum and force witnesses are scaled forward, while any
hypothetical target-viscosity solution is transported inversely to contradict
the viscosity-one nonexistence witness. -/
theorem periodicBreakdown_iff_atViscosityOne :
    ProblemStatements.PeriodicBreakdown ↔ PeriodicBreakdownAtViscosityOne := by
  unfold ProblemStatements.PeriodicBreakdown PeriodicBreakdownAtViscosityOne
  constructor
  · intro h
    exact h 1 zero_lt_one
  · intro h nu hnu
    rcases h with ⟨u₀, hu₀, f, hf, hbad⟩
    refine ⟨viscosityScaledDatum nu u₀,
      periodicInitialDatum_viscosityScaled nu u₀ hu₀,
      viscosityScaledForce nu f,
      periodicForcedDataRapidDecay_viscosityScaled nu hnu f hf, ?_⟩
    intro hsolution
    rcases hsolution with ⟨u, p, hsol⟩
    apply hbad
    refine ⟨viscosityScaledVelocity nu⁻¹ u,
      viscosityScaledPressure nu⁻¹ p, ?_⟩
    have hback :=
      isPeriodicClassicalSolution_viscosity_to_one
        nu hnu (viscosityScaledForce nu f)
          (viscosityScaledDatum nu u₀) u p hsol
    rw [viscosityScaledForce_inv nu hnu.ne' f,
      viscosityScaledDatum_inv nu hnu.ne' u₀] at hback
    exact hback

/-- A zero-force whole-space breakdown witness at viscosity one is sufficient
for the official all-positive-viscosity alternative C.

At viscosity `nu`, the witness datum is its forward amplitude scaling by
`nu`.  Any hypothetical solution for that datum inverse-transports to the
forbidden viscosity-one solution.  The reverse implication is not asserted:
an official C witness may rely essentially on a nonzero force. -/
theorem wholeSpaceBreakdown_of_zeroForceAtViscosityOne
    (h : WholeSpaceBreakdownZeroForceAtViscosityOne) : ProblemStatements.WholeSpaceBreakdown := by
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
theorem periodicBreakdown_of_zeroForceAtViscosityOne
    (h : PeriodicBreakdownZeroForceAtViscosityOne) : ProblemStatements.PeriodicBreakdown := by
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

end Navier.Analysis.ViscosityEndpoints
