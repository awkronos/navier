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

/-! ## DC-1: the zero-force breakdown surfaces are exactly the negations of
the viscosity-one existence surfaces (de Morgan pairs)

`WholeSpaceBreakdownZeroForceAtViscosityOne` says some admissible datum has no
unforced viscosity-one solution; `WholeSpaceGlobalRegularityAtViscosityOne`
says every admissible datum has one.  The two are literal quantifier
negations of each other over the same contract, so each pair is an `iff` and
the proofs below are pure quantifier logic — no analysis, no transport.
These edges turn the two orphan `¬`-surfaces into web nodes. -/

/-- **Zero-force whole-space breakdown is exactly the failure of the
viscosity-one existence surface A₁.**  Both sides are defined in this module
(`:75` and `:40`); the proof is de Morgan over the shared `∀`/`∃` shape. -/
theorem wholeSpaceBreakdownZeroForce_iff_not_wholeSpaceGlobalRegularityAtViscosityOne :
    WholeSpaceBreakdownZeroForceAtViscosityOne ↔
      ¬ WholeSpaceGlobalRegularityAtViscosityOne := by
  constructor
  · rintro ⟨u₀, hu₀, hbad⟩ hA
    exact hbad (hA u₀ hu₀)
  · intro h
    by_contra hneg
    exact h fun u₀ hu₀ => Classical.byContradiction
      fun hno => hneg ⟨u₀, hu₀, hno⟩

/-- **Zero-force periodic breakdown is exactly the failure of the viscosity-one
periodic existence surface B₁.**  The periodic twin of the pair above, over
`:87` and `:47`. -/
theorem periodicBreakdownZeroForce_iff_not_periodicGlobalRegularityAtViscosityOne :
    PeriodicBreakdownZeroForceAtViscosityOne ↔
      ¬ PeriodicGlobalRegularityAtViscosityOne := by
  constructor
  · rintro ⟨u₀, hu₀, hbad⟩ hB
    exact hbad (hB u₀ hu₀)
  · intro h
    by_contra hneg
    exact h fun u₀ hu₀ => Classical.byContradiction
      fun hno => hneg ⟨u₀, hu₀, hno⟩

/-! ## DC-2: negation-transport corollaries off the endpoint `iff`s

The viscosity-one endpoints `A ↔ A₁` (`:94`) and `B ↔ B₁` (`:115`) transport
negations between the official all-viscosity surfaces and the viscosity-one
surfaces, and the DC-1 pairs then place each official existence statement in
direct contradiction with its zero-force breakdown surface. -/

/-- **¬A₁ ⇒ ¬A.**  Failure of the viscosity-one whole-space existence surface
contradicts the official statement A through
`wholeSpaceGlobalRegularity_iff_atViscosityOne`. -/
theorem not_wholeSpaceGlobalRegularity_of_notAtViscosityOne
    (h : ¬ WholeSpaceGlobalRegularityAtViscosityOne) :
    ¬ ProblemStatements.WholeSpaceGlobalRegularity := by
  rintro hA
  exact h (wholeSpaceGlobalRegularity_iff_atViscosityOne.mp hA)

/-- **A ⇒ ¬(zero-force breakdown at viscosity one).**  If A holds then its
viscosity-one transport gives a solution for every admissible datum, so no
datum can witness `WholeSpaceBreakdownZeroForceAtViscosityOne`. -/
theorem not_wholeSpaceBreakdownZeroForce_of_wholeSpaceGlobalRegularity
    (h : ProblemStatements.WholeSpaceGlobalRegularity) :
    ¬ WholeSpaceBreakdownZeroForceAtViscosityOne := by
  rintro ⟨u₀, hu₀, hbad⟩
  exact hbad (wholeSpaceGlobalRegularity_iff_atViscosityOne.mp h u₀ hu₀)

/-- **¬B₁ ⇒ ¬B.**  The periodic twin. -/
theorem not_periodicGlobalRegularity_of_notAtViscosityOne
    (h : ¬ PeriodicGlobalRegularityAtViscosityOne) :
    ¬ ProblemStatements.PeriodicGlobalRegularity := by
  rintro hB
  exact h (periodicGlobalRegularity_iff_atViscosityOne.mp hB)

/-- **B ⇒ ¬(zero-force periodic breakdown at viscosity one).**  The periodic
twin. -/
theorem not_periodicBreakdownZeroForce_of_periodicGlobalRegularity
    (h : ProblemStatements.PeriodicGlobalRegularity) :
    ¬ PeriodicBreakdownZeroForceAtViscosityOne := by
  rintro ⟨u₀, hu₀, hbad⟩
  exact hbad (periodicGlobalRegularity_iff_atViscosityOne.mp h u₀ hu₀)

/-! ## DC-4: the forced regularity surface and the ¬C ⇒ A contrapositive edge

Alternative A fixes the force to `zeroForce`; official C existentially
quantifies an admissible force.  The surface between them is regularity for
*every* admissible force: `ForcedWholeSpaceGlobalRegularity`.  Its negation
side is exact: `¬C` says the breakdown witness fails to exist at *some*
viscosity; the viscosity-one normalization `wholeSpaceBreakdown_iff_atViscosityOne`
then leaves no admissible datum/force pair without a viscosity-one solution
(otherwise that pair would itself be a C₁ witness), and the existing
transport lemmas lift every pair to every positive viscosity.

A and official C are separated EXACTLY by force-dependence: the reverse edge
`A ⇒ ¬C` is honestly absent (a world where every *unforced* datum is globally
regular can still host a forced breakdown — this is recorded for the
zero-force surface in the docstring at `:206`), and nothing here claims it. -/

/-- The all-viscosity, all-datum, all-admissible-force existence surface:
every positive viscosity, every divergence-free Schwartz datum, and every
rapid-decay admissible force jointly admit a classical solution pair.  This is
the force-quantified strengthening of A whose specialization to `zeroForce`
recovers A exactly. -/
def ForcedWholeSpaceGlobalRegularity : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ f : ForceField, ForcedDataRapidDecay f →
      ∃ (u : VelocityEvolution) (p : PressureEvolution),
        IsClassicalSolution ν f u₀ u p

/-- **¬C ⇒ ForcedWholeSpaceGlobalRegularity.**  If the official breakdown
alternative C fails, then its viscosity-one twin C₁ fails too
(`wholeSpaceBreakdown_iff_atViscosityOne`), so at viscosity one no admissible
datum/force pair can lack a solution — any such pair would itself be a C₁
witness.  For a general `nu > 0`, the inverse viscosity scaling
(`ViscosityTransport`) moves any datum/force pair to viscosity one preserving
admissibility (`forcedDataRapidDecay_viscosityScaled`); a viscosity-one
solution transports forward by `isClassicalSolution_one_to_viscosity` and the
round-trip identities `viscosityScaledForce_inv` /
`viscosityScaledSchwartzDatum_inv` return it at `nu`.  Failure of solvability
at `(nu, u₀, f)` would therefore manufacture a C₁ witness, hence an official
C witness, contradicting `¬C`. -/
theorem forcedWholeSpaceGlobalRegularity_of_not_wholeSpaceBreakdown
    (h : ¬ ProblemStatements.WholeSpaceBreakdown) :
    ForcedWholeSpaceGlobalRegularity := by
  intro nu hnu u₀ hu₀ f hf
  by_contra hno
  refine absurd ?_ h
  apply wholeSpaceBreakdown_iff_atViscosityOne.mpr
  refine ⟨viscosityScaledSchwartzDatum nu⁻¹ u₀,
    divergenceFreeInitial_viscosityScaledSchwartzDatum nu⁻¹ u₀ hu₀,
    viscosityScaledForce nu⁻¹ f,
    forcedDataRapidDecay_viscosityScaled nu⁻¹ (inv_pos.mpr hnu) f hf, ?_⟩
  rintro ⟨u, p, hsol⟩
  have hup :=
    isClassicalSolution_one_to_viscosity nu hnu (viscosityScaledForce nu⁻¹ f)
      (viscosityScaledSchwartzDatum nu⁻¹ u₀) u p hsol
  have hforce : viscosityScaledForce nu (viscosityScaledForce nu⁻¹ f) = f := by
    simpa using viscosityScaledForce_inv nu⁻¹ (inv_ne_zero hnu.ne') f
  have hdatum :
      viscosityScaledSchwartzDatum nu (viscosityScaledSchwartzDatum nu⁻¹ u₀) = u₀ := by
    simpa using viscosityScaledSchwartzDatum_inv nu⁻¹ (inv_ne_zero hnu.ne') u₀
  rw [hforce, hdatum] at hup
  exact hno ⟨viscosityScaledVelocity nu u, viscosityScaledPressure nu p, hup⟩

/-- **ForcedWholeSpaceGlobalRegularity ⇒ A.**  Specializing the forced surface
to the admissible zero force (`forcedDataRapidDecay_zeroForce`) recovers the
official statement A verbatim. -/
theorem wholeSpaceGlobalRegularity_of_forcedWholeSpaceGlobalRegularity
    (h : ForcedWholeSpaceGlobalRegularity) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  intro nu hnu u₀ hu₀
  exact h nu hnu u₀ hu₀ zeroForce forcedDataRapidDecay_zeroForce

/-- **The contrapositive edge ¬C ⇒ A**, composing the two rows above: if the
forced breakdown alternative C fails, then the unforced alternative A holds.
This closes the C/A edge of the equivalence web; it says nothing about the
truth values of A or C themselves, both of which remain at their registered
statuses (A OPEN, C PROVED for the forced contract). -/
theorem wholeSpaceGlobalRegularity_of_not_wholeSpaceBreakdown
    (h : ¬ ProblemStatements.WholeSpaceBreakdown) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_forcedWholeSpaceGlobalRegularity
    (forcedWholeSpaceGlobalRegularity_of_not_wholeSpaceBreakdown h)

end Navier.Analysis.ViscosityEndpoints

#print axioms Navier.Analysis.ViscosityEndpoints.wholeSpaceBreakdownZeroForce_iff_not_wholeSpaceGlobalRegularityAtViscosityOne
#print axioms Navier.Analysis.ViscosityEndpoints.periodicBreakdownZeroForce_iff_not_periodicGlobalRegularityAtViscosityOne
#print axioms Navier.Analysis.ViscosityEndpoints.not_wholeSpaceGlobalRegularity_of_notAtViscosityOne
#print axioms Navier.Analysis.ViscosityEndpoints.not_wholeSpaceBreakdownZeroForce_of_wholeSpaceGlobalRegularity
#print axioms Navier.Analysis.ViscosityEndpoints.not_periodicGlobalRegularity_of_notAtViscosityOne
#print axioms Navier.Analysis.ViscosityEndpoints.not_periodicBreakdownZeroForce_of_periodicGlobalRegularity
#print axioms Navier.Analysis.ViscosityEndpoints.ForcedWholeSpaceGlobalRegularity
#print axioms Navier.Analysis.ViscosityEndpoints.forcedWholeSpaceGlobalRegularity_of_not_wholeSpaceBreakdown
#print axioms Navier.Analysis.ViscosityEndpoints.wholeSpaceGlobalRegularity_of_forcedWholeSpaceGlobalRegularity
#print axioms Navier.Analysis.ViscosityEndpoints.wholeSpaceGlobalRegularity_of_not_wholeSpaceBreakdown
