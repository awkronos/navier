import Navier.Analysis.ContinuousLeiLinMildFixedPoint
import Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
import Navier.Analysis.ContinuousLeiLinPhysicalVelocity
import Navier.Analysis.ContinuousLeiLinRecentTailInputs
import Navier.Analysis.PeriodicRealizationSchwartzObstruction

/-!
# The exact mild-uniqueness interface for a whole-space restart slab

The completed weighted-lattice fixed point is a periodic Fourier theory.  It
cannot represent a nonzero whole-space Schwartz trace even at the initial
time; `no_periodicLatticeInitialRepresentation_of_ne_zero` records that
carrier obstruction without any PDE or radius hypothesis.

The repository's faithful whole-space replacement is the continuous
Lei--Lin carrier.  On that carrier, `fixedPointTrajectory_eq_of_commonBox`
proves the reusable part of the desired overlap argument: two fixed points in
the same completed linked box, for the same viscosity, horizon, datum and
assembly leaves, have identical pointwise mild trajectories.  The box type
itself records their common `X⁻¹`/viscous-`X¹` bounds.

`velocity_eq_on_Icc_of_commonBox_mildRepresentations` transports this
frequency-side uniqueness to arbitrary physical velocity evolutions once
each has been identified with the inverse-Fourier trajectory on the compact
slab.  Thus the exact remaining analytic provider for a classical restart is
not another uniqueness theorem: it is a classical-to-continuous-Fourier
Duhamel representation, together with membership in one common linked box.
The existing small-data engine additionally requires the trace radius
`R ≤ ν/16` through `MildAssemblyLeaves.hRν`; no such smallness follows from a
general BKM restart budget.  Construction of `MildAssemblyLeaves` is itself
decomposed in `ContinuousLeiLinMildAssemblyLeaves`: its time leaves still need
the named `SourceL1X1` input.  The theorems below consume that record; they do
not silently claim those analytic leaves.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal FourierTransform SchwartzMap

namespace Navier.Analysis.WholeSpaceRestartMildInterface

open Navier
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinMildFixedPoint
open Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinRecentTailInputs
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.FourierMajorant
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicRealizationSchwartzObstruction

/-- No nonzero whole-space Schwartz datum can be the initial slice of the
physical realization of any weighted-lattice path.  This refutes the proposed
weighted-lattice restart representation before a common-ball estimate is
even relevant. -/
theorem no_periodicLatticeInitialRepresentation_of_ne_zero
    (u₀ : SchwartzVelocity) (hu₀ : u₀ ≠ 0) :
    ¬ ∃ A : ℝ → WeightedLatticeBanach,
        ∀ x : Space, physicalMildVelocity A 0 x = u₀ x := by
  rintro ⟨A, hA⟩
  exact hu₀
    (schwartzVelocity_eq_zero_of_physicalMildVelocity_slice A le_rfl u₀ hA)

section ContinuousCarrier

variable (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
variable (a : ES → ComplexSpace)
variable (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
variable (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
variable (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
variable (haR : coordinateXm1Mass a ≤ R)
variable (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR)

/-- The exact pointwise continuous-Fourier trajectory associated to a linked
box element.  It is the mild image of the repository's canonical everywhere
representative, matching the pointwise fixed-point interface. -/
def fixedPointTrajectory
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) : ℝ → ES → ComplexSpace :=
  mildImage ν hν a (everywhereRawRepresentative ν T x.1)

/-- Two fixed points in the same completed whole-space linked box determine
the same pointwise mild trajectory.  This consumes the existing Banach
uniqueness theorem; no second fixed-point stack is introduced. -/
theorem fixedPointTrajectory_eq_of_commonBox
    (x y : ActualLinkedBox ν T (2 * R) (2 * R))
    (hx : actualMildSelfMap ν hν T R hT a haM ha ha1 haR L x = x)
    (hy : actualMildSelfMap ν hν T R hT a haM ha ha1 haR L y = y) :
    fixedPointTrajectory ν hν T R a x = fixedPointTrajectory ν hν T R a y := by
  obtain ⟨z, _hz, huniq⟩ :=
    actual_existsUnique_mildFixedPoint ν hν T R hT a haM ha ha1 haR L
  have hxy : x = y := (huniq x hx).trans (huniq y hy).symm
  subst y
  rfl

/-- The smallest physical overlap bridge.  Once two velocity evolutions on a
compact restart slab are represented by fixed points in one common
continuous-Fourier linked box, they agree throughout the slab.  Producing
`hu` and `hv` from the classical PDE is the remaining Duhamel-representation
input; the uniqueness and physical transport are discharged here. -/
theorem velocity_eq_on_Icc_of_commonBox_mildRepresentations
    (u v : VelocityEvolution)
    (x y : ActualLinkedBox ν T (2 * R) (2 * R))
    (hx : actualMildSelfMap ν hν T R hT a haM ha ha1 haR L x = x)
    (hy : actualMildSelfMap ν hν T R hT a haM ha ha1 haR L y = y)
    (hu : ∀ t ∈ Icc (0 : ℝ) T,
      u t = physicalVelocity (fixedPointTrajectory ν hν T R a x) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) T,
      v t = physicalVelocity (fixedPointTrajectory ν hν T R a y) t) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t := by
  have htraj := fixedPointTrajectory_eq_of_commonBox
    ν hν T R hT a haM ha ha1 haR L x y hx hy
  intro t ht
  rw [hu t ht, hv t ht, htraj]

/-! ## Specialization to the actual Fourier transform of a restart trace -/

/-- The Fourier datum of a Schwartz restart trace is strongly measurable in
each coordinate.  This removes the generic datum-measurability premise at the
statement-A carrier. -/
theorem fourierDatum_aestronglyMeasurable (u₀ : SchwartzVelocity) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ : ES => fourierDatum u₀ ξ i) volume := by
  simpa [fourierDatum] using
    ((𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).continuous.aestronglyMeasurable)

/-- The Fourier datum of a Schwartz restart trace has finite homogeneous
`X⁻¹` mass in each coordinate. -/
theorem fourierDatum_integrable_Xm1 (u₀ : SchwartzVelocity) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖fourierDatum u₀ ξ i‖) := by
  simpa [fourierDatum] using
    fourier_schwartz_integrable_Xm1 (euclidComponent u₀ i)

/-- The same Fourier datum has the degree-one moment required by the mild
assembly. -/
theorem fourierDatum_integrable_X1 (u₀ : SchwartzVelocity) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖fourierDatum u₀ ξ i‖) := by
  simpa [fourierDatum] using
    fourier_schwartz_integrable_X1 (euclidComponent u₀ i)

/-- The named source premise is genuinely populated beyond the zero box:
the time-constant trajectory equal to the Fourier datum of any Schwartz
velocity has spacetime `X¹`-integrable self-interaction on every compact
horizon.  This is a strict supplier for `SourceL1X1`, obtained from the
degree-two Schwartz moments through the existing joint source-moment theorem.

It does not discharge the stronger assembly premise quantified over every
element of an `ActualLinkedBox`; a constant Fourier trajectory need not be the
box representative selected by the completed fixed-point carrier. -/
theorem sourceL1X1_constant_fourierDatum (T : ℝ) (u₀ : SchwartzVelocity) :
    SourceL1X1 T (fun _ => fourierDatum u₀) := by
  have hcont (i : Fin 3) : Continuous (fun p : ES × ℝ => fourierDatum u₀ p.1 i) := by
    convert
      ((𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).continuous.comp continuous_fst)
    rfl
  have hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint
        (continuousNavierSource (fun _ => fourierDatum u₀)
          (fun _ => fourierDatum u₀) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))) :=
    continuousNavierSource_joint_aestronglyMeasurable_of_continuous
      (fun _ => fourierDatum u₀) (fun _ => fourierDatum u₀) 0 T hcont hcont
  have hmeas : ∀ s : ℝ, ∀ i : Fin 3,
      AEStronglyMeasurable (fun ξ : ES => fourierDatum u₀ ξ i) volume := by
    intro s i
    simpa [fourierDatum] using
      ((𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).continuous.aestronglyMeasurable)
  have hzero : ∀ s : ℝ, ∀ i : Fin 3,
      Integrable (fun ξ : ES => ‖fourierDatum u₀ ξ i‖) := by
    intro s i
    simpa [fourierDatum] using
      (𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).integrable.norm
  have htwo : ∀ s : ℝ, ∀ i : Fin 3,
      Integrable (fun ξ : ES => ‖ξ‖ ^ (1 + 1) * ‖fourierDatum u₀ ξ i‖) := by
    intro s i
    simpa [fourierDatum] using
      (𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).integrable_pow_mul volume 2
  have hmajor : Integrable (fun _ : ℝ =>
      sourceMomentMajorant 1 (fourierDatum u₀) (fourierDatum u₀))
      (volume.restrict (Icc (0 : ℝ) T)) := by
    exact integrableOn_const measure_Icc_lt_top.ne
  intro i
  simpa [SourceL1X1] using
    (integrable_joint_pow_norm_continuousNavierSource_coord 1
      (fun _ => fourierDatum u₀) (fun _ => fourierDatum u₀) 0 T i
      hjoint hmeas hmeas hzero hzero htwo htwo hmajor)

/-- A concrete nonzero Schwartz datum whose constant Fourier trajectory
satisfies `SourceL1X1` on any compact horizon.  This strengthens the prior
zero-box satisfiability witness without asserting the universal box premise. -/
theorem exists_ne_zero_constant_fourierDatum_sourceL1X1 (T : ℝ) :
    ∃ u₀ : SchwartzVelocity, u₀ ≠ 0 ∧
      SourceL1X1 T (fun _ => fourierDatum u₀) := by
  refine ⟨Navier.Analysis.MadelungDecoderCurlObstruction.rotationalDatum 1, ?_,
    sourceL1X1_constant_fourierDatum T _⟩
  exact Navier.Analysis.MadelungDecoderCurlObstruction.rotationalDatum_ne_zero 1 one_ne_zero

/-- The exact critical radius of a restart trace in the continuous
Lei--Lin carrier. -/
def restartRadius (u₀ : SchwartzVelocity) : ℝ :=
  coordinateXm1Mass (fourierDatum u₀)

/-- At time zero the raw mild image is exactly its Fourier datum, independently
of the driving trajectory. -/
theorem fixedPointTrajectory_zero
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    fixedPointTrajectory ν hν T R a x 0 = a := by
  funext ξ i
  simp [fixedPointTrajectory, mildImage,
    Navier.Analysis.ContinuousLeiLinSelfMap.continuousMildImage,
    Navier.Analysis.ContinuousLeiLinDissipation.heatVec,
    heatMode, continuousDuhamel]

/-- For a literal Schwartz Fourier datum, the physical trajectory associated
to every linked-box element has the prescribed restart trace at time zero.
No fixed-point or PDE hypothesis is needed for this initial-time identity. -/
theorem physical_fixedPointTrajectory_fourierDatum_zero
    (u₀ : SchwartzVelocity)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    physicalVelocity
        (fixedPointTrajectory ν hν T R (fourierDatum u₀) x) 0 = u₀ := by
  funext z i
  exact physicalVelocity_fourierDatum u₀
    (fixedPointTrajectory ν hν T R (fourierDatum u₀) x) 0
    (fixedPointTrajectory_zero ν hν T R (fourierDatum u₀) x) z i

/-- The full fixed-point assembly for the Fourier transform of a Schwartz
restart trace.  All generic datum premises and all polarization leaves are
discharged.  The two genuine residuals are exposed in the arguments:

* the critical small-data condition on the actual `X⁻¹` radius, and
* `SourceL1X1` for every representative in the completed common box.
-/
theorem fourierDatumAssemblyLeaves
    (u₀ : SchwartzVelocity)
    (hsmall : restartRadius u₀ ≤ (ν : ℝ) / 16)
    (H : ∀ x : ActualLinkedBox ν T
        (2 * restartRadius u₀) (2 * restartRadius u₀),
      SourceL1X1 T (everywhereRawRepresentative ν T x.1)) :
    MildAssemblyLeaves ν hν T (restartRadius u₀) hT (fourierDatum u₀)
      (fourierDatum_aestronglyMeasurable u₀)
      (fourierDatum_integrable_Xm1 u₀)
      (fourierDatum_integrable_X1 u₀) (by rfl) :=
  mildAssemblyLeaves_of_namedLeaves ν hν T (restartRadius u₀) hT
    (fourierDatum u₀)
    (fourierDatum_aestronglyMeasurable u₀)
    (fourierDatum_integrable_Xm1 u₀)
    (fourierDatum_integrable_X1 u₀) (by rfl) hsmall
    (mildAssemblyTimeLeaves_of_sourceL1X1 ν hν T (restartRadius u₀) hT
      (fourierDatum u₀)
      (fourierDatum_aestronglyMeasurable u₀)
      (fourierDatum_integrable_Xm1 u₀)
      (fourierDatum_integrable_X1 u₀) (by rfl) H)
    (mildPolarizationLeaves_actualBox ν hν T (restartRadius u₀) hT
      (fourierDatum u₀)
      (fourierDatum_aestronglyMeasurable u₀)
      (fourierDatum_integrable_Xm1 u₀)
      (fourierDatum_integrable_X1 u₀) (by rfl))

/-- A small Schwartz restart trace with the named source regularity produces
an actual unique mild fixed point in the continuous whole-space linked box,
and its physical inversion has exactly the prescribed initial velocity.

This removes the generic `MildAssemblyLeaves`, datum measurability and datum
moment premises from the restart interface.  It does not manufacture either
the smallness inequality or `SourceL1X1`. -/
theorem existsUnique_mildFixedPoint_fourierDatum_of_sourceL1X1
    (u₀ : SchwartzVelocity)
    (hsmall : restartRadius u₀ ≤ (ν : ℝ) / 16)
    (H : ∀ x : ActualLinkedBox ν T
        (2 * restartRadius u₀) (2 * restartRadius u₀),
      SourceL1X1 T (everywhereRawRepresentative ν T x.1)) :
    ∃ x : ActualLinkedBox ν T
        (2 * restartRadius u₀) (2 * restartRadius u₀),
      actualMildSelfMap ν hν T (restartRadius u₀) hT (fourierDatum u₀)
          (fourierDatum_aestronglyMeasurable u₀)
          (fourierDatum_integrable_Xm1 u₀)
          (fourierDatum_integrable_X1 u₀) (by rfl)
          (fourierDatumAssemblyLeaves ν hν T hT u₀ hsmall H) x = x ∧
      physicalVelocity
          (fixedPointTrajectory ν hν T (restartRadius u₀)
            (fourierDatum u₀) x) 0 = u₀ ∧
      ∀ y : ActualLinkedBox ν T
          (2 * restartRadius u₀) (2 * restartRadius u₀),
        actualMildSelfMap ν hν T (restartRadius u₀) hT (fourierDatum u₀)
            (fourierDatum_aestronglyMeasurable u₀)
            (fourierDatum_integrable_Xm1 u₀)
            (fourierDatum_integrable_X1 u₀) (by rfl)
            (fourierDatumAssemblyLeaves ν hν T hT u₀ hsmall H) y = y → y = x := by
  obtain ⟨x, hx, huniq⟩ := actual_existsUnique_mildFixedPoint ν hν T
    (restartRadius u₀) hT (fourierDatum u₀)
    (fourierDatum_aestronglyMeasurable u₀)
    (fourierDatum_integrable_Xm1 u₀)
    (fourierDatum_integrable_X1 u₀) (by rfl)
    (fourierDatumAssemblyLeaves ν hν T hT u₀ hsmall H)
  exact ⟨x, hx,
    physical_fixedPointTrajectory_fourierDatum_zero ν hν T (restartRadius u₀)
      u₀ x,
    huniq⟩

end ContinuousCarrier

end Navier.Analysis.WholeSpaceRestartMildInterface

#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.no_periodicLatticeInitialRepresentation_of_ne_zero
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.fixedPointTrajectory_eq_of_commonBox
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.velocity_eq_on_Icc_of_commonBox_mildRepresentations
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.fourierDatum_aestronglyMeasurable
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.fourierDatum_integrable_Xm1
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.fourierDatum_integrable_X1
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.sourceL1X1_constant_fourierDatum
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.exists_ne_zero_constant_fourierDatum_sourceL1X1
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.fixedPointTrajectory_zero
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.physical_fixedPointTrajectory_fourierDatum_zero
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.fourierDatumAssemblyLeaves
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.existsUnique_mildFixedPoint_fourierDatum_of_sourceL1X1

set_option pp.fullNames true in
#check @Navier.Analysis.WholeSpaceRestartMildInterface.sourceL1X1_constant_fourierDatum
set_option pp.fullNames true in
#check @Navier.Analysis.WholeSpaceRestartMildInterface.exists_ne_zero_constant_fourierDatum_sourceL1X1
set_option pp.fullNames true in
#check @Navier.Analysis.WholeSpaceRestartMildInterface.existsUnique_mildFixedPoint_fourierDatum_of_sourceL1X1
set_option pp.fullNames true in
#print axioms Navier.Analysis.WholeSpaceRestartMildInterface.existsUnique_mildFixedPoint_fourierDatum_of_sourceL1X1
