import Navier.Routes.R7.FiniteConvolution

/-!
# Finite-stage viscous Fourier-amplitude dynamics

Under the Fourier convention fixed in `FiniteConvolution`, the unforced
Navier--Stokes amplitude equation has the algebraic right-hand side

`-ν |q|² a(q) - P(q) ∑_{k+l=q} I (l · a(k)) a(l)`.

This file defines that right-hand side over an explicit finite input support.
It proves that the linear term stays on the retained support, the quadratic
term stays on the pairwise Minkowski sum, and their sum therefore stays on
`S ∪ (S+S)`.  It also proves zero-mode and divergence identities under the
explicit modewise divergence-free condition.

This is an instantaneous finite algebraic vector field.  It does not assert
ODE existence, compatibility across infinitely many generations, conjugate
symmetry, an infinite Fourier series, energy conservation, shell summability,
or cascade exclusion.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Routes.R7

open Navier.Analysis.ComplexLerayProjection

/-- Squared real frequency in the repository's coordinate representation. -/
def squaredFrequency (q : Space) : ℝ :=
  q ⬝ᵥ q

/-- Fourier multiplier of the viscous Laplacian in the amplitude RHS. -/
def viscosityMultiplier (ν : ℝ) (q : Space) : ℂ :=
  -((ν * squaredFrequency q : ℝ) : ℂ)

/-- Linear viscous contribution `-ν |q|² a(q)`. -/
def viscousLinearRHS
    (ν : ℝ) (a : Space → ComplexSpace) (q : Space) : ComplexSpace :=
  viscosityMultiplier ν q • a q

/-- Negative Leray-projected finite convection contribution. -/
def finiteProjectedNonlinearRHS
    (support : Finset Space) (a : Space → ComplexSpace)
    (q : Space) : ComplexSpace :=
  -projectedFiniteConvectionCoefficient support a q

/-- Exact finite-stage unforced viscous Fourier-amplitude RHS. -/
def finiteAmplitudeRHS
    (ν : ℝ) (support : Finset Space) (a : Space → ComplexSpace)
    (q : Space) : ComplexSpace :=
  viscousLinearRHS ν a q + finiteProjectedNonlinearRHS support a q

/-- An amplitude table vanishes outside an explicit finite support. -/
def AmplitudeSupportedOn
    (support : Finset Space) (a : Space → ComplexSpace) : Prop :=
  ∀ q, q ∉ support → a q = 0

/-- Every amplitude is complex-bilinearly transverse to its own frequency. -/
def ModewiseDivergenceFree (a : Space → ComplexSpace) : Prop :=
  ∀ q, complexWaveDot q (a q) = 0

/-- Negating the real frequency negates its complex bilinear pairing. -/
theorem complexWaveDot_neg_wave (q : Space) (z : ComplexSpace) :
    complexWaveDot (-q) z = -complexWaveDot q z := by
  simp [complexWaveDot, complexBilinearDot, complexifiedWave,
    Finset.sum_neg_distrib]

/-- Negating the complex amplitude negates its wave pairing. -/
theorem complexWaveDot_neg_amplitude (q : Space) (z : ComplexSpace) :
    complexWaveDot q (-z) = -complexWaveDot q z := by
  simpa only [neg_one_smul, neg_mul, one_mul] using
    complexWaveDot_smul q (-1) z

/-- The wave pairing preserves subtraction of amplitudes. -/
theorem complexWaveDot_sub (q : Space) (z w : ComplexSpace) :
    complexWaveDot q (z - w) = complexWaveDot q z - complexWaveDot q w := by
  rw [sub_eq_add_neg, complexWaveDot_add, complexWaveDot_neg_amplitude]
  rfl

/-- Zero frequency has zero squared frequency. -/
@[simp] theorem squaredFrequency_zero : squaredFrequency 0 = 0 := by
  simp [squaredFrequency]

/-- The viscosity multiplier vanishes at zero frequency. -/
@[simp] theorem viscosityMultiplier_zero_frequency (ν : ℝ) :
    viscosityMultiplier ν 0 = 0 := by
  simp [viscosityMultiplier]

/-- The linear viscous contribution vanishes at zero frequency. -/
@[simp] theorem viscousLinearRHS_zero_frequency
    (ν : ℝ) (a : Space → ComplexSpace) :
    viscousLinearRHS ν a 0 = 0 := by
  simp [viscousLinearRHS]

/-- Under explicit finite-support membership, the viscous term vanishes
outside the retained support. -/
theorem viscousLinearRHS_eq_zero_of_not_mem
    {ν : ℝ} {support : Finset Space} {a : Space → ComplexSpace} {q : Space}
    (ha : AmplitudeSupportedOn support a) (hq : q ∉ support) :
    viscousLinearRHS ν a q = 0 := by
  simp [viscousLinearRHS, ha q hq]

/-- The finite projected nonlinear RHS vanishes outside `S+S`. -/
theorem finiteProjectedNonlinearRHS_eq_zero_of_not_mem_pairwiseMinkowskiSum
    {support : Finset Space} {a : Space → ComplexSpace} {q : Space}
    (hq : q ∉ pairwiseMinkowskiSum support) :
    finiteProjectedNonlinearRHS support a q = 0 := by
  unfold finiteProjectedNonlinearRHS
  rw [projectedFiniteConvectionCoefficient_eq_zero_of_not_mem_pairwiseMinkowskiSum hq]
  exact neg_zero

/-- For an input table supported on `S`, the full finite amplitude RHS
vanishes outside the retained one-step support `S ∪ (S+S)`. -/
theorem finiteAmplitudeRHS_eq_zero_of_not_mem_generatedSupportStep
    {ν : ℝ} {support : Finset Space} {a : Space → ComplexSpace} {q : Space}
    (ha : AmplitudeSupportedOn support a)
    (hq : q ∉ generatedSupportStep support) :
    finiteAmplitudeRHS ν support a q = 0 := by
  have hqSupport : q ∉ support := by
    intro hmem
    exact hq (subset_generatedSupportStep support hmem)
  have hqSum : q ∉ pairwiseMinkowskiSum support := by
    intro hmem
    apply hq
    unfold generatedSupportStep
    exact Finset.mem_union_right support hmem
  unfold finiteAmplitudeRHS
  rw [viscousLinearRHS_eq_zero_of_not_mem ha hqSupport,
    finiteProjectedNonlinearRHS_eq_zero_of_not_mem_pairwiseMinkowskiSum hqSum]
  exact add_zero 0

/-- The finite amplitude RHS maps a table supported on `S` to a table
supported on the retained one-step support `S ∪ (S+S)`. -/
theorem finiteAmplitudeRHS_supportedOn_generatedSupportStep
    {ν : ℝ} {support : Finset Space} {a : Space → ComplexSpace}
    (ha : AmplitudeSupportedOn support a) :
    AmplitudeSupportedOn (generatedSupportStep support)
      (finiteAmplitudeRHS ν support a) := by
  intro q hq
  exact finiteAmplitudeRHS_eq_zero_of_not_mem_generatedSupportStep ha hq

/-- If every input amplitude is transverse to its own frequency, then the
unprojected finite convection coefficient vanishes at zero output. -/
theorem finiteConvectionCoefficient_zero_output
    {support : Finset Space} {a : Space → ComplexSpace}
    (hdiv : ModewiseDivergenceFree a) :
    finiteConvectionCoefficient support a 0 = 0 := by
  classical
  unfold finiteConvectionCoefficient
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hsum : PairSumsToOutput k l 0
  · have hlneg : l = -k := eq_neg_of_add_eq_zero_right hsum
    rw [if_pos hsum]
    simp [orderedConvectionCoefficient, hlneg,
      complexWaveDot_neg_wave, hdiv k]
  · simp [hsum]

/-- The projected finite convection coefficient also vanishes at zero output
under modewise divergence freedom. -/
theorem projectedFiniteConvectionCoefficient_zero_output
    {support : Finset Space} {a : Space → ComplexSpace}
    (hdiv : ModewiseDivergenceFree a) :
    projectedFiniteConvectionCoefficient support a 0 = 0 := by
  unfold projectedFiniteConvectionCoefficient
  rw [finiteConvectionCoefficient_zero_output hdiv]
  exact map_zero (complexLeray 0)

/-- The nonlinear RHS has no zero-frequency contribution under modewise
divergence freedom. -/
theorem finiteProjectedNonlinearRHS_zero_output
    {support : Finset Space} {a : Space → ComplexSpace}
    (hdiv : ModewiseDivergenceFree a) :
    finiteProjectedNonlinearRHS support a 0 = 0 := by
  simp [finiteProjectedNonlinearRHS,
    projectedFiniteConvectionCoefficient_zero_output hdiv]

/-- The full finite viscous amplitude RHS vanishes at zero output under
modewise divergence freedom. -/
theorem finiteAmplitudeRHS_zero_output
    {ν : ℝ} {support : Finset Space} {a : Space → ComplexSpace}
    (hdiv : ModewiseDivergenceFree a) :
    finiteAmplitudeRHS ν support a 0 = 0 := by
  simp [finiteAmplitudeRHS, finiteProjectedNonlinearRHS_zero_output hdiv]

/-- Viscous multiplication preserves modewise transversality. -/
theorem viscousLinearRHS_divergence
    {ν : ℝ} {a : Space → ComplexSpace} {q : Space}
    (hdiv : ModewiseDivergenceFree a) :
    complexWaveDot q (viscousLinearRHS ν a q) = 0 := by
  rw [viscousLinearRHS, complexWaveDot_smul, hdiv q, mul_zero]

/-- The negative projected nonlinear RHS is transverse at every output
frequency, without an input transversality assumption. -/
theorem finiteProjectedNonlinearRHS_divergence
    (support : Finset Space) (a : Space → ComplexSpace) (q : Space) :
    complexWaveDot q (finiteProjectedNonlinearRHS support a q) = 0 := by
  rw [finiteProjectedNonlinearRHS, complexWaveDot_neg_amplitude,
    projectedFiniteConvectionCoefficient_divergence, neg_zero]

/-- The full finite amplitude RHS preserves modewise divergence freedom. -/
theorem finiteAmplitudeRHS_divergence
    {ν : ℝ} {support : Finset Space} {a : Space → ComplexSpace}
    (hdiv : ModewiseDivergenceFree a) (q : Space) :
    complexWaveDot q (finiteAmplitudeRHS ν support a q) = 0 := by
  rw [finiteAmplitudeRHS, complexWaveDot_add,
    viscousLinearRHS_divergence hdiv,
    finiteProjectedNonlinearRHS_divergence, zero_add]

/-- The finite amplitude RHS maps a modewise divergence-free amplitude table
to another modewise divergence-free table. -/
theorem finiteAmplitudeRHS_modewiseDivergenceFree
    {ν : ℝ} {support : Finset Space} {a : Space → ComplexSpace}
    (hdiv : ModewiseDivergenceFree a) :
    ModewiseDivergenceFree (finiteAmplitudeRHS ν support a) :=
  finiteAmplitudeRHS_divergence hdiv

end Navier.Routes.R7
