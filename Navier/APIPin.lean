/-
# Pinned public API surface of the two code-map T0 modules

The code map ranks `Navier/Analysis/ContinuousLeiLinSpace.lean` and
`Navier/Construction/PeriodizedWaveBounds.lean` as T0 change-risk targets, whose
exported names the repository treats as a stable API. This module is that API as
a *test*: it references every top-level name those two modules publish, so a rename,
a removal or an arity change fails `lake build` (and therefore CI) here instead of
silently breaking a downstream consumer.

Two pin strengths, deliberately separated:
* `#check @<name>` pins the NAME and its existence as a top-level declaration.
  Renaming or deleting a pinned declaration is a compile error.
* `example : <type> := <name>` pins the STATED TYPE up to definitional equality.
  Those are written inside the declaring namespace, where the module's own names
  (`ES`, `ComplexSpace`, `convolution`, …) resolve exactly as they do at the site
  that states the type, so the pin text is the source text and not a paraphrase.

Nothing here proves or restates mathematics: every line is a reference to an
existing declaration. No placeholder proof, no new named theorem, no edited proof.

Axiom footprint: the pinned declarations inherit the project census, which CI
enforces transitively over every `Navier` declaration via
`scripts/AuditAllAxioms.lean` against {propext, Classical.choice, Quot.sound}.
-/
import Navier.Analysis.ContinuousLeiLinSpace
import Navier.Construction.PeriodizedWaveBounds

-- The pinned types are written with every binder explicit; no implicit invention.
set_option autoImplicit false

-- Every `example` below only *states* a type, so its binder names are never used in a
-- term position; that is the point of a signature pin, not an oversight.
set_option linter.unusedVariables false

noncomputable section

-- Navier.Analysis.ContinuousLeiLinSpace: 75 source-declared exported names (compiler env under this prefix: 82)
-- ======  #check pins --
#check @Navier.Analysis.ContinuousLeiLinSpace.ES
#check @Navier.Analysis.ContinuousLeiLinSpace.ComplexSpace
#check @Navier.Analysis.ContinuousLeiLinSpace.ComplexE3
#check @Navier.Analysis.ContinuousLeiLinSpace.normXm1
#check @Navier.Analysis.ContinuousLeiLinSpace.normX1
#check @Navier.Analysis.ContinuousLeiLinSpace.normX0_sq_le_normXm1_mul_normX1
#check @Navier.Analysis.ContinuousLeiLinSpace.heatMode
#check @Navier.Analysis.ContinuousLeiLinSpace.continuousLeray
#check @Navier.Analysis.ContinuousLeiLinSpace.continuousLerayE
#check @Navier.Analysis.ContinuousLeiLinSpace.continuous_complexFrequency
#check @Navier.Analysis.ContinuousLeiLinSpace.continuousLeray_norm_le
#check @Navier.Analysis.ContinuousLeiLinSpace.continuousLerayE_norm_le
#check @Navier.Analysis.ContinuousLeiLinSpace.integrable_continuousLerayE_of_aestronglyMeasurable
#check @Navier.Analysis.ContinuousLeiLinSpace.continuousLerayE_aestronglyMeasurable
#check @Navier.Analysis.ContinuousLeiLinSpace.integrable_continuousLerayE
#check @Navier.Analysis.ContinuousLeiLinSpace.continuousLeray_weighted_norm_le
#check @Navier.Analysis.ContinuousLeiLinSpace.convolution
#check @Navier.Analysis.ContinuousLeiLinSpace.normX0
#check @Navier.Analysis.ContinuousLeiLinSpace.normX0_convolution_eq
#check @Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_convolution_integrable
#check @Navier.Analysis.ContinuousLeiLinSpace.schwartz_integrable_norm_inv_mul
#check @Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_Xm1
#check @Navier.Analysis.ContinuousLeiLinSpace.schwartz_integrable_X1
#check @Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_X1
#check @Navier.Analysis.ContinuousLeiLinSpace.heat_contracts_Xm1
#check @Navier.Analysis.ContinuousLeiLinSpace.frequency_triangle
#check @Navier.Analysis.ContinuousLeiLinSpace.frequency_weighted_product_split
#check @Navier.Analysis.ContinuousLeiLinSpace.frequency_weighted_norm_product_split
#check @Navier.Analysis.ContinuousLeiLinSpace.frequency_weighted_convolution_pointwise
#check @Navier.Analysis.ContinuousLeiLinSpace.integrable_left_frequency_kernel
#check @Navier.Analysis.ContinuousLeiLinSpace.integrable_right_frequency_kernel
#check @Navier.Analysis.ContinuousLeiLinSpace.integral_left_frequency_kernel
#check @Navier.Analysis.ContinuousLeiLinSpace.integral_right_frequency_kernel
#check @Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_left_frequency_kernel
#check @Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_right_frequency_kernel
#check @Navier.Analysis.ContinuousLeiLinSpace.integrable_scalar_convolution
#check @Navier.Analysis.ContinuousLeiLinSpace.ae_frequency_weighted_convolution_pointwise
#check @Navier.Analysis.ContinuousLeiLinSpace.integrable_weighted_convolution
#check @Navier.Analysis.ContinuousLeiLinSpace.weighted_convolution_mass_le
#check @Navier.Analysis.ContinuousLeiLinSpace.integrable_weighted_continuousLerayE
#check @Navier.Analysis.ContinuousLeiLinSpace.weighted_continuousLerayE_mass_le
#check @Navier.Analysis.ContinuousLeiLinSpace.norm_complex_convolution_le
#check @Navier.Analysis.ContinuousLeiLinSpace.rawNavierConvection
#check @Navier.Analysis.ContinuousLeiLinSpace.continuousNavierBilinear
#check @Navier.Analysis.ContinuousLeiLinSpace.complexE3PiMeasurableSpace_eq_borel
#check @Navier.Analysis.ContinuousLeiLinSpace.complexE3EuclideanMeasurableSpace_eq_borel
#check @Navier.Analysis.ContinuousLeiLinSpace.complexE3_measurableSpace_coherent
#check @Navier.Analysis.ContinuousLeiLinSpace.esPiMeasurableSpace_eq_borel
#check @Navier.Analysis.ContinuousLeiLinSpace.esEuclideanMeasurableSpace_eq_borel
#check @Navier.Analysis.ContinuousLeiLinSpace.es_measurableSpace_coherent
#check @Navier.Analysis.ContinuousLeiLinSpace.euclidean_norm_le_coordinate_sum
#check @Navier.Analysis.ContinuousLeiLinSpace.navier_frequency_factor_le
#check @Navier.Analysis.ContinuousLeiLinSpace.continuousNavierBilinear_majorant
#check @Navier.Analysis.ContinuousLeiLinSpace.inv_mul_derivative_le
#check @Navier.Analysis.ContinuousLeiLinSpace.normXm1_continuousNavierBilinear_pointwise
#check @Navier.Analysis.ContinuousLeiLinSpace.continuousNavierBilinear_aestronglyMeasurable
#check @Navier.Analysis.ContinuousLeiLinSpace.integrable_normXm1_continuousNavierBilinear
#check @Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_coordinate_aestronglyMeasurable
#check @Navier.Analysis.ContinuousLeiLinSpace.normXm1_continuousNavierBilinear_mass_le
#check @Navier.Analysis.ContinuousLeiLinSpace.normXm1_continuousNavierBilinear_mass_le_of_aestronglyMeasurable
#check @Navier.Analysis.ContinuousLeiLinSpace.normXm1_comp_smul
#check @Navier.Analysis.ContinuousLeiLinSpace.normX1_comp_smul
#check @Navier.Analysis.ContinuousLeiLinSpace.normX0_comp_smul
#check @Navier.Analysis.ContinuousLeiLinSpace.parabolicRescale
#check @Navier.Analysis.ContinuousLeiLinSpace.normXm1_parabolicRescale
#check @Navier.Analysis.ContinuousLeiLinSpace.normX0_parabolicRescale
#check @Navier.Analysis.ContinuousLeiLinSpace.normX1_parabolicRescale
#check @Navier.Analysis.ContinuousLeiLinSpace.admissible_parabolicRescale
#check @Navier.Analysis.ContinuousLeiLinSpace.parabolicRescale_heatMode
#check @Navier.Analysis.ContinuousLeiLinSpace.normXm1_heatMode_parabolicRescale
#check @Navier.Analysis.ContinuousLeiLinSpace.complexE3EuclideanMeasurableSpace
#check @Navier.Analysis.ContinuousLeiLinSpace.complexE3PiMeasurableSpace
#check @Navier.Analysis.ContinuousLeiLinSpace.continuousLeray_zero
#check @Navier.Analysis.ContinuousLeiLinSpace.esEuclideanMeasurableSpace
#check @Navier.Analysis.ContinuousLeiLinSpace.esPiMeasurableSpace

-- Navier.Construction.PeriodizedWaveBounds: 138 source-declared exported names (compiler env under this prefix: 193)
-- ======  #check pins --
#check @Navier.Construction.PeriodizedWaveBounds.Cells
#check @Navier.Construction.PeriodizedWaveBounds.LocalJets
#check @Navier.Construction.PeriodizedWaveBounds.jets_eq_of_germ
#check @Navier.Construction.PeriodizedWaveBounds.memClass_of_local_germs
#check @Navier.Construction.PeriodizedWaveBounds.zero_germ_of_support
#check @Navier.Construction.PeriodizedWaveBounds.copySum_germ
#check @Navier.Construction.PeriodizedWaveBounds.copySum_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.copySum_germ_cover
#check @Navier.Construction.PeriodizedWaveBounds.copySum_memClass
#check @Navier.Construction.PeriodizedWaveBounds.copySum_jet_bound
#check @Navier.Construction.PeriodizedWaveBounds.copySum_support
#check @Navier.Construction.PeriodizedWaveBounds.copySum_eventually_finite
#check @Navier.Construction.PeriodizedWaveBounds.copySum_tsupport
#check @Navier.Construction.PeriodizedWaveBounds.copySum_translate
#check @Navier.Construction.PeriodizedWaveBounds.ComplementJets
#check @Navier.Construction.PeriodizedWaveBounds.majorant_mono_constant
#check @Navier.Construction.PeriodizedWaveBounds.memClass_of_local_and_complement_germs
#check @Navier.Construction.PeriodizedWaveBounds.source_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.UniformLocalJets
#check @Navier.Construction.PeriodizedWaveBounds.UniformLocalJets.each
#check @Navier.Construction.PeriodizedWaveBounds.uniform_germ_cover
#check @Navier.Construction.PeriodizedWaveBounds.uniformClass_of_local_germs
#check @Navier.Construction.PeriodizedWaveBounds.copySum_uniformClass
#check @Navier.Construction.PeriodizedWaveBounds.nativeCell_closed
#check @Navier.Construction.PeriodizedWaveBounds.nativeCell_locallyFinite
#check @Navier.Construction.PeriodizedWaveBounds.native_cutoff_support
#check @Navier.Construction.PeriodizedWaveBounds.native_localized_support
#check @Navier.Construction.PeriodizedWaveBounds.periodizedCopies_memClass
#check @Navier.Construction.PeriodizedWaveBounds.finite_le_infty
#check @Navier.Construction.PeriodizedWaveBounds.bilinear_jet_at
#check @Navier.Construction.PeriodizedWaveBounds.LocalJets.of_memClass
#check @Navier.Construction.PeriodizedWaveBounds.LocalJets.map
#check @Navier.Construction.PeriodizedWaveBounds.LocalJets.add
#check @Navier.Construction.PeriodizedWaveBounds.LocalJets.fderiv
#check @Navier.Construction.PeriodizedWaveBounds.LocalJets.bilinear
#check @Navier.Construction.PeriodizedWaveBounds.LocalJets.smul
#check @Navier.Construction.PeriodizedWaveBounds.LocalJets.band_smul
#check @Navier.Construction.PeriodizedWaveBounds.local_gaussian_tail_bound
#check @Navier.Construction.PeriodizedWaveBounds.local_gaussian_all_gains
#check @Navier.Construction.PeriodizedWaveBounds.principal_germ
#check @Navier.Construction.PeriodizedWaveBounds.remainder_germ
#check @Navier.Construction.PeriodizedWaveBounds.curlCorrection_germ
#check @Navier.Construction.PeriodizedWaveBounds.potential_germ
#check @Navier.Construction.PeriodizedWaveBounds.divergence_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGaussian_eq
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_amplitude_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_pressure_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.commonCorrected_amplitude_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.commonCorrected_residual_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localized_amplitude_support
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localized_pressure_support
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localized_zero_germs
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localized_correction_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.corrected_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGood_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localTail_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGood_support
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localTail_support
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.corrected_support
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_zero_germs
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.commonCorrected_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.commonResidual_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGood_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGood_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian_uncovered_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_cancellation
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_classes
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.commonCorrected_class_of_native
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGood_class_of_native
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian_class_of_covered_source
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian_class_with_complement
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian_of_source_zero
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGood_support
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian_support
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.differentialGood_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.differentialGood_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGood_eq_differentialGood
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_inputBounds
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_bounds_from_native
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGaussian_wave_jets
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGaussian_zero_of_cutoff_one
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGaussian_zero_of_fields
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGaussian_all_gains_from_native
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian_all_gains_from_native
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_potential_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_potential_zero_germ
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_realizes_curl
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_divergence_zero
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_amplitude_invariant
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_pressure_invariant
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.commonCorrected_invariant
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian_invariant
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGood_invariant
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common_translate
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian_translate
#check @Navier.Construction.PeriodizedWaveBounds.complexCopyData_common
#check @Navier.Construction.PeriodizedWaveBounds.complexCopyData_common_periodic
#check @Navier.Construction.PeriodizedWaveBounds.complexCopyData_cutoff_support
#check @Navier.Construction.PeriodizedWaveBounds.particularData_eq_complexCopyData
#check @Navier.Construction.PeriodizedWaveBounds.particularData_raw
#check @Navier.Construction.PeriodizedWaveBounds.particularData_source
#check @Navier.Construction.PeriodizedWaveBounds.particularData_frequency
#check @Navier.Construction.PeriodizedWaveBounds.particularData_phase
#check @Navier.Construction.PeriodizedWaveBounds.particularData_cutoff_support
#check @Navier.Construction.PeriodizedWaveBounds.particularData_common
#check @Navier.Construction.PeriodizedWaveBounds.particularData_commonCorrected
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.backgroundOnly
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.commonCorrected
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.corrected
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.cutoffSum
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.differentialGood
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGood
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalTail
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGaussian
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGood
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localTail
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localized
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.raw
#check @Navier.Construction.PeriodizedWaveBounds.along_zero
#check @Navier.Construction.PeriodizedWaveBounds.coefficient_zero
#check @Navier.Construction.PeriodizedWaveBounds.complexCopyData
#check @Navier.Construction.PeriodizedWaveBounds.copySum
#check @Navier.Construction.PeriodizedWaveBounds.curlRemainder_zero
#check @Navier.Construction.PeriodizedWaveBounds.cylindricalCurl_zero
#check @Navier.Construction.PeriodizedWaveBounds.cylindricalDivergence_zero
#check @Navier.Construction.PeriodizedWaveBounds.linearResidual_zero
#check @Navier.Construction.PeriodizedWaveBounds.nativeCell
#check @Navier.Construction.PeriodizedWaveBounds.nativeCells
#check @Navier.Construction.PeriodizedWaveBounds.normalCoefficient_zero
#check @Navier.Construction.PeriodizedWaveBounds.particularData
#check @Navier.Construction.PeriodizedWaveBounds.principal_zero
#check @Navier.Construction.PeriodizedWaveBounds.realizedCoefficient_zero
#check @Navier.Construction.PeriodizedWaveBounds.remainder_zero
#check @Navier.Construction.PeriodizedWaveBounds.vectorPotential_zero

-- Exact-type pins. Section contexts copied from the declaring file so the
-- pinned type resolves in the same scope that states it.

namespace Navier.Analysis.ContinuousLeiLinSpace
open MeasureTheory Set
open scoped FourierTransform SchwartzMap Convolution BigOperators
open Navier.Analysis.FourierWeightedPlancherel
open Navier.Analysis.FourierMajorant
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm

/- pin: ES -/
example : Type := ES

/- pin: ComplexSpace -/
example : Type := ComplexSpace

/- pin: ComplexE3 -/
example : Type := ComplexE3

/- pin: normXm1 -/
example : ∀ (f : ES → ℂ), ℝ := normXm1

/- pin: normX1 -/
example : ∀ (f : ES → ℂ), ℝ := normX1

/- pin: normX0 -/
example : ∀ (f : ES → ℝ), ℝ := normX0

/- pin: heatMode -/
example : ∀ (ν t : ℝ) (f : ES → ℂ) (ξ : ES), ℂ := heatMode

/- pin: continuousLeray -/
example : ∀ (ξ : ES) (z : ComplexSpace), ComplexSpace := continuousLeray

/- pin: continuousLerayE -/
example : ∀ (ξ : ES) (z : ComplexE3), ComplexE3 := continuousLerayE

/- pin: convolution -/
example : ∀ (f g : ES → ℝ), ES → ℝ := convolution

/- pin: rawNavierConvection -/
example : ∀ (u v : ES → ComplexSpace) (ξ : ES), ComplexSpace := rawNavierConvection

/- pin: continuousNavierBilinear -/
example : ∀ (u v : ES → ComplexSpace) (ξ : ES), ComplexSpace := continuousNavierBilinear

/- pin: complexE3_measurableSpace_coherent -/
example : complexE3PiMeasurableSpace = complexE3EuclideanMeasurableSpace := complexE3_measurableSpace_coherent

/- pin: continuousLeray_norm_le -/
example : ∀ (ξ : ES) (z : ComplexSpace), complexEuclideanNorm (continuousLeray ξ z) ≤ complexEuclideanNorm z := continuousLeray_norm_le

/- pin: heat_contracts_Xm1 -/
example : ∀ {ν t : ℝ}, 0 ≤ ν → 0 ≤ t → (f : ES → ℂ) → Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖) → normXm1 (heatMode ν t f) ≤ normXm1 f := heat_contracts_Xm1

/- pin: continuousNavierBilinear_majorant -/
example : ∀ (u v : ES → ComplexSpace) (ξ : ES), complexEuclideanNorm (continuousNavierBilinear u v ξ) ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ * convolution (fun η => ‖u η j‖) (fun η => ‖v η i‖) ξ := continuousNavierBilinear_majorant
example : ∀ (f : ES → ℂ) (c a : ℝ), 0 < a →
    normXm1 (fun ξ => c • f (a • ξ)) = |c| * (a ^ 2)⁻¹ * normXm1 f := normXm1_comp_smul
example : ∀ (lambda : ℝ) (m : ES → ℂ), ES → ℂ := parabolicRescale
example : ∀ (m : ES → ℂ) (nu t lambda : ℝ), 0 < lambda →
    parabolicRescale lambda (heatMode nu t m) =
      heatMode ((lambda ^ 2)⁻¹ * nu) t (parabolicRescale lambda m) := parabolicRescale_heatMode

-- Exact-type pins for the remaining exported names of this module: with these in
-- place, every one of the 75 exported `Navier.Analysis.ContinuousLeiLinSpace`
-- names is pinned to the type the source states, so a signature change (not just a
-- rename or removal) fails `lake build` here. Each `example` below is the declaring
-- line's own binder list prefixed with `∀`, copied from
-- `Navier/Analysis/ContinuousLeiLinSpace.lean` under that file's comment-masking
-- lexer; no proof, statement or existing pin was edited.

/- pin: admissible_parabolicRescale -/
example : ∀ (m : ES → ℂ) (nu lambda : ℝ) (hl : 0 < lambda), normXm1 (parabolicRescale lambda m) + (lambda ^ 2)⁻¹ * nu * normX1 (parabolicRescale lambda m) = normXm1 m + nu * normX1 m := admissible_parabolicRescale

/- pin: ae_frequency_weighted_convolution_pointwise -/
example : ∀ (f g : ES → ℝ) (hf0 : Integrable f) (hg0 : Integrable g) (hf1 : Integrable (fun η => ‖η‖ * f η)) (hg1 : Integrable (fun η => ‖η‖ * g η)) (hfn : ∀ η, 0 ≤ f η) (hgn : ∀ η, 0 ≤ g η), ∀ᵐ ξ : ES, ‖ξ‖ * convolution f g ξ ≤ convolution (fun η => ‖η‖ * f η) g ξ + convolution f (fun η => ‖η‖ * g η) ξ := ae_frequency_weighted_convolution_pointwise

/- pin: complexE3EuclideanMeasurableSpace -/
example : MeasurableSpace ComplexE3 := complexE3EuclideanMeasurableSpace

/- pin: complexE3EuclideanMeasurableSpace_eq_borel -/
example : complexE3EuclideanMeasurableSpace = borel ComplexE3 := complexE3EuclideanMeasurableSpace_eq_borel

/- pin: complexE3PiMeasurableSpace -/
example : MeasurableSpace ComplexE3 := complexE3PiMeasurableSpace

/- pin: complexE3PiMeasurableSpace_eq_borel -/
example : complexE3PiMeasurableSpace = borel ComplexE3 := complexE3PiMeasurableSpace_eq_borel

/- pin: continuousLerayE_aestronglyMeasurable -/
example : ∀ (v : ES → ComplexE3) (hv : AEStronglyMeasurable v), AEStronglyMeasurable (fun ξ => continuousLerayE ξ (v ξ)) := continuousLerayE_aestronglyMeasurable

/- pin: continuousLerayE_norm_le -/
example : ∀ (ξ : ES) (z : ComplexE3), ‖continuousLerayE ξ z‖ ≤ ‖z‖ := continuousLerayE_norm_le

/- pin: continuousLeray_weighted_norm_le -/
example : ∀ (w : ES → ℝ) (ξ : ES) (z : ComplexSpace) (hw : 0 ≤ w ξ), w ξ * complexEuclideanNorm (continuousLeray ξ z) ≤ w ξ * complexEuclideanNorm z := continuousLeray_weighted_norm_le

/- pin: continuousLeray_zero -/
example : ∀ (z : ComplexSpace), continuousLeray 0 z = z := continuousLeray_zero

/- pin: continuousNavierBilinear_aestronglyMeasurable -/
example : ∀ (u v : ES → ComplexSpace) (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j)) (hv : ∀ i : Fin 3, AEStronglyMeasurable (fun η : ES => v η i)) (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) (hv0 : ∀ i : Fin 3, Integrable (fun η : ES => ‖v η i‖)), AEStronglyMeasurable (fun ξ : ES => complexEuclideanPoint (continuousNavierBilinear u v ξ)) := continuousNavierBilinear_aestronglyMeasurable

/- pin: continuous_complexFrequency -/
example : Continuous (complexFrequency : Space → ComplexE3) := continuous_complexFrequency

/- pin: esEuclideanMeasurableSpace -/
example : MeasurableSpace ES := esEuclideanMeasurableSpace

/- pin: esEuclideanMeasurableSpace_eq_borel -/
example : esEuclideanMeasurableSpace = borel ES := esEuclideanMeasurableSpace_eq_borel

/- pin: esPiMeasurableSpace -/
example : MeasurableSpace ES := esPiMeasurableSpace

/- pin: esPiMeasurableSpace_eq_borel -/
example : esPiMeasurableSpace = borel ES := esPiMeasurableSpace_eq_borel

/- pin: es_measurableSpace_coherent -/
example : esPiMeasurableSpace = esEuclideanMeasurableSpace := es_measurableSpace_coherent

/- pin: euclidean_norm_le_coordinate_sum -/
example : ∀ (z : ComplexSpace), complexEuclideanNorm z ≤ ∑ i : Fin 3, ‖z i‖ := euclidean_norm_le_coordinate_sum

/- pin: fourier_schwartz_convolution_integrable -/
example : ∀ (f g : SchwartzMap ES ℂ), Integrable (((𝓕 f : SchwartzMap ES ℂ) : ES → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ((𝓕 g : SchwartzMap ES ℂ) : ES → ℂ)) := fourier_schwartz_convolution_integrable

/- pin: fourier_schwartz_coordinate_aestronglyMeasurable -/
example : ∀ (f : Fin 3 → SchwartzMap ES ℂ) (i : Fin 3), AEStronglyMeasurable (fun ξ : ES => ((𝓕 (f i) : SchwartzMap ES ℂ) : ES → ℂ) ξ) := fourier_schwartz_coordinate_aestronglyMeasurable

/- pin: fourier_schwartz_integrable_X1 -/
example : ∀ (f : SchwartzMap ES ℂ), Integrable (fun ξ : ES => ‖ξ‖ * ‖(𝓕 f) ξ‖) := fourier_schwartz_integrable_X1

/- pin: fourier_schwartz_integrable_Xm1 -/
example : ∀ (f : SchwartzMap ES ℂ), Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖(𝓕 f) ξ‖) := fourier_schwartz_integrable_Xm1

/- pin: fourier_schwartz_integrable_left_frequency_kernel -/
example : ∀ (f g : SchwartzMap ES ℂ), Integrable (fun p : ES × ES => (‖p.2‖ * ‖(𝓕 f) p.2‖) * ‖(𝓕 g) (p.1 - p.2)‖) (volume.prod volume) := fourier_schwartz_integrable_left_frequency_kernel

/- pin: fourier_schwartz_integrable_right_frequency_kernel -/
example : ∀ (f g : SchwartzMap ES ℂ), Integrable (fun p : ES × ES => ‖(𝓕 f) p.2‖ * (‖p.1 - p.2‖ * ‖(𝓕 g) (p.1 - p.2)‖)) (volume.prod volume) := fourier_schwartz_integrable_right_frequency_kernel

/- pin: frequency_triangle -/
example : ∀ (ξ η : ES), ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := frequency_triangle

/- pin: frequency_weighted_convolution_pointwise -/
example : ∀ (f g : ES → ℝ) (hf : ∀ η, 0 ≤ f η) (hg : ∀ η, 0 ≤ g η) (ξ : ES) (hfg : Integrable (fun η : ES => f η * g (ξ - η))) (hl : Integrable (fun η : ES => (‖η‖ * f η) * g (ξ - η))) (hr : Integrable (fun η : ES => f η * (‖ξ - η‖ * g (ξ - η)))), ‖ξ‖ * convolution f g ξ ≤ convolution (fun η => ‖η‖ * f η) g ξ + convolution f (fun η => ‖η‖ * g η) ξ := frequency_weighted_convolution_pointwise

/- pin: frequency_weighted_norm_product_split -/
example : ∀ (f g : ES → ℂ) (ξ η : ES), ‖ξ‖ * (‖f η‖ * ‖g (ξ - η)‖) ≤ (‖η‖ * ‖f η‖) * ‖g (ξ - η)‖ + ‖f η‖ * (‖ξ - η‖ * ‖g (ξ - η)‖) := frequency_weighted_norm_product_split

/- pin: frequency_weighted_product_split -/
example : ∀ (ξ η : ES) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b), ‖ξ‖ * (a * b) ≤ (‖η‖ * a) * b + a * (‖ξ - η‖ * b) := frequency_weighted_product_split

/- pin: integrable_continuousLerayE -/
example : ∀ (v : ES → ComplexE3) (hv : Integrable v), Integrable (fun ξ => continuousLerayE ξ (v ξ)) := integrable_continuousLerayE

/- pin: integrable_continuousLerayE_of_aestronglyMeasurable -/
example : ∀ (v : ES → ComplexE3) (hv_meas : AEStronglyMeasurable (fun ξ => continuousLerayE ξ (v ξ))) (hv : Integrable (fun ξ => ‖v ξ‖)), Integrable (fun ξ => continuousLerayE ξ (v ξ)) := integrable_continuousLerayE_of_aestronglyMeasurable

/- pin: integrable_left_frequency_kernel -/
example : ∀ (f g : ES → ℝ) (hf : Integrable (fun η => ‖η‖ * f η)) (hg : Integrable g), Integrable (fun p : ES × ES => (‖p.2‖ * f p.2) * g (p.1 - p.2)) (volume.prod volume) := integrable_left_frequency_kernel

/- pin: integrable_normXm1_continuousNavierBilinear -/
example : ∀ (u v : ES → ComplexSpace) (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j)) (hv : ∀ i : Fin 3, AEStronglyMeasurable (fun η : ES => v η i)) (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) (hv0 : ∀ i : Fin 3, Integrable (fun η : ES => ‖v η i‖)), Integrable (fun ξ : ES => ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierBilinear u v ξ)) := integrable_normXm1_continuousNavierBilinear

/- pin: integrable_right_frequency_kernel -/
example : ∀ (f g : ES → ℝ) (hf : Integrable f) (hg : Integrable (fun η => ‖η‖ * g η)), Integrable (fun p : ES × ES => f p.2 * (‖p.1 - p.2‖ * g (p.1 - p.2))) (volume.prod volume) := integrable_right_frequency_kernel

/- pin: integrable_scalar_convolution -/
example : ∀ (f g : ES → ℝ) (hf : Integrable f) (hg : Integrable g), Integrable (convolution f g) := integrable_scalar_convolution

/- pin: integrable_weighted_continuousLerayE -/
example : ∀ (v : ES → ComplexE3) (hv : AEStronglyMeasurable v) (hw : Integrable (fun ξ : ES => ‖ξ‖ * ‖v ξ‖)), Integrable (fun ξ : ES => ‖ξ‖ * ‖continuousLerayE ξ (v ξ)‖) := integrable_weighted_continuousLerayE

/- pin: integrable_weighted_convolution -/
example : ∀ (f g : ES → ℝ) (hf0 : Integrable f) (hg0 : Integrable g) (hf1 : Integrable (fun η => ‖η‖ * f η)) (hg1 : Integrable (fun η => ‖η‖ * g η)) (hfn : ∀ η, 0 ≤ f η) (hgn : ∀ η, 0 ≤ g η), Integrable (fun ξ : ES => ‖ξ‖ * convolution f g ξ) := integrable_weighted_convolution

/- pin: integral_left_frequency_kernel -/
example : ∀ (f g : ES → ℝ) (hf : Integrable (fun η => ‖η‖ * f η)) (hg : Integrable g), (∫ p : ES × ES, (‖p.2‖ * f p.2) * g (p.1 - p.2) ∂(volume.prod volume)) = (∫ η : ES, ‖η‖ * f η) * normX0 g := integral_left_frequency_kernel

/- pin: integral_right_frequency_kernel -/
example : ∀ (f g : ES → ℝ) (hf : Integrable f) (hg : Integrable (fun η => ‖η‖ * g η)), (∫ p : ES × ES, f p.2 * (‖p.1 - p.2‖ * g (p.1 - p.2)) ∂(volume.prod volume)) = normX0 f * (∫ η : ES, ‖η‖ * g η) := integral_right_frequency_kernel

/- pin: inv_mul_derivative_le -/
example : ∀ (r a : ℝ) (_hr : 0 ≤ r) (ha : 0 ≤ a), r⁻¹ * (r * a) ≤ a := inv_mul_derivative_le

/- pin: navier_frequency_factor_le -/
example : ∀ (ξ : ES) (a : ℂ) (j : Fin 3), ‖(ξ j : ℂ) * a‖ ≤ ‖ξ‖ * ‖a‖ := navier_frequency_factor_le

/- pin: normX0_comp_smul -/
example : ∀ (f : ES → ℝ) (c a : ℝ) (ha : 0 < a), normX0 (fun ξ => c • f (a • ξ)) = c * (a ^ 3)⁻¹ * normX0 f := normX0_comp_smul

/- pin: normX0_convolution_eq -/
example : ∀ (f g : ES → ℝ) (hf : Integrable f) (hg : Integrable g), normX0 (convolution f g) = normX0 f * normX0 g := normX0_convolution_eq

/- pin: normX0_parabolicRescale -/
example : ∀ (m : ES → ℝ) (lambda : ℝ) (hl : 0 < lambda), normX0 (fun ξ => (lambda ^ 2)⁻¹ • m (lambda⁻¹ • ξ)) = lambda * normX0 m := normX0_parabolicRescale

/- pin: normX0_sq_le_normXm1_mul_normX1 -/
example : ∀ (f : ES → ℂ) (hxm1 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖)) (hx1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖f ξ‖)), (∫ ξ : ES, ‖f ξ‖) ^ 2 ≤ normXm1 f * normX1 f := normX0_sq_le_normXm1_mul_normX1

/- pin: normX1_comp_smul -/
example : ∀ (f : ES → ℂ) (c a : ℝ) (ha : 0 < a), normX1 (fun ξ => c • f (a • ξ)) = |c| * (a ^ 4)⁻¹ * normX1 f := normX1_comp_smul

/- pin: normX1_parabolicRescale -/
example : ∀ (m : ES → ℂ) (lambda : ℝ) (hl : 0 < lambda), normX1 (parabolicRescale lambda m) = lambda ^ 2 * normX1 m := normX1_parabolicRescale

/- pin: normXm1_continuousNavierBilinear_mass_le -/
example : ∀ (u v : ES → ComplexSpace) (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) (hv0 : ∀ i : Fin 3, Integrable (fun η : ES => ‖v η i‖)) (hout : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierBilinear u v ξ))), (∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierBilinear u v ξ)) ≤ ∑ i : Fin 3, ∑ j : Fin 3, (∫ η : ES, ‖u η j‖) * (∫ η : ES, ‖v η i‖) := normXm1_continuousNavierBilinear_mass_le

/- pin: normXm1_continuousNavierBilinear_mass_le_of_aestronglyMeasurable -/
example : ∀ (u v : ES → ComplexSpace) (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j)) (hv : ∀ i : Fin 3, AEStronglyMeasurable (fun η : ES => v η i)) (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) (hv0 : ∀ i : Fin 3, Integrable (fun η : ES => ‖v η i‖)), (∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierBilinear u v ξ)) ≤ ∑ i : Fin 3, ∑ j : Fin 3, (∫ η : ES, ‖u η j‖) * (∫ η : ES, ‖v η i‖) := normXm1_continuousNavierBilinear_mass_le_of_aestronglyMeasurable

/- pin: normXm1_continuousNavierBilinear_pointwise -/
example : ∀ (u v : ES → ComplexSpace) (ξ : ES), ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierBilinear u v ξ) ≤ ∑ i : Fin 3, ∑ j : Fin 3, convolution (fun η => ‖u η j‖) (fun η => ‖v η i‖) ξ := normXm1_continuousNavierBilinear_pointwise

/- pin: normXm1_heatMode_parabolicRescale -/
example : ∀ (m : ES → ℂ) (nu t lambda : ℝ) (hl : 0 < lambda), normXm1 (heatMode ((lambda ^ 2)⁻¹ * nu) t (parabolicRescale lambda m)) = normXm1 (heatMode nu t m) := normXm1_heatMode_parabolicRescale

/- pin: normXm1_parabolicRescale -/
example : ∀ (m : ES → ℂ) (lambda : ℝ) (hl : 0 < lambda), normXm1 (parabolicRescale lambda m) = normXm1 m := normXm1_parabolicRescale

/- pin: norm_complex_convolution_le -/
example : ∀ (f g : ES → ℂ) (ξ : ES), ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) ξ‖ ≤ convolution (fun η => ‖f η‖) (fun η => ‖g η‖) ξ := norm_complex_convolution_le

/- pin: schwartz_integrable_X1 -/
example : ∀ (g : SchwartzMap ES ℂ), Integrable (fun ξ : ES => ‖ξ‖ * ‖g ξ‖) := schwartz_integrable_X1

/- pin: schwartz_integrable_norm_inv_mul -/
example : ∀ (g : SchwartzMap ES ℂ), Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖) := schwartz_integrable_norm_inv_mul

/- pin: weighted_continuousLerayE_mass_le -/
example : ∀ (v : ES → ComplexE3) (hv : AEStronglyMeasurable v) (hw : Integrable (fun ξ : ES => ‖ξ‖ * ‖v ξ‖)), (∫ ξ : ES, ‖ξ‖ * ‖continuousLerayE ξ (v ξ)‖) ≤ ∫ ξ : ES, ‖ξ‖ * ‖v ξ‖ := weighted_continuousLerayE_mass_le

/- pin: weighted_convolution_mass_le -/
example : ∀ (f g : ES → ℝ) (hf0 : Integrable f) (hg0 : Integrable g) (hf1 : Integrable (fun η => ‖η‖ * f η)) (hg1 : Integrable (fun η => ‖η‖ * g η)) (hfn : ∀ η, 0 ≤ f η) (hgn : ∀ η, 0 ≤ g η), (∫ ξ : ES, ‖ξ‖ * convolution f g ξ) ≤ (∫ η : ES, ‖η‖ * f η) * (∫ η : ES, g η) + (∫ η : ES, f η) * (∫ η : ES, ‖η‖ * g η) := weighted_convolution_mass_le

end Navier.Analysis.ContinuousLeiLinSpace

-- The `Navier.Construction.PeriodizedWaveBounds` half is name-pinned above and
-- type-pinned for the section-scoped names below. That file states its signatures under
-- seven `section`-scoped `variable` blocks (its own `{D E : Type*}
-- [NormedAddCommGroup D] …` contexts), so a faithful type pin has to re-declare the
-- block that binds the theorem it pins; a re-declared context that differs in binder
-- order is a *different* type, which is why the `variable` block below is copied
-- verbatim and only the pinned names' own section is restated. `Navier.APIPin` is
-- wired into `Navier.lean`'s import closure, and CI runs this module's build plus
-- `scripts/api_pin_census.py` on every push.
/-! ## Type pins for the `Navier.Construction.PeriodizedWaveBounds` half

The name pins above already cover all 108 exported declarations of that module.
The pins below discharge the section-scoped type pins that this file previously
declined as a named follow-up: the `open` lines and the `variable` block are
copied verbatim from the head of that module and from its `LocalGluing` section,
so the type written here is the type the source states it — a re-declared context
with a different binder order would state a different type.  No proof, statement
or existing pin was edited; every line below only references an existing
declaration. -/

namespace Navier.Construction.PeriodizedWaveBounds

open Set Function Filter WeightedClasses
open scoped Topology ContDiff BigOperators

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Type*}

/- pin: finite_le_infty -/
example : ∀ (m : ℕ), (m : WithTop ℕ∞) ≤ ∞ := finite_le_infty

/- pin: jets_eq_of_germ -/
example : ∀ {f g : D → E} {x : D}, f =ᶠ[𝓝 x] g → ∀ (m : ℕ),
    iteratedFDeriv ℝ m f x = iteratedFDeriv ℝ m g x := jets_eq_of_germ

/- pin: zero_germ_of_support -/
example : ∀ {K : Set D}, IsClosed K → ∀ {f : D → E}, support f ⊆ K →
    ∀ {x : D}, x ∉ K → f =ᶠ[𝓝 x] fun _ => 0 := zero_germ_of_support

/- pin: copySum_germ -/
example : ∀ (K : Cells D I) (n : ℕ) (f : I → D → E),
    (∀ i, support (f i) ⊆ K.carrier n i) → ∀ {i : I} {x : D},
      x ∈ K.carrier n i → copySum f =ᶠ[𝓝 x] f i := copySum_germ

/- pin: memClass_of_local_germs -/
example : ∀ {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {K : ℕ → I → Set D}
    {f : ℕ → I → D → E} {F : ℕ → D → E}, (∀ n x, x ∈ s.domain → 0 ≤ w n x) →
    LocalJets s w α K f → (∀ n x, x ∈ s.domain →
      (∃ i, x ∈ K n i ∧ F n =ᶠ[𝓝 x] f n i) ∨ F n =ᶠ[𝓝 x] fun _ => 0) →
    MemClass s w α F := memClass_of_local_germs

end Navier.Construction.PeriodizedWaveBounds

-- Coverage guard: this contract is machine-checked, name by name, against the
-- compiler's own declaration environment: `make api-pin-census`
-- (scripts/api_pin_census.py) runs scripts/ApiEnvCensus.lean, takes every
-- non-internal environment name under the two module prefixes, keeps those the
-- two modules' sources declare (private names are not pinnable), and fails if
-- the `#check` pins above are not exactly that set. Compiler-measured at the
-- commit that closed the grep-census blind spot (measured on leanprover/lean4:v4.35.0-rc4,
-- origin main a72c19b): 213 source-declared names,
-- 213 pinned here — every name pinned, 80 also type-pinned
-- (all 75 exported names of `Navier.Analysis.ContinuousLeiLinSpace`, 5 of
-- `Navier.Construction.PeriodizedWaveBounds`).
-- The previous census `grep -cE '^\s*(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b'`
-- could not match declaration lines whose keyword is preceded by modifiers or
-- attributes (`noncomputable def parabolicRescale`, `@[simp] theorem along_zero`,
-- `@[reducible] def esPiMeasurableSpace`); the compiler census sees them all.
