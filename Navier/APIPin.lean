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

-- Navier.Analysis.ContinuousLeiLinSpace: 70 exported declarations (57 theorems/lemmas,
-- 3 abbrev, 9 def, 1 noncomputable def); the 2 private `weight_dilation` theorems are not
-- exported and not pinned. All 70 exported names are pinned below.
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

-- Navier.Construction.PeriodizedWaveBounds: 127 exported declarations (103 theorems/lemmas,
-- 5 structures, 19 noncomputable defs); all 127 names pinned.
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

-- The 19 exported `noncomputable def`s of this module, omitted from the list above by
-- the grep census this file's footer documents as a blind spot, pinned now.
#check @Navier.Construction.PeriodizedWaveBounds.copySum
#check @Navier.Construction.PeriodizedWaveBounds.nativeCell
#check @Navier.Construction.PeriodizedWaveBounds.nativeCells
#check @Navier.Construction.PeriodizedWaveBounds.complexCopyData
#check @Navier.Construction.PeriodizedWaveBounds.particularData
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.raw
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localized
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.corrected
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.common
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGood
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localTail
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.localGaussian
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.commonCorrected
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGood
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.cutoffSum
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalTail
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.globalGaussian
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.backgroundOnly
#check @Navier.Construction.PeriodizedWaveBounds.CopyData.differentialGood

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

end Navier.Analysis.ContinuousLeiLinSpace

-- The `Navier.Construction.PeriodizedWaveBounds` half is name-pinned above but not
-- type-pinned here: that file states its signatures under seven `section`-scoped
-- `variable` blocks (its own `{D E : Type*} [NormedAddCommGroup D] …` contexts), so a
-- faithful type pin has to re-declare the block that binds the theorem it pins, and a
-- re-declared context that differs in binder order is a *different* type. Copying the
-- whole file's header would make this module depend on the module's internals, which is
-- the opposite of an API test. Wiring `Navier.APIPin` into `Navier.lean` and adding those
-- section-scoped type pins is left as the named follow-up; the name pins cover all 127.
/-! ## Type pins for the `Navier.Construction.PeriodizedWaveBounds` half

The name pins above already cover all 127 exported declarations of that module (108 from the
original grep census plus the 19 `noncomputable def` names that census omitted; see the
coverage guard at the end of this file).
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

-- Coverage guard (gap closed at this commit): every exported name of both modules is
-- #check-pinned above -- ContinuousLeiLinSpace 70/70, PeriodizedWaveBounds 127/127;
-- 24 of the pins are type pins. The original generating census was
--   grep -cE '^\s*(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b' <module>
-- with comments masked; it does not match `noncomputable def`, which is 1 export in
-- ContinuousLeiLinSpace (`parabolicRescale`, already pinned by hand) and 19 in
-- PeriodizedWaveBounds -- exactly the 19 names added to the pin list above.
-- The closure measurement is a lexer-masked census (/-- -/ and `--` comments stripped,
-- `noncomputable`/`private`/`protected` prefixes tracked, `namespace`/`end` tracked so
-- `CopyData.*` pins carry their namespace while section-scoped names stay bare as the
-- environment sees them) run name-by-name against the fully qualified references in this
-- file; at 23419d6 it reports 70/70 and 127/127 with zero pinned-not-declared.
-- Residual limitation, disclosed: the census reads source text, not the compiler
-- environment, so it cannot see macro-generated declarations. `lake build` remains the
-- authoritative direction (a renamed, deleted or arity-changed pin fails CI here); the
-- census guards the other direction (an export that has no pin).
