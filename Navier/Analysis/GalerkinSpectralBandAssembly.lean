import Navier.Analysis.GalerkinSpectralBands
import Navier.Analysis.DivFreeGradientEnstrophy

/-!
# Fourier-band estimates on actual velocity fields

The comparisons here transport the Hilbert-valued Fourier estimate to the
repository's real Schwartz velocities and Euclidean curl energy.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Navier.Analysis.GalerkinSpectralBandAssembly

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity
open Navier.Analysis.DivFreeGradientEnstrophy
open Navier.Analysis.GalerkinSpectralBands

/-- The physical velocity mass agrees exactly with the complex Euclidean
model mass. The coordinate change preserves Lebesgue measure. -/
theorem velocityMass_eq_modelMass (u : SchwartzVelocity) :
    (∫ x : Space, officialEuclideanNorm (u x) ^ 2) =
      ∫ ξ : EuclSpace, ‖euclModel u ξ‖ ^ 2 := by
  rw [integral_space_eq_euclSpace]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [euclModel_apply, norm_realToCx_sq]

/-- A physical `L²` contraction between divergence-free velocities in one
dyadic Fourier band contracts curl energy up to a scale-independent factor
four. Every carrier and integral is the original velocity/curl object. -/
theorem velocity_dyadicBand_curl_energy_le
    (u v : SchwartzVelocity)
    (hu : DivergenceFreeInitial u) (hv : DivergenceFreeInitial v)
    {a : ℝ} (ha : 0 < a)
    (huBand : ∀ ξ, (𝓕 (euclModel u)) ξ ≠ 0 →
      a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * a)
    (hvBand : ∀ ξ, (𝓕 (euclModel v)) ξ ≠ 0 →
      a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * a)
    (hL2 : (∫ x : Space, officialEuclideanNorm (v x) ^ 2) ≤
      ∫ x : Space, officialEuclideanNorm (u x) ^ 2) :
    (∫ x : Space, officialEuclideanNorm (staticCurl v x) ^ 2) ≤
      4 * ∫ x : Space, officialEuclideanNorm (staticCurl u x) ^ 2 := by
  rw [velocityMass_eq_modelMass, velocityMass_eq_modelMass] at hL2
  have h := dyadicBand_L2_contraction_dirichlet
    (euclModel u) (euclModel v) ha huBand hvBand hL2
  rw [curl_sq_eq_fourierWeight_of_divFree u hu,
    curl_sq_eq_fourierWeight_of_divFree v hv]
  nlinarith [mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 4 * Real.pi ^ 2)]

end Navier.Analysis.GalerkinSpectralBandAssembly
