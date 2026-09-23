import Navier.Analysis.WienerMoments
import Navier.Analysis.WienerPointwiseBridge
import Navier.Analysis.ContinuousLeiLinPhysicalCarrier
import Navier.Analysis.WienerSmoothPath

/-!
# Large-data local solutions from Schwartz data on the Wiener carrier

For a Schwartz velocity `u₀` the Fourier datum `wienerDatum u₀ ∈ L¹(ℝ³;ℂ)³`
(coordinates of `ContinuousLeiLinPhysicalCarrier.fourierDatum u₀`) has every
Fourier moment finite (`momV_wienerDatum_ne_top`).  Consequently the Wiener
fixed point on any horizon with `10⁴ T ‖â₀‖² ≤ ν` has every Fourier moment
bounded on the whole horizon, and it is represented by a pointwise fixed
point of `continuousMildImage` with datum `fourierDatum u₀`
(`exists_wienerSchwartzSolution`).

Scope: this is the Fourier-side local solution with all moments.  The
physical-space regularity lift to `CriticalControlDecomposition.SolvesBefore`
is not claimed here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff

namespace Navier.Analysis.WienerSchwartzLocal

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.FourierMajorant
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerLocalMild
open Navier.Analysis.WienerMoments
open Navier.Analysis.WienerPointwiseBridge

/-- The Wiener datum of a Schwartz velocity: the `L¹` classes of the Fourier
coordinates. -/
def wienerDatum (u₀ : Navier.SchwartzVelocity) : V1 := fun i =>
  ((𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).integrable (μ := volume)).toL1 _

theorem coeFn_wienerDatum (u₀ : Navier.SchwartzVelocity) (i : Fin 3) :
    ⇑(wienerDatum u₀ i) =ᵐ[volume] fun ξ => fourierDatum u₀ ξ i :=
  Integrable.coeFn_toL1 _

theorem mom_wienerDatum_ne_top (u₀ : Navier.SchwartzVelocity) (n : ℕ) (i : Fin 3) :
    mom n (wienerDatum u₀ i) ≠ ⊤ := by
  have h := ((𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).integrable_pow_mul volume n)
  have hfin := h.hasFiniteIntegral
  unfold mom
  refine ne_of_lt (lt_of_eq_of_lt ?_ hfin)
  apply lintegral_congr_ae
  filter_upwards [coeFn_wienerDatum u₀ i] with ξ hξ
  rw [hξ, enorm_mul, Real.enorm_eq_ofReal (by positivity), enorm_norm]
  rfl

theorem momV_wienerDatum_ne_top (u₀ : Navier.SchwartzVelocity) (n : ℕ) :
    momV n (wienerDatum u₀) ≠ ⊤ := by
  unfold momV
  exact ENNReal.sum_ne_top.mpr fun i _ => mom_wienerDatum_ne_top u₀ n i

/-- **Large-data local Fourier-side solution from Schwartz data, with every
moment.**  For every `ν > 0`, every Schwartz `u₀` and every horizon with
`10⁴ T ‖wienerDatum u₀‖² ≤ ν`, there are a Wiener path `x` and a pointwise
field `w` such that: `x` solves the mild equation, every Fourier moment of
`x` is bounded on `[0,T]` by `2 m_n e^{γ_n t}`, every time section of `w`
represents `x`, and `w` is a pointwise fixed point of `continuousMildImage`
with datum `fourierDatum u₀` at every time of `[0,T]` and every frequency. -/
theorem exists_wienerSchwartzSolution {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (u₀ : Navier.SchwartzVelocity) (hsmall : 10 ^ 4 * T * ‖wienerDatum u₀‖ ^ 2 ≤ ν) :
    ∃ x : C(Icc (0 : ℝ) T, V1),
      x = heatPath hν (wienerDatum u₀) + duhamelPath hν hT.le x x ∧
      (∀ n : ℕ, x ∈ momSet n (2 * (momV n (wienerDatum u₀)).toReal)
        (momRate ν n (wienerDatum u₀))) ∧
      ∃ w : ℝ → ES → ComplexSpace,
        (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
          (fun ξ => w t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i)) ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ : ES,
          w t ξ = continuousMildImage ν hν (fourierDatum u₀) w t ξ := by
  obtain ⟨x, -, hxeq, hmom⟩ := exists_wienerMildSolution_moments hν hT (wienerDatum u₀) hsmall
  obtain ⟨w, hw, hfix⟩ := exists_pointwise_of_fixedPoint hν hT (wienerDatum u₀) x hxeq
  set a₀' : ES → ComplexSpace := fun ξ i => wienerDatum u₀ i ξ with ha₀'
  have hdat : ∀ᵐ ξ ∂(volume : Measure ES), a₀' ξ = fourierDatum u₀ ξ := by
    filter_upwards [ae_all_iff.mpr (coeFn_wienerDatum u₀)] with ξ h
    funext i
    exact h i
  set w' : ℝ → ES → ComplexSpace := continuousMildImage ν hν (fourierDatum u₀) w with hw'
  have hww : ∀ t ∈ Icc (0 : ℝ) T, w' t =ᵐ[volume] w t := by
    intro t ht
    filter_upwards [hdat] with ξ hξ
    rw [hfix t ht ξ, hw']
    unfold continuousMildImage
    congr 1
    funext i
    unfold Navier.Analysis.ContinuousLeiLinDissipation.heatVec heatMode
    simp only
    rw [← hξ]
  refine ⟨x, hxeq, fun n => hmom n _ ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal (momV_wienerDatum_ne_top u₀ n)).ge, w', ?_, fun t ht ξ => ?_⟩
  · intro t ht i
    filter_upwards [hww t ht, hw t ht i] with ξ h1 h2
    rw [h1]; exact h2
  · have huv : ∀ᵐ s ∂Navier.Analysis.ContinuousLeiLinActualSlots.leiLinTimeMeasure T,
        w' s =ᵐ[volume] w s := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact hww s hs
    rw [Navier.Analysis.ContinuousLeiLinRepresentativeInvariant.continuousMildImage_congr_ae_on_horizon
      ν hν T (fourierDatum u₀) w' w huv t ht ξ]

/-! ## The heat part of a Schwartz datum is a smooth Fourier path -/

theorem integrable_pow_mul_fourierDatum (u₀ : Navier.SchwartzVelocity) (i : Fin 3) (n : ℕ) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ n * ‖fourierDatum u₀ ξ i‖) :=
  (𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).integrable_pow_mul volume n

/-- The heat evolution of each Fourier coordinate of a Schwartz datum, as a
smooth Fourier path on every horizon. -/
def heatSchwartzPath {ν : ℝ} (hν : 0 ≤ ν) (u₀ : Navier.SchwartzVelocity) (i : Fin 3) (T : ℝ) :
    Navier.Analysis.WienerSmoothPath.SmoothFourierPath T :=
  Navier.Analysis.WienerSmoothPath.heatPathSFP hν
    ((𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).continuous.aestronglyMeasurable)
    (integrable_pow_mul_fourierDatum u₀ i) T

/-- **Joint `C^∞` smoothness of the physical heat field of a Schwartz datum on
`[0, T) × ℝ³`,** obtained by consuming `WienerSmoothPath.contDiffOn_phys` at the
heat instance. -/
theorem contDiffOn_heatField {ν T : ℝ} (hν : 0 ≤ ν) (hT : 0 < T)
    (u₀ : Navier.SchwartzVelocity) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ES => 𝓕⁻ (fun ξ =>
        Navier.Analysis.WienerSmoothPath.heatSym ν (fun ξ => fourierDatum u₀ ξ i) 0 0 z.1 ξ) z.2)
      (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) := by
  refine (Navier.Analysis.WienerSmoothPath.contDiffOn_phys hT
    (heatSchwartzPath hν u₀ i T)).congr fun z _ => ?_
  exact Navier.Analysis.WienerSmoothPath.fourierInv_congr
    (Navier.Analysis.WienerSmoothPath.coeFn_heatD hν
      ((𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).continuous.aestronglyMeasurable)
      (integrable_pow_mul_fourierDatum u₀ i) 0 0 z.1).symm z.2

end Navier.Analysis.WienerSchwartzLocal

set_option pp.fullNames true in
#check @Navier.Analysis.WienerSchwartzLocal.exists_wienerSchwartzSolution
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerSchwartzLocal.exists_wienerSchwartzSolution
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerSchwartzLocal.contDiffOn_heatField
