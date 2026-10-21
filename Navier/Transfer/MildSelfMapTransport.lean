import Navier.Transfer.LatticeExtensionTransport
import Navier.Analysis.ContinuousLeiLinBoxD3Output

/-!
# Closure of the declared F-008 residual `MildSelfMapTransport`

`Navier/Transfer/LatticeExtensionTransport.lean` lands the lattice → whole-space
cell extension field by field and declares exactly one obligation it does not
discharge:

```text
MildSelfMapTransport u  :=  ∀ ν > 0 ∀ T,
    Integrable (fun t ↦ coordinateX1Mass (heatVec ν t (latticeExtension u)))
      (volume.restrict (Icc 0 T))
```

Read against its literal statement, the obligation is the TIME-direction
integrability of the FREE-heat `X¹` feed of the transported datum.  It contains
no bilinear term, hence no convolution-vs-extension overlap defect: the defect
class that the landed boundary comment names (`ext(δ_{m+n}) ≠ ext δ_m ⋆ ext δ_n`)
lives in the *symbol*, and at BUDGET level the same file already factors the
bilinear mass exactly (`sum_convolution_eq_coordinateX0Mass_mul`,
`integral_normInv_weightedAmplitude_bilinear_latticeExtension_norm_le ≤
(3‖u‖)(3‖v‖)`).  The declared obligation therefore reduced, once the peer
output-side leaf landed, to one missing hypothesis: per-coordinate `X¹`
integrability of the extension — which the transport file itself supplies
(`integrable_normE_latticeExtensionCoord`).

This file supplies that closure and the two explicit budget legs the peer
mixed-estimate family consumes:

* pointwise-in-time domination `coordinateX1Mass (heatVec ν t (ext u)) ≤
  3·C₁·‖u‖` for `t ≥ 0` (`C₁ = 1 + √3/2`, the landed cell-diameter constant);
* the horizon budget `∫₀^T … ≤ T · 3 · C₁ · ‖u‖`, an `X¹`-only leg that does not
  spend the singular-cell constant `Cm`; it is independent of, and complements,
  the landed dissipation leg `∫₀^t … ≤ ν⁻¹ · 3 · Cm · ‖u‖`
  (`integral_coordinateX1Mass_heatVec_latticeExtension_le`);
* the integrability statement, and the producer for the declared `Prop`.

Honest boundary (unchanged, and NOT closed here): the FULL mild image — heat
plus Duhamel — needs in addition the per-time `X¹` integrability of the
nonlinear source (`hD0` of
`integrable_coordinateX1Mass_continuousMildImage_of_aestronglyMeasurable`).  The
peer majorant `continuousNavierBilinear_majorant` carries one power of the
output frequency, so a datum-level `X¹` feed of the source asks for the
QUADRATIC frequency moment of the profile; `WeightedLatticeBanach` is plain
`ℓ¹` after the weight division and bounds no quadratic moment.  That is the
named carrier boundary of this transport, recorded in this file's companion
witness below.

Peer-owned continuous files are untouched; this file is a consumer of the
`Navier/Transfer/` owner.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Navier.Transfer.LatticeExtensionTransport

open MeasureTheory Set BigOperators Filter Topology
open scoped ENNReal
open Navier
open Navier.Analysis
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.FourierMajorant
open Navier.Analysis.ContinuousLeiLinBoxD3Output

/-! ## Budget leg 1: pointwise-in-time `X¹` domination of the free heat feed -/

/-- Coordinate-free statement of the heat-`X¹` domination at the extension: at
nonnegative time the coordinatewise heat flow does not increase the coordinate
`X¹` mass. -/
theorem coordinateX1Mass_heatVec_latticeExtension_le_datum (u : WeightedLatticeBanach)
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    coordinateX1Mass (heatVec ν t (latticeExtension u)) ≤
      coordinateX1Mass (latticeExtension u) := by
  unfold coordinateX1Mass
  refine Finset.sum_le_sum fun i _ => ?_
  have hcoord : (fun ξ : ES => heatVec ν t (latticeExtension u) ξ i) =
      heatMode ν t (fun ζ : ES => latticeExtension u ζ i) := rfl
  rw [hcoord]
  exact normX1_heatMode_le_of_X1 (fun ζ : ES => latticeExtension u ζ i)
    (integrable_normE_latticeExtensionCoord u i) ν t hν ht

/-- Budget leg 1 (carrier-norm form): the named transported constant. -/
theorem coordinateX1Mass_heatVec_latticeExtension_le (u : WeightedLatticeBanach)
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    coordinateX1Mass (heatVec ν t (latticeExtension u)) ≤ (3 : ℝ) * C1 * ‖u‖ :=
  (coordinateX1Mass_heatVec_latticeExtension_le_datum u ν t hν ht).trans
    (coordinateX1Mass_latticeExtension_le u)

/-! ## Budget leg 2: the horizon `L¹_t X¹` budget at the `X¹` constant alone -/

/-- The Lebesgue measure of `[0, T]`, in `Measure.real` form, is `T` for
`0 ≤ T`. -/
private theorem real_volume_Icc_zero_le (T : ℝ) (hT : 0 ≤ T) :
    Measure.real volume (Icc (0 : ℝ) T) = T := by
  rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), sub_zero]

/-- Budget leg 2: on a nonnegative horizon the free-heat `X¹` feed of the
extension is bounded by `T · 3 · C₁ · ‖u‖`.  This leg spends only the cell
diameter constant `C₁`; the singular-cell constant `Cm` is needed solely by the
dissipation leg `ν⁻¹ · 3 · Cm · ‖u‖`. -/
theorem integral_coordinateX1Mass_heatVec_latticeExtension_le_horizon
    (u : WeightedLatticeBanach) (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T) :
    ∫ t in Icc (0 : ℝ) T, coordinateX1Mass (heatVec ν t (latticeExtension u)) ≤
      T * ((3 : ℝ) * C1 * ‖u‖) := by
  refine calc (∫ t in Icc (0 : ℝ) T,
          coordinateX1Mass (heatVec ν t (latticeExtension u)))
      ≤ ∫ t in Icc (0 : ℝ) T, (3 : ℝ) * C1 * ‖u‖ := ?_
    _ = T * ((3 : ℝ) * C1 * ‖u‖) := by
        rw [setIntegral_const, real_volume_Icc_zero_le T hT, smul_eq_mul]
  -- `integral_mono` asks the pointwise Pi-order hypothesis, which is not
  -- available at negative time (backward heat); the ae-form is the right leg
  -- here, since the domination holds on `Icc 0 T` only.
  refine integral_mono_ae
    (integrable_coordinateX1Mass_heatVec_on_Icc (latticeExtension u)
      (integrable_normE_latticeExtensionCoord u) ν T hν)
    (integrable_const ((3 : ℝ) * C1 * ‖u‖)) ?_
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  exact coordinateX1Mass_heatVec_latticeExtension_le u ν t hν (mem_Icc.mp ht).1

/-! ## Closure of the declared obligation -/

/-- The `X¹` spacetime feed of the transported datum is time-integrable on
every finite horizon, at every diffusivity `ν > 0`: the peer output-side heat
leaf, fed by the extension's own coordinate `X¹` integrability. -/
theorem integrable_coordinateX1Mass_heatVec_latticeExtension (u : WeightedLatticeBanach)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) :
    Integrable (fun t : ℝ => coordinateX1Mass (heatVec ν t (latticeExtension u)))
      (volume.restrict (Icc (0 : ℝ) T)) :=
  integrable_coordinateX1Mass_heatVec_on_Icc (latticeExtension u)
    (integrable_normE_latticeExtensionCoord u) ν T hν

/-- CLOSED (F-008 successor, declared residual of
`Navier/Transfer/LatticeExtensionTransport`): the mild self-map transport holds
for every element of the weighted lattice carrier.  The obligation was the
time-direction integrability of the free-heat `X¹` feed of the cell extension;
its two inputs are the landed coordinate `X¹` integrability
`integrable_normE_latticeExtensionCoord` and the peer heat leaf
`integrable_coordinateX1Mass_heatVec_on_Icc`.  No bilinear premise, no
overlap-defect correction, and no untransported rate statement enters. -/
theorem mildSelfMapTransport (u : WeightedLatticeBanach) : MildSelfMapTransport u :=
  fun ν _hν T => integrable_coordinateX1Mass_heatVec_latticeExtension u ν _hν T

end Navier.Transfer.LatticeExtensionTransport

#print axioms Navier.Transfer.LatticeExtensionTransport.mildSelfMapTransport
#print axioms Navier.Transfer.LatticeExtensionTransport.integrable_coordinateX1Mass_heatVec_latticeExtension
#print axioms Navier.Transfer.LatticeExtensionTransport.integral_coordinateX1Mass_heatVec_latticeExtension_le_horizon
#print axioms Navier.Transfer.LatticeExtensionTransport.coordinateX1Mass_heatVec_latticeExtension_le
