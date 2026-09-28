import Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
import Navier.Analysis.ContinuousLeiLinRecentTailInputs

/-!
# Sufficient spacetime `X¹` moment budget for the actual continuous Navier source

`ContinuousLeiLinMildAssemblyLeaves.SourceL1X1` names the single strengthened
input that upgrades the every-time leaves 2c/2e from `a.e.` to `∀ t ∈ Icc 0 T`:
the `‖ξ‖`-weighted `L¹` integrability of the genuine self-interaction source
over frequency times the causal interval.  This module supplies that input from
a *velocity-side* budget — uniform `X⁰` mass plus a time-integrated `X²` moment
(the `X⁰·X²` allocation of the frequency-triangle split) — so the named input
is discharged, not assumed.

The route is a transport, not a new estimate class: the degree-1 case of the
existing joint moment bridge
`ContinuousLeiLinRecentTailJoint.integrable_joint_pow_norm_continuousNavierSource_coord`
(`‖ξ‖ ^ 1` weight, both profiles carrying degree `1 + 1 = 2`) with its
time-majorant hypothesis supplied by a new degree-1 instance of the
`RecentTailInputs` majorant pattern — the existing file carries only degree 0
(uniform `X⁰`, integrable `X¹`).

Satisfiability is inherited, not asserted abstractly: `v = 0` has every
hypothesis of the budget (all moment masses vanish), and the leaves file
records the same non-vacuity via the zero box.

Nothing here assumes `SourceL1X1` itself in any hypothesis, and the two
consumption theorems at the end call the existing assembly leaves
`mildTimeLeaf_hmX1_of_sourceL1X1` (2c) and
`mildTimeLeaf_hmX1Time_of_sourceL1X1` (2e) with the budget-supplied input,
verifying the wiring at the consumer.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators Convolution NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinMildFixedPoint
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinRecentTailMoment
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinRecentTailInputs
open Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves

namespace Navier.Analysis.ContinuousLeiLinSourceX1MomentBound

/-- **The degree-1 source-moment time budget.**  The explicit
`sourceMomentMajorant 1` (each input carrying degree `2`, accounting for the
output derivative in the symbol) is time integrable on `[τ, t]` from joint
continuity, uniform `X⁰` masses, and merely *time-integrable* degree-2 moments
— the same shape as the existing degree-0 theorem
`integrable_sourceMomentMajorant_zero_of_continuous_uniformX0_integrableX1`,
with the budget allocation shifted from `X⁰·X¹` to `X⁰·X²`. -/
theorem integrable_sourceMomentMajorant_degree1_of_continuous_uniformX0_integrableX2
    (u v : ℝ → ES → ComplexSpace) (τ t U0 V0 : ℝ)
    (hu : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => u p.2 p.1 j))
    (hv : ∀ i : Fin 3, Continuous (fun p : ES × ℝ => v p.2 p.1 i))
    (hu0 : ∀ s ∈ Icc τ t, coordinateMomentMass 0 (u s) ≤ U0)
    (hv0 : ∀ s ∈ Icc τ t, coordinateMomentMass 0 (v s) ≤ V0)
    (huX2 : Integrable (fun s => coordinateMomentMass 2 (u s))
      (volume.restrict (Icc τ t)))
    (hvX2 : Integrable (fun s => coordinateMomentMass 2 (v s))
      (volume.restrict (Icc τ t))) :
    Integrable (fun s => sourceMomentMajorant 1 (u s) (v s))
      (volume.restrict (Icc τ t)) := by
  let μ : Measure ℝ := volume.restrict (Icc τ t)
  have hU0meas : AEStronglyMeasurable (fun s => coordinateMomentMass 0 (u s)) μ :=
    coordinateMomentMass_aestronglyMeasurable_of_continuous u 0 μ hu
  have hV0meas : AEStronglyMeasurable (fun s => coordinateMomentMass 0 (v s)) μ :=
    coordinateMomentMass_aestronglyMeasurable_of_continuous v 0 μ hv
  have hformula : (fun s => sourceMomentMajorant 1 (u s) (v s)) =
      fun s => (2 : ℝ) * (coordinateMomentMass 2 (u s) * coordinateMomentMass 0 (v s) +
        coordinateMomentMass 0 (u s) * coordinateMomentMass 2 (v s)) := by
    funext s
    rw [sourceMomentMajorant_eq_coordinateMomentMass]
    norm_num
  have hmajorMeas : AEStronglyMeasurable
      (fun s => sourceMomentMajorant 1 (u s) (v s)) μ := by
    rw [hformula]
    exact continuous_const.aestronglyMeasurable.mul
      ((huX2.aestronglyMeasurable.mul hV0meas).add
        (hU0meas.mul hvX2.aestronglyMeasurable))
  have hdom : Integrable (fun s => (2 : ℝ) *
      (coordinateMomentMass 2 (u s) * V0 + U0 * coordinateMomentMass 2 (v s))) μ :=
    ((huX2.mul_const V0).add (hvX2.const_mul U0)).const_mul (2 : ℝ)
  refine hdom.mono' hmajorMeas ?_
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with s hs
  rw [congrFun hformula s]
  have hu2nonneg : 0 ≤ coordinateMomentMass 2 (u s) := coordinateMomentMass_nonneg 2 (u s)
  have hv2nonneg : 0 ≤ coordinateMomentMass 2 (v s) := coordinateMomentMass_nonneg 2 (v s)
  have hu0nonneg : 0 ≤ coordinateMomentMass 0 (u s) := coordinateMomentMass_nonneg 0 (u s)
  have hv0nonneg : 0 ≤ coordinateMomentMass 0 (v s) := coordinateMomentMass_nonneg 0 (v s)
  have hleft : coordinateMomentMass 2 (u s) * coordinateMomentMass 0 (v s) ≤
      coordinateMomentMass 2 (u s) * V0 :=
    mul_le_mul_of_nonneg_left (hv0 s hs) hu2nonneg
  have hright : coordinateMomentMass 0 (u s) * coordinateMomentMass 2 (v s) ≤
      U0 * coordinateMomentMass 2 (v s) :=
    mul_le_mul_of_nonneg_right (hu0 s hs) hv2nonneg
  have hL : 0 ≤ (2 : ℝ) * (coordinateMomentMass 2 (u s) * coordinateMomentMass 0 (v s) +
      coordinateMomentMass 0 (u s) * coordinateMomentMass 2 (v s)) :=
    mul_nonneg two_pos.le (add_nonneg (mul_nonneg hu2nonneg hv0nonneg)
      (mul_nonneg hu0nonneg hv2nonneg))
  simp only [Real.norm_eq_abs, abs_of_nonneg hL]
  exact mul_le_mul_of_nonneg_left (add_le_add hleft hright) two_pos.le

/-- **The sufficient estimate supplying `SourceL1X1`.**  A jointly continuous
frequency trajectory `v` with per-time `X⁰` and `X²` integrability, uniform
`X⁰` mass on `[0, T]`, and a time-integrated `X²` moment satisfies the named
strengthened input `SourceL1X1 T v` of the mild assembly leaves.  The proof is
the degree-1 instance of the existing Tonelli/Fubini joint moment bridge; the
new content is the `X⁰·X²` time budget above, which is what makes the majorant
hypothesis of that bridge dischargeable from velocity-side data.  No
`SourceL1X1`-shaped assumption appears in any hypothesis. -/
theorem sourceL1X1_of_continuous_uniformX0_integrableX2
    (T : ℝ) (v : ℝ → ES → ComplexSpace) (U0 : ℝ)
    (hv : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => v p.2 p.1 j))
    (hv0 : ∀ s j, Integrable (fun η : ES => ‖v s η j‖))
    (hv2 : ∀ s j, Integrable (fun η : ES => ‖η‖ ^ 2 * ‖v s η j‖))
    (hbdd : ∀ s ∈ Icc (0 : ℝ) T, coordinateMomentMass 0 (v s) ≤ U0)
    (hX2 : Integrable (fun s => coordinateMomentMass 2 (v s))
      (volume.restrict (Icc (0 : ℝ) T))) :
    SourceL1X1 T v := by
  have hjoint := continuousNavierSource_joint_aestronglyMeasurable_of_continuous
    v v 0 T hv hv
  have hmeas (s : ℝ) (j : Fin 3) :
      AEStronglyMeasurable (fun η : ES => v s η j) volume :=
    ((hv j).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hmajor := integrable_sourceMomentMajorant_degree1_of_continuous_uniformX0_integrableX2
    v v 0 T U0 U0 hv hv hbdd hbdd hX2 hX2
  intro i
  simpa [pow_one] using
    (integrable_joint_pow_norm_continuousNavierSource_coord 1 v v 0 T i hjoint
      hmeas hmeas hv0 hv0 (fun s j => hv2 s j) (fun s j => hv2 s j) hmajor)

/-- **Consumption at leaf 2c.**  Under the velocity-side budget, the mild
image lies in `X¹` at **every** horizon time — the existing assembly leaf
`mildTimeLeaf_hmX1_of_sourceL1X1` is fed the budget-supplied input rather than
assuming it. -/
theorem mildTimeLeaf_hmX1_of_sourceX1MomentBudget
    (ν : ℝ≥0) (hν : 0 < ν) (T U0 : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (hmM : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, AEStronglyMeasurable
        (fun ξ : ES => mildImage ν hν a v t ξ i) volume)
    (hv : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => v p.2 p.1 j))
    (hv0 : ∀ s j, Integrable (fun η : ES => ‖v s η j‖))
    (hv2 : ∀ s j, Integrable (fun η : ES => ‖η‖ ^ 2 * ‖v s η j‖))
    (hbdd : ∀ s ∈ Icc (0 : ℝ) T, coordinateMomentMass 0 (v s) ≤ U0)
    (hX2 : Integrable (fun s => coordinateMomentMass 2 (v s))
      (volume.restrict (Icc (0 : ℝ) T))) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ i : Fin 3, Integrable (fun ξ : ES =>
      ‖ξ‖ * ‖mildImage ν hν a v t ξ i‖) :=
  mildTimeLeaf_hmX1_of_sourceL1X1 ν hν T a v haM ha1 hmM
    (continuousNavierSource_joint_aestronglyMeasurable_of_continuous v v 0 T hv hv)
    (sourceL1X1_of_continuous_uniformX0_integrableX2 T v U0 hv hv0 hv2 hbdd hX2)

/-- **Consumption at leaf 2e.**  The viscous `X¹`-valued time section of the
horizon-truncated mild image is strongly measurable under the same
velocity-side budget — the existing leaf
`mildTimeLeaf_hmX1Time_of_sourceL1X1` is fed the budget-supplied input. -/
theorem mildTimeLeaf_hmX1Time_of_sourceX1MomentBudget
    (ν : ℝ≥0) (hν : 0 < ν) (T U0 : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (hmM : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, AEStronglyMeasurable
        (fun ξ : ES => mildImage ν hν a v t ξ i) volume)
    (hv : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => v p.2 p.1 j))
    (hv0 : ∀ s j, Integrable (fun η : ES => ‖v s η j‖))
    (hv2 : ∀ s j, Integrable (fun η : ES => ‖η‖ ^ 2 * ‖v s η j‖))
    (hbdd : ∀ s ∈ Icc (0 : ℝ) T, coordinateMomentMass 0 (v s) ≤ U0)
    (hX2 : Integrable (fun s => coordinateMomentMass 2 (v s))
      (volume.restrict (Icc (0 : ℝ) T))) :
    AEStronglyMeasurable
      (viscousX1Section (mildImageIcc ν hν T a v)
        (mildImageIcc_aestronglyMeasurable ν hν T a v hmM)
        (mildImageIcc_integrableX1 ν hν T a v
          (mildTimeLeaf_hmX1_of_sourceX1MomentBudget ν hν T U0 a v haM ha1 hmM
            hv hv0 hv2 hbdd hX2)) ν)
      (leiLinTimeMeasure T) :=
  mildTimeLeaf_hmX1Time_of_sourceL1X1 ν hν T a v haM ha1 hmM
    (continuousNavierSource_joint_aestronglyMeasurable_of_continuous v v 0 T hv hv)
    (sourceL1X1_of_continuous_uniformX0_integrableX2 T v U0 hv hv0 hv2 hbdd hX2)

end Navier.Analysis.ContinuousLeiLinSourceX1MomentBound

#check @Navier.Analysis.ContinuousLeiLinSourceX1MomentBound.sourceL1X1_of_continuous_uniformX0_integrableX2

#print axioms Navier.Analysis.ContinuousLeiLinSourceX1MomentBound.integrable_sourceMomentMajorant_degree1_of_continuous_uniformX0_integrableX2
#print axioms Navier.Analysis.ContinuousLeiLinSourceX1MomentBound.sourceL1X1_of_continuous_uniformX0_integrableX2
#print axioms Navier.Analysis.ContinuousLeiLinSourceX1MomentBound.mildTimeLeaf_hmX1_of_sourceX1MomentBudget
#print axioms Navier.Analysis.ContinuousLeiLinSourceX1MomentBound.mildTimeLeaf_hmX1Time_of_sourceX1MomentBudget
