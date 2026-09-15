import Navier.Problem
import Navier.Analysis.ContinuousLeiLinPhysicalCarrier
import Navier.Analysis.ContinuousLeiLinSelfMap
import Navier.Analysis.ContinuousLeiLinPhysicalVelocity
import Navier.Analysis.ContinuousLeiLinPhysicalODEDomination
import Navier.Analysis.ContinuousLeiLinRecentTailJoint

/-!
# Supply ground-check and the joint window-moment restatement for obligation 1

Wave-1 named `Navier.SatisfiesNavierStokes` (`Problem.lean:148`) as the first
input supplying the travelling premises of
`ContinuousLeiLinPhysicalODEDomination.hasDerivAt_physicalVelocity_continuousMildImage_of_windowMoments`
(§9).  This module records the import-graph verdict and lands the Pattern-A
replacement.

## Verdict: `SatisfiesNavierStokes` carries NONE of the §9 premises

* `SatisfiesNavierStokes ν f u p` is the pointwise physical-space classical
  identity `∂ₜu + (u·∇)u = νΔu − ∇p + f` on `[0,∞) × ℝ³` for
  `u : VelocityEvolution` (physical `Fin 3 → ℝ` coordinates).  It quantifies
  no integral, no measurability, no frequency-side object; the only
  `Integrable` content of `IsClassicalSolution` is `finite_energy`
  (physical-space `L²` of the sup-norm density), which is a sibling field,
  not part of the equation.
* Import graph (mechanically checked on this repo; `lean-lsp` refs are a
  measured false-zero observer here): no file in the `ContinuousLeiLin*`
  family takes `SatisfiesNavierStokes` or `IsClassicalSolution` in any theorem
  signature (docstring roadmap mentions only), and no theorem anywhere
  converts a classical solution into the frequency carrier
  `ℝ → ES → ComplexSpace`.  The constructed map `physicalVelocity` runs the
  opposite direction (frequency → physical), so the §9 conclusion is about
  `physicalVelocity (continuousMildImage ν hν a v)` for a free frequency-side
  trajectory `v` that the classical predicate does not reach.

A physical → frequency `𝓕` bridge for classical solutions is therefore the
first missing primitive *on the statement-A side*.  It is not manufactured
here: §9's premises are weighted `L¹(ξ × s)` joint moments on the Duhamel
carrier, whose actual estate suppliers are the linked-box / recent-tail
machinery, not the pointwise equation.

## Producer table for the §9 premises (the real supply map)

| §9 premise | exact shape | actual producer |
|---|---|---|
| `ha1` | `Integrable (λ ξ => ‖ξ‖ * ‖a ξ i‖)` | **this file**: `integrable_norm_mul_fourierDatum_coord` from a Schwartz datum (statement-A side) |
| `hmeas` | joint a.e.-measurability on `[0,τ]` | `hmeas_of_sliceMeasurability` here, via `ContinuousLeiLinRecentTailJoint.continuousNavierSource_coord_aestronglyMeasurable` |
| `hmeas₁` (bundle field, not a §9 premise) | joint a.e.-measurability on `[τ,t₁]` | `hmeas₁_of_sliceMeasurability` here — the recent-window instance of the same wire; consumed by the obligation-4 fibre package (`ContinuousLeiLinOb4FrequencyODESupply`) |
| `hsrc₀` | joint `X⁻¹` moment on `[0,τ]` | `ContinuousLeiLinBoxB1Joint.integrable_weightedContinuousNavierSource_coord_of_actualBox` (box carrier; needs the joint-measurability leaf of `MildAssemblyLeaves`) |
| `hsrc₁` | joint degree-2 moment on `[τ,t₁]` | `hsrc₁_of_sliceMoments` here, via `ContinuousLeiLinRecentTailJoint.integrable_joint_pow_norm_continuousNavierSource_coord` (demands degree-3 slice moments + `sourceMomentMajorant 2` integrability — beyond the box's `X⁰/X⁻¹/X¹` slots) |
| `hsrc` | pointwise-in-`s` `L¹(ξ)` envelope | **no producer**: measured impossibility from moment estimates (module header of `ContinuousLeiLinPhysicalODEDomination`, `∃`-premise of §9; the `|ξ−s|^(−1/2)` slice family has uniformly bounded `L¹` norms but pointwise-in-`ξ` infinite sup).  Not re-attacked here; kept as an explicit travelling premise whose needed content is genuine pointwise-in-`ξ` time regularity (e.g. an `L¹`-majorized essential-supremum hypothesis). |
| `hw_meas`/`hw_int`/`hdv_meas` | mild-slice measurability/integrability | `ContinuousLeiLinMildAssemblyLeaves` family (horizon-restricted slot fields) |
| `hdv_diff` | frequency-side pointwise ODE | obligation 4: `ContinuousLeiLinFrequencyODE.hasDerivAt_continuousMildImage_coord` under its three `weightedSource` regularity premises (supplier: admissible-ball trajectory continuity + mixed-`X¹`) |

## What this file adds

1. `integrable_norm_mul_fourierDatum_coord` — the `ha1` producer from the
   Schwartz initial datum: the one §9 premise whose producer genuinely lives
   on the statement-A surface (`WholeSpaceGlobalRegularity` quantifies over
   divergence-free `SchwartzVelocity` data).
2. `PhysicalODEWindowSupply` — the Pattern-A replacement hypothesis bundle at
   the joint window-moment level: the three joint-moment premises of §9
   collected as one named carrier whose producers are the estate surfaces
   tabled above (box / recent-tail machinery), *not* `SatisfiesNavierStokes`.
3. `hmeas_of_sliceMeasurability` / `hmeas₁_of_sliceMeasurability` /
   `hsrc₁_of_sliceMoments` — wires turning the existing recent-tail producers
   into bundle fields (`hmeas₁` serves the obligation-4 fibre package).
4. `hasDerivAt_physicalVelocity_continuousMildImage_fourierDatum` — §9
   consumed at `a := fourierDatum u₀` with `ha1` discharged: the obligation-1
   physical pointwise ODE under exactly one named bundle plus the explicitly
   named residuals (`hsrc`, the mild-slice measurability fields, and
   `hdv_diff`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Topology Filter
open scoped FourierTransform Filter
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm (complexEuclideanPoint)
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier (fourierDatum)
open Navier.Analysis.FourierMajorant (euclidComponent)
open Navier.Analysis.ContinuousLeiLinSelfMap (continuousMildImage)
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity
  (physicalVelocity realPhysicalCoord euclidPoint)
open Navier.Analysis.ContinuousLeiLinPhysicalODEDomination

namespace Navier.Analysis.ContinuousLeiLinODEDominationSupply

/-! ## 1. The `ha1` producer: initial-data moment of the Schwartz datum -/

/-- **`ha1` from the statement-A datum.**  For a Schwartz initial velocity
`u₀`, the frequency-side initial datum `fourierDatum u₀` has the degree-1
coordinate moment `∫ ‖ξ‖ ‖fourierDatum u₀ ξ i‖ < ∞`: the Schwartz Fourier
transform is Schwartz and `SchwartzMap.integrable_pow_mul` bounds every
polynomial-weighted mass.  This discharges the `ha1` premise of
`ContinuousLeiLinPhysicalODEDomination` §9 at `a := fourierDatum u₀`. -/
theorem integrable_norm_mul_fourierDatum_coord (u₀ : Navier.SchwartzVelocity)
    (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖fourierDatum u₀ ξ i‖) := by
  set g := euclidComponent u₀ i with hg
  have h := (𝓕 g : SchwartzMap ES ℂ).integrable_pow_mul volume 1
  refine' h.congr ?_
  filter_upwards with ξ
  rw [pow_one, fourierDatum]

/-! ## 2. The replacement hypothesis bundle at the joint window-moment level -/

/-- **The joint window-moment supply bundle.**  This packages exactly the
three spacetime joint-moment premises of §9
(`hasDerivAt_physicalVelocity_continuousMildImage_of_windowMoments`) —
`hmeas`/`hsrc₀` over the strict-past window `[0, τ]` and `hsrc₁` over the
recent window `[τ, t₁]` — together with the recent-window complex
joint-measurability leaf `hmeas₁` that the obligation-4 fibre package needs
(see its field docstring).  Its producers are the estate's linked-box and
recent-tail surfaces (module header table) — the bundle replaces the
wave-1 hypothesis that `SatisfiesNavierStokes` supplies them, which the
import-graph check in the module header refutes.  The remaining §9 premises
are deliberately NOT absorbed into this bundle: `hsrc` is the measured
pointwise-envelope residual (no moment producer exists; see the
`ContinuousLeiLinPhysicalODEDomination` header), and `hdv_diff` is
obligation 4 with its own supplier surface. -/
structure PhysicalODEWindowSupply (v : ℝ → ES → ComplexSpace) (i : Fin 3)
    (τ t₁ : ℝ) : Prop where
  hmeas : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource v v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ)))
  hsrc₀ : Integrable (fun p : ES × ℝ =>
      ‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 i‖)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ)))
  hsrc₁ : Integrable (fun p : ES × ℝ =>
      ‖p.1‖ ^ 2 * ‖continuousNavierSource v v p.2 p.1 i‖)
      (volume.prod (volume.restrict (Icc τ t₁)))
  /-- Joint a.e.-strong measurability of the *complex* source coordinate over
  the recent window `[τ, t₁]`.  Bundle producers already prove it: it is the
  `hmeas` leaf of the same recent-tail slice-moment route that yields `hsrc₁`
  (`hsrc₁_of_sliceMoments` calls
  `ContinuousLeiLinRecentTailJoint.integrable_joint_pow_norm_continuousNavierSource_coord`,
  whose hypotheses give
  `ContinuousLeiLinRecentTailJoint.continuousNavierSource_coord_aestronglyMeasurable`
  over `[τ, t₁]` verbatim; see `hmeas₁_of_sliceMeasurability`).  It is stored
  as a field — not derived — because `hsrc₁` alone is the real-valued norm
  moment and carries no complex-measurability information.
  Obligation-4 consumer: `ContinuousLeiLinOb4FrequencyODESupply` Fubini-slices
  it to per-`ξ` a.e. strong measurability of the fibre source, which is what
  turns fibre `L¹`-norm integrability into `IntervalIntegrable` of the
  complex-valued Duhamel integrand. -/
  hmeas₁ : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource v v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc τ t₁)))

/-- Bundle field `hmeas`: joint Euclidean measurability of the source supplies
every coordinate's joint measurability (recent-tail wire). -/
theorem hmeas_of_sliceMeasurability (v : ℝ → ES → ComplexSpace) (τ : ℝ) (i : Fin 3)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource v v p.2 p.1))
        (volume.prod (volume.restrict (Icc (0 : ℝ) τ)))) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource v v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ))) :=
  continuousNavierSource_coord_aestronglyMeasurable v v 0 τ hjoint i

/-- Bundle field `hmeas₁`: joint Euclidean measurability over the RECENT
window `[τ, t₁]` supplies every coordinate's joint complex measurability over
that window (the recent-window instance of the same wire as
`hmeas_of_sliceMeasurability`). -/
theorem hmeas₁_of_sliceMeasurability (v : ℝ → ES → ComplexSpace) (τ t₁ : ℝ) (i : Fin 3)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource v v p.2 p.1))
        (volume.prod (volume.restrict (Icc τ t₁)))) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource v v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc τ t₁))) :=
  continuousNavierSource_coord_aestronglyMeasurable v v τ t₁ hjoint i

/-- Bundle field `hsrc₁`: the degree-2 joint window moment follows from the
per-slice coordinate `L¹`/degree-3 moments, the joint Euclidean measurability,
and integrability of the fixed-time source-moment majorant over `[τ, t₁]`
(the degree-2 instance of the recent-tail joint bridge). -/
theorem hsrc₁_of_sliceMoments (v : ℝ → ES → ComplexSpace) (τ t₁ : ℝ) (i : Fin 3)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource v v p.2 p.1))
        (volume.prod (volume.restrict (Icc τ t₁))))
    (hvm : ∀ s j, AEStronglyMeasurable (fun η : ES => v s η j))
    (hv0 : ∀ s j, Integrable (fun η : ES => ‖v s η j‖))
    (hv3 : ∀ s j, Integrable (fun η : ES => ‖η‖ ^ 3 * ‖v s η j‖))
    (hmajor : Integrable (fun s => sourceMomentMajorant 2 (v s) (v s))
      (volume.restrict (Icc τ t₁))) :
    Integrable (fun p : ES × ℝ =>
      ‖p.1‖ ^ 2 * ‖continuousNavierSource v v p.2 p.1 i‖)
      (volume.prod (volume.restrict (Icc τ t₁))) :=
  integrable_joint_pow_norm_continuousNavierSource_coord 2 v v τ t₁ i
    hjoint hvm hvm hv0 hv0 hv3 hv3 hmajor

/-! ## 3. §9 consumed at the Schwartz Fourier datum -/

/-- **Obligation 1 at the statement-A datum: §9 consumed from one named
bundle.**  Instantiating
`ContinuousLeiLinPhysicalODEDomination.hasDerivAt_physicalVelocity_continuousMildImage_of_windowMoments`
at `a := fourierDatum u₀` discharges `ha1` by
`integrable_norm_mul_fourierDatum_coord` and reads the joint window moments
from `PhysicalODEWindowSupply`.  The physical velocity of the mild image is
differentiable at `t₀ > 0` with the Navier–Stokes right-hand side (inverted)
as derivative, under exactly: the pointwise-in-time source envelope `hsrc`
(the measured moment-free residual), the mild-slice measurability/integrability
fields `hw_meas`/`hw_int`/`hdv_meas`, and the frequency-side pointwise ODE
`hdv_diff` (obligation 4). -/
theorem hasDerivAt_physicalVelocity_continuousMildImage_fourierDatum
    (ν : ℝ) (hν : 0 < ν) (u₀ : Navier.SchwartzVelocity)
    (v : ℝ → ES → ComplexSpace) (i : Fin 3) (x : Navier.Space)
    (t₀ τ t₁ : ℝ) (ht₀ : 0 < t₀) (hτ : 0 ≤ τ) (hτt : τ < t₀) (ht₀t₁ : t₀ < t₁)
    (sup : PhysicalODEWindowSupply v i τ t₁)
    (hsrc : ∃ u ∈ 𝓝 t₀, ∃ g : ES → ℝ, Integrable g ∧
        ∀ᵐ ξ ∂volume, ∀ s ∈ u, ‖continuousNavierSource v v s ξ i‖ ≤ g ξ)
    (u : Set ℝ) (hu : u ∈ 𝓝 t₀)
    (hw_meas : ∀ᶠ s in 𝓝 t₀,
      AEStronglyMeasurable (fun ξ : ES =>
        continuousMildImage ν hν (fourierDatum u₀) v s ξ i))
    (hw_int : Integrable (fun ξ : ES =>
        continuousMildImage ν hν (fourierDatum u₀) v t₀ ξ i))
    (hdv_meas : AEStronglyMeasurable (fun ξ : ES =>
        -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν (fourierDatum u₀) v t₀ ξ i
          + continuousNavierSource v v t₀ ξ i))
    (hdv_diff : ∀ᵐ ξ ∂volume, ∀ s ∈ u,
        HasDerivAt (fun r : ℝ => continuousMildImage ν hν (fourierDatum u₀) v r ξ i)
          (-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν (fourierDatum u₀) v s ξ i
            + continuousNavierSource v v s ξ i) s) :
    HasDerivAt (fun s : ℝ =>
        physicalVelocity (continuousMildImage ν hν (fourierDatum u₀) v) s x i)
      (realPhysicalCoord (fun ξ : ES =>
          -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν (fourierDatum u₀) v t₀ ξ
            + continuousNavierSource v v t₀ ξ) i (euclidPoint x)) t₀ :=
  hasDerivAt_physicalVelocity_continuousMildImage_of_windowMoments ν hν
    (fourierDatum u₀) v i x t₀ τ t₁ ht₀ hτ hτt ht₀t₁
    (integrable_norm_mul_fourierDatum_coord u₀ i)
    sup.hmeas sup.hsrc₀ sup.hsrc₁ hsrc u hu hw_meas hw_int hdv_meas hdv_diff

end Navier.Analysis.ContinuousLeiLinODEDominationSupply

