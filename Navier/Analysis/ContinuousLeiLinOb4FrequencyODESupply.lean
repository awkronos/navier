import Navier.Analysis.ContinuousLeiLinODEDominationSupply
import Navier.Analysis.ContinuousLeiLinFrequencyODE
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Obligation 4 supply: the frequency-side pointwise ODE fiber package

`ContinuousLeiLinPhysicalODEDomination` §9 consumes `hdv_diff` — the
`∀ᵐ ξ, ∀ s ∈ u` frequency-side pointwise ODE — and
`ContinuousLeiLinFrequencyODE.hasDerivAt_continuousMildImage_coord` supplies
it fiberwise under three `weightedSource` regularity premises (interval
integrability on `[0, t₀]`, strong measurability at `𝓝 t₀`, continuity at
`t₀`).  This module discharges the interval-integrability premise outright
from the joint window-moment bundle `PhysicalODEWindowSupply` of the companion
supply file, and assembles the full `hdv_diff` family under ONE further named
residual, the fiber continuity of the reweighted source.

## Discharged here: interval integrability (fiberwise, one null set in `ξ`,
## all recent times at once)

`sup.hsrc₀` (joint `X⁻¹` moment on `[0, τ]`) and `sup.hsrc₁` (joint degree-2
moment on `[τ, t₁]`) are `Integrable` over product measures, so
`integrable_prod_iff` Fubini-slices them to per-`ξ` `s`-integrability for
almost every `ξ`; the `ξ`-powers `‖ξ‖⁻¹`, `‖ξ‖²` are constants once `ξ` is
fixed and invertible off the volume-null set `{ξ | ξ = 0}`
(`volume.ae_ne`).  The complex joint measurability `sup.hmeas` /
`sup.hmeas₁` slices via `AEStronglyMeasurable.prodMk_left` to fibre
a.e.-strong measurability on `[0, τ]` and `[τ, t₁]`, which promotes the
norm-integrability to `Integrable` of the complex source
(`integrable_norm_iff`) and glues across `[0, τ] ∪ [τ, s'] = [0, s']`
(`IntegrableOn.union`, `aestronglyMeasurable_union_iff`).  Multiplying by the
`s`-continuous heat scalar `exp (ν‖ξ‖²s)` (`continuousOn_smul`) yields
`IntervalIntegrable (weightedSource ν v v ξ i) volume 0 s'` for EVERY
`s' ∈ (max 0 τ, t₁)` simultaneously outside a single null set — no
time-continuity hypothesis is used.

## Named residual (exact type, supplier named)

`hcont : ∀ᵐ ξ ∂volume, ContinuousOn (weightedSource ν v v ξ i)
    (u ∩ Ioo (max 0 τ) t₁)` — fiber continuity of the reweighted source on an
open time neighbourhood inside the recent window.  At each fibre it supplies
BOTH remaining FrequencyODE premises verbatim:
`ContinuousOn.continuousAt` gives `hG_cont` and
`ContinuousOn.stronglyMeasurableAtFilter` gives `hG_meas`.  Its intended
supplier per the `ContinuousLeiLinFrequencyODE` header is the admissible-ball
trajectory (jointly continuous representative + mixed-`X¹` estimates);
`ContinuousLeiLinMildAssemblyLeaves` records that a general box element's
everywhere representative carries NO joint continuity, so this residual is
exactly the box-side gap (the degree-3 slice moments and degree-2
`sourceMomentMajorant` integrability beyond the box's `X⁰/X⁻¹/X¹` slots, as
named in the `ContinuousLeiLinODEDominationSupply` header table).  This is a
DIFFERENT object from the `hsrc` pointwise-in-time `L¹(ξ)` envelope residual
of §9 (fiber continuity in `s` at fixed `ξ` versus an `L¹`-majorized
essential supremum over `ξ`); the wave-1 slice-level impossibility
measurement for `hsrc` is untouched and not re-attacked here.

**Status (2026-09-19, §5 below):** `hcont` is no longer a travelling
hypothesis on the fixed-point route.  §4 decomposes it into (FC-rep)/(FC-dom)
and §5 DERIVES both from the pointwise mild identity
`v s η = continuousMildImage ν hν a v s η` on the window
(`ae_ContinuousOn_weightedSource_of_mildFixed`), and
`ContinuousLeiLinMildFixedPointPointwise.hcont_fixedPoint` instantiates that
identity at the actual box fixed point of
`actual_existsUnique_mildFixedPoint`.  What now travels at the fixed point is
the window bundle at every coordinate plus the recent-window `X⁻¹` source
moment of its representative (the degree-2 recent moment is the input beyond
the box slots, as the `ContinuousLeiLinODEDominationSupply` header records).

The conclusion is stated over the shrunk neighbourhood
`u ∩ Ioo (max 0 τ) t₁`, which lies in `𝓝 t₀` under `0 ≤ τ`, `0 < t₀`,
`τ < t₀ < t₁` with `u` open and `t₀ ∈ u`, so §9's `hu : u ∈ 𝓝 t₀` and its
neighbourhood intersection transport consume it verbatim — see the glue
theorem at the end of this file, which feeds `hdv_diff` straight into the
obligation-1 physical pointwise ODE.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Topology Filter
open scoped Topology BigOperators
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap (continuousMildImage)
open Navier.Analysis.ContinuousLeiLinFrequencyODE
open Navier.Analysis.ContinuousLeiLinODEDominationSupply
open Navier.Analysis.ComplexLerayProjection (complexLeray)
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier (fourierDatum)
open Navier.Analysis.ContinuousLeiLinDissipation (heatVec)
open Navier.Analysis.FourierMajorant (euclidComponent spaceProj)
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity
  (physicalVelocity realPhysicalCoord euclidPoint)
open scoped FourierTransform

namespace Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply

/-! ## 1. Interval integrability of the reweighted source from the window
bundle -/

/-- **Fiberwise interval integrability of the reweighted source from the
joint window moments.**  For almost every frequency `ξ`, the
`s ↦ exp (ν‖ξ‖²s) • continuousNavierSource v v s ξ i` coordinate is
interval-integrable on `[0, s']` simultaneously for every recent time
`s' ∈ (max 0 τ, t₁)`.  No time-continuity hypothesis is used: the two joint
window moments Fubini-slice to per-`ξ` norm-integrability, the complex joint
measurability slices to fibre a.e.-strong measurability, the two windows glue
on `[0, τ] ∪ [τ, s'] = [0, s']`, and the heat weight is a continuous scalar.
-/
theorem ae_intervalIntegrable_weightedSource_of_windowMoments
    (ν : ℝ) (v : ℝ → ES → ComplexSpace) (i : Fin 3) (τ t₁ : ℝ)
    (hτ : 0 ≤ τ)
    (sup : PhysicalODEWindowSupply v i τ t₁) :
    ∀ᵐ ξ ∂volume, ∀ s' ∈ Ioo (max 0 τ) t₁,
      IntervalIntegrable (weightedSource ν v v ξ i) volume 0 s' := by
  have hs0 : ∀ᵐ ξ ∂volume,
      Integrable (fun s : ℝ => ‖ξ‖⁻¹ * ‖continuousNavierSource v v s ξ i‖)
        (volume.restrict (Icc (0 : ℝ) τ)) :=
    ((integrable_prod_iff sup.hsrc₀.aestronglyMeasurable).mp sup.hsrc₀).1
  have hs1 : ∀ᵐ ξ ∂volume,
      Integrable (fun s : ℝ => ‖ξ‖ ^ 2 * ‖continuousNavierSource v v s ξ i‖)
        (volume.restrict (Icc τ t₁)) :=
    ((integrable_prod_iff sup.hsrc₁.aestronglyMeasurable).mp sup.hsrc₁).1
  have ha0 : ∀ᵐ ξ ∂volume,
      AEStronglyMeasurable (fun s : ℝ => continuousNavierSource v v s ξ i)
        (volume.restrict (Icc (0 : ℝ) τ)) := sup.hmeas.prodMk_left
  have ha1 : ∀ᵐ ξ ∂volume,
      AEStronglyMeasurable (fun s : ℝ => continuousNavierSource v v s ξ i)
        (volume.restrict (Icc τ t₁)) := sup.hmeas₁.prodMk_left
  have hne : ∀ᵐ ξ ∂volume, (ξ : ES) ≠ 0 := volume.ae_ne (0 : ES)
  filter_upwards [hs0, hs1, ha0, ha1, hne] with ξ hpin hpip hA0 hA1 hξ
  intro s' hs'
  have hmax : max 0 τ < s' := hs'.1
  have hs'τ : τ ≤ s' := le_trans (le_max_right 0 τ) hmax.le
  have hs't₁ : s' < t₁ := hs'.2
  have hpos : 0 < s' := lt_of_le_of_lt (le_max_left 0 τ) hmax
  have hn0 : ‖(ξ : ES)‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  -- strict-past window: remove the ‖ξ‖⁻¹ constant
  have hw0 : ∀ w : ℝ, ‖(ξ : ES)‖ * (‖ξ‖⁻¹ * ‖continuousNavierSource v v w ξ i‖) =
      ‖continuousNavierSource v v w ξ i‖ := fun w => by
    rw [← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  have hE : Integrable (fun s : ℝ => ‖continuousNavierSource v v s ξ i‖)
      (volume.restrict (Icc (0 : ℝ) τ)) :=
    (hpin.const_mul ‖(ξ : ES)‖).congr (ae_of_all _ hw0)
  -- recent window: shrink to [τ, s'], remove the ‖ξ‖² constant
  have hn2 : ‖(ξ : ES)‖ ^ 2 ≠ 0 := pow_ne_zero 2 hn0
  have h1 : Integrable (fun s : ℝ => ‖ξ‖ ^ 2 * ‖continuousNavierSource v v s ξ i‖)
      (volume.restrict (Icc τ s')) :=
    hpip.mono_measure (Measure.restrict_mono (Icc_subset_Icc_right hs't₁.le) le_rfl)
  have hw2 : ∀ w : ℝ,
      ((‖(ξ : ES)‖ ^ 2)⁻¹) * (‖ξ‖ ^ 2 * ‖continuousNavierSource v v w ξ i‖) =
        ‖continuousNavierSource v v w ξ i‖ := fun w => by
    rw [← mul_assoc, inv_mul_cancel₀ hn2, one_mul]
  have hR : Integrable (fun s : ℝ => ‖continuousNavierSource v v s ξ i‖)
      (volume.restrict (Icc τ s')) :=
    (h1.const_mul ((‖(ξ : ES)‖ ^ 2)⁻¹)).congr (ae_of_all _ hw2)
  -- glue the norm integrability across [0, τ] ∪ [τ, s'] = [0, s']
  have hU : Icc (0 : ℝ) τ ∪ Icc τ s' = Icc 0 s' := by
    ext x
    simp only [mem_union, mem_Icc]
    constructor
    · rintro (⟨hx0, hxτ⟩ | ⟨hxτ, hxs⟩)
      · exact ⟨hx0, le_trans hxτ hs'τ⟩
      · exact ⟨le_trans hτ hxτ, hxs⟩
    · intro hx
      rcases lt_or_ge x τ with hlt | hge
      · exact Or.inl ⟨hx.1, hlt.le⟩
      · exact Or.inr ⟨hge, hx.2⟩
  have hI : Integrable (fun s : ℝ => ‖continuousNavierSource v v s ξ i‖)
      (volume.restrict (Icc 0 s')) := by
    have hmeas : volume.restrict (Icc (0 : ℝ) τ ∪ Icc τ s') = volume.restrict (Icc 0 s') :=
      congr_arg _ hU
    rw [← hmeas]
    exact IntegrableOn.union hE hR
  -- glue the complex fibre measurability the same way, then promote
  have hAESu : AEStronglyMeasurable (fun s : ℝ => continuousNavierSource v v s ξ i)
      (volume.restrict (Icc (0 : ℝ) τ ∪ Icc τ s')) :=
    aestronglyMeasurable_union_iff.mpr
      ⟨hA0, hA1.mono_measure
        (Measure.restrict_mono (Icc_subset_Icc_right hs't₁.le) le_rfl)⟩
  have hAES : AEStronglyMeasurable (fun s : ℝ => continuousNavierSource v v s ξ i)
      (volume.restrict (Icc 0 s')) :=
    hAESu.mono_measure (by rw [hU])
  have hsrcint : Integrable (fun s : ℝ => continuousNavierSource v v s ξ i)
      (volume.restrict (Icc 0 s')) :=
    (integrable_norm_iff hAES).mp hI
  have hg : IntervalIntegrable (fun s : ℝ => continuousNavierSource v v s ξ i)
      volume 0 s' :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hpos.le).mpr hsrcint
  -- multiply by the continuous heat scalar
  show IntervalIntegrable
    (fun s : ℝ => ((Real.exp (ν * ‖(ξ : ES)‖ ^ 2 * s) : ℝ) : ℂ) •
      continuousNavierSource v v s ξ i) volume 0 s'
  refine' hg.continuousOn_smul ((Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn)

/-- **Obligation 4 assembly.**  At every fibre `ξ` outside one null set and at
every time `s` of the shrunk window neighbourhood `u ∩ Ioo (max 0 τ) t₁`
(`u` open), the mild coordinate satisfies the frequency ODE
`∂ₜ mild = -(ν‖ξ‖²) • mild + source`.  The three `weightedSource` premises of
`hasDerivAt_continuousMildImage_coord` are supplied as: interval integrability
by `ae_intervalIntegrable_weightedSource_of_windowMoments` (pure measure
theory — joint window moments + fibre measurability, no continuity), and
strong measurability at `𝓝 s` plus continuity at `s` by the single named
residual `hcont` (fiber continuity of the reweighted source on the window
neighbourhood) via `ContinuousOn.stronglyMeasurableAtFilter` /
`ContinuousOn.continuousAt`.  A §9 consumer whose `t₀` satisfies
`0 < t₀`, `τ < t₀ < t₁`, `t₀ ∈ u` gets the neighbourhood membership from
`mem_nhds_window`. -/
theorem hdvDiff_of_windowMoments_and_sourceContinuous
    (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace) (i : Fin 3)
    (τ t₁ : ℝ) (hτ : 0 ≤ τ) (u : Set ℝ) (hu : IsOpen u)
    (sup : PhysicalODEWindowSupply v i τ t₁)
    (hcont : ∀ᵐ ξ ∂volume,
      ContinuousOn (weightedSource ν v v ξ i) (u ∩ Ioo (max 0 τ) t₁)) :
    ∀ᵐ ξ ∂volume, ∀ s ∈ u ∩ Ioo (max 0 τ) t₁,
      HasDerivAt (fun r : ℝ => continuousMildImage ν hν a v r ξ i)
        (-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a v s ξ i
          + continuousNavierSource v v s ξ i) s := by
  have key :=
    ae_intervalIntegrable_weightedSource_of_windowMoments ν v i τ t₁ hτ sup
  filter_upwards [key, hcont] with ξ hI hc
  intro s hs
  have hU : IsOpen (u ∩ Ioo (max 0 τ) t₁) := hu.inter isOpen_Ioo
  have hpos : 0 < s := lt_of_le_of_lt (le_max_left 0 τ) hs.2.1
  refine' hasDerivAt_continuousMildImage_coord ν hν a v s hpos ξ i
    (hI s ⟨hs.2.1, hs.2.2⟩)
    (ContinuousOn.stronglyMeasurableAtFilter hU hc s hs)
    (hc.continuousAt (IsOpen.mem_nhds hU hs))

/-- **The shrunk window neighbourhood is a neighbourhood of `t₀`** — the
transport that lets §9's `hu : u ∈ 𝓝 t₀` premise consume the shrunk set
verbatim. -/
theorem mem_nhds_window (τ t₀ t₁ : ℝ) (ht₀ : 0 < t₀) (hτt₀ : τ < t₀) (ht₀t₁ : t₀ < t₁)
    (u : Set ℝ) (hu : IsOpen u) (hut₀ : t₀ ∈ u) :
    u ∩ Ioo (max 0 τ) t₁ ∈ 𝓝 t₀ :=
  IsOpen.mem_nhds (hu.inter isOpen_Ioo) ⟨hut₀, max_lt ht₀ hτt₀, ht₀t₁⟩

/-- **Glue: obligation 4 feeding obligation 1.**  The §9 physical pointwise
ODE at the Schwartz Fourier datum, with the `hdv_diff` premise DISCHARGED
from the window bundle plus the single named fiber-continuity residual
`hcont`; the genuinely-travelling residuals that remain are the `hsrc`
pointwise envelope (measured moment-free residual, not re-attacked), the
mild-slice measurability/integrability fields `hw_meas`/`hw_int`/`hdv_meas`,
and `hcont` itself. -/
theorem hasDerivAt_physicalVelocity_continuousMildImage_fourierDatum_of_sourceContinuous
    (ν : ℝ) (hν : 0 < ν) (u₀ : Navier.SchwartzVelocity)
    (v : ℝ → ES → ComplexSpace) (i : Fin 3) (x : Navier.Space)
    (t₀ τ t₁ : ℝ) (ht₀ : 0 < t₀) (hτ : 0 ≤ τ) (hτt : τ < t₀) (ht₀t₁ : t₀ < t₁)
    (sup : PhysicalODEWindowSupply v i τ t₁)
    (hsrc : ∃ u ∈ 𝓝 t₀, ∃ g : ES → ℝ, Integrable g ∧
        ∀ᵐ ξ ∂volume, ∀ s ∈ u, ‖continuousNavierSource v v s ξ i‖ ≤ g ξ)
    (u : Set ℝ) (hu : IsOpen u) (hut₀ : t₀ ∈ u)
    (hw_meas : ∀ᶠ s in 𝓝 t₀,
      AEStronglyMeasurable (fun ξ : ES =>
        continuousMildImage ν hν (fourierDatum u₀) v s ξ i))
    (hw_int : Integrable (fun ξ : ES =>
        continuousMildImage ν hν (fourierDatum u₀) v t₀ ξ i))
    (hdv_meas : AEStronglyMeasurable (fun ξ : ES =>
        -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν (fourierDatum u₀) v t₀ ξ i
          + continuousNavierSource v v t₀ ξ i))
    (hcont : ∀ᵐ ξ ∂volume,
      ContinuousOn (weightedSource ν v v ξ i) (u ∩ Ioo (max 0 τ) t₁)) :
    HasDerivAt (fun s : ℝ =>
        physicalVelocity (continuousMildImage ν hν (fourierDatum u₀) v) s x i)
      (realPhysicalCoord (fun ξ : ES =>
          -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν (fourierDatum u₀) v t₀ ξ
            + continuousNavierSource v v t₀ ξ) i (euclidPoint x)) t₀ :=
  hasDerivAt_physicalVelocity_continuousMildImage_fourierDatum ν hν u₀ v i x t₀ τ t₁
    ht₀ hτ hτt ht₀t₁ sup hsrc
    (u ∩ Ioo (max 0 τ) t₁)
    (mem_nhds_window τ t₀ t₁ ht₀ hτt ht₀t₁ u hu hut₀)
    hw_meas hw_int hdv_meas
    (hdvDiff_of_windowMoments_and_sourceContinuous ν hν (fourierDatum u₀) v i τ t₁
      hτ u hu sup hcont)

/-! ## 4. The `hcont` residual: named decomposition and first inhabitant -/

/-- **Decomposition of the fiber-continuity residual `hcont`.**  The named
residual `hcont : ∀ᵐ ξ ∂volume, ContinuousOn (weightedSource ν v v ξ i) w` of
this module is DERIVED here from two strictly more local leaves, stated at the
INPUT frequency variable `η` rather than the output `ξ`:

* **(FC-rep)** `∀ᵐ η, ∀ j, ContinuousOn (fun s => v s η j) w` — time-continuity
  of a pointwise representative of the trajectory on the window, almost every
  input frequency, all coordinates at once;
* **(FC-dom)** `∃ M, Integrable M ∧ ∀ᵐ η, ∀ s ∈ w, ∀ j, ‖v s η j‖ ≤ M η` — a
  single time-uniform `L¹(η)` profile majorant on the window;

together with the bare per-slice measurability **(FC-smeas)**
`∀ s ∈ w, ∀ j, AEStronglyMeasurable (fun η => v s η j)` (on the window only).  Mechanism: for almost every
output frequency `ξ`, at each `s₀ ∈ w` the fiberwise filter dominated
convergence theorem (`tendsto_integral_filter_of_dominated_convergence`)
along `𝓝[∩ w] s₀` acts on the convolution integrand
`η ↦ v s η j * v s (ξ - η) k`.  Its dominating function is the shifted profile
product `η ↦ M η * M (ξ - η)`, integrable in `η` for a.e. `ξ` because `M ∈ L¹`
makes `(ξ, η) ↦ M η * M (ξ - η)` product-integrable
(`Integrable.convolution_integrand`, then the first slice of
`integrable_prod_iff` — the same Fubini idiom as §1 above); the pointwise a.e.
limit comes from (FC-rep) transported along the volume-preserving
reflection-translation `η ↦ ξ - η` (`measurePreserving_sub_left volume`); the
heat weight `s ↦ exp (ν‖ξ‖²s)` is a continuous scalar, and the Leray phase is
harmless because `continuousLeray ξ` is a linear map on the finite-dimensional
coordinate carrier.

This retires `hcont` as an unanalyzed hypothesis in two directions.  It names
WHAT the intended supplier ("admissible-ball trajectory: jointly continuous
representative + mixed-`X¹` estimates") must actually deliver — (FC-rep) is
the jointly continuous representative, (FC-dom) its time-uniform `L¹`
domination — and the companion theorem `ae_ContinuousOn_weightedSource_heat`
exhibits a concrete trajectory satisfying all three leaves, so the bundle is
simultaneously satisfiable and the residual is not a disguised impossibility.
Relatedly, `hcont` is NOT invariant under null-set re-prepresentativization of
`v` on the quotient-`L¹` box carriers (modify `v` on one time slice `{s₀}`:
every joint window moment of `PhysicalODEWindowSupply` is unchanged while a
fiber jumps at `s₀`), so no moment/slot-level datum can imply it; the route
this forces is exactly the pointwise-representative class (FC-rep)+(FC-dom). -/
theorem ae_ContinuousOn_weightedSource_of_fiberData
    (ν : ℝ) (v : ℝ → ES → ComplexSpace) (i : Fin 3) (w : Set ℝ)
    (hv_meas : ∀ s ∈ w, ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => v s η j))
    (hv_cont : ∀ᵐ η ∂volume, ∀ j : Fin 3, ContinuousOn (fun s : ℝ => v s η j) w)
    (hdom : ∃ M : ES → ℝ, Integrable M ∧
      ∀ᵐ η ∂volume, ∀ s ∈ w, ∀ j : Fin 3, ‖v s η j‖ ≤ M η) :
    ∀ᵐ ξ ∂volume, ContinuousOn (weightedSource ν v v ξ i) w := by
  obtain ⟨M, hMint, hMmaj⟩ := hdom
  have hpint : Integrable (fun p : ES × ES => M p.2 * M (p.1 - p.2))
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      hMint.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hMint
  have hbound : ∀ᵐ ξ ∂volume, Integrable (fun η : ES => M η * M (ξ - η)) :=
    ((integrable_prod_iff hpint.aestronglyMeasurable).mp hpint).1
  filter_upwards [hbound] with ξ hbound
  have hsubpres : MeasurePreserving (fun η : ES => ξ - η) volume volume :=
    Measure.measurePreserving_sub_left volume ξ
  -- transport the a.e. leaves along the volume-preserving reflection-translation
  have hAEm : AEMeasurable (fun η : ES => ξ - η) volume :=
    (continuous_const.sub continuous_id).aemeasurable
  have transport (p : ES → Prop) (hp : ∀ᵐ η ∂volume, p η) :
      ∀ᵐ η ∂volume, p (ξ - η) := by
    rw [← hsubpres.map_eq] at hp
    exact ae_of_ae_map hAEm hp
  have hcont_shift : ∀ᵐ η ∂volume, ∀ j : Fin 3,
      ContinuousOn (fun s : ℝ => v s (ξ - η) j) w := transport _ hv_cont
  have hMmaj_shift : ∀ᵐ η ∂volume, ∀ s ∈ w, ∀ j : Fin 3,
      ‖v s (ξ - η) j‖ ≤ M (ξ - η) := transport _ hMmaj
  -- fiber continuity of one convolution integrand pair at the output frequency
  have hpair : ∀ j k : Fin 3, ∀ s₀ ∈ w, ContinuousWithinAt
      (fun s : ℝ => ∫ η : ES,
          ContinuousLinearMap.mul ℂ ℂ (v s η j) (v s (ξ - η) k)) w s₀ := by
    intro j k s₀ hs₀
    have hmeas : ∀ s ∈ w, AEStronglyMeasurable
        (fun η : ES => ContinuousLinearMap.mul ℂ ℂ (v s η j) (v s (ξ - η) k)) := by
      intro s hs
      have hg : AEStronglyMeasurable (fun x : ES => v s x k)
          (Measure.map (fun η : ES => ξ - η) volume) := by
        rw [hsubpres.map_eq]
        exact hv_meas s hs k
      exact (hv_meas s hs j).convolution_integrand_snd' (ContinuousLinearMap.mul ℂ ℂ) hg
    refine tendsto_integral_filter_of_dominated_convergence
        (fun η : ES => M η * M (ξ - η)) (eventually_nhdsWithin_of_forall hmeas)
        (eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun s hs =>
          (hMmaj.and hMmaj_shift).mono fun η hη => by
            rw [ContinuousLinearMap.mul_apply', norm_mul]
            exact mul_le_mul (hη.1 s hs j) (hη.2 s hs k) (norm_nonneg _)
              (le_trans (norm_nonneg _) (hη.1 s hs j))))
        hbound
        ((hv_cont.and hcont_shift).mono fun η hc => by
          rw [ContinuousLinearMap.mul_apply']
          exact Tendsto.mul ((hc.1 j).continuousWithinAt hs₀).tendsto
            ((hc.2 k).continuousWithinAt hs₀).tendsto)
  -- assemble the raw convection vector coordinatewise
  have hraw : ∀ s₀ ∈ w, ContinuousWithinAt
      (fun s : ℝ => rawNavierConvection (v s) (v s) ξ) w s₀ := by
    intro s₀ hs₀
    refine continuousWithinAt_pi.mpr fun k => ?_
    show ContinuousWithinAt (fun s : ℝ =>
        ∑ j : Fin 3, (ξ j : ℂ) * ∫ η : ES,
          ContinuousLinearMap.mul ℂ ℂ (v s η j) (v s (ξ - η) k)) w s₀
    refine tendsto_finsetSum Finset.univ fun j _ => Tendsto.mul tendsto_const_nhds
      ((hpair j k s₀ hs₀).tendsto)
  -- the Leray phase is a continuous linear map on the finite-dimensional carrier
  have hsm : Continuous (fun z : ComplexSpace => Complex.I • z) :=
    Continuous.smul (continuous_const : Continuous (fun _ : ComplexSpace => Complex.I))
      continuous_id
  have hleray : Continuous (fun z : ComplexSpace =>
      continuousLeray ξ (Complex.I • z)) :=
    (complexLeray (spaceProj ξ)).continuous_of_finiteDimensional.comp hsm
  have hsrc : ∀ s₀ ∈ w, ContinuousWithinAt
      (fun s : ℝ => continuousNavierSource v v s ξ i) w s₀ := by
    intro s₀ hs₀
    exact (((continuous_apply i).comp hleray).tendsto
        (rawNavierConvection (v s₀) (v s₀) ξ)).comp (hraw s₀ hs₀).tendsto
  -- the heat weight is a continuous scalar
  have hsc : Continuous (fun s : ℝ =>
      ((Real.exp (ν * ‖ξ‖ ^ 2 * s) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  intro s₀ hs₀
  refine Tendsto.mul (Tendsto.mono_left (hsc.tendsto s₀) nhdsWithin_le_nhds)
    (hsrc s₀ hs₀)

/-- **The `hcont` residual is inhabited: the free heat trajectory of a
Schwartz datum satisfies it on every window.**  For
`v := fun s => heatVec ν s (fourierDatum u₀)`, each slice `η ↦ v s η j` is a
continuous Gaussian factor times a Schwartz Fourier coordinate
(continuous, hence a.e.-strongly measurable: FC-smeas); each fiber
`s ↦ v s η j` is `exp (-(ν‖η‖²s))` times a constant, continuous in `s` on all
of `ℝ` (FC-rep); and for `ν > 0`, `s ∈ w ⊆ (0, ∞)` the factor is `≤ 1`, so the
time-uniform profile majorant `M η := ∑ j, ‖fourierDatum u₀ η j‖` — Schwartz,
hence integrable — dominates pointwise a.e. (FC-dom).  This is the first
pointwise trajectory recorded in this repo inhabiting `hcont`; together with
the decomposition it converts the box-side gap measurement (module header of
`ContinuousLeiLinMildAssemblyLeaves`) from "unprovable from slots" into
"provable from the named representative-level leaves". -/
theorem ae_ContinuousOn_weightedSource_heat (ν : ℝ) (hν : 0 < ν)
    (u₀ : Navier.SchwartzVelocity) (i : Fin 3) (w : Set ℝ) (hw : w ⊆ Ioi 0) :
    ∀ᵐ ξ ∂volume, ContinuousOn
      (weightedSource ν (fun s => heatVec ν s (fourierDatum u₀))
        (fun s => heatVec ν s (fourierDatum u₀)) ξ i) w := by
  refine ae_ContinuousOn_weightedSource_of_fiberData ν _ i w ?_ ?_ ?_
  · -- (FC-smeas): continuous Gaussian factor times a Schwartz Fourier coordinate
    intro s _ j
    show AEStronglyMeasurable (fun η : ES =>
        ((Real.exp (-(ν * ‖η‖ ^ 2 * s) : ℝ) : ℂ) * fourierDatum u₀ η j)) volume
    refine Continuous.aestronglyMeasurable (Continuous.mul ?_ ?_)
    · exact Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp
          (((continuous_const.mul (continuous_norm.pow 2)).mul continuous_const).neg))
    · exact (𝓕 (euclidComponent u₀ j) : SchwartzMap ES ℂ).continuous
  · -- (FC-rep): exponential in `s` times a constant, continuous everywhere
    refine ae_of_all volume fun η j => ?_
    show ContinuousOn (fun s : ℝ =>
        ((Real.exp (-(ν * ‖η‖ ^ 2 * s) : ℝ) : ℂ) * fourierDatum u₀ η j)) w
    refine ((Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)))
      |>.mul continuous_const).continuousOn
  · -- (FC-dom): the summed Schwartz profile
    refine ⟨fun η : ES => ∑ j : Fin 3, ‖fourierDatum u₀ η j‖, ?_, ?_⟩
    · refine integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => ?_
      exact ((𝓕 (euclidComponent u₀ j) : SchwartzMap ES ℂ).integrable).norm
    · refine ae_of_all volume fun η s hs j => ?_
      have hs0 : 0 < s := hw hs
      have hexp : Real.exp (-(ν * ‖η‖ ^ 2 * s)) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have h0 : 0 ≤ ν * ‖η‖ ^ 2 * s := by positivity
        linarith
      calc ‖heatVec ν s (fourierDatum u₀) η j‖
          = Real.exp (-(ν * ‖η‖ ^ 2 * s)) * ‖fourierDatum u₀ η j‖ := by
            rw [show heatVec ν s (fourierDatum u₀) η j =
                  ((Real.exp (-(ν * ‖η‖ ^ 2 * s) : ℝ) : ℂ) * fourierDatum u₀ η j) from rfl,
                Complex.norm_mul, Complex.norm_real,
                Real.norm_of_nonneg (Real.exp_pos _).le]
        _ ≤ ‖fourierDatum u₀ η j‖ :=
            by simpa using mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
        _ ≤ ∑ j : Fin 3, ‖fourierDatum u₀ η j‖ :=
            Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

/-- **`hcont` at the free heat trajectory with the exact §9 window shape.**
With `w = u ∩ Ioo (max 0 τ) t₁` — the set occurring verbatim in the `hcont`
hypothesis of `hdvDiff_of_windowMoments_and_sourceContinuous` — the heat
inhabitation applies (the window lies in `Ioi 0` by `max 0 τ < x`).  Feeding
this together with a `PhysicalODEWindowSupply` at the SAME trajectory into
that theorem yields `hdv_diff` at the heat flow; producing the bundle fields
at heat (slice moments + `sourceMomentMajorant 2` integrability) is the
remaining named obligation (see lane NOTES). -/
theorem hcont_heat (ν : ℝ) (hν : 0 < ν) (u₀ : Navier.SchwartzVelocity)
    (i : Fin 3) (τ t₁ : ℝ) (u : Set ℝ) :
    ∀ᵐ ξ ∂volume, ContinuousOn
      (weightedSource ν (fun s => heatVec ν s (fourierDatum u₀))
        (fun s => heatVec ν s (fourierDatum u₀)) ξ i) (u ∩ Ioo (max 0 τ) t₁) :=
  ae_ContinuousOn_weightedSource_heat ν hν u₀ i _
    fun _x hx => lt_of_le_of_lt (le_max_left 0 τ) hx.2.1

/-! ## 5. `hcont` at pointwise mild fixed points: (FC-rep) and (FC-dom) from the
mild identity

The three leaves of §4 are DISCHARGED here for every trajectory that is, on
the window and at almost every input frequency, its own mild image
(`hfix : ∀ᵐ η, ∀ s ∈ w, v s η = continuousMildImage ν hν a v s η`) — the
exact shape a pointwise representative of the box fixed point carries (its
mild image is again a mild image of itself, because the Duhamel source only
reads its input up to spacetime null sets).  No continuity or majorant
hypothesis on `v` enters; both are DERIVED from the mild identity:

* **(FC-rep)** the mild coordinate is `heat + exp(−ν‖η‖²s)·∫₀ˢ weightedSource`
  by the pull-out identity `continuousDuhamel_coord_eq`, and a primitive of an
  interval-integrable function is continuous
  (`intervalIntegral.continuousOn_primitive_interval'`); the interval
  integrability is §1's `ae_intervalIntegrable_weightedSource_of_windowMoments`
  at every coordinate — so time-continuity of the fixed point's fibres is a
  consequence of the joint window moments alone;
* **(FC-dom)** on the shrunk window `w ⊆ (τ', t₁)`, `τ < τ'`, the Duhamel
  coordinate is dominated uniformly in `s` by
  `C·∫₀^τ ‖η‖⁻¹‖src‖ + ∫_τ^{t₁} (‖η‖⁻¹ + ‖η‖²)‖src‖` with
  `C = 1 + (ν(τ'−τ))⁻¹`: on the strict past the heat factor obeys
  `‖η‖·exp(−ν‖η‖²(s−σ)) ≤ C` (`mul_exp_neg_sq_le`, the lag `s − σ ≥ τ' − τ`
  buys one `‖η‖`), and on the recent window `exp ≤ 1` and
  `1 ≤ ‖η‖⁻¹ + ‖η‖²` (`one_le_inv_add_sq`).  Tonelli
  (`Integrable.integral_norm_prod_left`) makes the three fibre integrals
  `L¹(η)` from the joint moments `hsrc₀`, `hsrc₁` and the box-native recent
  `X⁻¹` product moment `hsrcm1`; the heat term is dominated by the datum.

The surviving inputs are therefore: the window bundle at every coordinate,
the recent-window `X⁻¹` source moment (the weight the box slots supply), the
datum's `L¹` mass (free for the Schwartz datum), slice measurability on the
window, and the pointwise mild identity `hfix`.  The residual `hcont` of §2
is no longer a travelling hypothesis on this route. -/

/-- Scalar leaf: with a positive lag `δ ≤ x`, the heat factor buys one power
of the frequency, `r·exp(−ν r² x) ≤ 1 + (νδ)⁻¹`. -/
theorem mul_exp_neg_sq_le (ν δ r x : ℝ) (hν : 0 < ν) (hδ : 0 < δ) (hr : 0 ≤ r)
    (hx : δ ≤ x) :
    r * Real.exp (-(ν * r ^ 2 * x)) ≤ 1 + (ν * δ)⁻¹ := by
  have hνδ : 0 < ν * δ := mul_pos hν hδ
  have hinvnn : 0 ≤ (ν * δ)⁻¹ := (inv_pos.mpr hνδ).le
  have hνr : 0 ≤ ν * r ^ 2 := mul_nonneg hν.le (sq_nonneg r)
  have hexp_le : Real.exp (-(ν * r ^ 2 * x)) ≤ Real.exp (-(ν * δ * r ^ 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hx hνr]
  have hinv : Real.exp (-(ν * δ * r ^ 2)) ≤ (1 + ν * δ * r ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    have hpos : 0 < 1 + ν * δ * r ^ 2 := by positivity
    exact inv_anti₀ hpos (by linarith [Real.add_one_le_exp (ν * δ * r ^ 2)])
  rcases le_or_gt r 1 with h1 | h1
  · have hone : Real.exp (-(ν * r ^ 2 * x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hνr (hδ.le.trans hx)])
    calc r * Real.exp (-(ν * r ^ 2 * x)) ≤ 1 * 1 :=
          mul_le_mul h1 hone (Real.exp_pos _).le zero_le_one
      _ ≤ 1 + (ν * δ)⁻¹ := by linarith
  · have hpos : 0 < 1 + ν * δ * r ^ 2 := by positivity
    calc r * Real.exp (-(ν * r ^ 2 * x))
        ≤ r * (1 + ν * δ * r ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (hexp_le.trans hinv) hr
      _ ≤ (ν * δ)⁻¹ := by
          rw [← div_eq_mul_inv, div_le_iff₀ hpos]
          have hcalc : (ν * δ)⁻¹ * (1 + ν * δ * r ^ 2) = (ν * δ)⁻¹ + r ^ 2 := by
            rw [mul_add, mul_one, ← mul_assoc, inv_mul_cancel₀ hνδ.ne', one_mul]
          rw [hcalc]
          nlinarith
      _ ≤ 1 + (ν * δ)⁻¹ := by linarith

/-- Scalar leaf: `1 ≤ r⁻¹ + r²` for `r > 0`. -/
theorem one_le_inv_add_sq (r : ℝ) (hr : 0 < r) : 1 ≤ r⁻¹ + r ^ 2 := by
  rcases le_or_gt r 1 with h | h
  · have h1 : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr h
    nlinarith [sq_nonneg r]
  · have h1 : 1 ≤ r ^ 2 := by nlinarith
    have h2 : 0 ≤ r⁻¹ := (inv_pos.mpr hr).le
    linarith

/-- The fibre data of the window bundle at one coordinate, Fubini-sliced to
almost every input frequency: the three fibre moments and the two fibre
measurabilities. -/
theorem ae_fiberSliceData (v : ℝ → ES → ComplexSpace) (j : Fin 3) (τ t₁ : ℝ)
    (sup : PhysicalODEWindowSupply v j τ t₁)
    (hsrcm1 : Integrable (fun p : ES × ℝ =>
        ‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 j‖)
      (volume.prod (volume.restrict (Icc τ t₁)))) :
    ∀ᵐ η ∂volume,
      Integrable (fun s : ℝ => ‖η‖⁻¹ * ‖continuousNavierSource v v s η j‖)
        (volume.restrict (Icc (0 : ℝ) τ)) ∧
      Integrable (fun s : ℝ => ‖η‖⁻¹ * ‖continuousNavierSource v v s η j‖)
        (volume.restrict (Icc τ t₁)) ∧
      Integrable (fun s : ℝ => ‖η‖ ^ 2 * ‖continuousNavierSource v v s η j‖)
        (volume.restrict (Icc τ t₁)) ∧
      AEStronglyMeasurable (fun s : ℝ => continuousNavierSource v v s η j)
        (volume.restrict (Icc (0 : ℝ) τ)) ∧
      AEStronglyMeasurable (fun s : ℝ => continuousNavierSource v v s η j)
        (volume.restrict (Icc τ t₁)) := by
  have h0 := ((integrable_prod_iff sup.hsrc₀.aestronglyMeasurable).mp sup.hsrc₀).1
  have hm := ((integrable_prod_iff hsrcm1.aestronglyMeasurable).mp hsrcm1).1
  have h1 := ((integrable_prod_iff sup.hsrc₁.aestronglyMeasurable).mp sup.hsrc₁).1
  have ha0 := sup.hmeas.prodMk_left
  have ha1 := sup.hmeas₁.prodMk_left
  filter_upwards [h0, hm, h1, ha0, ha1] with η h0 hm h1 ha0 ha1
  exact ⟨h0, hm, h1, ha0, ha1⟩

/-- **Time-uniform Duhamel majorant on the shrunk window.**  For `s ∈ (τ', t₁)`
with `τ < τ'`, and a fibre `η ≠ 0` carrying the sliced window data, the
Duhamel coordinate is bounded — independently of `s` — by the strict-past
`X⁻¹` fibre moment times `1 + (ν(τ'−τ))⁻¹` plus the recent-window
`X⁻¹ + X²` fibre moments. -/
theorem norm_continuousDuhamel_le_window (ν : ℝ) (hν : 0 < ν)
    (v : ℝ → ES → ComplexSpace) (j : Fin 3) (τ τ' t₁ s : ℝ) (hτ : 0 ≤ τ) (hττ' : τ < τ')
    (hs : s ∈ Ioo τ' t₁) (η : ES) (hη : η ≠ 0)
    (h0 : Integrable (fun s : ℝ => ‖η‖⁻¹ * ‖continuousNavierSource v v s η j‖)
      (volume.restrict (Icc (0 : ℝ) τ)))
    (hm : Integrable (fun s : ℝ => ‖η‖⁻¹ * ‖continuousNavierSource v v s η j‖)
      (volume.restrict (Icc τ t₁)))
    (h1 : Integrable (fun s : ℝ => ‖η‖ ^ 2 * ‖continuousNavierSource v v s η j‖)
      (volume.restrict (Icc τ t₁)))
    (ha0 : AEStronglyMeasurable (fun s : ℝ => continuousNavierSource v v s η j)
      (volume.restrict (Icc (0 : ℝ) τ)))
    (ha1 : AEStronglyMeasurable (fun s : ℝ => continuousNavierSource v v s η j)
      (volume.restrict (Icc τ t₁))) :
    ‖continuousDuhamel ν v v s η j‖ ≤
      (1 + (ν * (τ' - τ))⁻¹) *
          (∫ σ in Icc (0 : ℝ) τ, ‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖) +
        ((∫ σ in Icc τ t₁, ‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖) +
          ∫ σ in Icc τ t₁, ‖η‖ ^ 2 * ‖continuousNavierSource v v σ η j‖) := by
  set C : ℝ := 1 + (ν * (τ' - τ))⁻¹ with hC
  set F : ℝ → ℂ := fun σ =>
    heatMode ν (s - σ) (fun ζ : ES => continuousNavierSource v v σ ζ j) η with hF
  have hFnorm : ∀ σ : ℝ, ‖F σ‖ =
      Real.exp (-(ν * ‖η‖ ^ 2 * (s - σ))) * ‖continuousNavierSource v v σ η j‖ := by
    intro σ
    show ‖((Real.exp (-(ν * ‖η‖ ^ 2 * (s - σ))) : ℝ) : ℂ) *
        continuousNavierSource v v σ η j‖ = _
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hτs : τ ≤ s := (hττ'.trans hs.1).le
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  have hexpc : Continuous (fun σ : ℝ => ((Real.exp (-(ν * ‖η‖ ^ 2 * (s - σ))) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_const.sub continuous_id)).neg))
  have hFm0 : AEStronglyMeasurable F (volume.restrict (Icc (0 : ℝ) τ)) :=
    hexpc.aestronglyMeasurable.mul ha0
  have hFm1 : AEStronglyMeasurable F (volume.restrict (Icc τ t₁)) :=
    hexpc.aestronglyMeasurable.mul ha1
  -- strict past: the lag buys one power of `‖η‖`
  have hpast : ∀ σ ∈ Icc (0 : ℝ) τ,
      ‖F σ‖ ≤ C * (‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖) := by
    intro σ hσ
    rw [hFnorm]
    have hx : τ' - τ ≤ s - σ := by linarith [hσ.2, hs.1]
    have key := mul_exp_neg_sq_le ν (τ' - τ) ‖η‖ (s - σ) hν (sub_pos.mpr hττ')
      (norm_nonneg η) hx
    have hfac : Real.exp (-(ν * ‖η‖ ^ 2 * (s - σ))) ≤ C * ‖η‖⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hn]
      linarith [key]
    calc Real.exp (-(ν * ‖η‖ ^ 2 * (s - σ))) * ‖continuousNavierSource v v σ η j‖
        ≤ (C * ‖η‖⁻¹) * ‖continuousNavierSource v v σ η j‖ :=
          mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
      _ = C * (‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖) := by ring
  -- recent window: the heat factor is a contraction and `1 ≤ ‖η‖⁻¹ + ‖η‖²`
  have hrecent : ∀ σ ∈ Icc τ s, ‖F σ‖ ≤
      ‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖ +
        ‖η‖ ^ 2 * ‖continuousNavierSource v v σ η j‖ := by
    intro σ hσ
    rw [hFnorm]
    have hsσ : 0 ≤ s - σ := by linarith [hσ.2]
    have hexp1 : Real.exp (-(ν * ‖η‖ ^ 2 * (s - σ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have := mul_nonneg (mul_nonneg hν.le (sq_nonneg ‖η‖)) hsσ
      linarith
    have h1' := one_le_inv_add_sq ‖η‖ hn
    calc Real.exp (-(ν * ‖η‖ ^ 2 * (s - σ))) * ‖continuousNavierSource v v σ η j‖
        ≤ 1 * ‖continuousNavierSource v v σ η j‖ :=
          mul_le_mul_of_nonneg_right hexp1 (norm_nonneg _)
      _ ≤ (‖η‖⁻¹ + ‖η‖ ^ 2) * ‖continuousNavierSource v v σ η j‖ :=
          mul_le_mul_of_nonneg_right h1' (norm_nonneg _)
      _ = _ := by ring
  -- integrability of the Duhamel integrand on both pieces
  have hsub : Ioc τ s ⊆ Icc τ t₁ := fun σ hσ => ⟨hσ.1.le, hσ.2.trans hs.2.le⟩
  have hG : Integrable (fun σ : ℝ => ‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖ +
      ‖η‖ ^ 2 * ‖continuousNavierSource v v σ η j‖) (volume.restrict (Icc τ t₁)) :=
    hm.add h1
  have hGr : Integrable (fun σ : ℝ => ‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖ +
      ‖η‖ ^ 2 * ‖continuousNavierSource v v σ η j‖) (volume.restrict (Ioc τ s)) :=
    hG.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hFi0 : IntegrableOn F (Icc (0 : ℝ) τ) :=
    (h0.const_mul C).mono' hFm0
      ((ae_restrict_mem measurableSet_Icc).mono fun σ hσ => hpast σ hσ)
  have hFi1 : IntegrableOn F (Ioc τ s) :=
    hGr.mono' (hFm1.mono_measure (Measure.restrict_mono hsub le_rfl))
      ((ae_restrict_mem measurableSet_Ioc).mono fun σ hσ => hrecent σ ⟨hσ.1.le, hσ.2⟩)
  -- split the causal integral at `τ`
  have hunion : Icc (0 : ℝ) τ ∪ Ioc τ s = Icc 0 s := Icc_union_Ioc_eq_Icc hτ hτs
  have hdisj : Disjoint (Icc (0 : ℝ) τ) (Ioc τ s) := by
    rw [Set.disjoint_left]
    intro σ hσ hσ'
    exact absurd hσ'.1 (not_lt.mpr hσ.2)
  have hsplit : continuousDuhamel ν v v s η j =
      (∫ σ in Icc (0 : ℝ) τ, F σ) + ∫ σ in Ioc τ s, F σ := by
    show ∫ σ in Icc (0 : ℝ) s, F σ = _
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc hFi0 hFi1]
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_integral_le_of_norm_le (h0.const_mul C)
      ((ae_restrict_mem measurableSet_Icc).mono fun σ hσ => hpast σ hσ)).trans ?_
    rw [integral_const_mul]
  · refine (norm_integral_le_of_norm_le hGr
      ((ae_restrict_mem measurableSet_Ioc).mono fun σ hσ =>
        hrecent σ ⟨hσ.1.le, hσ.2⟩)).trans ?_
    refine (setIntegral_mono_set hG
      (Eventually.of_forall fun σ => by
        simp only [Pi.zero_apply]
        positivity)
      (Eventually.of_forall fun σ hσ => hsub hσ)).trans ?_
    rw [integral_add hm h1]

/-- **`hcont` at a pointwise mild fixed point.**  If `v` is its own mild image
on the window `w ⊆ (τ', t₁)` at almost every input frequency, then the
reweighted source is fibre-continuous on `w` for almost every output
frequency — the residual `hcont` of §2 — from the window bundle at every
coordinate, the recent-window `X⁻¹` source moment, the datum's `L¹` mass and
slice measurability on the window.  (FC-rep) and (FC-dom) are derived, not
assumed (module header of §5). -/
theorem ae_ContinuousOn_weightedSource_of_mildFixed
    (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace) (i : Fin 3)
    (τ τ' t₁ : ℝ) (hτ : 0 ≤ τ) (hττ' : τ < τ') (w : Set ℝ) (hw : w ⊆ Ioo τ' t₁)
    (ha0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖a η j‖))
    (sup : ∀ j : Fin 3, PhysicalODEWindowSupply v j τ t₁)
    (hsrcm1 : ∀ j : Fin 3, Integrable (fun p : ES × ℝ =>
        ‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 j‖)
      (volume.prod (volume.restrict (Icc τ t₁))))
    (hv_meas : ∀ s ∈ w, ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => v s η j))
    (hfix : ∀ᵐ η ∂volume, ∀ s ∈ w, ∀ j : Fin 3,
      v s η j = continuousMildImage ν hν a v s η j) :
    ∀ᵐ ξ ∂volume, ContinuousOn (weightedSource ν v v ξ i) w := by
  have hdata := ae_all_iff.mpr fun j : Fin 3 => ae_fiberSliceData v j τ t₁ (sup j) (hsrcm1 j)
  have hII : ∀ᵐ η ∂volume, ∀ j : Fin 3, ∀ s' ∈ Ioo (max 0 τ) t₁,
      IntervalIntegrable (weightedSource ν v v η j) volume 0 s' :=
    ae_all_iff.mpr fun j =>
      ae_intervalIntegrable_weightedSource_of_windowMoments ν v j τ t₁ hτ (sup j)
  have hne : ∀ᵐ η ∂volume, (η : ES) ≠ 0 := volume.ae_ne (0 : ES)
  refine ae_ContinuousOn_weightedSource_of_fiberData ν v i w hv_meas ?_ ?_
  · -- (FC-rep): fibre continuity of the mild image, transported to `v`
    filter_upwards [hfix, hII] with η hfixη hIIη
    intro j
    have hEη : Continuous (fun s : ℝ => ((Real.exp (-(ν * ‖η‖ ^ 2 * s)) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))
    have hmild : ContinuousOn (fun s : ℝ => continuousMildImage ν hν a v s η j) w := by
      intro s₀ hs₀
      have hs₀' := hw hs₀
      have hpos : 0 < s₀ := by linarith [hs₀'.1]
      have hs'mem : (s₀ + t₁) / 2 ∈ Ioo (max 0 τ) t₁ :=
        ⟨max_lt (by linarith [hs₀'.2]) (by linarith [hs₀'.1, hs₀'.2]), by linarith [hs₀'.2]⟩
      have hs₀s' : s₀ < (s₀ + t₁) / 2 := by linarith [hs₀'.2]
      have hprim : ContinuousOn
          (fun b : ℝ => ∫ x in (0 : ℝ)..b, weightedSource ν v v η j x)
          (Icc 0 ((s₀ + t₁) / 2)) := by
        have := intervalIntegral.continuousOn_primitive_interval'
          (hIIη j _ hs'mem) (left_mem_uIcc (a := (0 : ℝ)) (b := (s₀ + t₁) / 2))
        rwa [uIcc_of_le (by linarith : (0 : ℝ) ≤ (s₀ + t₁) / 2)] at this
      have hprimAt : ContinuousAt
          (fun b : ℝ => ∫ x in (0 : ℝ)..b, weightedSource ν v v η j x) s₀ :=
        hprim.continuousAt (Icc_mem_nhds hpos hs₀s')
      have hD : ContinuousAt (fun s : ℝ => ((Real.exp (-(ν * ‖η‖ ^ 2 * s)) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..s, weightedSource ν v v η j x) s₀ :=
        hEη.continuousAt.mul hprimAt
      have hheat : ContinuousAt (fun s : ℝ => heatVec ν s a η j) s₀ := by
        show ContinuousAt (fun s : ℝ => ((Real.exp (-(ν * ‖η‖ ^ 2 * s)) : ℝ) : ℂ) * a η j) s₀
        exact hEη.continuousAt.mul continuousAt_const
      refine (hheat.add hD).continuousWithinAt.congr ?_ ?_
      · intro s hs
        rw [ContinuousLeiLinSelfMap.continuousMildImage_coord_apply,
          continuousDuhamel_coord_eq ν v v s (by linarith [(hw hs).1] : (0 : ℝ) ≤ s) η j]
        try rfl
      · rw [ContinuousLeiLinSelfMap.continuousMildImage_coord_apply,
          continuousDuhamel_coord_eq ν v v s₀ hpos.le η j]
        try rfl
    exact hmild.congr fun s hs => hfixη s hs j
  · -- (FC-dom): the time-uniform majorant of the mild image
    set C : ℝ := 1 + (ν * (τ' - τ))⁻¹ with hC
    have hCnn : 0 ≤ C := add_nonneg zero_le_one (inv_pos.mpr (mul_pos hν (sub_pos.mpr hττ'))).le
    refine ⟨fun η : ES => ∑ j : Fin 3, (‖a η j‖ +
      C * (∫ σ in Icc (0 : ℝ) τ, ‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖) +
      ((∫ σ in Icc τ t₁, ‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖) +
        ∫ σ in Icc τ t₁, ‖η‖ ^ 2 * ‖continuousNavierSource v v σ η j‖)), ?_, ?_⟩
    · refine integrable_finsetSum Finset.univ fun j _ => ?_
      have hnn0 : ∀ (η : ES) (σ : ℝ),
          0 ≤ ‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖ :=
        fun η σ => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
      have hnn2 : ∀ (η : ES) (σ : ℝ),
          0 ≤ ‖η‖ ^ 2 * ‖continuousNavierSource v v σ η j‖ :=
        fun η σ => mul_nonneg (sq_nonneg _) (norm_nonneg _)
      have hI0 : Integrable (fun η : ES =>
          ∫ σ in Icc (0 : ℝ) τ, ‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖) := by
        refine (sup j).hsrc₀.integral_norm_prod_left.congr (ae_of_all _ fun η => ?_)
        exact integral_congr_ae (ae_of_all _ fun σ => Real.norm_of_nonneg (hnn0 η σ))
      have hIm : Integrable (fun η : ES =>
          ∫ σ in Icc τ t₁, ‖η‖⁻¹ * ‖continuousNavierSource v v σ η j‖) := by
        refine (hsrcm1 j).integral_norm_prod_left.congr (ae_of_all _ fun η => ?_)
        exact integral_congr_ae (ae_of_all _ fun σ => Real.norm_of_nonneg (hnn0 η σ))
      have hI1 : Integrable (fun η : ES =>
          ∫ σ in Icc τ t₁, ‖η‖ ^ 2 * ‖continuousNavierSource v v σ η j‖) := by
        refine (sup j).hsrc₁.integral_norm_prod_left.congr (ae_of_all _ fun η => ?_)
        exact integral_congr_ae (ae_of_all _ fun σ => Real.norm_of_nonneg (hnn2 η σ))
      exact ((ha0 j).add (hI0.const_mul C)).add (hIm.add hI1)
    · filter_upwards [hfix, hdata, hne] with η hfixη hdataη hη
      intro s hs j
      have hs' := hw hs
      have hs0 : 0 ≤ s := by linarith [hs'.1]
      obtain ⟨h0, hm, h1, ha0', ha1'⟩ := hdataη j
      have hD := norm_continuousDuhamel_le_window ν hν v j τ τ' t₁ s hτ hττ' hs' η hη
        h0 hm h1 ha0' ha1'
      have hheat : ‖heatVec ν s a η j‖ ≤ ‖a η j‖ := by
        show ‖((Real.exp (-(ν * ‖η‖ ^ 2 * s)) : ℝ) : ℂ) * a η j‖ ≤ _
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
        have := mul_nonneg (mul_nonneg hν.le (sq_nonneg ‖η‖)) hs0
        linarith
      rw [← hC] at hD
      rw [hfixη s hs j, ContinuousLeiLinSelfMap.continuousMildImage_coord_apply]
      refine (norm_add_le _ _).trans ((add_le_add hheat hD).trans ?_)
      refine le_trans (le_of_eq (by ring)) (Finset.single_le_sum (f := fun k : Fin 3 => ‖a η k‖ +
        C * (∫ σ in Icc (0 : ℝ) τ, ‖η‖⁻¹ * ‖continuousNavierSource v v σ η k‖) +
        ((∫ σ in Icc τ t₁, ‖η‖⁻¹ * ‖continuousNavierSource v v σ η k‖) +
          ∫ σ in Icc τ t₁, ‖η‖ ^ 2 * ‖continuousNavierSource v v σ η k‖))
        (fun k _ => ?_) (Finset.mem_univ j))
      try dsimp only
      have hi0 : 0 ≤ ∫ σ in Icc (0 : ℝ) τ, ‖η‖⁻¹ * ‖continuousNavierSource v v σ η k‖ :=
        integral_nonneg fun σ => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
      have him : 0 ≤ ∫ σ in Icc τ t₁, ‖η‖⁻¹ * ‖continuousNavierSource v v σ η k‖ :=
        integral_nonneg fun σ => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
      have hi1 : 0 ≤ ∫ σ in Icc τ t₁, ‖η‖ ^ 2 * ‖continuousNavierSource v v σ η k‖ :=
        integral_nonneg fun σ => mul_nonneg (sq_nonneg _) (norm_nonneg _)
      have := mul_nonneg hCnn hi0
      linarith [norm_nonneg (a η k)]

/-- **Obligation 4 at a pointwise mild fixed point.**  The `hdv_diff` family of
§2 on the shrunk window `u ∩ (τ', t₁)`, with the residual `hcont` DISCHARGED
by `ae_ContinuousOn_weightedSource_of_mildFixed`. -/
theorem hdvDiff_of_windowMoments_mildFixed
    (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace) (i : Fin 3)
    (τ τ' t₁ : ℝ) (hτ : 0 ≤ τ) (hττ' : τ < τ') (u : Set ℝ) (hu : IsOpen u)
    (ha0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖a η j‖))
    (sup : ∀ j : Fin 3, PhysicalODEWindowSupply v j τ t₁)
    (hsrcm1 : ∀ j : Fin 3, Integrable (fun p : ES × ℝ =>
        ‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 j‖)
      (volume.prod (volume.restrict (Icc τ t₁))))
    (hv_meas : ∀ s ∈ Ioo τ' t₁, ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => v s η j))
    (hfix : ∀ᵐ η ∂volume, ∀ s ∈ Ioo τ' t₁, ∀ j : Fin 3,
      v s η j = continuousMildImage ν hν a v s η j) :
    ∀ᵐ ξ ∂volume, ∀ s ∈ u ∩ Ioo τ' t₁,
      HasDerivAt (fun r : ℝ => continuousMildImage ν hν a v r ξ i)
        (-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a v s ξ i
          + continuousNavierSource v v s ξ i) s := by
  have hcont := ae_ContinuousOn_weightedSource_of_mildFixed ν hν a v i τ τ' t₁ hτ hττ'
    (u ∩ Ioo τ' t₁) inter_subset_right ha0 sup hsrcm1
    (fun s hs => hv_meas s hs.2) (hfix.mono fun η h s hs => h s hs.2)
  have hu' : IsOpen (u ∩ Ioo τ' t₁) := hu.inter isOpen_Ioo
  have key := hdvDiff_of_windowMoments_and_sourceContinuous ν hν a v i τ t₁ hτ
    (u ∩ Ioo τ' t₁) hu' (sup i) (hcont.mono fun ξ h => h.mono inter_subset_left)
  filter_upwards [key] with ξ hξ
  intro s hs
  exact hξ s ⟨hs, max_lt (by linarith [hs.2.1, hττ', hτ]) (hττ'.trans hs.2.1), hs.2.2⟩

/-- **Glue: obligation 4 feeding obligation 1 at a pointwise mild fixed point
of the Schwartz datum.**  The §9 physical pointwise ODE with `hcont` no
longer a hypothesis: the datum's `L¹` mass is the Schwartz Fourier
transform's, and the fibre continuity is derived from the window bundle at
every coordinate, the recent-window `X⁻¹` source moment and the pointwise
mild identity on `(τ', t₁)`.  The genuinely-travelling residuals are now the
`hsrc` pointwise envelope, the mild-slice fields `hw_meas`/`hw_int`/`hdv_meas`,
the bundle and moment inputs, and `hfix` itself. -/
theorem hasDerivAt_physicalVelocity_continuousMildImage_fourierDatum_of_mildFixed
    (ν : ℝ) (hν : 0 < ν) (u₀ : Navier.SchwartzVelocity)
    (v : ℝ → ES → ComplexSpace) (i : Fin 3) (x : Navier.Space)
    (t₀ τ τ' t₁ : ℝ) (ht₀ : 0 < t₀) (hτ : 0 ≤ τ) (hττ' : τ < τ') (hτ't : τ' < t₀)
    (ht₀t₁ : t₀ < t₁)
    (sup : ∀ j : Fin 3, PhysicalODEWindowSupply v j τ t₁)
    (hsrcm1 : ∀ j : Fin 3, Integrable (fun p : ES × ℝ =>
        ‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 j‖)
      (volume.prod (volume.restrict (Icc τ t₁))))
    (hsrc : ∃ u ∈ 𝓝 t₀, ∃ g : ES → ℝ, Integrable g ∧
        ∀ᵐ ξ ∂volume, ∀ s ∈ u, ‖continuousNavierSource v v s ξ i‖ ≤ g ξ)
    (hw_meas : ∀ᶠ s in 𝓝 t₀,
      AEStronglyMeasurable (fun ξ : ES =>
        continuousMildImage ν hν (fourierDatum u₀) v s ξ i))
    (hw_int : Integrable (fun ξ : ES =>
        continuousMildImage ν hν (fourierDatum u₀) v t₀ ξ i))
    (hdv_meas : AEStronglyMeasurable (fun ξ : ES =>
        -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν (fourierDatum u₀) v t₀ ξ i
          + continuousNavierSource v v t₀ ξ i))
    (hv_meas : ∀ s ∈ Ioo τ' t₁, ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => v s η j))
    (hfix : ∀ᵐ η ∂volume, ∀ s ∈ Ioo τ' t₁, ∀ j : Fin 3,
      v s η j = continuousMildImage ν hν (fourierDatum u₀) v s η j) :
    HasDerivAt (fun s : ℝ =>
        physicalVelocity (continuousMildImage ν hν (fourierDatum u₀) v) s x i)
      (realPhysicalCoord (fun ξ : ES =>
          -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν (fourierDatum u₀) v t₀ ξ
            + continuousNavierSource v v t₀ ξ) i (euclidPoint x)) t₀ := by
  have ha0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖fourierDatum u₀ η j‖) := fun j =>
    ((𝓕 (euclidComponent u₀ j) : SchwartzMap ES ℂ).integrable).norm
  refine hasDerivAt_physicalVelocity_continuousMildImage_fourierDatum_of_sourceContinuous
    ν hν u₀ v i x t₀ τ t₁ ht₀ hτ (hττ'.trans hτ't) ht₀t₁ (sup i) hsrc
    (Ioo τ' t₁) isOpen_Ioo ⟨hτ't, ht₀t₁⟩ hw_meas hw_int hdv_meas ?_
  exact ae_ContinuousOn_weightedSource_of_mildFixed ν hν (fourierDatum u₀) v i τ τ' t₁
    hτ hττ' (Ioo τ' t₁ ∩ Ioo (max 0 τ) t₁) inter_subset_left ha0 sup hsrcm1
    (fun s hs => hv_meas s hs.1) (hfix.mono fun η h s hs => h s hs.1)


end Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply

#print axioms Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_of_fiberData
#print axioms Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_heat
#print axioms Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.hcont_heat
#check @Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_of_fiberData
#check @Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_heat
#check @Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.hcont_heat
#print axioms Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.norm_continuousDuhamel_le_window
#print axioms Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_of_mildFixed
#print axioms Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.hdvDiff_of_windowMoments_mildFixed
#print axioms Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.hasDerivAt_physicalVelocity_continuousMildImage_fourierDatum_of_mildFixed
#check @Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_of_mildFixed
#check @Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.hasDerivAt_physicalVelocity_continuousMildImage_fourierDatum_of_mildFixed
