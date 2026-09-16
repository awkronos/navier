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
`∀ s j, AEStronglyMeasurable (fun η => v s η j)`.  Mechanism: for almost every
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
    (hv_meas : ∀ s : ℝ, ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => v s η j))
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
    have hmeas : ∀ s : ℝ, AEStronglyMeasurable
        (fun η : ES => ContinuousLinearMap.mul ℂ ℂ (v s η j) (v s (ξ - η) k)) := by
      intro s
      have hg : AEStronglyMeasurable (fun x : ES => v s x k)
          (Measure.map (fun η : ES => ξ - η) volume) := by
        rw [hsubpres.map_eq]
        exact hv_meas s k
      exact (hv_meas s j).convolution_integrand_snd' (ContinuousLinearMap.mul ℂ ℂ) hg
    refine tendsto_integral_filter_of_dominated_convergence
        (fun η : ES => M η * M (ξ - η)) (Eventually.of_forall hmeas)
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
    intro s j
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

end Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply

#print axioms Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_of_fiberData
#print axioms Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_heat
#print axioms Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.hcont_heat
#check @Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_of_fiberData
#check @Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_heat
#check @Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply.hcont_heat
