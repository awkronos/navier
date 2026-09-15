import Navier.Analysis.ContinuousLeiLinODEDominationSupply
import Navier.Analysis.ContinuousLeiLinFrequencyODE

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
open scoped Topology
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap (continuousMildImage)
open Navier.Analysis.ContinuousLeiLinFrequencyODE
open Navier.Analysis.ContinuousLeiLinODEDominationSupply
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier (fourierDatum)
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity
  (physicalVelocity realPhysicalCoord euclidPoint)

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

end Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply
