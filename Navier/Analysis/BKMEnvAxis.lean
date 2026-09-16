/-
Lane NS5-ENV (2026-09-15): the axis-shortcut conversion and the boundedness
one-liner that feed the third bridge
`Analysis.BKMProfileSelectedEnvelope.vorticityRateBound_of_polyUpper_axisLower`
for the concrete assembled candidate field.

Contents, in dependency order:

1. `vort_eq_spatialCurl` — the carrier weld: the official pointwise
   `vorticity (uncurry v) t x` equals the construction curl
   `spatialCurl v (t, WithLp.toLp 2 x)` as plain vectors.
2. `exists_Ico_of_eventually` — extraction of a uniform late window
   `[t₀, 1)` from a `𝓝[<] 1` event.
3. `uSel_germ` — the axis-shortcut conversion: near `(t, 0)`, for late `t`
   inside the local domain, the assembled activated/cut selected velocity
   agrees with the `FinalSlowBase` base field.
4. `axis_lower_bound` — the bridge's `haxis` at the exact constants
   `c₁ = 2 * modulation.profiles.f (0, 0)` and `αL = A h + 1/2 > 1`,
   unconditional in the schedule.
5. `v_bounded_before` — the bridge's `hbdd` from the `V_continuousOn`
   one-liner plus compactness.
6. Packaging: the bridge instantiated for `uSel a` / the selected witness
   `uSel aSel`, conditional ONLY on the polynomial upper envelope `hup`
   (the T1–T4 residual, see NOTES), yielding `VorticityRateBound` and both
   divergence crowns.
-/
import Navier.Analysis.BKMProfileSelectedEnvelope
import Navier.Analysis.BKMProfileGronwallPair
import Navier.Construction.R3ActualCandidate
import Navier.Construction.BaseVorticityAxis

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff
open Navier Navier.Analysis.Vorticity Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BKMVorticityIntegralDivergence
open Navier.Analysis.BKMForcedBreakdownNecessity
open Navier.Analysis.BKMProfileGronwallPair Navier.Analysis.BKMProfileRateBound
open Navier.Analysis.BKMProfileSelectedEnvelope
open Navier.Construction ProblemStatement SpatialCurl
open Navier.Construction.CorrectionInitialization
  Navier.Construction.CorrectionInitialization.ActualPrimary

private abbrev ESpace := Navier.Construction.ProblemStatement.Space

namespace Navier.Analysis.BKMEnvAxis

open Navier.Construction.R3CompactCandidate

noncomputable def budgetSel : ℕ := ActualCandidateConstruction.selectedBudget
noncomputable def thresholdSel : ℕ := ActualCandidateConstruction.selectedThreshold
noncomputable def qbigSel : ℝ := ActualCandidateConstruction.qbig budgetSel thresholdSel

private theorem hNsel : ActualCarrierGeometry.geometricThreshold ≤ thresholdSel :=
  ActualCandidateConstruction.selectedThreshold_geometry

private theorem qbigSel_pos : 0 < qbigSel :=
  ActualCandidateConstruction.qbig_pos budgetSel thresholdSel

/-- The retained selected potential sum for the schedule `a`. -/
noncomputable def ASum (a : ℕ → ℕ) : ProblemStatement.VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    ActualCandidateAssembly.selectedPotentialStages

/-- The retained selected direct angular sum for the schedule `a`. -/
noncomputable def BSum (a : ℕ → ℕ) : ProblemStatement.VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    ActualCandidateAssembly.selectedDirectStages

/-- The retained selected pressure sum for the schedule `a`. -/
noncomputable def PSum (a : ℕ → ℕ) : ProblemStatement.PressureField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    ActualCandidateAssembly.selectedPressureStages

/-- The assembled compact candidate velocity built from the selected raw sums. -/
noncomputable def uSel (a : ℕ → ℕ) : ProblemStatement.VelocityField :=
  R3CompactCandidate.velocity (ASum a) (BSum a)

/-- Vector-level weld of the official coordinate curl to the construction curl. -/
theorem vort_eq_spatialCurl {v : ProblemStatement.VelocityField}
    (hv : ContDiffOn ℝ ∞ v preSingularDomain)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x : Navier.Space) :
    vorticity (uncurry v) t x =
      (spatialCurl v (t, WithLp.toLp 2 x) : Navier.Space) := by
  show staticCurl (uncurry v t) x = _
  have hD : ∀ i : Fin 3, fderiv ℝ (uncurry v t) x (basisVector i) =
      ((fderiv ℝ (fun y : ESpace => v (t, y)) (WithLp.toLp 2 x) (coordinateVector i) : ESpace)
        : Navier.Space) := fun i => by
    rw [fderiv_uncurry_eq hv ht x]
    rfl
  unfold staticCurl spatialCurl curl
  simp only [hD]
  ext k
  fin_cases k
  · simp [Finset.sum_apply, cross_apply, basisVector,
      Pi.single_apply, curlLinear_apply_zero]
  · simp [Finset.sum_apply, cross_apply, basisVector,
      Pi.single_apply, curlLinear_apply_one]
  · simp [Finset.sum_apply, cross_apply, basisVector,
      Pi.single_apply, curlLinear_apply_two]

/-- A `𝓝[<] 1` event is eventually true on one uniform window `[t₀, 1)`. -/
theorem exists_Ico_of_eventually {P : ℝ → Prop}
    (hP : ∀ᶠ t in 𝓝[<] (1 : ℝ), P t) :
    ∃ t₀ ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico t₀ (1 : ℝ), P t := by
  rw [show (𝓝[<] (1 : ℝ)) = 𝓝 (1 : ℝ) ⊓ principal (Iio (1 : ℝ)) from rfl,
    eventually_inf_principal] at hP
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp hP
  refine ⟨max 0 (1 - ε / 2),
    ⟨le_max_left 0 _, max_lt zero_lt_one (sub_lt_self 1 (half_pos hε))⟩, fun t ht => ?_⟩
  have hlt : dist t 1 < ε := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2.le)]
    have hbound : (1 : ℝ) - ε / 2 ≤ t := le_trans (le_max_right 0 (1 - ε / 2)) ht.1
    linarith [hbound, half_lt_self hε]
  exact hall hlt ht.2

/-- **Axis-shortcut conversion.** For late `t` in the local domain with the
zero-scale cutoff small, the assembled selected velocity agrees near `(t, 0)`
with the `FinalSlowBase` base field: activation is switched on, the spatial
cutoff is one, the potential sum collapses to the gauge base by the axis
zero-germs, and the direct angular sum vanishes. -/
theorem uSel_germ {a : ℕ → ℕ} (haT : Tendsto (fun j => (a j : ℝ)) atTop atTop)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (hgt : 3 / 4 < t)
    (hdom : (t, (0 : ESpace)) ∈ MixedAxisPreservation.localDomain h qbigSel)
    (hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ h (t, (0 : ESpace))| < 1 / 2) :
    uSel a =ᶠ[𝓝 (t, (0 : ESpace))]
      FinalSlowBase.velocity certificate modulation upper budgetSel := by
  have hzero : (0 : ESpace) ∈ SpatialLocalization.plateau := SpatialLocalization.zero_mem_plateau
  have hrad0 : PhysicalGraphBounds.radialProjection (t, (0 : ESpace)) = 0 :=
    MixedAxisPreservation.radialProjection_origin t
  have hq : ContinuousAt (PhysicalWaveSum.physicalQ h) (t, (0 : ESpace)) :=
    (PhysicalWaveSum.physicalQ_smoothAt outgoing.data.h_pos outgoing.data.h_lt_half ht.2).continuousAt
  have hpos : 0 < PhysicalWaveSum.physicalQ h (t, (0 : ESpace)) :=
    PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half ht.2
  -- potential-side zero germs from the AxisZeroOn instances
  have hInit : ActualCandidateAssembly.initialPotential budgetSel thresholdSel =ᶠ[𝓝 (t, (0 : ESpace))]
      fun _ => 0 :=
    (ActualCandidateAssembly.initialPotential_axisZeroOn budgetSel thresholdSel)
      (t, (0 : ESpace)) hdom hrad0
  have hStages : ∀ j, ActualCandidateAssembly.positivePotential budgetSel thresholdSel hNsel j
      =ᶠ[𝓝 (t, (0 : ESpace))] fun _ => 0 := fun j =>
    (ActualCandidateAssembly.positivePotential_axisZeroOn budgetSel thresholdSel hNsel j)
      (t, (0 : ESpace)) hdom hrad0
  have hAs : ASum a =ᶠ[𝓝 (t, (0 : ESpace))]
      TailGaugePotential.finalPotential certificate modulation upper budgetSel := by
    refine GermCandidateAssembly.potentialSum_eq_base_germ haT hq hpos hInit hStages hsmall
  -- direct-side zero germs: every raw angular stage vanishes near the axis
  have hB0 : ∀ j, LocalAngularDiagonal.rawSeries
      (ActualCandidateAssembly.directData budgetSel thresholdSel hNsel) j
      =ᶠ[𝓝 (t, (0 : ESpace))] fun _ => 0 := by
    intro j
    have hU : IsOpen (LocalAngularDiagonal.localSlowDomain h qbigSel) :=
      LocalAngularDiagonal.localSlowDomain_open outgoing.data.h_pos outgoing.data.h_lt_half qbigSel
    have hw : (t, (0 : ESpace)) ∈ DirectAngularDiagonal.physicalDomain
        (LocalAngularDiagonal.localSlowDomain h qbigSel) := hdom
    have hr : DirectAngularDiagonal.radius (t, (0 : ESpace)) = 0 :=
      MixedAxisPreservation.radius_zero_of_axis hrad0
    have hinner : 0 < (ActualCandidateAssembly.directData budgetSel thresholdSel hNsel j).inner
        (DirectAngularDiagonal.slowPoint (t, (0 : ESpace))) :=
      (ActualCandidateAssembly.directData budgetSel thresholdSel hNsel j).inner_pos
        (DirectAngularDiagonal.slowPoint (t, (0 : ESpace))) hw
    have hzf := (ActualCandidateAssembly.directData budgetSel thresholdSel hNsel j).field_zero_germ
      hU hw (by rw [hr]; exact hinner)
    simpa [LocalAngularDiagonal.rawSeries] using hzf
  have hBz : BSum a =ᶠ[𝓝 (t, (0 : ESpace))] fun _ => 0 := by
    refine ((AxisPreservation.potentialSum_eq_first_near haT hq hpos (fun j _ => hB0 j)).trans ?_)
    filter_upwards [hB0 0] with y hy
    simp only [SolenoidalDiagonal.cutStage, hy, smul_zero]
  -- curl transport of the potential side, and the exact base identity
  have hsA : SpatialCurl.spatialCurl (ASum a) =ᶠ[𝓝 (t, (0 : ESpace))]
      SpatialCurl.spatialCurl (TailGaugePotential.finalPotential certificate modulation upper budgetSel) :=
    SolenoidalDiagonal.spatialCurl_eventuallyEq hAs
  have hne : ∀ᶠ z in 𝓝 (t, (0 : ESpace)), z.1 < 1 :=
    (continuous_fst.continuousAt).preimage_mem_nhds (Iio_mem_nhds ht.2)
  have hbase : (fun z => SpatialCurl.spatialCurl
      (TailGaugePotential.finalPotential certificate modulation upper budgetSel) z + 0)
      =ᶠ[𝓝 (t, (0 : ESpace))]
      FinalSlowBase.velocity certificate modulation upper budgetSel := by
    filter_upwards [hne] with z hz
    rw [add_zero]
    exact TailGaugePotential.finalPotential_sameCurl certificate modulation upper budgetSel hz
  -- cut and activation transports
  have hcutA : SpatialLocalization.cutVelocity (ASum a) =ᶠ[𝓝 (t, (0 : ESpace))]
      SpatialCurl.spatialCurl (ASum a) := by
    simpa [SpatialLocalization.cutVelocity] using
      SolenoidalDiagonal.spatialCurl_eventuallyEq
        (SpatialLocalization.cutPotential_eventuallyEq (ASum a) hzero)
  have hcutB : SpatialLocalization.cutPotential (BSum a) =ᶠ[𝓝 (t, (0 : ESpace))] BSum a :=
    SpatialLocalization.cutPotential_eventuallyEq (BSum a) hzero
  have hact : (fun z => SpatialLocalization.cutVelocity (ASum a) z +
      SpatialLocalization.cutPotential (BSum a) z)
      =ᶠ[𝓝 (t, (0 : ESpace))] uSel a := by
    simpa [uSel, R3CompactCandidate.velocity] using
      (TimeLocalization.activatedVelocity_eventuallyEq_late
        (fun z => SpatialLocalization.cutVelocity (ASum a) z +
          SpatialLocalization.cutPotential (BSum a) z) hgt (0 : ESpace)).symm
  have hmid : (fun z => SpatialLocalization.cutVelocity (ASum a) z +
      SpatialLocalization.cutPotential (BSum a) z)
      =ᶠ[𝓝 (t, (0 : ESpace))] fun z => SpatialCurl.spatialCurl (ASum a) z + BSum a z :=
    hcutA.add hcutB
  have hsum : (fun z => SpatialCurl.spatialCurl (ASum a) z + BSum a z)
      =ᶠ[𝓝 (t, (0 : ESpace))] fun z => SpatialCurl.spatialCurl
        (TailGaugePotential.finalPotential certificate modulation upper budgetSel) z + 0 :=
    hsA.add hBz
  exact hact.symm.trans (hmid.trans (hsum.trans hbase))

/-- **Bridge input `haxis`, unconditional.** On the assembled selected field
the axis vorticity dominates `c₁ (1-t)^(-αL)` with `αL = A h + 1/2 > 1`. -/
theorem axis_lower_bound {a : ℕ → ℕ}
    (hsm : ContDiffOn ℝ ∞ (uSel a) preSingularDomain)
    (haT : Tendsto (fun j => (a j : ℝ)) atTop atTop)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1)
    (hlate : ∀ t ∈ Ico t₀ (1 : ℝ), 3 / 4 < t ∧
      (t, (0 : ESpace)) ∈ MixedAxisPreservation.localDomain h qbigSel ∧
      |(a 0 : ℝ) * PhysicalWaveSum.physicalQ h (t, (0 : ESpace))| < 1 / 2) :
    ∀ t ∈ Ico t₀ (1 : ℝ),
      (2 * modulation.profiles.f (0, 0)) * (1 - t) ^ (-(CoordinateAlgebra.A h + 1 / 2)) ≤
        officialEuclideanNorm (vorticity (uncurry (uSel a)) t (0 : Navier.Space)) := by
  intro t ht
  obtain ⟨hgt, hdom, hsmall⟩ := hlate t ht
  have h0 : WithLp.toLp 2 (0 : Navier.Space) = (0 : ESpace) := rfl
  rw [vort_eq_spatialCurl hsm ⟨le_trans ht₀.1 ht.1, ht.2⟩ (0 : Navier.Space), h0]
  have hgv := uSel_germ haT ⟨le_trans ht₀.1 ht.1, ht.2⟩ hgt hdom hsmall
  rw [SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq hgv,
    FinalSlowBase.axis_vorticity_origin certificate modulation upper budgetSel ht.2, neg_add]
  have hcpos : 0 < 2 * modulation.profiles.f (0, 0) * (1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2) :=
    mul_pos (mul_pos zero_lt_two (FinalSlowBase.f_axis_positive modulation))
      (Real.rpow_pos_of_pos (sub_pos.mpr ht.2) _)
  rw [show officialEuclideanNorm
        (((2 * modulation.profiles.f (0, 0) * (1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2)) •
            coordinateVector 2 : ESpace) : Navier.Space)
      = 2 * modulation.profiles.f (0, 0) * (1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2) from by
    set c : ℝ := 2 * modulation.profiles.f (0, 0) * (1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2)
        with hcdef
    show officialEuclideanNorm ((c • coordinateVector 2 : ESpace) : Navier.Space) = c
    calc officialEuclideanNorm ((c • coordinateVector 2 : ESpace) : Navier.Space)
        = ‖c • coordinateVector 2‖ := rfl
      _ = |c| := by
        rw [norm_smul]
        simp only [ProblemStatement.coordinateVector, PiLp.norm_single, norm_one, mul_one,
          Real.norm_eq_abs]
      _ = c := abs_of_pos hcpos]
  exact le_refl _

/-- **Bridge input `hbdd`.** `V u` is bounded on `[0, t₀]` by continuity on the
compact subinterval: the `V_continuousOn` one-liner plus `IsCompact.exists_forall_le`. -/
theorem v_bounded_before {u p f : _} (hprop : Properties u p f)
    {t₀ t₁ : ℝ} (h0₁ : 0 ≤ t₁) (ht₀₁ : t₀ ≤ t₁) (ht₁ : t₁ < 1) :
    ∃ C₃, ∀ t ∈ Ico (0 : ℝ) t₀, V u t ≤ C₃ := by
  obtain ⟨K, hK, hsupp⟩ := hprop.velocity_support
  have hc := V_continuousOn hprop.velocity_smooth hK hsupp
  have hsub : Icc (0 : ℝ) t₁ ⊆ Ico (0 : ℝ) 1 := fun _ hx => ⟨hx.1, lt_of_le_of_lt hx.2 ht₁⟩
  obtain ⟨y, _, hmax⟩ :=
    IsCompact.exists_isMaxOn isCompact_Icc ⟨0, ⟨le_refl 0, h0₁⟩⟩ (hc.mono hsub)
  have hle : ∀ b ∈ Icc (0 : ℝ) t₁, V u b ≤ V u y := hmax
  exact ⟨V u y, fun t ht => hle t ⟨ht.1, le_of_lt (lt_of_lt_of_le ht.2 ht₀₁)⟩⟩

/-- The three late events in one bundled `𝓝[<] 1` event. -/
theorem late_event {a : ℕ → ℕ} :
    ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), 3 / 4 < t ∧
      (t, (0 : ESpace)) ∈ MixedAxisPreservation.localDomain h qbigSel ∧
      |(a 0 : ℝ) * PhysicalWaveSum.physicalQ h (t, (0 : ESpace))| < 1 / 2 := by
  have hE1 : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), (3 / 4 : ℝ) < t := by
    rw [show (𝓝[<] (1 : ℝ)) = 𝓝 (1 : ℝ) ⊓ principal (Iio (1 : ℝ)) from rfl,
      eventually_inf_principal]
    refine eventually_of_mem (lt_mem_nhds (by norm_num : (3 / 4 : ℝ) < (1 : ℝ))) ?_
    intro x hx _
    exact hx
  have hE2 : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ),
      (t, (0 : ESpace)) ∈ MixedAxisPreservation.localDomain h qbigSel :=
    MixedAxisPreservation.origin_eventually_localDomain outgoing.data.h_pos
      outgoing.data.h_lt_half qbigSel_pos
  have hl : Tendsto (fun t : ℝ => |(a 0 : ℝ) * PhysicalWaveSum.physicalQ h (t, (0 : ESpace))|)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hkey := ((tendsto_const_nhds.mul
        (AxisPreservation.physicalQ_origin_tendsto outgoing.data.h_pos
          outgoing.data.h_lt_half)).abs :
      Tendsto (fun t : ℝ => |(a 0 : ℝ) * PhysicalWaveSum.physicalQ h (t, (0 : ESpace))|)
        (𝓝[<] (1 : ℝ)) (𝓝 |(a 0 : ℝ) * 0|))
    simpa only [mul_zero, abs_zero] using hkey
  have hE3 := hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hE1, hE2, hE3] with t ht1 ht2 ht3
  exact ⟨ht1, ht2, ht3⟩

/-- The third bridge instantiated for the assembled selected field: every
bridge input is proved here except the polynomial upper envelope `hup`
(the T1–T4 residual). -/
theorem vorticityRateBound_of_polyUpper {a : ℕ → ℕ}
    (hS : MixedCandidateWitness.SelectedSchedule h qbigSel
      ActualCandidateAssembly.selectedPotentialStages
      ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages a)
    {forcing : ProblemStatement.VelocityField}
    (hc : CandidateProperties (R3CompactCandidate.periodicVelocity (ASum a) (BSum a))
      (R3CompactCandidate.periodicPressure (PSum a)) forcing)
    {β c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1)
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), V (uSel a) t ≤ c₂ * (1 - t) ^ (-β)) :
    VorticityRateBound (uSel a) := by
  obtain ⟨_, _, _, _, haT, _, _, _⟩ := hS
  have hprop := of_localized_fields hc
  obtain ⟨tL, htL, hlate⟩ := exists_Ico_of_eventually (late_event (a := a))
  set tm := max t₀ tL with htmdef
  have htmI : tm ∈ Ico (0 : ℝ) 1 :=
    ⟨le_trans ht₀.1 (le_max_left _ _), max_lt ht₀.2 htL.2⟩
  have hup' : ∀ t ∈ Ico tm (1 : ℝ), V (uSel a) t ≤ c₂ * (1 - t) ^ (-β) :=
    fun t ht => hup t ⟨(le_max_left t₀ tL).trans ht.1, ht.2⟩
  have haxis' : ∀ t ∈ Ico tm (1 : ℝ),
      (2 * modulation.profiles.f (0, 0)) * (1 - t) ^ (-(CoordinateAlgebra.A h + 1 / 2)) ≤
        officialEuclideanNorm (vorticity (uncurry (uSel a)) t (0 : Navier.Space)) :=
    axis_lower_bound hprop.velocity_smooth haT htmI
      (fun t ht => hlate t ⟨(le_max_right t₀ tL).trans ht.1, ht.2⟩)
  have h0tm : 0 ≤ tm := le_trans ht₀.1 (le_max_left t₀ tL)
  have hbdd' : ∃ C₃, ∀ t ∈ Ico (0 : ℝ) tm, V (uSel a) t ≤ C₃ :=
    v_bounded_before (u := uSel a) (t₀ := tm) (t₁ := (tm + 1) / 2) hprop
      (by linarith [h0tm]) (by linarith [htmI.2]) (by linarith [htmI.2])
  exact vorticityRateBound_of_polyUpper_axisLower hprop htmI hc₂ hup'
    (mul_pos zero_lt_two (FinalSlowBase.f_axis_positive modulation))
    (by have heq : CoordinateAlgebra.A h = 1 / 2 + h := rfl; linarith [outgoing.data.h_pos])
    haxis' hbdd'

/-- The retained concrete schedule selected by the witness. -/
noncomputable def aSel : ℕ → ℕ :=
  Classical.choose ActualCandidateAssembly.selected_witness

/-- Rate bound for the concrete selected compact candidate field: the axis
lower bound and the pre-window boundedness are proved; the single remaining
assumption is the T1–T4 polynomial upper envelope. -/
theorem vorticityRateBound_sel_of_polyUpper {β c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1)
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), V (uSel aSel) t ≤ c₂ * (1 - t) ^ (-β)) :
    VorticityRateBound (uSel aSel) := by
  obtain ⟨hS, _, _, _, forcing, hc, _⟩ :=
    Classical.choose_spec ActualCandidateAssembly.selected_witness
  exact vorticityRateBound_of_polyUpper hS hc hc₂ ht₀ hup

/-- The first divergence crown for the selected compact candidate, conditional
only on the named T1–T4 upper-envelope hypothesis. -/
theorem vorticity_integral_divergence_sel_of_polyUpper {β c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1)
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), V (uSel aSel) t ≤ c₂ * (1 - t) ^ (-β)) :
    ¬ ∃ B : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, V (uSel aSel) s ≤ B := by
  obtain ⟨hS, _, _, _, forcing, hc, _⟩ :=
    Classical.choose_spec ActualCandidateAssembly.selected_witness
  exact vorticity_integral_divergence_of_rate_bound (of_localized_fields hc)
    (vorticityRateBound_of_polyUpper hS hc hc₂ ht₀ hup)

/-- The `lintegral` crown for the selected compact candidate, conditional only
on the named T1–T4 upper-envelope hypothesis. -/
theorem lintegral_vorticity_divergence_sel_of_polyUpper {β c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1)
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), V (uSel aSel) t ≤ c₂ * (1 - t) ^ (-β)) :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (V (uSel aSel) t) = ⊤ := by
  obtain ⟨hS, _, _, _, forcing, hc, _⟩ :=
    Classical.choose_spec ActualCandidateAssembly.selected_witness
  exact lintegral_vorticity_integral_divergence_of_rate_bound (of_localized_fields hc)
    (vorticityRateBound_of_polyUpper hS hc hc₂ ht₀ hup)

end Navier.Analysis.BKMEnvAxis

#check @Navier.Analysis.BKMEnvAxis.uSel_germ
#print axioms Navier.Analysis.BKMEnvAxis.uSel_germ
#check @Navier.Analysis.BKMEnvAxis.vort_eq_spatialCurl
#print axioms Navier.Analysis.BKMEnvAxis.vort_eq_spatialCurl
#check @Navier.Analysis.BKMEnvAxis.axis_lower_bound
#print axioms Navier.Analysis.BKMEnvAxis.axis_lower_bound
#check @Navier.Analysis.BKMEnvAxis.v_bounded_before
#print axioms Navier.Analysis.BKMEnvAxis.v_bounded_before
#check @Navier.Analysis.BKMEnvAxis.vorticityRateBound_sel_of_polyUpper
#print axioms Navier.Analysis.BKMEnvAxis.vorticityRateBound_sel_of_polyUpper
#check @Navier.Analysis.BKMEnvAxis.vorticity_integral_divergence_sel_of_polyUpper
#print axioms Navier.Analysis.BKMEnvAxis.vorticity_integral_divergence_sel_of_polyUpper
#check @Navier.Analysis.BKMEnvAxis.lintegral_vorticity_divergence_sel_of_polyUpper
#print axioms Navier.Analysis.BKMEnvAxis.lintegral_vorticity_divergence_sel_of_polyUpper
