import Navier.Analysis.SourceL1X1ShellFalsification
import Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
import Navier.Analysis.ContinuousLeiLinRepresentativeInvariant

/-!
# The general linked-box `SourceL1X1` premise is false

This module lifts the shell cascade from `SourceL1X1ShellFalsification` into
the repository's completed linked trajectory carrier.  For every positive
radius `ρ`, it supplies an element of `ActualLinkedBox 1 1 ρ ρ` whose
canonical everywhere representative fails `SourceL1X1`.

This is a statement about the general completed box, not about trajectories
which solve Navier--Stokes.  The proved scoped source-integrability route is
`LinkedBoxX2Carrier.boxX2_sourceL1X1_of_hv`: an `ActualLinkedBoxX2` record
supplies the integrated `X²` budget, while continuity of its gated
representative remains an explicit hypothesis.  `ActualLinkedBoxX2ContRep`
packages a continuous pinned representative, but transporting the provider
to that representative remains a separately named obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

namespace Navier.Analysis.SourceL1X1BoxFalsification

open Navier
open Navier.Analysis
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinRepresentativeInvariant
open Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
open Navier.Analysis.ContinuousLeiLinBoxProduct
open Navier.Analysis.SourceL1X1ShellFalsification

/-- A fixed point in the interior of the `m`-th shell window. -/
def tMid (m : ℕ) : ℝ := (tEnd m + tEnd (m + 1)) / 2

theorem tMid_mem_timeE (m : ℕ) : tMid m ∈ timeE m := by
  constructor <;> simp only [tMid] <;> linarith [tEnd_lt m]

theorem uu_time_eq_of_mem (a : ℝ) {s t : ℝ} {m : ℕ}
    (hs : s ∈ timeE m) (ht : t ∈ timeE m) : uu a s = uu a t := by
  funext ξ i
  rw [uu_slice a hs, uu_slice a ht]

theorem xm1Section_eq_of_mem (a : ℝ) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m) :
    xm1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_Xm1 a) t =
      xm1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_Xm1 a) (tMid m) := by
  have hraw := uu_time_eq_of_mem a ht (tMid_mem_timeE m)
  change toXm1Spatial (uu a t) (uu_coord_aes a t) (uu_coord_integrable_Xm1 a t) =
    toXm1Spatial (uu a (tMid m)) (uu_coord_aes a (tMid m))
      (uu_coord_integrable_Xm1 a (tMid m))
  apply Lp.ext
  have htRep := coeFn_toXm1Spatial (uu a t) (uu_coord_aes a t)
    (uu_coord_integrable_Xm1 a t)
  have hmRep := coeFn_toXm1Spatial (uu a (tMid m)) (uu_coord_aes a (tMid m))
    (uu_coord_integrable_Xm1 a (tMid m))
  filter_upwards [htRep, hmRep] with ξ htξ hmξ
  rw [htξ, hmξ, hraw]

theorem viscousX1Section_eq_of_mem (a : ℝ) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m) :
    viscousX1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_X1 a) 1 t =
      viscousX1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_X1 a) 1 (tMid m) := by
  have hraw := uu_time_eq_of_mem a ht (tMid_mem_timeE m)
  change toViscousX1Spatial 1 (uu a t) (uu_coord_aes a t)
      (uu_coord_integrable_X1 a t) =
    toViscousX1Spatial 1 (uu a (tMid m)) (uu_coord_aes a (tMid m))
      (uu_coord_integrable_X1 a (tMid m))
  apply Lp.ext
  have htRep := coeFn_toViscousX1Spatial 1 (uu a t) (uu_coord_aes a t)
    (uu_coord_integrable_X1 a t)
  have hmRep := coeFn_toViscousX1Spatial 1 (uu a (tMid m))
    (uu_coord_aes a (tMid m)) (uu_coord_integrable_X1 a (tMid m))
  filter_upwards [htRep, hmRep] with ξ htξ hmξ
  rw [htξ, hmξ, hraw]

def xm1ShellSimple (a : ℝ) (t : ℝ) : Xm1Spatial :=
  ∑' m : ℕ, (timeE m).indicator
    (fun _ => xm1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_Xm1 a) (tMid m)) t

def x1ShellSimple (a : ℝ) (t : ℝ) : ViscousX1Spatial 1 :=
  ∑' m : ℕ, (timeE m).indicator
    (fun _ => viscousX1Section (uu a) (uu_coord_aes a)
      (uu_coord_integrable_X1 a) 1 (tMid m)) t

theorem xm1ShellSimple_stronglyMeasurable (a : ℝ) :
    StronglyMeasurable (xm1ShellSimple a) := by
  apply StronglyMeasurable.tsum
  intro m
  exact stronglyMeasurable_const.indicator (timeE_measurable m)

theorem x1ShellSimple_stronglyMeasurable (a : ℝ) :
    StronglyMeasurable (x1ShellSimple a) := by
  apply StronglyMeasurable.tsum
  intro m
  exact stronglyMeasurable_const.indicator (timeE_measurable m)

theorem timeE_index_unique {t : ℝ} {m n : ℕ}
    (hm : t ∈ timeE m) (hn : t ∈ timeE n) : n = m := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have hd := timeE_disjoint n m hlt
    rw [disjoint_left] at hd
    exact (hd hn hm).elim
  · exact heq
  · have hd := timeE_disjoint m n hgt
    rw [disjoint_left] at hd
    exact (hd hm hn).elim

theorem xm1Section_eq_zero_of_off (a : ℝ) {t : ℝ}
    (ht : ∀ m, t ∉ timeE m) :
    xm1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_Xm1 a) t = 0 := by
  change toXm1Spatial (uu a t) (uu_coord_aes a t) (uu_coord_integrable_Xm1 a t) = 0
  apply Lp.ext
  have hrep := coeFn_toXm1Spatial (uu a t) (uu_coord_aes a t)
    (uu_coord_integrable_Xm1 a t)
  have hzero := Lp.coeFn_zero FourierCoordinateL1 1 xm1FrequencyMeasure
  filter_upwards [hrep, hzero] with ξ hξ hz
  rw [hξ, hz]
  apply PiLp.ext
  intro i
  simp [coordinateL1_apply, uu_notmem a ht]

theorem viscousX1Section_eq_zero_of_off (a : ℝ) {t : ℝ}
    (ht : ∀ m, t ∉ timeE m) :
    viscousX1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_X1 a) 1 t = 0 := by
  change toViscousX1Spatial 1 (uu a t) (uu_coord_aes a t)
    (uu_coord_integrable_X1 a t) = 0
  apply Lp.ext
  have hrep := coeFn_toViscousX1Spatial 1 (uu a t) (uu_coord_aes a t)
    (uu_coord_integrable_X1 a t)
  have hzero := Lp.coeFn_zero FourierCoordinateL1 1 (viscousX1FrequencyMeasure 1)
  filter_upwards [hrep, hzero] with ξ hξ hz
  rw [hξ, hz]
  apply PiLp.ext
  intro i
  simp [coordinateL1_apply, uu_notmem a ht]

theorem xm1ShellSimple_eq_section (a : ℝ) (t : ℝ) :
    xm1ShellSimple a t =
      xm1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_Xm1 a) t := by
  by_cases h : ∃ m, t ∈ timeE m
  · obtain ⟨m, hm⟩ := h
    have hsummand :
        (fun n : ℕ => (timeE n).indicator
          (fun _ => xm1Section (uu a) (uu_coord_aes a)
            (uu_coord_integrable_Xm1 a) (tMid n)) t) =
        fun n => if n = m then
          xm1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_Xm1 a) (tMid m)
        else 0 := by
      funext n
      rw [Set.indicator_apply]
      by_cases hn : t ∈ timeE n
      · have hnm : n = m := timeE_index_unique hm hn
        subst n
        simp [hm]
      · have hne : n ≠ m := fun hnm => hn (hnm ▸ hm)
        simp [hn, hne]
    rw [xm1ShellSimple, hsummand, tsum_ite_eq]
    exact (xm1Section_eq_of_mem a hm).symm
  · have hoff : ∀ m, t ∉ timeE m := fun m hm => h ⟨m, hm⟩
    rw [xm1Section_eq_zero_of_off a hoff]
    simp [xm1ShellSimple, hoff]

theorem x1ShellSimple_eq_section (a : ℝ) (t : ℝ) :
    x1ShellSimple a t =
      viscousX1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_X1 a) 1 t := by
  by_cases h : ∃ m, t ∈ timeE m
  · obtain ⟨m, hm⟩ := h
    have hsummand :
        (fun n : ℕ => (timeE n).indicator
          (fun _ => viscousX1Section (uu a) (uu_coord_aes a)
            (uu_coord_integrable_X1 a) 1 (tMid n)) t) =
        fun n => if n = m then
          viscousX1Section (uu a) (uu_coord_aes a)
            (uu_coord_integrable_X1 a) 1 (tMid m)
        else 0 := by
      funext n
      rw [Set.indicator_apply]
      by_cases hn : t ∈ timeE n
      · have hnm : n = m := timeE_index_unique hm hn
        subst n
        simp [hm]
      · have hne : n ≠ m := fun hnm => hn (hnm ▸ hm)
        simp [hn, hne]
    rw [x1ShellSimple, hsummand, tsum_ite_eq]
    exact (viscousX1Section_eq_of_mem a hm).symm
  · have hoff : ∀ m, t ∉ timeE m := fun m hm => h ⟨m, hm⟩
    rw [viscousX1Section_eq_zero_of_off a hoff]
    simp [x1ShellSimple, hoff]

theorem xm1Section_aestronglyMeasurable (a : ℝ) :
    AEStronglyMeasurable
      (xm1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_Xm1 a))
      (leiLinTimeMeasure 1) := by
  exact (xm1ShellSimple_stronglyMeasurable a).aestronglyMeasurable.congr
    (ae_of_all _ (xm1ShellSimple_eq_section a))

theorem x1Section_aestronglyMeasurable (a : ℝ) :
    AEStronglyMeasurable
      (viscousX1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_X1 a) 1)
      (leiLinTimeMeasure 1) := by
  exact (x1ShellSimple_stronglyMeasurable a).aestronglyMeasurable.congr
    (ae_of_all _ (x1ShellSimple_eq_section a))

theorem coordinateXm1Mass_uu_eq_zero_of_off (a : ℝ) {t : ℝ}
    (ht : ∀ m, t ∉ timeE m) : coordinateXm1Mass (uu a t) = 0 := by
  rw [← norm_xm1Section (uu a) (uu_coord_aes a) (uu_coord_integrable_Xm1 a) t,
    xm1Section_eq_zero_of_off a ht, norm_zero]

theorem coordinateX1Mass_uu_eq_zero_of_off (a : ℝ) {t : ℝ}
    (ht : ∀ m, t ∉ timeE m) : coordinateX1Mass (uu a t) = 0 := by
  have hnorm := norm_viscousX1Section (uu a) (uu_coord_aes a)
    (uu_coord_integrable_X1 a) 1 t
  rw [viscousX1Section_eq_zero_of_off a ht, norm_zero] at hnorm
  simpa using hnorm.symm

/-- A deliberately coarse uniform `X⁻¹` bound.  The first shell starts at
radius `32`, so the sharper shell bound has denominator at least `31`. -/
theorem coordinateXm1Mass_uu_uniform (a : ℝ) (t : ℝ) :
    coordinateXm1Mass (uu a t) ≤ |a| * muB := by
  by_cases h : ∃ m, t ∈ timeE m
  · obtain ⟨m, hm⟩ := h
    calc
      coordinateXm1Mass (uu a t) ≤ |a| * muB / (rsh m - 1) :=
        coordinateXm1Mass_uu a hm
      _ ≤ |a| * muB := by
        apply div_le_self
        · exact mul_nonneg (abs_nonneg a) muB_pos.le
        · linarith [rsh_ge m]
  · rw [coordinateXm1Mass_uu_eq_zero_of_off a (fun m hm => h ⟨m, hm⟩)]
    exact mul_nonneg (abs_nonneg a) muB_pos.le

theorem leiLinTimeMeasure_timeE (m : ℕ) :
    leiLinTimeMeasure 1 (timeE m) = volume (timeE m) := by
  rw [leiLinTimeMeasure, Measure.restrict_apply (timeE_measurable m)]
  congr 1
  rw [inter_eq_left]
  intro t ht
  exact ⟨(timeE_subset m ht).1.le, (timeE_subset m ht).2.le⟩

theorem leiLinTimeMeasure_timeE_toReal (m : ℕ) :
    (leiLinTimeMeasure 1 (timeE m)).toReal =
      (3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m := by
  rw [leiLinTimeMeasure_timeE, measure_timeE, ENNReal.toReal_ofReal]
  positivity

theorem summable_x1_shell_budget (a : ℝ) :
    Summable (fun m : ℕ =>
      ((rsh m + 1) * |a| * muB) * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m)) := by
  have hhalf : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hquarter : Summable (fun m : ℕ => (1 / 4 : ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine ((hhalf.mul_left (24 * |a| * muB)).add
    (hquarter.mul_left ((3 / 4 : ℝ) * |a| * muB))).congr ?_
  intro m
  symm
  have hpow : (2 : ℝ) ^ m * (1 / 4 : ℝ) ^ m = (1 / 2 : ℝ) ^ m := by
    rw [← mul_pow]
    norm_num
  calc
    ((rsh m + 1) * |a| * muB) * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) =
        (24 * |a| * muB) * ((2 : ℝ) ^ m * (1 / 4 : ℝ) ^ m) +
          ((3 / 4 : ℝ) * |a| * muB) * (1 / 4 : ℝ) ^ m := by
            rw [rsh, pow_add]
            norm_num
            ring
    _ = _ := by rw [hpow]

theorem pairwise_disjoint_timeE :
    Pairwise (fun m n => Disjoint (timeE m) (timeE n)) := by
  intro m n hmn
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact timeE_disjoint m n hlt
  · exact (hmn heq).elim
  · exact (timeE_disjoint n m hgt).symm

theorem tsum_x1_shell_budget (a : ℝ) :
    (∑' m : ℕ,
      ((rsh m + 1) * |a| * muB) * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m)) =
      49 * |a| * muB := by
  have hhalf : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hquarter : Summable (fun m : ℕ => (1 / 4 : ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have heq : (fun m : ℕ =>
      ((rsh m + 1) * |a| * muB) * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m)) =
      fun m => (24 * |a| * muB) * (1 / 2 : ℝ) ^ m +
        ((3 / 4 : ℝ) * |a| * muB) * (1 / 4 : ℝ) ^ m := by
    funext m
    have hpow : (2 : ℝ) ^ m * (1 / 4 : ℝ) ^ m = (1 / 2 : ℝ) ^ m := by
      rw [← mul_pow]
      norm_num
    calc
      ((rsh m + 1) * |a| * muB) * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) =
          (24 * |a| * muB) * ((2 : ℝ) ^ m * (1 / 4 : ℝ) ^ m) +
            ((3 / 4 : ℝ) * |a| * muB) * (1 / 4 : ℝ) ^ m := by
              rw [rsh, pow_add]
              norm_num
              ring
      _ = _ := by rw [hpow]
  rw [heq, Summable.tsum_add (hhalf.mul_left _) (hquarter.mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_geometric_two,
    tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)]
  norm_num
  ring

/-- The shell cascade has the time-integrated `X¹` budget required by the
actual trajectory lift. -/
theorem coordinateX1Mass_uu_integrable (a : ℝ) :
    Integrable (fun t => coordinateX1Mass (uu a t)) (leiLinTimeMeasure 1) := by
  let f : ℝ → ℝ := fun t => coordinateX1Mass (uu a t)
  have hfM : AEStronglyMeasurable f (leiLinTimeMeasure 1) := by
    have hnorm := (x1Section_aestronglyMeasurable a).norm
    apply hnorm.congr
    filter_upwards with t
    rw [norm_viscousX1Section]
    simp [f]
  have hwindow : ∀ m : ℕ, IntegrableOn f (timeE m) (leiLinTimeMeasure 1) := by
    intro m
    apply Integrable.mono'
      (integrableOn_const (μ := leiLinTimeMeasure 1) (s := timeE m)
        (C := (rsh m + 1) * |a| * muB))
      (hfM.mono_measure Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem (timeE_measurable m)] with t ht
    rw [Real.norm_of_nonneg]
    · simpa [f] using coordinateX1Mass_uu a ht
    · exact coordinateX1Mass_nonneg _
  have hsum : Summable (fun m : ℕ =>
      ∫ t in timeE m, ‖f t‖ ∂leiLinTimeMeasure 1) := by
    apply Summable.of_nonneg_of_le
      (fun m => integral_nonneg fun _ => norm_nonneg _)
      (fun m => ?_) (summable_x1_shell_budget a)
    calc
      (∫ t in timeE m, ‖f t‖ ∂leiLinTimeMeasure 1)
          = ‖∫ t in timeE m, ‖f t‖ ∂leiLinTimeMeasure 1‖ := by
              rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      _ ≤ ((rsh m + 1) * |a| * muB) *
          (leiLinTimeMeasure 1 (timeE m)).toReal := by
            apply norm_setIntegral_le_of_norm_le_const
              (measure_lt_top (leiLinTimeMeasure 1) (timeE m))
            intro t ht
            rw [Real.norm_of_nonneg (norm_nonneg _),
              Real.norm_of_nonneg (coordinateX1Mass_nonneg _)]
            simpa [f] using coordinateX1Mass_uu a ht
      _ = ((rsh m + 1) * |a| * muB) *
          ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) := by
            rw [leiLinTimeMeasure_timeE_toReal]
  have hunion := integrableOn_iUnion_of_summable_integral_norm hwindow hsum
  have hind : Integrable ((⋃ m : ℕ, timeE m).indicator f) (leiLinTimeMeasure 1) :=
    hunion.integrable_indicator (MeasurableSet.iUnion timeE_measurable)
  apply hind.congr
  filter_upwards with t
  rw [Set.indicator_apply]
  by_cases ht : t ∈ ⋃ m : ℕ, timeE m
  · simp [ht, f]
  · have hoff : ∀ m, t ∉ timeE m := by
      intro m hm
      exact ht (mem_iUnion_of_mem m hm)
    simp [ht, f, coordinateX1Mass_uu_eq_zero_of_off a hoff]

theorem integral_coordinateX1Mass_uu_le (a : ℝ) :
    (∫ t, coordinateX1Mass (uu a t) ∂leiLinTimeMeasure 1) ≤
      49 * |a| * muB := by
  let f : ℝ → ℝ := fun t => coordinateX1Mass (uu a t)
  have hf := coordinateX1Mass_uu_integrable a
  have hunion : IntegrableOn f (⋃ m : ℕ, timeE m) (leiLinTimeMeasure 1) :=
    hf.integrableOn
  have hwhole : (∫ t, f t ∂leiLinTimeMeasure 1) =
      ∫ t in ⋃ m : ℕ, timeE m, f t ∂leiLinTimeMeasure 1 := by
    rw [← integral_indicator (MeasurableSet.iUnion timeE_measurable)]
    apply integral_congr_ae
    filter_upwards with t
    rw [Set.indicator_apply]
    by_cases ht : t ∈ ⋃ m : ℕ, timeE m
    · simp [ht]
    · have hoff : ∀ m, t ∉ timeE m := by
        intro m hm
        exact ht (mem_iUnion_of_mem m hm)
      simp [ht, f, coordinateX1Mass_uu_eq_zero_of_off a hoff]
  rw [show (∫ t, coordinateX1Mass (uu a t) ∂leiLinTimeMeasure 1) =
      ∫ t, f t ∂leiLinTimeMeasure 1 by rfl,
    hwhole, integral_iUnion timeE_measurable pairwise_disjoint_timeE hunion]
  calc
    (∑' m : ℕ, ∫ t in timeE m, f t ∂leiLinTimeMeasure 1) ≤
        ∑' m : ℕ, ((rsh m + 1) * |a| * muB) *
          ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) := by
      apply Summable.tsum_le_tsum
      · intro m
        calc
          (∫ t in timeE m, f t ∂leiLinTimeMeasure 1)
              ≤ ‖∫ t in timeE m, f t ∂leiLinTimeMeasure 1‖ := le_abs_self _
          _ ≤ ((rsh m + 1) * |a| * muB) *
              (leiLinTimeMeasure 1 (timeE m)).toReal := by
                apply norm_setIntegral_le_of_norm_le_const
                  (measure_lt_top (leiLinTimeMeasure 1) (timeE m))
                intro t ht
                rw [Real.norm_of_nonneg]
                · simpa [f] using coordinateX1Mass_uu a ht
                · exact coordinateX1Mass_nonneg _
          _ = ((rsh m + 1) * |a| * muB) *
              ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) := by
                rw [leiLinTimeMeasure_timeE_toReal]
      · exact (hasSum_integral_iUnion timeE_measurable pairwise_disjoint_timeE hunion).summable
      · exact summable_x1_shell_budget a
    _ = 49 * |a| * muB := tsum_x1_shell_budget a

theorem norm_toXm1TimeSlot_uu_le (a R : ℝ)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, coordinateXm1Mass (uu a t) ≤ R) :
    ‖toXm1TimeSlot (uu a) (uu_coord_aes a) (uu_coord_integrable_Xm1 a)
      1 R (xm1Section_aestronglyMeasurable a) hR‖ ≤ |a| * muB := by
  have h := Lp.norm_le_of_ae_bound (f := toXm1TimeSlot (uu a)
    (uu_coord_aes a) (uu_coord_integrable_Xm1 a) 1 R
    (xm1Section_aestronglyMeasurable a) hR)
    (mul_nonneg (abs_nonneg a) muB_pos.le) (by
      have hcoe := coeFn_toXm1TimeSlot (uu a) (uu_coord_aes a)
        (uu_coord_integrable_Xm1 a) 1 R (xm1Section_aestronglyMeasurable a) hR
      filter_upwards [hcoe] with t ht
      rw [ht, norm_xm1Section]
      exact coordinateXm1Mass_uu_uniform a t)
  simpa using h

theorem norm_toViscousX1TimeSlot_uu (a : ℝ) :
    ‖toViscousX1TimeSlot (uu a) (uu_coord_aes a) (uu_coord_integrable_X1 a)
      1 1 (x1Section_aestronglyMeasurable a) (coordinateX1Mass_uu_integrable a)‖ =
      ∫ t, coordinateX1Mass (uu a t) ∂leiLinTimeMeasure 1 := by
  rw [L1.norm_eq_integral_norm]
  have hcoe := coeFn_toViscousX1TimeSlot (uu a) (uu_coord_aes a)
    (uu_coord_integrable_X1 a) 1 1 (x1Section_aestronglyMeasurable a)
    (coordinateX1Mass_uu_integrable a)
  apply integral_congr_ae
  filter_upwards [hcoe] with t ht
  rw [ht, norm_viscousX1Section]
  simp

/-- Amplitude small enough for both completed box coordinates. -/
def boxAmplitude (ρ : ℝ) : ℝ := ρ / (100 * (muB + 1))

theorem boxAmplitude_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < boxAmplitude ρ := by
  unfold boxAmplitude
  exact div_pos hρ (mul_pos (by norm_num) (by linarith [muB_pos]))

theorem boxAmplitude_xm1_le {ρ : ℝ} (hρ : 0 < ρ) :
    |boxAmplitude ρ| * muB ≤ ρ := by
  rw [abs_of_pos (boxAmplitude_pos hρ)]
  unfold boxAmplitude
  have hden : 0 < 100 * (muB + 1) := mul_pos (by norm_num) (by linarith [muB_pos])
  have heq : ρ / (100 * (muB + 1)) * muB =
      (ρ * muB) / (100 * (muB + 1)) := by ring
  rw [heq]
  apply (div_le_iff₀ hden).2
  nlinarith [muB_pos, mul_pos hρ muB_pos]

theorem boxAmplitude_x1_le {ρ : ℝ} (hρ : 0 < ρ) :
    49 * |boxAmplitude ρ| * muB ≤ ρ := by
  rw [abs_of_pos (boxAmplitude_pos hρ)]
  unfold boxAmplitude
  have hden : 0 < 100 * (muB + 1) := mul_pos (by norm_num) (by linarith [muB_pos])
  have heq : 49 * (ρ / (100 * (muB + 1))) * muB =
      (49 * ρ * muB) / (100 * (muB + 1)) := by ring
  rw [heq]
  apply (div_le_iff₀ hden).2
  nlinarith [muB_pos, mul_pos hρ muB_pos]

def cascadeCarrier (ρ : ℝ) (hρ : 0 < ρ) : ActualLinkedCarrier 1 1 :=
  actualLinkedOfRaw 1 1 ρ (uu (boxAmplitude ρ))
    (uu_coord_aes (boxAmplitude ρ))
    (uu_coord_integrable_Xm1 (boxAmplitude ρ))
    (uu_coord_integrable_X1 (boxAmplitude ρ))
    (xm1Section_aestronglyMeasurable (boxAmplitude ρ))
    (x1Section_aestronglyMeasurable (boxAmplitude ρ))
    (fun t _ => (coordinateXm1Mass_uu_uniform (boxAmplitude ρ) t).trans
      (boxAmplitude_xm1_le hρ))
    (coordinateX1Mass_uu_integrable (boxAmplitude ρ))

/-- The shell cascade as a genuine element of the completed linked box. -/
def cascadeBox (ρ : ℝ) (hρ : 0 < ρ) : ActualLinkedBox 1 1 ρ ρ := by
  refine ⟨cascadeCarrier ρ hρ, ?_⟩
  constructor
  · change ‖toXm1TimeSlot (uu (boxAmplitude ρ))
        (uu_coord_aes (boxAmplitude ρ))
        (uu_coord_integrable_Xm1 (boxAmplitude ρ)) 1 ρ
        (xm1Section_aestronglyMeasurable (boxAmplitude ρ))
        (fun t _ => (coordinateXm1Mass_uu_uniform (boxAmplitude ρ) t).trans
          (boxAmplitude_xm1_le hρ))‖ ≤ ρ
    exact (norm_toXm1TimeSlot_uu_le (boxAmplitude ρ) ρ
      (fun t _ => (coordinateXm1Mass_uu_uniform (boxAmplitude ρ) t).trans
        (boxAmplitude_xm1_le hρ))).trans
      (boxAmplitude_xm1_le hρ)
  · change ‖toViscousX1TimeSlot (uu (boxAmplitude ρ))
        (uu_coord_aes (boxAmplitude ρ))
        (uu_coord_integrable_X1 (boxAmplitude ρ)) 1 1
        (x1Section_aestronglyMeasurable (boxAmplitude ρ))
        (coordinateX1Mass_uu_integrable (boxAmplitude ρ))‖ ≤ ρ
    rw [norm_toViscousX1TimeSlot_uu]
    exact (integral_coordinateX1Mass_uu_le (boxAmplitude ρ)).trans
      (boxAmplitude_x1_le hρ)

theorem cascade_ae_everywhereRepresentative (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᵐ t ∂leiLinTimeMeasure 1,
      uu (boxAmplitude ρ) t =ᵐ[volume]
        everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ) t := by
  let u := uu (boxAmplitude ρ)
  let x := cascadeCarrier ρ hρ
  have hrawBound : ∀ t ∈ Icc (0 : ℝ) 1, coordinateXm1Mass (u t) ≤ ρ :=
    fun t _ => (coordinateXm1Mass_uu_uniform (boxAmplitude ρ) t).trans
      (boxAmplitude_xm1_le hρ)
  have hslot :
      toXm1TimeSlot u (uu_coord_aes (boxAmplitude ρ))
          (uu_coord_integrable_Xm1 (boxAmplitude ρ)) 1 ρ
          (xm1Section_aestronglyMeasurable (boxAmplitude ρ)) hrawBound =
        everywhereXm1TimeSlot 1 (by norm_num) 1 x := by
    rw [everywhereXm1TimeSlot_eq]
    rfl
  exact nested_ae_eq_of_toXm1TimeSlot_eq 1 (by norm_num) 1 ρ
    ‖(x.1.fst : Xm1TimeSlot 1)‖ u (everywhereRawRepresentative 1 1 x)
    (uu_coord_aes (boxAmplitude ρ))
    (everywhereRawRepresentative_aestronglyMeasurable 1 (by norm_num) 1 x)
    (uu_coord_integrable_Xm1 (boxAmplitude ρ))
    (everywhereRawRepresentative_xm1_integrable 1 1 x)
    (xm1Section_aestronglyMeasurable (boxAmplitude ρ))
    (everywhereXm1Section_aestronglyMeasurable 1 (by norm_num) 1 x)
    hrawBound
    (fun t _ => coordinateXm1Mass_everywhereRawRepresentative_le 1 (by norm_num) 1 x t)
    hslot

theorem not_sourceL1X1_cascadeRepresentative (ρ : ℝ) (hρ : 0 < ρ) :
    ¬ SourceL1X1 1
      (everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ)) := by
  intro hrep
  let u := uu (boxAmplitude ρ)
  let v := everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ)
  have hae : ∀ᵐ t ∂leiLinTimeMeasure 1, u t =ᵐ[volume] v t := by
    simpa [u, v] using cascade_ae_everywhereRepresentative ρ hρ
  have hsource : ∀ᵐ t ∂leiLinTimeMeasure 1,
      continuousNavierSource u u t = continuousNavierSource v v t :=
    continuousNavierSource_congr_ae 1 u v hae
  have hsourceProd : ∀ᵐ p : ES × ℝ ∂volume.prod (leiLinTimeMeasure 1),
      continuousNavierSource u u p.2 p.1 =
        continuousNavierSource v v p.2 p.1 := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd).ae hsource] with p hp
    exact congrFun hp p.1
  have hraw : SourceL1X1 1 u := by
    intro i
    apply (hrep i).congr
    filter_upwards [hsourceProd] with p hp
    rw [hp]
  exact not_sourceL1X1_uu (boxAmplitude ρ) (boxAmplitude_pos hρ) hraw

/-- The exact universal premise consumed by the general restart box is false
already at `(ν,T)=(1,1)` for every positive radius. -/
theorem not_forall_actualLinkedBox_sourceL1X1 (ρ : ℝ) (hρ : 0 < ρ) :
    ¬ ∀ x : ActualLinkedBox 1 1 ρ ρ,
      SourceL1X1 1 (everywhereRawRepresentative 1 1 x.1) := by
  intro h
  exact not_sourceL1X1_cascadeRepresentative ρ hρ (h (cascadeBox ρ hρ))

#check @not_forall_actualLinkedBox_sourceL1X1
#print axioms not_forall_actualLinkedBox_sourceL1X1

end Navier.Analysis.SourceL1X1BoxFalsification
