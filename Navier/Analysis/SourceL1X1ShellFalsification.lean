import Mathlib.Analysis.Normed.Lp.PiLp
import Navier.Analysis.ContinuousLeiLinTimeDuhamel
import Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
import Navier.Routes.R7.PhaseSymbol

/-!
# Kernel falsification of the general-box `SourceL1X1` estimate

The restart interface `Navier.Analysis.WholeSpaceRestartMildInterface` exposes
as a genuine residual the premise

```
H : ∀ x : ActualLinkedBox ν T (2 * restartRadius u₀) (2 * restartRadius u₀),
      SourceL1X1 T (everywhereRawRepresentative ν T x.1)
```

i.e. that every element of the completed linked `(L∞_t X⁻¹ ∩ L¹_t νX¹)` box
has a self-interaction source that is spacetime `‖ξ‖`-integrable.  This module
kernel-refutes the raw-field reading of that claim at `ν = 1, T = 1`: for
every amplitude `a > 0` it constructs an explicit frequency-shell cascade
`uu a` whose every time section is coordinatewise `X⁻¹`- and `X¹`-integrable
with budgets `O(a)` (the `X⁻¹` slice weight is bounded by `(rₘ−1)⁻¹ |a|` on the
shell support and the `X¹` slice weight by `(rₘ+1) |a|`), and whose
coordinate-zero source integrand `‖ξ‖ · ‖B(uu a, uu a) ξ 0‖` has the fixed
per-rectangle integral

`K₀ = (9/25) · a² · μ₃₈ · μ_C · 768`

on each rectangle `ballWₘ × Eₘ` — the shell self-interaction output lands at
`≈ 2·rₘ·v₀`, the Leray correction keeps at least a `9/25` fraction of the
`e₀`-polarized convection coordinate there, the convolution of the shell
indicator with itself is at least `μ₃₈` on `ballWₘ`, and `rₘ² · |Eₘ| = 768`
is constant in `m`.  The total weighted source integral is therefore `⊤`.

The companion module `SourceL1X1BoxFalsification` lifts this explicit field
into an actual `ActualLinkedBox 1 1 ρ ρ` element through the repository's own
trajectory lift (`realized_time_slots_eq_of_raw`) and transfers the
divergence to the canonical `everywhereRawRepresentative` through
`continuousNavierSource_congr_ae`, refuting `H` at the exact interface type.

Scope of the kill: the universal reading of `H` instantiated at
`(ν, T) = (1, 1)` and any box radius `ρ > 0`.  The companion suppliers
`sourceL1X1_constant_fourierDatum` and
`exists_ne_zero_constant_fourierDatum_sourceL1X1` (constant-in-time Fourier
trajectories) are unaffected, and crown A
(`ProblemStatements.WholeSpaceGlobalRegularity`) is untouched by this entry.
The witness carries no claim about classical Navier–Stokes solutions.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Convolution Matrix

attribute [local instance] Classical.propDecidable

namespace Navier.Analysis.SourceL1X1ShellFalsification

open Navier
open Navier.Analysis
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ComplexLerayProjection
open Navier.Routes.R7

/-! ## Fixed shell geometry -/

/-- Shell frequency radii `2^(m+5)`, all at least `32`. -/
def rsh (m : ℕ) : ℝ := (2 : ℝ) ^ (m + 5)

theorem rsh_ge (m : ℕ) : (32 : ℝ) ≤ rsh m := by
  have h : (2 : ℝ) ^ (m + 5) = (2 : ℝ) ^ m * 2 ^ 5 := by
    rw [pow_add]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2) m
    simpa using this
  calc (32 : ℝ) = (1 : ℝ) * (2 : ℝ) ^ 5 := by norm_num
    _ ≤ (2 : ℝ) ^ m * 2 ^ 5 :=
      mul_le_mul_of_nonneg_right h1 (pow_nonneg (le_of_lt zero_lt_two) 5)
    _ = (2 : ℝ) ^ (m + 5) := h.symm

theorem rsh_pos (m : ℕ) : (0 : ℝ) < rsh m := pow_pos zero_lt_two _

theorem rsh_sub_one_pos (m : ℕ) : (0 : ℝ) < rsh m - 1 := by
  linarith [rsh_ge m]

/-- The shell direction `(3/5, 4/5, 0)`: a unit vector with content in
coordinates `0` and `1`, so the Leray correction never cancels completely. -/
def v0 : ES := !₂[(3 / 5 : ℝ), (4 / 5 : ℝ), (0 : ℝ)]

theorem norm_v0 : ‖v0‖ = 1 := by
  have h : ‖v0‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    have h0 : v0 0 = (3 / 5 : ℝ) := rfl
    have h1 : v0 1 = (4 / 5 : ℝ) := rfl
    have h2 : v0 2 = (0 : ℝ) := rfl
    rw [h0, h1, h2]
    norm_num
  nlinarith [norm_nonneg v0]

/-- Shell center of shell `m`. -/
def eta (m : ℕ) : ES := rsh m • v0

theorem norm_eta (m : ℕ) : ‖eta m‖ = rsh m := by
  rw [eta, norm_smul, norm_v0, mul_one, Real.norm_of_nonneg (le_of_lt (rsh_pos m))]

/-- The shell support ball in frequency space. -/
def ballB (m : ℕ) : Set ES := Metric.ball (eta m) 1

/-- The output ball where the self-interaction of shell `m` lands. -/
def ballW (m : ℕ) : Set ES := Metric.ball ((2 : ℝ) • eta m) (1 / 2)

theorem measurableSet_ballB (m : ℕ) : MeasurableSet (ballB m) :=
  IsOpen.measurableSet Metric.isOpen_ball

theorem measurableSet_ballW (m : ℕ) : MeasurableSet (ballW m) :=
  IsOpen.measurableSet Metric.isOpen_ball

theorem mem_ballB (m : ℕ) (ξ : ES) : ξ ∈ ballB m ↔ dist ξ (eta m) < 1 := by
  simp [ballB, Metric.mem_ball]

theorem mem_ballW (m : ℕ) (ξ : ES) : ξ ∈ ballW m ↔ dist ξ ((2 : ℝ) • eta m) < 1 / 2 := by
  simp [ballW, Metric.mem_ball]

/-- Unit-ball volume at the origin is finite. -/
theorem volume_ball_origin_lt_top {r : ℝ} (_hr : 0 < r) :
    volume (Metric.ball (0 : ES) r) < ⊤ := by
  rw [EuclideanSpace.volume_ball]
  refine ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    ENNReal.ofReal_lt_top

theorem volume_ballB_lt_top (m : ℕ) : volume (ballB m) < ⊤ := by
  rw [ballB, EuclideanSpace.volume_ball, ← EuclideanSpace.volume_ball (Fin 3) (0 : ES) (1 : ℝ)]
  exact volume_ball_origin_lt_top zero_lt_one

theorem volume_ballW_lt_top (m : ℕ) : volume (ballW m) < ⊤ := by
  rw [ballW, EuclideanSpace.volume_ball,
    ← EuclideanSpace.volume_ball (Fin 3) (0 : ES) (1 / 2 : ℝ)]
  exact volume_ball_origin_lt_top (by norm_num)

theorem measure_ballW_pos (m : ℕ) :
    (0 : ENNReal) < volume (ballW m) := by
  rw [ballW]
  exact Metric.measure_ball_pos volume ((2 : ℝ) • eta m) (by norm_num : (0 : ℝ) < 1 / 2)

theorem measure_ballB_pos (m : ℕ) : (0 : ENNReal) < volume (ballB m) := by
  rw [ballB]
  exact Metric.measure_ball_pos volume (eta m) zero_lt_one

theorem measure_ball38_pos (m : ℕ) :
    (0 : ENNReal) < volume (Metric.ball (eta m) (3 / 8)) :=
  Metric.measure_ball_pos volume (eta m) (by norm_num : (0 : ℝ) < (3 / 8 : ℝ))

theorem measure_ball38_lt_top (m : ℕ) :
    volume (Metric.ball (eta m) (3 / 8)) < ⊤ := by
  rw [EuclideanSpace.volume_ball,
    ← EuclideanSpace.volume_ball (Fin 3) (0 : ES) (3 / 8 : ℝ)]
  exact volume_ball_origin_lt_top (by norm_num)

/-- Real unit-ball volume, used only through its finite positivity. -/
def muB : ℝ := (volume (Metric.ball (0 : ES) 1)).toReal

/-- Real half-ball volume (the volume of `ballW m`). -/
def muC : ℝ := (volume (Metric.ball (0 : ES) (1 / 2))).toReal

/-- Real `3/8`-ball volume (the convolution floor). -/
def mu38 : ℝ := (volume (Metric.ball (0 : ES) (3 / 8))).toReal

theorem muB_pos : 0 < muB := by
  rw [muB]
  exact ENNReal.toReal_pos
    ((Metric.measure_ball_pos volume (0 : ES) zero_lt_one).ne')
    (volume_ball_origin_lt_top zero_lt_one).ne

theorem muC_pos : 0 < muC := by
  rw [muC]
  exact ENNReal.toReal_pos
    ((Metric.measure_ball_pos volume (0 : ES) (by norm_num : (0 : ℝ) < 1 / 2)).ne')
    (volume_ball_origin_lt_top (by norm_num)).ne

theorem mu38_pos : 0 < mu38 := by
  rw [mu38]
  exact ENNReal.toReal_pos
    ((Metric.measure_ball_pos volume (0 : ES) (by norm_num : (0 : ℝ) < 3 / 8)).ne')
    (volume_ball_origin_lt_top (by norm_num)).ne

theorem volume_ballW_toReal (m : ℕ) : (volume (ballW m)).toReal = muC := by
  rw [ballW, muC, EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]

theorem volume_ball38_toReal (m : ℕ) :
    (volume (Metric.ball (eta m) (3 / 8))).toReal = mu38 := by
  rw [mu38, EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]

theorem volume_ballB_toReal (m : ℕ) : (volume (ballB m)).toReal = muB := by
  rw [ballB, muB, EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]

/-! ### Shell time windows `Eₘ = Ioo (1 − 4⁻ᵐ) (1 − 4⁻ᵐ⁺¹)` -/

/-- Right endpoints of the shell time windows. -/
def tEnd (m : ℕ) : ℝ := 1 - (1 / 4 : ℝ) ^ m

def timeE (m : ℕ) : Set ℝ := Ioo (tEnd m) (tEnd (m + 1))

theorem inv4_pow_lt (m : ℕ) :
    (1 / 4 : ℝ) ^ (m + 1) < (1 / 4 : ℝ) ^ m := by
  have hp : 0 < (1 / 4 : ℝ) ^ m := pow_pos (by norm_num) m
  calc (1 / 4 : ℝ) ^ (m + 1) = (1 / 4 : ℝ) ^ m * (1 / 4) := by rw [pow_add, pow_one]
    _ < (1 / 4 : ℝ) ^ m * 1 := mul_lt_mul_of_pos_left (by norm_num) hp
    _ = _ := mul_one _

theorem inv4_pow_le_one (m : ℕ) : (1 / 4 : ℝ) ^ m ≤ 1 := by
  have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ))
    (by norm_num : (1 / 4 : ℝ) ≤ (1 : ℝ)) m
  simpa using this

theorem tEnd_zero : tEnd 0 = 0 := by simp [tEnd]

theorem tEnd_lt (m : ℕ) : tEnd m < tEnd (m + 1) := by
  simp only [tEnd]
  linarith [inv4_pow_lt m]

theorem tEnd_le_one (m : ℕ) : tEnd m ≤ 1 := by
  simp only [tEnd]
  have hpos : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ m := pow_nonneg (by norm_num) m
  linarith [inv4_pow_le_one m, hpos]

theorem tEnd_nonneg (m : ℕ) : (0 : ℝ) ≤ tEnd m := by
  simp only [tEnd]
  linarith [inv4_pow_le_one m]

theorem tEnd_mono {k j : ℕ} (hkj : k ≤ j) : tEnd k ≤ tEnd j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  have hpow : (1 / 4 : ℝ) ^ (k + d) = (1 / 4 : ℝ) ^ k * (1 / 4 : ℝ) ^ d :=
    pow_add _ _ _
  have hle : (1 / 4 : ℝ) ^ d ≤ 1 := inv4_pow_le_one d
  have hge : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k := pow_nonneg (by norm_num) k
  have hpow' : (1 / 4 : ℝ) ^ (k + d) ≤ (1 / 4 : ℝ) ^ k := by
    rw [hpow]
    calc (1 / 4 : ℝ) ^ k * (1 / 4 : ℝ) ^ d ≤ (1 / 4 : ℝ) ^ k * 1 :=
        mul_le_mul_of_nonneg_left hle hge
      _ = (1 / 4 : ℝ) ^ k := mul_one _
  simp only [tEnd]
  linarith

theorem timeE_subset (m : ℕ) : timeE m ⊆ Ioo (0 : ℝ) 1 := by
  intro t ht
  exact ⟨lt_of_le_of_lt (tEnd_nonneg m) ht.1, lt_of_lt_of_le ht.2 (tEnd_le_one (m + 1))⟩

theorem timeE_disjoint (m n : ℕ) (h : m < n) : Disjoint (timeE m) (timeE n) := by
  rw [disjoint_left]
  intro t ht1 ht2
  have hmn : tEnd (m + 1) ≤ tEnd n := tEnd_mono (by omega)
  linarith [ht1.2, ht2.1, hmn]

theorem timeE_measurable (m : ℕ) : MeasurableSet (timeE m) :=
  isOpen_Ioo.measurableSet

theorem measure_timeE (m : ℕ) :
    volume (timeE m) = ENNReal.ofReal ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) := by
  rw [timeE, Real.volume_Ioo]
  congr 1
  have h1 : (1 / 4 : ℝ) ^ (m + 1) = (1 / 4 : ℝ) ^ m * (1 / 4) := by rw [pow_add, pow_one]
  simp only [tEnd, h1]
  ring

theorem measure_timeE_lt_top (m : ℕ) : volume (timeE m) < ⊤ := by
  rw [measure_timeE]
  exact ENNReal.ofReal_lt_top

/-! ## The shell-cascade field `uu a` -/

/-- The shell-pulse spacetime Fourier field: shell `m` fires on
`ballB m × timeE m` in coordinate `0` with constant amplitude `a`. -/
def uu (a : ℝ) : ℝ → ES → ContinuousLeiLinSpace.ComplexSpace := by
  classical
  exact fun t ξ i => ∑' m : ℕ,
    if t ∈ timeE m ∧ i = 0 ∧ ξ ∈ ballB m then (a : ℂ) else 0

theorem uu_slice (a : ℝ) {t m₀ ξ i} (ht : t ∈ timeE m₀) :
    uu a t ξ i = if i = 0 ∧ ξ ∈ ballB m₀ then (a : ℂ) else 0 := by
  classical
  show (∑' m : ℕ, if t ∈ timeE m ∧ i = 0 ∧ ξ ∈ ballB m then (a : ℂ) else 0) = _
  have hf : (fun m : ℕ => if t ∈ timeE m ∧ i = 0 ∧ ξ ∈ ballB m then (a : ℂ) else 0)
      = fun m => if m = m₀ then (if i = 0 ∧ ξ ∈ ballB m₀ then (a : ℂ) else 0) else 0 := by
    funext m
    by_cases h : m = m₀
    · rw [h]
      by_cases hc : i = 0 ∧ ξ ∈ ballB m₀
      · simp [hc, ht]
      · simp [hc]
    · have hmt : t ∉ timeE m := by
        rcases lt_trichotomy m m₀ with hlt | heq | hgt
        · have := timeE_disjoint m m₀ hlt
          rw [disjoint_left] at this
          intro hmem
          exact this hmem ht
        · exact (h heq).elim
        · have := timeE_disjoint m₀ m hgt
          rw [disjoint_left] at this
          intro hmem
          exact this ht hmem
      simp [hmt, h]
  rw [hf, tsum_ite_eq m₀]

theorem uu_notmem (a : ℝ) {t ξ i} (h : ∀ m, t ∉ timeE m) : uu a t ξ i = 0 := by
  classical
  show (∑' m : ℕ, if t ∈ timeE m ∧ i = 0 ∧ ξ ∈ ballB m then (a : ℂ) else 0) = 0
  have hf : (fun m : ℕ => if t ∈ timeE m ∧ i = 0 ∧ ξ ∈ ballB m then (a : ℂ) else 0)
      = fun _ => 0 := by
    funext m
    simp [h m]
  rw [hf, tsum_zero]

theorem uu_coord_eq (a : ℝ) (t : ℝ) {m₀ : ℕ} (ht : t ∈ timeE m₀) (i : Fin 3) :
    (fun ξ => uu a t ξ i) =
      (ballB m₀).indicator (fun _ : ES => if i = 0 then (a : ℂ) else 0) := by
  funext ξ
  rw [Set.indicator_apply, uu_slice a ht]
  by_cases hi : i = 0 <;> by_cases hξ : ξ ∈ ballB m₀ <;> simp [hi, hξ]

theorem uu_zero_coord (a : ℝ) (t : ℝ) {m₀ : ℕ} (ht : t ∈ timeE m₀) (i : Fin 3)
    (hi : i ≠ 0) : (fun ξ => uu a t ξ i) = 0 := by
  funext ξ
  rw [uu_slice a ht]
  simp [hi]

/-- A point outside every shell window. -/
theorem uu_slice_off (a : ℝ) {t : ℝ} (h : ∀ m, t ∉ timeE m) (ξ : ES) (i : Fin 3) :
    uu a t ξ i = 0 := uu_notmem a h

/-- Pointwise value of coordinate `0` on an active slice. -/
theorem uu_coord0_eq (a : ℝ) {t : ℝ} {m₀ : ℕ} (ht : t ∈ timeE m₀) (ξ : ES) :
    uu a t ξ (0 : Fin 3) = if ξ ∈ ballB m₀ then (a : ℂ) else 0 := by
  classical
  rw [uu_slice a ht]
  simp

/-- Pointwise vanishing of the off-coordinates on an active slice. -/
theorem uu_coord_off_eq (a : ℝ) {t : ℝ} {m₀ : ℕ} (ht : t ∈ timeE m₀) {i : Fin 3}
    (hi : i ≠ 0) (ξ : ES) : uu a t ξ i = 0 := by
  rw [uu_slice a ht]
  simp [hi]

/-! ### Slice measurability and integrability -/

theorem uu_coord_aes (a : ℝ) (t : ℝ) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ : ES => uu a t ξ i) volume := by
  by_cases h : ∃ m, t ∈ timeE m
  · obtain ⟨m, hm⟩ := h
    rw [uu_coord_eq a t hm i]
    exact (measurable_const.indicator (measurableSet_ballB m)).aestronglyMeasurable
  · have h0 : (fun ξ => uu a t ξ i) = fun _ => 0 := by
      funext ξ
      exact uu_notmem a (fun m hmem => h ⟨m, hmem⟩)
    rw [h0]
    exact aestronglyMeasurable_const

/-- A nonnegative constant on a finite-measure ball is integrable as an
indicator function. -/
theorem integrable_indicator_nnreal_ball (s : Set ES) (hs : MeasurableSet s)
    (hs_top : volume s < ⊤) (C : NNReal) :
    Integrable (fun ξ : ES => s.indicator (fun _ : ES => (C : ℝ)) ξ) volume := by
  refine ⟨(measurable_const.indicator hs).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hfn : (fun ξ => ENNReal.ofReal ‖s.indicator (fun _ : ES => (C : ℝ)) ξ‖)
      =ᵐ[volume] fun ξ => (C : ℝ≥0∞) * s.indicator (fun _ : ES => (1 : ℝ≥0∞)) ξ := by
    filter_upwards with ξ
    by_cases hξ : ξ ∈ s
    · simp [hξ]
    · simp [hξ]
  rw [lintegral_congr_ae hfn]
  have hm : Measurable (s.indicator (fun _ : ES => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hs
  rw [lintegral_const_mul _ hm, lintegral_indicator hs, setLIntegral_one]
  exact ENNReal.mul_lt_top (ENNReal.coe_lt_top (r := C)) hs_top

theorem integrable_zero_fun : Integrable (fun _ : ES => (0 : ℝ)) :=
  ⟨aestronglyMeasurable_const, by
    rw [hasFiniteIntegral_iff_norm]
    simp⟩

/-! ### Pointwise shell geometry bounds -/

theorem norm_sub_ballB_lt_one (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballB m) : ‖ξ - eta m‖ < 1 := by
  rw [← dist_eq_norm]
  exact (mem_ballB m ξ).mp hξ

theorem norm_ballB_gt_sub (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballB m) : rsh m - 1 < ‖ξ‖ := by
  have h1 : ‖eta m‖ ≤ ‖eta m - ξ‖ + ‖ξ‖ :=
    calc ‖eta m‖ = ‖(eta m - ξ) + ξ‖ := by rw [sub_add_cancel]
      _ ≤ ‖eta m - ξ‖ + ‖ξ‖ := norm_add_le _ _
  have hd : ‖eta m - ξ‖ < 1 := by
    rw [← dist_eq_norm, dist_comm]
    exact (mem_ballB m ξ).mp hξ
  rw [norm_eta] at h1
  linarith

theorem norm_ballB_lt (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballB m) : ‖ξ‖ < rsh m + 1 := by
  have h1 : ‖ξ‖ ≤ ‖ξ - eta m‖ + ‖eta m‖ :=
    calc ‖ξ‖ = ‖(ξ - eta m) + eta m‖ := by rw [sub_add_cancel]
      _ ≤ ‖ξ - eta m‖ + ‖eta m‖ := norm_add_le _ _
  have hd : ‖ξ - eta m‖ < 1 := norm_sub_ballB_lt_one m hξ
  rw [norm_eta] at h1
  linarith

theorem norm_sub_ballW_lt_half (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) : ‖ξ - (2 : ℝ) • eta m‖ < 1 / 2 := by
  rw [← dist_eq_norm]
  exact (mem_ballW m ξ).mp hξ

theorem norm_two_eta (m : ℕ) : ‖(2 : ℝ) • eta m‖ = 2 * rsh m := by
  rw [norm_smul, Real.norm_of_nonneg (le_of_lt two_pos), norm_eta]

theorem norm_ballW_gt (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) :
    2 * rsh m - 1 / 2 < ‖ξ‖ ∧ ‖ξ‖ < 2 * rsh m + 1 / 2 := by
  constructor
  · have h1 : ‖(2 : ℝ) • eta m‖ ≤ ‖(2 : ℝ) • eta m - ξ‖ + ‖ξ‖ :=
      calc ‖(2 : ℝ) • eta m‖ = ‖((2 : ℝ) • eta m - ξ) + ξ‖ := by rw [sub_add_cancel]
        _ ≤ ‖(2 : ℝ) • eta m - ξ‖ + ‖ξ‖ := norm_add_le _ _
    have hd : ‖(2 : ℝ) • eta m - ξ‖ < 1 / 2 := by
      rw [← dist_eq_norm, dist_comm]
      exact (mem_ballW m ξ).mp hξ
    rw [norm_two_eta] at h1
    linarith
  · have h1 : ‖ξ‖ ≤ ‖ξ - (2 : ℝ) • eta m‖ + ‖(2 : ℝ) • eta m‖ :=
      calc ‖ξ‖ = ‖(ξ - (2 : ℝ) • eta m) + (2 : ℝ) • eta m‖ := by rw [sub_add_cancel]
        _ ≤ ‖ξ - (2 : ℝ) • eta m‖ + ‖(2 : ℝ) • eta m‖ := norm_add_le _ _
    rw [norm_two_eta] at h1
    linarith [norm_sub_ballW_lt_half m hξ]

theorem two_eta_coords (m : ℕ) :
    ((2 : ℝ) • eta m) 0 = (6 / 5) * rsh m ∧ ((2 : ℝ) • eta m) 1 = (8 / 5) * rsh m ∧
      ((2 : ℝ) • eta m) 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [eta, v0, PiLp.smul_apply, smul_smul, mul_assoc] <;> ring

theorem abs_apply_le_norm {f : ES} (i : Fin 3) : |f i| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs]
  simpa using PiLp.norm_apply_le f i

/-- The four working geometric facts on the shell window `ballW m`. -/
theorem ballW_geometry (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) :
    rsh m ≤ ‖ξ‖ ∧ rsh m ≤ ξ 0 ∧ (3 / 2) * rsh m ≤ ξ 1 ∧ ‖ξ‖ ≤ (5 / 2) * rsh m := by
  obtain ⟨hgt, hlt⟩ := norm_ballW_gt m hξ
  have h₀ : (ξ - (2 : ℝ) • eta m) 0 ≥ -‖ξ - (2 : ℝ) • eta m‖ := by
    have h1 : |(ξ - (2 : ℝ) • eta m) 0| ≤ ‖ξ - (2 : ℝ) • eta m‖ := abs_apply_le_norm 0
    have h2 : -|(ξ - (2 : ℝ) • eta m) 0| ≤ (ξ - (2 : ℝ) • eta m) 0 := neg_abs_le _
    linarith [h1, h2]
  have h₁ : (ξ - (2 : ℝ) • eta m) 1 ≥ -‖ξ - (2 : ℝ) • eta m‖ := by
    have h1 : |(ξ - (2 : ℝ) • eta m) 1| ≤ ‖ξ - (2 : ℝ) • eta m‖ := abs_apply_le_norm 1
    have h2 : -|(ξ - (2 : ℝ) • eta m) 1| ≤ (ξ - (2 : ℝ) • eta m) 1 := neg_abs_le _
    linarith [h1, h2]
  obtain ⟨c₀, c₁, -⟩ := two_eta_coords m
  have hd : ‖ξ - (2 : ℝ) • eta m‖ < 1 / 2 := norm_sub_ballW_lt_half m hξ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (by linarith [rsh_ge m, hgt] : (rsh m : ℝ) < ‖ξ‖).le
  · calc rsh m ≤ (6 / 5) * rsh m - ‖ξ - (2 : ℝ) • eta m‖ := by linarith [rsh_ge m, hd]
      _ ≤ ((2 : ℝ) • eta m) 0 + (ξ - (2 : ℝ) • eta m) 0 := by linarith [h₀, c₀]
      _ = ξ 0 := by rw [← PiLp.add_apply, add_comm, sub_add_cancel]
  · calc (3 / 2) * rsh m ≤ (8 / 5) * rsh m - ‖ξ - (2 : ℝ) • eta m‖ := by linarith [rsh_ge m, hd]
      _ ≤ ((2 : ℝ) • eta m) 1 + (ξ - (2 : ℝ) • eta m) 1 := by linarith [h₁, c₁]
      _ = ξ 1 := by rw [← PiLp.add_apply, add_comm, sub_add_cancel]
  · exact (by linarith [rsh_ge m, hlt] : ‖ξ‖ < (5 / 2 : ℝ) * rsh m).le

theorem ratio_ge (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) :
    (9 / 25 : ℝ) ≤ (ξ 1 ^ 2 + ξ 2 ^ 2) / ‖ξ‖ ^ 2 := by
  obtain ⟨_, _, hξ₁, hnorm⟩ := ballW_geometry m hξ
  have hn0 : (0 : ℝ) < ‖ξ‖ := by
    obtain ⟨hgt, -⟩ := norm_ballW_gt m hξ
    linarith [rsh_ge m]
  have hξ₁pos : (0 : ℝ) ≤ ξ 1 := by linarith [rsh_ge m]
  have hA : (9 / 4 : ℝ) * rsh m ^ 2 ≤ ξ 1 ^ 2 := by
    calc (9 / 4 : ℝ) * rsh m ^ 2 = ((3 / 2 : ℝ) * rsh m) * ((3 / 2 : ℝ) * rsh m) := by ring
      _ ≤ (3 / 2 * rsh m) * ξ 1 := mul_le_mul_of_nonneg_left hξ₁ (by linarith [rsh_pos m])
      _ ≤ ξ 1 * ξ 1 := mul_le_mul_of_nonneg_right hξ₁ hξ₁pos
      _ = ξ 1 ^ 2 := (pow_two _).symm
  have hB : ‖ξ‖ ^ 2 ≤ (25 / 4) * rsh m ^ 2 := by
    have h5 : (0 : ℝ) ≤ (5 / 2 : ℝ) * rsh m := by linarith [rsh_pos m]
    calc ‖ξ‖ ^ 2 = ‖ξ‖ * ‖ξ‖ := pow_two _
      _ ≤ ((5 / 2 : ℝ) * rsh m) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right hnorm (le_of_lt hn0)
      _ ≤ ((5 / 2 : ℝ) * rsh m) * ((5 / 2 : ℝ) * rsh m) :=
        mul_le_mul_of_nonneg_left hnorm h5
      _ = (25 / 4 : ℝ) * rsh m ^ 2 := by ring
  calc (9 / 25 : ℝ) = ((9 / 4) * rsh m ^ 2) / ((25 / 4) * rsh m ^ 2) := by
        field_simp [show (rsh m : ℝ) ≠ 0 by linarith [rsh_ge m]]
      _ ≤ ξ 1 ^ 2 / ‖ξ‖ ^ 2 :=
        div_le_div₀ (sq_nonneg (ξ 1)) hA (pow_pos hn0 2) hB
      _ ≤ (ξ 1 ^ 2 + ξ 2 ^ 2) / ‖ξ‖ ^ 2 := by
        refine div_le_div₀ ?_ (le_add_of_nonneg_right (sq_nonneg (ξ 2))) (pow_pos hn0 2) le_rfl
        nlinarith [sq_nonneg (ξ 1), sq_nonneg (ξ 2)]

/-! ### Coordinate integrability of every slice -/

theorem uu_coord_integrable_Xm1 (a : ℝ) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖uu a t ξ i‖) := by
  by_cases h : ∃ m, t ∈ timeE m
  · obtain ⟨m, hm⟩ := h
    by_cases hi : i = 0
    · subst hi
      set C : NNReal :=
        ⟨(rsh m - 1)⁻¹ * |a|, mul_nonneg (inv_nonneg.2 (rsh_sub_one_pos m).le) (abs_nonneg a)⟩
      have hinv : AEStronglyMeasurable (fun ξ : ES => ‖ξ‖⁻¹) volume :=
        continuous_norm.aestronglyMeasurable.inv₀
      have haes : AEStronglyMeasurable (fun ξ : ES => ‖ξ‖⁻¹ * ‖uu a t ξ (0 : Fin 3)‖) volume :=
        hinv.mul ((uu_coord_aes a t (0 : Fin 3)).norm)
      have hdom : ∀ᵐ ξ ∂volume, ‖ξ‖⁻¹ * ‖uu a t ξ (0 : Fin 3)‖ ≤
          (ballB m).indicator (fun _ : ES => (C : ℝ)) ξ := by
        filter_upwards with ξ
        by_cases hξ : ξ ∈ ballB m
        · have hge : rsh m - 1 < ‖ξ‖ := norm_ballB_gt_sub m hξ
          have hX : (0 : ℝ) < ‖ξ‖ := lt_trans (rsh_sub_one_pos m) hge
          have hinv : ‖ξ‖⁻¹ ≤ (rsh m - 1)⁻¹ :=
            (inv_lt_inv₀ hX (rsh_sub_one_pos m)).mpr hge |>.le
          have huu : ‖uu a t ξ (0 : Fin 3)‖ = |a| := by
            rw [uu_coord0_eq a hm ξ]
            simp [hξ]
          rw [Set.indicator_apply, huu]
          simp only [hξ]
          exact mul_le_mul_of_nonneg_right hinv (abs_nonneg a)
        · have hz : uu a t ξ (0 : Fin 3) = 0 := by
            rw [uu_coord0_eq a hm ξ]
            simp [hξ]
          rw [Set.indicator_apply]
          simp [hξ, hz]
      exact Integrable.mono_nonneg
        (integrable_indicator_nnreal_ball (ballB m) (measurableSet_ballB m)
          (volume_ballB_lt_top m) C)
        haes (by filter_upwards with ξ; positivity) hdom
    · have h0 : (fun ξ => uu a t ξ i) = 0 := uu_zero_coord a t hm i hi
      have hpt : ∀ ξ, uu a t ξ i = 0 := fun ξ => congr_fun h0 ξ
      have hf : (fun ξ : ES => ‖ξ‖⁻¹ * ‖uu a t ξ i‖) = fun _ => 0 := by
        funext ξ
        simp [hpt ξ]
      rw [hf]
      exact integrable_zero_fun
  · have h0 : (fun ξ => uu a t ξ i) = fun _ => 0 := by
      funext ξ
      exact uu_notmem a (fun m hmem => h ⟨m, hmem⟩)
    have hpt : ∀ ξ, uu a t ξ i = 0 := fun ξ => congr_fun h0 ξ
    have hf : (fun ξ : ES => ‖ξ‖⁻¹ * ‖uu a t ξ i‖) = fun _ => 0 := by
      funext ξ
      simp [hpt ξ]
    rw [hf]
    exact integrable_zero_fun

theorem uu_coord_integrable_X1 (a : ℝ) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖uu a t ξ i‖) := by
  by_cases h : ∃ m, t ∈ timeE m
  · obtain ⟨m, hm⟩ := h
    by_cases hi : i = 0
    · subst hi
      have hpos : (0 : ℝ) < rsh m + 1 := by linarith [rsh_pos m]
      set C : NNReal := ⟨(rsh m + 1) * |a|, mul_nonneg hpos.le (abs_nonneg a)⟩
      have haes : AEStronglyMeasurable (fun ξ : ES => ‖ξ‖ * ‖uu a t ξ (0 : Fin 3)‖) volume :=
        continuous_norm.aestronglyMeasurable.mul ((uu_coord_aes a t (0 : Fin 3)).norm)
      have hdom : ∀ᵐ ξ ∂volume, ‖ξ‖ * ‖uu a t ξ (0 : Fin 3)‖ ≤
          (ballB m).indicator (fun _ : ES => (C : ℝ)) ξ := by
        filter_upwards with ξ
        by_cases hξ : ξ ∈ ballB m
        · have hlt : ‖ξ‖ < rsh m + 1 := norm_ballB_lt m hξ
          have huu : ‖uu a t ξ (0 : Fin 3)‖ = |a| := by
            rw [uu_coord0_eq a hm ξ]
            simp [hξ]
          rw [Set.indicator_apply, huu]
          simp only [hξ]
          exact mul_le_mul_of_nonneg_right hlt.le (abs_nonneg a)
        · have hz : uu a t ξ (0 : Fin 3) = 0 := by
            rw [uu_coord0_eq a hm ξ]
            simp [hξ]
          rw [Set.indicator_apply]
          simp [hξ, hz]
      exact Integrable.mono_nonneg
        (integrable_indicator_nnreal_ball (ballB m) (measurableSet_ballB m)
          (volume_ballB_lt_top m) C)
        haes (by filter_upwards with ξ; positivity) hdom
    · have h0 : (fun ξ => uu a t ξ i) = 0 := uu_zero_coord a t hm i hi
      have hpt : ∀ ξ, uu a t ξ i = 0 := fun ξ => congr_fun h0 ξ
      have hf : (fun ξ : ES => ‖ξ‖ * ‖uu a t ξ i‖) = fun _ => 0 := by
        funext ξ
        simp [hpt ξ]
      rw [hf]
      exact integrable_zero_fun
  · have h0 : (fun ξ => uu a t ξ i) = fun _ => 0 := by
      funext ξ
      exact uu_notmem a (fun m hmem => h ⟨m, hmem⟩)
    have hpt : ∀ ξ, uu a t ξ i = 0 := fun ξ => congr_fun h0 ξ
    have hf : (fun ξ : ES => ‖ξ‖ * ‖uu a t ξ i‖) = fun _ => 0 := by
      funext ξ
      simp [hpt ξ]
    rw [hf]
    exact integrable_zero_fun

/-! ### Slice mass budgets -/

/-- The `X⁻¹` budget of every slice: `|a| · μ_B · (rₘ − 1)⁻¹` on shell `m`. -/
theorem coordinateXm1Mass_uu (a : ℝ) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m) :
    coordinateXm1Mass (uu a t) ≤ |a| * muB / (rsh m - 1) := by
  classical
  have hpos : (0 : ℝ) < rsh m - 1 := rsh_sub_one_pos m
  unfold coordinateXm1Mass
  rw [Fin.sum_univ_three]
  have h1 : normXm1 (fun ξ : ES => uu a t ξ (1 : Fin 3)) = 0 := by
    have h0 : (fun ξ : ES => uu a t ξ (1 : Fin 3)) = 0 :=
      uu_zero_coord a t ht (1 : Fin 3) (by decide)
    rw [h0]
    simp [normXm1]
  have h2 : normXm1 (fun ξ : ES => uu a t ξ (2 : Fin 3)) = 0 := by
    have h0 : (fun ξ : ES => uu a t ξ (2 : Fin 3)) = 0 :=
      uu_zero_coord a t ht (2 : Fin 3) (by decide)
    rw [h0]
    simp [normXm1]
  have hle : (fun ξ : ES => ‖ξ‖⁻¹ * ‖uu a t ξ (0 : Fin 3)‖) ≤ᵐ[volume]
      fun ξ : ES => (ballB m).indicator (fun _ : ES => (rsh m - 1)⁻¹ * |a|) ξ := by
    filter_upwards with ξ
    by_cases hξ : ξ ∈ ballB m
    · have hX : (0 : ℝ) < ‖ξ‖ := lt_trans hpos (norm_ballB_gt_sub m hξ)
      have hinv : ‖ξ‖⁻¹ ≤ (rsh m - 1)⁻¹ :=
        (inv_lt_inv₀ hX hpos).mpr (norm_ballB_gt_sub m hξ) |>.le
      have huu : ‖uu a t ξ (0 : Fin 3)‖ = |a| := by
        rw [uu_coord0_eq a ht ξ]
        simp [hξ]
      rw [Set.indicator_apply, huu]
      simp only [hξ]
      exact mul_le_mul_of_nonneg_right hinv (abs_nonneg a)
    · have hz : uu a t ξ (0 : Fin 3) = 0 := by
        rw [uu_coord0_eq a ht ξ]
        simp [hξ]
      rw [Set.indicator_apply]
      simp [hξ, hz]
  have hnonneg : (0 : ES → ℝ) ≤ᵐ[volume] (fun ξ : ES => ‖ξ‖⁻¹ * ‖uu a t ξ (0 : Fin 3)‖) := by
    filter_upwards with ξ
    exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) (norm_nonneg _)
  have hig : Integrable (fun ξ : ES =>
      (ballB m).indicator (fun _ : ES => (rsh m - 1)⁻¹ * |a|) ξ) volume := by
    refine (integrable_indicator_nnreal_ball (ballB m) (measurableSet_ballB m)
      (volume_ballB_lt_top m) ⟨(rsh m - 1)⁻¹ * |a|,
        mul_nonneg (inv_nonneg.2 (rsh_sub_one_pos m).le) (abs_nonneg a)⟩).congr ?_
    filter_upwards with ξ
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hξ : ξ ∈ ballB m
    · simp only [hξ]
      rfl
    · simp only [hξ]
      rfl
  have hval : ∫ ξ : ES, (ballB m).indicator (fun _ : ES => (rsh m - 1)⁻¹ * |a|) ξ
      = muB • ((rsh m - 1)⁻¹ * |a|) := by
    rw [integral_indicator_const _ (measurableSet_ballB m)]
    show (volume (ballB m)).toReal • ((rsh m - 1)⁻¹ * |a|) = muB • _
    rw [volume_ballB_toReal m]
  have hge : normXm1 (fun ξ : ES => uu a t ξ (0 : Fin 3))
      ≤ muB • ((rsh m - 1)⁻¹ * |a|) := by
    show (∫ ξ : ES, ‖ξ‖⁻¹ * ‖uu a t ξ (0 : Fin 3)‖) ≤ _
    refine (integral_mono_of_nonneg hnonneg hig hle).trans ?_
    rw [hval]
  rw [h1, h2]
  simp only [add_zero]
  refine le_trans hge ?_
  refine le_of_eq ?_
  show muB * ((rsh m - 1)⁻¹ * |a|) = |a| * muB / (rsh m - 1)
  field_simp [hpos.ne']

/-- The `X¹` budget of every slice: `|a| · μ_B · (rₘ + 1)` on shell `m`. -/
theorem coordinateX1Mass_uu (a : ℝ) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m) :
    coordinateX1Mass (uu a t) ≤ (rsh m + 1) * |a| * muB := by
  classical
  have hpos : (0 : ℝ) < rsh m + 1 := by linarith [rsh_pos m]
  unfold coordinateX1Mass
  rw [Fin.sum_univ_three]
  have h1 : normX1 (fun ξ : ES => uu a t ξ (1 : Fin 3)) = 0 := by
    have h0 : (fun ξ : ES => uu a t ξ (1 : Fin 3)) = 0 :=
      uu_zero_coord a t ht (1 : Fin 3) (by decide)
    rw [h0]
    simp [normX1]
  have h2 : normX1 (fun ξ : ES => uu a t ξ (2 : Fin 3)) = 0 := by
    have h0 : (fun ξ : ES => uu a t ξ (2 : Fin 3)) = 0 :=
      uu_zero_coord a t ht (2 : Fin 3) (by decide)
    rw [h0]
    simp [normX1]
  have hle : (fun ξ : ES => ‖ξ‖ * ‖uu a t ξ (0 : Fin 3)‖) ≤ᵐ[volume]
      fun ξ : ES => (ballB m).indicator (fun _ : ES => (rsh m + 1) * |a|) ξ := by
    filter_upwards with ξ
    by_cases hξ : ξ ∈ ballB m
    · have hlt : ‖ξ‖ < rsh m + 1 := norm_ballB_lt m hξ
      have huu : ‖uu a t ξ (0 : Fin 3)‖ = |a| := by
        rw [uu_coord0_eq a ht ξ]
        simp [hξ]
      rw [Set.indicator_apply, huu]
      simp only [hξ]
      exact mul_le_mul_of_nonneg_right hlt.le (abs_nonneg a)
    · have hz : uu a t ξ (0 : Fin 3) = 0 := by
        rw [uu_coord0_eq a ht ξ]
        simp [hξ]
      rw [Set.indicator_apply]
      simp [hξ, hz]
  have hnonneg : (0 : ES → ℝ) ≤ᵐ[volume] (fun ξ : ES => ‖ξ‖ * ‖uu a t ξ (0 : Fin 3)‖) := by
    filter_upwards with ξ
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hig : Integrable (fun ξ : ES =>
      (ballB m).indicator (fun _ : ES => (rsh m + 1) * |a|) ξ) volume := by
    refine (integrable_indicator_nnreal_ball (ballB m) (measurableSet_ballB m)
      (volume_ballB_lt_top m) ⟨(rsh m + 1) * |a|,
        mul_nonneg hpos.le (abs_nonneg a)⟩).congr ?_
    filter_upwards with ξ
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hξ : ξ ∈ ballB m
    · simp only [hξ]
      rfl
    · simp only [hξ]
      rfl
  have hval : ∫ ξ : ES, (ballB m).indicator (fun _ : ES => (rsh m + 1) * |a|) ξ
      = muB • ((rsh m + 1) * |a|) := by
    rw [integral_indicator_const _ (measurableSet_ballB m)]
    show (volume (ballB m)).toReal • ((rsh m + 1) * |a|) = muB • _
    rw [volume_ballB_toReal m]
  have hge : normX1 (fun ξ : ES => uu a t ξ (0 : Fin 3))
      ≤ muB • ((rsh m + 1) * |a|) := by
    show (∫ ξ : ES, ‖ξ‖ * ‖uu a t ξ (0 : Fin 3)‖) ≤ _
    refine (integral_mono_of_nonneg hnonneg hig hle).trans ?_
    rw [hval]
  rw [h1, h2]
  simp only [add_zero]
  refine le_trans hge ?_
  refine le_of_eq ?_
  show muB * ((rsh m + 1) * |a|) = (rsh m + 1) * |a| * muB
  ring

/-! ### The self-interaction source of one active shell -/

/-- Coordinate-0 slice as a plain `ℂ`-indicator. -/
noncomputable def shell0 (a : ℂ) (m : ℕ) : ES → ℂ :=
  (ballB m).indicator (fun _ : ES => a)

theorem uu_coord0_eq_shell0 (a : ℝ) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m) :
    (fun ξ : ES => uu a t ξ (0 : Fin 3)) = shell0 (a : ℂ) m := by
  classical
  funext ξ
  rw [shell0, Set.indicator_apply, uu_coord0_eq a ht ξ]

/-- Frequencies `η` with both `η` and `ξ − η` in shell `m`. -/
def overlapSet (m : ℕ) (ξ : ES) : Set ES :=
  ballB m ∩ (fun η : ES => ξ - η)⁻¹' ballB m

theorem mem_overlapSet (m : ℕ) (ξ η : ES) :
    η ∈ overlapSet m ξ ↔ η ∈ ballB m ∧ ξ - η ∈ ballB m := by
  simp [overlapSet]

theorem overlapSet_measurable (m : ℕ) (ξ : ES) : MeasurableSet (overlapSet m ξ) :=
  (measurableSet_ballB m).inter
    ((Metric.isOpen_ball.measurableSet : MeasurableSet (ballB m)).preimage
      (continuous_const.sub continuous_id).measurable)

theorem subset_overlapSet_ball38 (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) :
    Metric.ball (eta m) (3 / 8) ⊆ overlapSet m ξ := by
  classical
  intro η hη
  have h1 : ‖η - eta m‖ < 3 / 8 := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hη
  rw [mem_overlapSet]
  refine ⟨?_, ?_⟩
  · rw [mem_ballB, dist_eq_norm]
    linarith
  · rw [mem_ballB, dist_eq_norm]
    have h2 : ‖(ξ - η) - eta m‖ = ‖(ξ - (2 : ℝ) • eta m) + (eta m - η)‖ := by
      congr 1
      simp only [two_smul]
      abel_nf
    have h3 : ‖(ξ - (2 : ℝ) • eta m) + (eta m - η)‖ ≤ ‖ξ - (2 : ℝ) • eta m‖ + ‖eta m - η‖ :=
      norm_add_le _ _
    have h4 : ‖ξ - (2 : ℝ) • eta m‖ < 1 / 2 := norm_sub_ballW_lt_half m hξ
    have h5 : ‖eta m - η‖ < 3 / 8 := by
      rw [norm_sub_rev]
      exact h1
    rw [h2]
    linarith

theorem overlap_toReal_ge (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) :
    mu38 ≤ (volume (overlapSet m ξ)).toReal := by
  have htop : volume (overlapSet m ξ) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt
      (measure_mono (show overlapSet m ξ ⊆ ballB m from fun _ hx => hx.1))
      (volume_ballB_lt_top m))
  have h := ENNReal.toReal_mono htop (measure_mono (subset_overlapSet_ball38 m hξ))
  rwa [volume_ball38_toReal m] at h

/-- The shell self-convolution is the `ℂ`-indicator of the overlap set. -/
theorem shell0_convolution (a : ℂ) (m : ℕ) (ξ : ES) :
    ((shell0 a m) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (shell0 a m)) ξ =
      ∫ η : ES, (overlapSet m ξ).indicator (fun _ : ES => a * a) η ∂volume := by
  classical
  show ∫ η : ES, shell0 a m η * shell0 a m (ξ - η) ∂volume = _
  have h : (fun η : ES => shell0 a m η * shell0 a m (ξ - η)) =
      fun η : ES => (overlapSet m ξ).indicator (fun _ : ES => a * a) η := by
    funext η
    simp only [shell0, overlapSet, Set.mem_inter_iff, Set.mem_preimage, Set.indicator_apply]
    by_cases h1 : η ∈ ballB m <;> by_cases h2 : ξ - η ∈ ballB m <;> simp [h1, h2]
  rw [h]

theorem shell0_convolution_eq (a : ℝ) (m : ℕ) (ξ : ES) :
    ((shell0 (a : ℂ) m) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (shell0 (a : ℂ) m)) ξ =
      ((volume (overlapSet m ξ)).toReal * (a * a) : ℂ) := by
  rw [shell0_convolution, integral_indicator_const _ (overlapSet_measurable m ξ)]
  -- unfold the `ℝ≥0`-scalar multiplication down to `ℂ`-multiplication
  simp only [Measure.real, Complex.real_smul]

/-- Real amplitude of the shell-`m` self-interaction in coordinate `0`. -/
def rawVal (a : ℝ) (m : ℕ) (ξ : ES) : ℝ :=
  ξ 0 * ((volume (overlapSet m ξ)).toReal * (a * a))

theorem rawVal_nonneg (a : ℝ) (m : ℕ) (ξ : ES) (hξ0 : (0 : ℝ) ≤ ξ 0) :
    (0 : ℝ) ≤ rawVal a m ξ :=
  mul_nonneg hξ0 (mul_nonneg (ENNReal.toReal_nonneg) (mul_self_nonneg a))

theorem conv_zero_left (g : ES → ℂ) :
    ((0 : ES → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) = 0 := by
  funext ξ
  simp [MeasureTheory.convolution]

theorem conv_zero_right (f : ES → ℂ) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (0 : ES → ℂ)) = 0 := by
  funext ξ
  simp [MeasureTheory.convolution]

/-- On an active slice the convection is the real cast of `rawVal` in
coordinate `0` and zero elsewhere. -/
theorem rawNavierConvection_uu_single (a : ℝ) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m) (ξ : ES) :
    rawNavierConvection (uu a t) (uu a t) ξ =
      fun i => if i = 0 then (rawVal a m ξ : ℂ) else 0 := by
  classical
  ext i
  by_cases hi : i = 0
  · subst hi
    have h0 : (fun η : ES => uu a t η (0 : Fin 3)) = shell0 (a : ℂ) m :=
      uu_coord0_eq_shell0 a ht
    have h1 : (fun η : ES => uu a t η (1 : Fin 3)) = (0 : ES → ℂ) :=
      uu_zero_coord a t ht (1 : Fin 3) (by decide)
    have h2 : (fun η : ES => uu a t η (2 : Fin 3)) = (0 : ES → ℂ) :=
      uu_zero_coord a t ht (2 : Fin 3) (by decide)
    have hc0 : ((fun η : ES => uu a t η (0 : Fin 3)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => uu a t η (0 : Fin 3))) ξ =
          ((volume (overlapSet m ξ)).toReal * (a * a) : ℂ) := by
      rw [h0]
      exact shell0_convolution_eq a m ξ
    have hc1 : ((fun η : ES => uu a t η (1 : Fin 3)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => uu a t η (0 : Fin 3))) ξ = 0 := by
      rw [h1]
      exact congrFun (conv_zero_left _) ξ
    have hc2 : ((fun η : ES => uu a t η (2 : Fin 3)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => uu a t η (0 : Fin 3))) ξ = 0 := by
      rw [h2]
      exact congrFun (conv_zero_left _) ξ
    show (∑ j : Fin 3, (ξ j : ℂ) *
        (((fun η => uu a t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun η => uu a t η (0 : Fin 3))) ξ)) = (rawVal a m ξ : ℂ)
    rw [Fin.sum_univ_three, hc0, hc1, hc2]
    simp only [mul_zero, add_zero]
    rw [rawVal]
    simp only [Complex.ofReal_mul]
  · have hc : (fun η : ES => uu a t η i) = (0 : ES → ℂ) :=
      uu_zero_coord a t ht i hi
    have h0 : (fun η : ES => uu a t η (0 : Fin 3)) = shell0 (a : ℂ) m :=
      uu_coord0_eq_shell0 a ht
    have hc0 : ((fun η : ES => uu a t η (0 : Fin 3)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => uu a t η i)) ξ = 0 := by
      rw [h0, hc]
      exact congrFun (conv_zero_right _) ξ
    have hc1 : ((fun η : ES => uu a t η (1 : Fin 3)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => uu a t η i)) ξ = 0 := by
      rw [uu_zero_coord a t ht (1 : Fin 3) (by decide)]
      exact congrFun (conv_zero_left _) ξ
    have hc2 : ((fun η : ES => uu a t η (2 : Fin 3)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => uu a t η i)) ξ = 0 := by
      rw [uu_zero_coord a t ht (2 : Fin 3) (by decide)]
      exact congrFun (conv_zero_left _) ξ
    show (∑ j : Fin 3, (ξ j : ℂ) *
        (((fun η => uu a t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun η => uu a t η i)) ξ)) = if i = 0 then (rawVal a m ξ : ℂ) else 0
    rw [Fin.sum_univ_three, hc0, hc1, hc2]
    simp [hi, mul_zero, add_zero]

theorem realPart_raw (a : ℝ) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m) (ξ : ES) :
    Navier.Analysis.ComplexLerayProjection.realPart
      (rawNavierConvection (uu a t) (uu a t) ξ) =
      Pi.single (0 : Fin 3) (rawVal a m ξ) := by
  rw [rawNavierConvection_uu_single a ht ξ]
  ext i
  by_cases hi : i = 0
  · subst hi
    simp [Navier.Analysis.ComplexLerayProjection.realPart]
  · simp [hi, Navier.Analysis.ComplexLerayProjection.realPart]

theorem imaginaryPart_raw (a : ℝ) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m) (ξ : ES) :
    Navier.Analysis.ComplexLerayProjection.imaginaryPart
      (rawNavierConvection (uu a t) (uu a t) ξ) = 0 := by
  rw [rawNavierConvection_uu_single a ht ξ]
  ext i
  by_cases hi : i = 0
  · subst hi
    simp [Navier.Analysis.ComplexLerayProjection.imaginaryPart]
  · simp [hi, Navier.Analysis.ComplexLerayProjection.imaginaryPart]

theorem nls_zero_right (q : Space) : normalizedLeraySymbol q 0 = 0 := by
  have hz : (0 : Space) ⬝ᵥ q = (0 : ℝ) := by
    show ∑ i : Fin 3, (0 : Space) i * q i = 0
    simp
  rw [normalizedLeraySymbol, hz]
  simp

/-- The `spaceProj` transport applies as the identity. -/
theorem spaceProj_apply (ξ : ES) (i : Fin 3) :
    FourierMajorant.spaceProj ξ i = ξ i := rfl

/-- The source at coordinate `0` on an active slice is the rotated, corrected
Leray value. -/
theorem source_coord0 (a : ℝ) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m) (ξ : ES) :
    continuousNavierSource (uu a) (uu a) t ξ (0 : Fin 3) =
      Complex.I *
        (normalizedLeraySymbol (FourierMajorant.spaceProj ξ)
          (Pi.single (0 : Fin 3) (rawVal a m ξ)) (0 : Fin 3) : ℂ) := by
  show complexLeray (FourierMajorant.spaceProj ξ) (Complex.I •
      rawNavierConvection (uu a t) (uu a t) ξ) (0 : Fin 3) = _
  rw [complexLeray_apply, realPart_smul, imaginaryPart_smul, Complex.I_re, Complex.I_im,
    realPart_raw a ht ξ, imaginaryPart_raw a ht ξ]
  simp only [zero_smul, one_smul, sub_self, zero_add]
  rw [nls_zero_right]
  simp [Complex.ofReal_zero]

/-- The Leray-corrected coordinate value at frequency `ξ`. -/
theorem nls_single0_val (ξ : ES) (r : ℝ) :
    normalizedLeraySymbol (FourierMajorant.spaceProj ξ) (Pi.single (0 : Fin 3) r) 0 =
      r * (1 - ξ 0 ^ 2 / ‖ξ‖ ^ 2) := by
  classical
  have hdot : (Pi.single (0 : Fin 3) r) ⬝ᵥ FourierMajorant.spaceProj ξ = r * ξ 0 := by
    show ∑ i : Fin 3, ((Pi.single (0 : Fin 3) r : Fin 3 → ℝ) i) *
        (FourierMajorant.spaceProj ξ) i = r * ξ 0
    rw [Fin.sum_univ_three]
    simp [spaceProj_apply]
  have hqq : (FourierMajorant.spaceProj ξ) ⬝ᵥ FourierMajorant.spaceProj ξ = ‖ξ‖ ^ 2 := by
    show ∑ i : Fin 3, (FourierMajorant.spaceProj ξ) i * (FourierMajorant.spaceProj ξ) i = ‖ξ‖ ^ 2
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => by
      rw [spaceProj_apply, ← sq]
  rw [normalizedLeraySymbol, hdot, hqq]
  simp only [Pi.sub_apply, Pi.smul_apply, spaceProj_apply, smul_eq_mul]
  rw [Pi.single_apply]
  simp only [reduceIte]
  by_cases hz : (‖ξ‖ : ℝ) ^ 2 = (0 : ℝ)
  · rw [hz]
    simp
  · field_simp
    try ring

/-- Pointwise norm of the source on an active slice. -/
theorem source_coord0_norm (a : ℝ) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m) {ξ : ES}
    (hξ0 : (0 : ℝ) ≤ ξ 0) :
    ‖continuousNavierSource (uu a) (uu a) t ξ (0 : Fin 3)‖ =
      rawVal a m ξ * (1 - ξ 0 ^ 2 / ‖ξ‖ ^ 2) := by
  classical
  have hnorm (s : ℝ) (hs : (0 : ℝ) ≤ s) : ‖(s : ℂ)‖ = s := by
    simpa using hs
  rw [source_coord0 a ht ξ, nls_single0_val]
  have hr : (0 : ℝ) ≤ rawVal a m ξ * (1 - ξ 0 ^ 2 / ‖ξ‖ ^ 2) := by
    refine mul_nonneg (rawVal_nonneg a m ξ hξ0) ?_
    by_cases hz : ‖ξ‖ ^ 2 = (0 : ℝ)
    · rw [hz]
      simp
    · have hpos : (0 : ℝ) < ‖ξ‖ ^ 2 :=
        lt_of_not_ge fun h => hz (le_antisymm h (sq_nonneg _))
      have := abs_apply_le_norm (f := ξ) (i := (0 : Fin 3))
      have h1 : ξ 0 ^ 2 ≤ ‖ξ‖ ^ 2 := by
        calc ξ 0 ^ 2 = |ξ 0| ^ 2 := by rw [sq_abs]
          _ ≤ ‖ξ‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      have h2 : ξ 0 ^ 2 / ‖ξ‖ ^ 2 ≤ 1 := (div_le_one hpos).mpr h1
      linarith
  simp only [norm_mul, Complex.norm_I, one_mul]
  exact hnorm _ hr

/-- Pointwise lower bound of the coordinate-`0` source norm on the output
ball of an active slice: the Leray correction removes at most `16/25` of the
real amplitude, and the overlap mass floor gives the `mu38` factor. -/
theorem norm_source_ge (a : ℝ) (_ha : 0 < a) {t : ℝ} {m : ℕ} (ht : t ∈ timeE m)
    {ξ : ES} (hξ : ξ ∈ ballW m) :
    (9 / 25 : ℝ) * (a * a) * mu38 * rsh m ≤
      ‖continuousNavierSource (uu a) (uu a) t ξ (0 : Fin 3)‖ := by
  classical
  obtain ⟨hn, h₀, h₁, -⟩ := ballW_geometry m hξ
  obtain ⟨hgt, -⟩ := norm_ballW_gt m hξ
  have hn0 : (0 : ℝ) < ‖ξ‖ := by linarith [rsh_ge m]
  have hsum : ξ 0 ^ 2 + (ξ 1 ^ 2 + ξ 2 ^ 2) = ‖ξ‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    ring
  have hratio : (9 / 25 : ℝ) ≤ 1 - ξ 0 ^ 2 / ‖ξ‖ ^ 2 := by
    have hsq0 : (‖ξ‖ : ℝ) ^ 2 ≠ 0 := by positivity
    have hsub : 1 - ξ 0 ^ 2 / ‖ξ‖ ^ 2 = (ξ 1 ^ 2 + ξ 2 ^ 2) / ‖ξ‖ ^ 2 := by
      field_simp [hsq0]
      linarith [hsum]
    rw [hsub]
    exact ratio_ge m hξ
  have hqO : mu38 ≤ (volume (overlapSet m ξ)).toReal := overlap_toReal_ge m hξ
  have h1 : (a * a) * mu38 ≤ (a * a) * (volume (overlapSet m ξ)).toReal :=
    mul_le_mul_of_nonneg_left hqO (mul_self_nonneg a)
  have hraw : (a * a) * mu38 * rsh m ≤ rawVal a m ξ := by
    have h2 : (a * a) * (volume (overlapSet m ξ)).toReal * rsh m ≤
        (a * a) * (volume (overlapSet m ξ)).toReal * ξ 0 :=
      mul_le_mul_of_nonneg_left h₀ (mul_nonneg (mul_self_nonneg a) ENNReal.toReal_nonneg)
    calc (a * a) * mu38 * rsh m ≤ (a * a) * (volume (overlapSet m ξ)).toReal * rsh m :=
        mul_le_mul_of_nonneg_right h1 (rsh_pos m).le
      _ ≤ (a * a) * (volume (overlapSet m ξ)).toReal * ξ 0 := h2
      _ = rawVal a m ξ := by unfold rawVal; ring
  have hnonneg : (0 : ℝ) ≤ rawVal a m ξ :=
    rawVal_nonneg a m ξ (by linarith [h₀, rsh_ge m])
  calc (9 / 25 : ℝ) * (a * a) * mu38 * rsh m = (9 / 25) * ((a * a) * mu38 * rsh m) := by ring
    _ ≤ (9 / 25) * rawVal a m ξ :=
        mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ (9 / 25 : ℝ))
    _ ≤ rawVal a m ξ * (1 - ξ 0 ^ 2 / ‖ξ‖ ^ 2) :=
        (mul_le_mul_of_nonneg_right hratio hnonneg).trans_eq
          (mul_comm (1 - ξ 0 ^ 2 / ‖ξ‖ ^ 2) (rawVal a m ξ))
    _ = ‖continuousNavierSource (uu a) (uu a) t ξ (0 : Fin 3)‖ :=
        (source_coord0_norm a ht (by linarith [h₀, rsh_ge m])).symm

/-! ## Divergence of the weighted spacetime source integral -/

/-- Output rectangle of shell `m`: the frequency window where the shell-`m`
self-interaction is bounded below, crossed with its time window. -/
def shellRect (m : ℕ) : Set (ES × ℝ) := ballW m ×ˢ timeE m

theorem measurableSet_shellRect (m : ℕ) : MeasurableSet (shellRect m) :=
  (measurableSet_ballW m).prod (timeE_measurable m)

theorem mem_shellRect (m : ℕ) (p : ES × ℝ) :
    p ∈ shellRect m ↔ p.1 ∈ ballW m ∧ p.2 ∈ timeE m := Iff.rfl

theorem measure_restrict_timeE (m : ℕ) :
    (volume.restrict (Icc (0 : ℝ) 1)) (timeE m) = volume (timeE m) := by
  rw [Measure.restrict_apply (timeE_measurable m),
    Set.inter_eq_self_of_subset_left ((timeE_subset m).trans Set.Ioo_subset_Icc_self)]

theorem measure_ballW_eq (m : ℕ) : volume (ballW m) = ENNReal.ofReal muC := by
  rw [← ENNReal.ofReal_toReal (h := (volume_ballW_lt_top m).ne), volume_ballW_toReal m]

theorem measure_shellRect (m : ℕ) :
    (volume.prod (volume.restrict (Icc (0 : ℝ) 1))) (shellRect m) =
      ENNReal.ofReal muC * ENNReal.ofReal ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) := by
  rw [shellRect, Measure.prod_prod,
    measure_restrict_timeE m, measure_ballW_eq m, measure_timeE m]

/-- Frequency-window source lower bound for shell `m`. -/
noncomputable def K1 (a : ℝ) (m : ℕ) : ℝ :=
  (9 / 25) * (a * a) * mu38 * (rsh m) ^ 2

/-- The `m`-independent product of `K1` with the rectangle measure: the
`(rsh m)²` growth exactly cancels the `4⁻ᵐ` time-window decay. -/
noncomputable def K0 (a : ℝ) : ℝ :=
  (9 / 25) * (a * a) * mu38 * muC * 768

theorem K1_nonneg (a : ℝ) (m : ℕ) : (0 : ℝ) ≤ K1 a m := by
  unfold K1
  refine mul_nonneg (mul_nonneg (mul_nonneg
    (by norm_num : (0 : ℝ) ≤ (9 / 25 : ℝ)) (mul_self_nonneg a)) mu38_pos.le)
    (sq_nonneg _)

theorem K0_pos (a : ℝ) (ha : 0 < a) : (0 : ℝ) < K0 a := by
  have h₁ : (0 : ℝ) < mu38 := mu38_pos
  have h₂ : (0 : ℝ) < muC := muC_pos
  have h₃ : (0 : ℝ) < a * a := mul_pos ha ha
  unfold K0
  positivity

theorem rsh_sq (m : ℕ) : (rsh m) ^ 2 = (1024 : ℝ) * (4 : ℝ) ^ m := by
  unfold rsh
  have h : (2 : ℝ) ^ (m + 5) = (2 : ℝ) ^ m * 32 := by
    rw [pow_add]
    norm_num
  have h2 : (2 : ℝ) ^ m * (2 : ℝ) ^ m = (4 : ℝ) ^ m := by
    rw [← mul_pow]
    norm_num
  rw [h, mul_pow, pow_two, h2]
  norm_num
  ring

theorem K1_measure_eq (a : ℝ) (m : ℕ) :
    K1 a m * (muC * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m)) = K0 a := by
  unfold K1 K0
  rw [rsh_sq m]
  have h : (4 : ℝ) ^ m ≠ 0 := by positivity
  have h4 : (1 / 4 : ℝ) ^ m = ((4 : ℝ) ^ m)⁻¹ := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow]
  rw [h4]
  field_simp [h]
  ring

/-- The `SourceL1X1` coordinate-`0` spacetime integrand at `T = 1`. -/
noncomputable def srcIntegrand (a : ℝ) : ES × ℝ → ℝ :=
  fun p => ‖p.1‖ * ‖continuousNavierSource (uu a) (uu a) p.2 p.1 (0 : Fin 3)‖

theorem srcIntegrand_nonneg (a : ℝ) (p : ES × ℝ) : (0 : ℝ) ≤ srcIntegrand a p :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem srcIntegrand_apply (a : ℝ) (ξ : ES) (t : ℝ) :
    srcIntegrand a (ξ, t) =
      ‖ξ‖ * ‖continuousNavierSource (uu a) (uu a) t ξ (0 : Fin 3)‖ := rfl

/-- Pointwise: the sum over the first `N` shell rectangles is bounded by the
spacetime integrand. The rectangles are pairwise disjoint in time, so at most
one term is nonzero. -/
theorem srcIntegrand_sum_le (a : ℝ) (ha : 0 < a) (N : ℕ) (p : ES × ℝ) :
    ∑ m ∈ Finset.range N, ENNReal.ofReal (K1 a m) *
        (shellRect m).indicator (fun _ : ES × ℝ => (1 : ENNReal)) p ≤
      ENNReal.ofReal ‖srcIntegrand a p‖ := by
  classical
  obtain ⟨ξ, t⟩ := p
  by_cases h : ∃ m, m ∈ Finset.range N ∧ ξ ∈ ballW m ∧ t ∈ timeE m
  · obtain ⟨m, hmN, hξW, htm⟩ := h
    have hnotin : ∀ k : ℕ, k ≠ m → ¬(ξ ∈ ballW k ∧ t ∈ timeE k) := by
      intro k hkm hc
      rcases lt_trichotomy m k with hlt | heq | hgt
      · exact (Set.disjoint_left.mp (timeE_disjoint m k hlt) htm) hc.2
      · exact hkm heq.symm
      · exact absurd htm (Set.disjoint_left.mp (timeE_disjoint k m hgt) hc.2)
    have hge : ENNReal.ofReal (K1 a m) ≤ ENNReal.ofReal ‖srcIntegrand a (ξ, t)‖ := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hn : (rsh m : ℝ) ≤ ‖ξ‖ := (ballW_geometry m hξW).1
      have hsrc := norm_source_ge a ha htm hξW
      have hne : K1 a m ≤
          ‖continuousNavierSource (uu a) (uu a) t ξ (0 : Fin 3)‖ * ‖ξ‖ := by
        unfold K1
        calc (9 / 25 : ℝ) * (a * a) * mu38 * (rsh m) ^ 2
            = ((9 / 25 : ℝ) * (a * a) * mu38 * rsh m) * rsh m := by ring
          _ ≤ ‖continuousNavierSource (uu a) (uu a) t ξ (0 : Fin 3)‖ * rsh m :=
              mul_le_mul_of_nonneg_right hsrc (rsh_pos m).le
          _ ≤ ‖continuousNavierSource (uu a) (uu a) t ξ (0 : Fin 3)‖ * ‖ξ‖ :=
              mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (srcIntegrand_nonneg a (ξ, t)),
        srcIntegrand_apply, mul_comm]
      exact hne
    have hfun : (fun k => ENNReal.ofReal (K1 a k) *
        (shellRect k).indicator (fun _ : ES × ℝ => (1 : ENNReal)) (ξ, t)) =
        fun k => if m = k then ENNReal.ofReal (K1 a m) else 0 := by
      funext k
      by_cases hkm : k = m
      · subst hkm
        rw [Set.indicator_apply, mem_shellRect]
        simp [hξW, htm]
      · have hn : ¬((ξ, t) ∈ shellRect k) := by
          intro hc
          rw [mem_shellRect] at hc
          exact hnotin k hkm hc
        rw [Set.indicator_apply, if_neg hn, mul_zero,
          if_neg (fun h : m = k => hkm h.symm)]
    rw [hfun]
    have hcollapse :
        (∑ k ∈ Finset.range N, if m = k then ENNReal.ofReal (K1 a m) else 0) =
          ENNReal.ofReal (K1 a m) := by
      rw [Finset.sum_ite_eq (s := Finset.range N) (a := m)
          (b := fun _ => ENNReal.ofReal (K1 a m)),
        if_pos hmN]
    rw [hcollapse]
    exact hge
  · have hzero : ∀ k ∈ Finset.range N, ENNReal.ofReal (K1 a k) *
        (shellRect k).indicator (fun _ : ES × ℝ => (1 : ENNReal)) (ξ, t) = 0 := by
      intro k hk
      have hn2 : ¬((ξ, t) ∈ shellRect k) := by
        intro hc
        rw [mem_shellRect] at hc
        exact h ⟨k, hk, hc⟩
      rw [Set.indicator_apply]
      simp [hn2]
    rw [Finset.sum_eq_zero hzero]
    exact bot_le

/-- The `lintegral` of the shell-`m` rectangle lower function is the constant
`K0 a`: the `(rsh m)²` frequency growth cancels the `4⁻ᵐ` time decay. -/
theorem rect_lintegral (a : ℝ) (m : ℕ) :
    ∫⁻ p : ES × ℝ, ENNReal.ofReal (K1 a m) *
        (shellRect m).indicator (fun _ : ES × ℝ => (1 : ENNReal)) p
        ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 1))) =
      ENNReal.ofReal (K0 a) := by
  rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (K1 a m))
      (measurable_const.indicator (measurableSet_shellRect m)),
    MeasureTheory.lintegral_indicator (measurableSet_shellRect m)
      (fun _ : ES × ℝ => (1 : ENNReal)),
    MeasureTheory.setLIntegral_one (shellRect m),
    measure_shellRect m,
    ← ENNReal.ofReal_mul muC_pos.le,
    ← ENNReal.ofReal_mul (K1_nonneg a m),
    K1_measure_eq a m]

/-- The first `N` shells contribute `N · K0 a` to the spacetime integral. -/
theorem lintegral_K0_le (a : ℝ) (ha : 0 < a) (N : ℕ) :
    (N : ENNReal) * ENNReal.ofReal (K0 a) ≤
      ∫⁻ p : ES × ℝ, ENNReal.ofReal ‖srcIntegrand a p‖
        ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  classical
  have hmeas : ∀ m ∈ Finset.range N,
      Measurable (fun p : ES × ℝ =>
        ENNReal.ofReal (K1 a m) * (shellRect m).indicator (fun _ : ES × ℝ => (1 : ENNReal)) p) := by
    intro m _
    exact Measurable.mul measurable_const
      (measurable_const.indicator (measurableSet_shellRect m))
  calc (N : ENNReal) * ENNReal.ofReal (K0 a)
      = ∑ m ∈ Finset.range N, ENNReal.ofReal (K0 a) := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
    _ = ∑ m ∈ Finset.range N,
          ∫⁻ p : ES × ℝ, ENNReal.ofReal (K1 a m) *
            (shellRect m).indicator (fun _ : ES × ℝ => (1 : ENNReal)) p
            ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 1))) :=
          (Finset.sum_congr rfl (fun m _ => rect_lintegral a m)).symm
    _ ≤ ∫⁻ p : ES × ℝ, ∑ m ∈ Finset.range N, ENNReal.ofReal (K1 a m) *
          (shellRect m).indicator (fun _ : ES × ℝ => (1 : ENNReal)) p
          ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 1))) :=
          (MeasureTheory.lintegral_finsetSum' (Finset.range N)
            (fun m hm => (hmeas m hm).aemeasurable)).ge
    _ ≤ ∫⁻ p : ES × ℝ, ENNReal.ofReal ‖srcIntegrand a p‖
          ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 1))) :=
          MeasureTheory.lintegral_mono (srcIntegrand_sum_le a ha N)

/-- The weighted spacetime source integral of `uu a` diverges for `a > 0`. -/
theorem lintegral_srcIntegrand_eq_top (a : ℝ) (ha : 0 < a) :
    ∫⁻ p : ES × ℝ, ENNReal.ofReal ‖srcIntegrand a p‖
        ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 1))) = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le (fun r => ?_)
  obtain ⟨N, hN⟩ := exists_nat_gt ((r : ℝ) / K0 a)
  have hK : (0 : ℝ) < K0 a := K0_pos a ha
  have heq : (N : ENNReal) * ENNReal.ofReal (K0 a) =
      ENNReal.ofReal ((N : ℝ) * K0 a) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    simp
  have hr : (r : ENNReal) ≤ (N : ENNReal) * ENNReal.ofReal (K0 a) := by
    rw [heq, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (((div_lt_iff₀ hK).1 hN).le)
  exact le_trans hr (lintegral_K0_le a ha N)

/-- **Crown falsification witness.** The raw field `uu a`, `a > 0`, violates
the `SourceL1X1` integrability requirement at `(ν, T) = (1, 1)`: every slice
is `X⁻¹ ∩ X¹`-bounded (see `coordinateXm1Mass_uu`/`coordinateX1Mass_uu`),
while the self-interaction source has infinite weighted spacetime integral. -/
theorem not_sourceL1X1_uu (a : ℝ) (ha : 0 < a) :
    ¬ ContinuousLeiLinMildAssemblyLeaves.SourceL1X1 1 (uu a) := by
  intro hsrc
  have hf : MeasureTheory.HasFiniteIntegral (srcIntegrand a)
      (volume.prod (volume.restrict (Icc (0 : ℝ) 1))) :=
    (hsrc 0).hasFiniteIntegral
  rw [MeasureTheory.hasFiniteIntegral_iff_norm] at hf
  rw [lintegral_srcIntegrand_eq_top a ha] at hf
  exact lt_irrefl ⊤ hf

/-- There exists a raw field violating `SourceL1X1` at `T = 1`. -/
theorem exists_not_sourceL1X1_raw :
    ∃ v : ℝ → ES → ContinuousLeiLinSpace.ComplexSpace,
      ¬ ContinuousLeiLinMildAssemblyLeaves.SourceL1X1 1 v :=
  ⟨uu 1, not_sourceL1X1_uu 1 zero_lt_one⟩

#check @not_sourceL1X1_uu
#print axioms not_sourceL1X1_uu

end Navier.Analysis.SourceL1X1ShellFalsification
