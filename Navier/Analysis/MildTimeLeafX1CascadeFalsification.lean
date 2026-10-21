import Navier.Analysis.SourceL1X1BoxFalsification
import Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves

/-!
# Leaf 2c (`hmX1`, every-time) and leaf 2e (`hmX1Time`) are kernel-falsified

`MildAssemblyTimeLeaves` (leaf record `B = ProblemStatements.PeriodicGlobalRegularity`
machinery) survives with exactly two residuals: the every-time `hmX1` field
(2c) and `hmX1Time` (2e).  Both demand, for a completed box `x` and EVERY
`t ∈ Icc 0 T`, integrability of

```
fun ξ => ‖ξ‖ * ‖mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i‖
```

(the `hmX1Time` variant of the same obligation, with `mildImageIcc`).  This
module shows the every-time reading is FALSE, by exhibiting a structural
witness inside the repository's own cascade falsification.

## The witness

The cascade `SourceL1X1BoxFalsification.cascadeBox` is a firing shell cascade
whose time windows `timeE m = Ioo (1 − 4⁻ᵐ) (1 − 4⁻ᵐ⁺¹)` accumulate at the
horizon time `t = 1`, whose output balls `ballW m` are pairwise disjoint, and
whose `X¹`-weighted shell mass `K1 a m · volume (timeE m) = K0 a` is
`m`-independent (`K1_measure_eq`).  For the coordinate-`0` Duhamel integral at
`t = 1` the heat factor is `exp(−‖ξ‖² (1 − s))`; on `ballW m × timeE m`,

```
‖ξ‖² · (1 − s) ≤ (25/4)(rsh m)² · 4⁻ᵐ = (25/4) · 1024 = 6400,
```

again because the `(rsh m)²` growth exactly cancels the `4⁻ᵐ` window decay.  So
the damping is bounded below by a FIXED positive constant `damp = exp(−6400)`
uniformly in `m`, and since the source is constant in `s` on its window, the
Duhamel *integral* (not merely its maximal function) carries

```
‖ξ‖ · ‖continuousDuhamel 1 (uu a) (uu a) 1 ξ 0‖ ≥ damp · K0 a / muC
```

on every `ballW m`.  Summing over `N` disjoint balls gives `N · damp · K0 a`,
hence `⊤`, so the `X¹` moment of the mild image at `t = 1` is not integrable.
Because the datum `a = 0` is admissible (`zero_datum_admissible`) and
`heatVec 1 1 0 = 0`, the mild image at the horizon IS the Duhamel term, and
because `uu (boxAmplitude ρ)` agrees a.e. on the horizon with the canonical
everywhere representative of `cascadeBox ρ`
(`cascade_ae_everywhereRepresentative`), the failure lands on the completed box
itself through `continuousDuhamel_congr_ae_on_horizon` (pointwise on the
horizon, no a.e.-transfer gap).

The a.e. reading `mildTimeLeaf_hmX1_ae` is untouched: `t = 1` is a
`leiLinTimeMeasure 1`-null point, so nothing here contradicts it — the point is
that it cannot be upgraded.  Leaf 2e (`hmX1Time`) is blocked the same way: its
`viscousX1Section` constructor obligation IS the every-time leaf 2c, and for
the cascade box that obligation is a false proposition.

Nothing in this module touches the small-data periodic theorem
(`ProblemStatements.PeriodicGlobalRegularity`): the cascade is a statement
about the general completed box, not about Navier--Stokes solutions.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Convolution

attribute [local instance] Classical.propDecidable

namespace Navier.Analysis.MildTimeLeafX1CascadeFalsification

open Navier
open Navier.Analysis
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ComplexLerayProjection (complexLeray)
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinRepresentativeInvariant
open Navier.Analysis.ContinuousLeiLinMildFixedPoint
open Navier.Analysis.SourceL1X1ShellFalsification
open Navier.Analysis.SourceL1X1BoxFalsification

/-! ## S0: the output balls are pairwise separated -/

theorem rsh_succ (m : ℕ) : rsh (m + 1) = (2 : ℝ) * rsh m := by
  unfold rsh
  have hex : (m + 1) + 5 = m + 5 + 1 := by omega
  rw [hex, pow_add, pow_one]
  exact mul_comm _ _

theorem rsh_mono {j k : ℕ} (h : j ≤ k) : rsh j ≤ rsh k := by
  unfold rsh
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : (j : ℕ) + 5 ≤ k + 5)

theorem rsh_sub_ge {m k : ℕ} (h : m < k) : (32 : ℝ) ≤ rsh k - rsh m := by
  have h1 : rsh (m + 1) ≤ rsh k := rsh_mono (by omega : m + 1 ≤ k)
  rw [rsh_succ m] at h1
  linarith [rsh_ge m]

/-- Two distinct shell centres are at least `64` apart. -/
theorem ballW_separated {m k : ℕ} (h : m ≠ k) :
    (64 : ℝ) ≤ ‖(2 : ℝ) • eta m - (2 : ℝ) • eta k‖ := by
  have hetam : (2 : ℝ) • eta m = ((2 : ℝ) * rsh m) • v0 := by
    unfold eta
    rw [smul_smul]
  have hetak : (2 : ℝ) • eta k = ((2 : ℝ) * rsh k) • v0 := by
    unfold eta
    rw [smul_smul]
  rcases lt_trichotomy m k with hlt | heq | hgt
  · rw [norm_sub_rev]
    have hv : (2 : ℝ) • eta k - (2 : ℝ) • eta m
        = ((2 : ℝ) * rsh k - (2 : ℝ) * rsh m) • v0 := by
      rw [hetak, hetam, ← sub_smul]
    rw [hv, norm_smul, norm_v0, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [rsh_sub_ge hlt] :
        (0 : ℝ) ≤ (2 : ℝ) * rsh k - (2 : ℝ) * rsh m)]
    linarith [rsh_sub_ge hlt]
  · exact absurd heq h
  · have hv : (2 : ℝ) • eta m - (2 : ℝ) • eta k
          = ((2 : ℝ) * rsh m - (2 : ℝ) * rsh k) • v0 := by
      rw [hetam, hetak, ← sub_smul]
    rw [hv, norm_smul, norm_v0, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [rsh_sub_ge hgt] :
        (0 : ℝ) ≤ (2 : ℝ) * rsh m - (2 : ℝ) * rsh k)]
    linarith [rsh_sub_ge hgt]

theorem disjoint_ballW {m k : ℕ} (h : m ≠ k) : Disjoint (ballW m) (ballW k) := by
  rw [Set.disjoint_left]
  intro ξ hξm hξk
  have hd : dist ((2 : ℝ) • eta m) ((2 : ℝ) • eta k)
      ≤ dist ((2 : ℝ) • eta m) ξ + dist ξ ((2 : ℝ) • eta k) := dist_triangle _ _ _
  have hsep : dist ((2 : ℝ) • eta m) ((2 : ℝ) • eta k)
      = ‖(2 : ℝ) • eta m - (2 : ℝ) • eta k‖ := dist_eq_norm _ _
  have h1 : dist ((2 : ℝ) • eta m) ξ < 1 / 2 := by
    rw [dist_comm]
    exact (mem_ballW m ξ).mp hξm
  have h2 : dist ξ ((2 : ℝ) • eta k) < 1 / 2 := (mem_ballW k ξ).mp hξk
  linarith [ballW_separated h, hd, hsep, h1, h2]

/-- The `k`-th overlap set is empty at every frequency of a different shell. -/
theorem overlapSet_eq_empty_of_ballW {m k : ℕ} (h : m ≠ k) {ξ : ES}
    (hξ : ξ ∈ ballW m) : overlapSet k ξ = ∅ := by
  refine Set.eq_empty_of_forall_notMem (fun η hh => ?_)
  rw [mem_overlapSet] at hh
  have h1 : ξ - (2 : ℝ) • eta k = ((ξ - η) - eta k) + (η - eta k) := by
    simp only [two_smul]
    abel
  have hxi : ‖ξ - (2 : ℝ) • eta k‖ ≤ ‖(ξ - η) - eta k‖ + ‖η - eta k‖ := by
    rw [h1]
    exact norm_add_le _ _
  have hb1 : ‖η - eta k‖ < 1 := by
    rw [← dist_eq_norm]
    exact (mem_ballB k η).mp hh.1
  have hb2 : ‖(ξ - η) - eta k‖ < 1 := by
    rw [← dist_eq_norm]
    exact (mem_ballB k (ξ - η)).mp hh.2
  have hlt : ‖ξ - (2 : ℝ) • eta k‖ < 2 := by linarith [hxi, hb1, hb2]
  have ha : ‖(2 : ℝ) • eta k - ξ‖ < 2 := by
    rw [norm_sub_rev]
    exact hlt
  have hb : ‖ξ - (2 : ℝ) • eta m‖ < 1 / 2 := norm_sub_ballW_lt_half m hξ
  have h2 : (2 : ℝ) • eta k - (2 : ℝ) • eta m
      = ((2 : ℝ) • eta k - ξ) + (ξ - (2 : ℝ) • eta m) := by abel
  have hsep : ‖(2 : ℝ) • eta k - (2 : ℝ) • eta m‖
      ≤ ‖(2 : ℝ) • eta k - ξ‖ + ‖ξ - (2 : ℝ) • eta m‖ := by
    rw [h2]
    exact norm_add_le _ _
  linarith [ballW_separated (Ne.symm h), hsep, ha, hb]

theorem rawVal_eq_zero_of_ballW {m k : ℕ} (h : m ≠ k) {a : ℝ} {ξ : ES}
    (hξ : ξ ∈ ballW m) : rawVal a k ξ = 0 := by
  unfold rawVal
  rw [overlapSet_eq_empty_of_ballW h hξ, measure_empty, ENNReal.toReal_zero]
  simp

/-! ## S1: the coordinate-`0` source vanishes off its own window -/

theorem continuousNavierSource_uu_uu_zero {a : ℝ} {m : ℕ} {ξ : ES}
    (hξ : ξ ∈ ballW m) {s : ℝ} (hs : s ∉ timeE m) :
    continuousNavierSource (uu a) (uu a) s ξ (0 : Fin 3) = 0 := by
  classical
  by_cases hk : ∃ k, s ∈ timeE k
  · obtain ⟨k, hks⟩ := hk
    have hkm : k ≠ m := fun heq => hs (heq ▸ hks)
    have hvec : rawNavierConvection (uu a s) (uu a s) ξ = 0 := by
      rw [rawNavierConvection_uu_single a hks ξ]
      ext i
      fin_cases i
      · rw [rawVal_eq_zero_of_ballW (Ne.symm hkm) hξ]
        simp
      · rfl
      · rfl
    show complexLeray (FourierMajorant.spaceProj ξ)
      (Complex.I • rawNavierConvection (uu a s) (uu a s) ξ) (0 : Fin 3) = 0
    rw [hvec, smul_zero, map_zero]
    simp
  · have h0 : ∀ j, s ∉ timeE j := fun j hj => hk ⟨j, hj⟩
    have hu : ∀ η i, uu a s η i = 0 := fun η i => uu_notmem a h0
    have hfun : ∀ j, (fun η : ES => uu a s η j) = (0 : ES → ℂ) := by
      intro j
      funext η
      exact hu η j
    have hconv : ∀ j i, ((fun η : ES => uu a s η j)
        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η : ES => uu a s η i)) = 0 := by
      intro j i
      rw [hfun j, conv_zero_left]
    have hconv' : rawNavierConvection (uu a s) (uu a s) ξ = 0 := by
      unfold rawNavierConvection
      ext i
      simp only [hconv, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    show complexLeray (FourierMajorant.spaceProj ξ)
      (Complex.I • rawNavierConvection (uu a s) (uu a s) ξ) (0 : Fin 3) = 0
    rw [hconv', smul_zero, map_zero]
    simp

/-- Nonnegativity of `ξ 0` on an output ball: the first coordinate of
`ballW m` is positive. -/
theorem ballW_coord0_nonneg {m : ℕ} {ξ : ES} (hξ : ξ ∈ ballW m) :
    (0 : ℝ) ≤ ξ 0 :=
  (rsh_pos m).le.trans ((ballW_geometry m hξ).2.1)

/-! ## S2: the horizon Duhamel integral as a real scalar profile -/

/-- The uniform heat-damping floor `exp(−6400)`. -/
noncomputable def damp : ℝ := Real.exp (-6400)

theorem damp_pos : (0 : ℝ) < damp := Real.exp_pos _

theorem damp_nonneg : (0 : ℝ) ≤ damp := damp_pos.le

/-- The scalar heat multiplier of the horizon Duhamel integrand at frequency
`ξ` and retarded time `1 − s`. -/
noncomputable def dampScalar (ξ : ES) (s : ℝ) : ℝ :=
  Real.exp (-((1 : ℝ) * ‖ξ‖ ^ 2 * (1 - s)))

theorem dampScalar_le_one {ξ : ES} {s : ℝ} (hs : s ≤ (1 : ℝ)) :
    dampScalar ξ s ≤ 1 := by
  unfold dampScalar
  refine (Real.exp_le_exp.mpr ?_).trans (Real.exp_zero.le : Real.exp (0 : ℝ) ≤ 1)
  rw [one_mul, neg_nonpos]
  exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hs)

theorem dampScalar_nonneg (ξ : ES) (s : ℝ) : (0 : ℝ) ≤ dampScalar ξ s :=
  le_of_lt (Real.exp_pos _)

theorem dampScalar_measurable (ξ : ES) : Measurable (fun s : ℝ => dampScalar ξ s) := by
  have h1 : Measurable (fun s : ℝ => -((1 : ℝ) * ‖ξ‖ ^ 2 * (1 - s))) := by
    fun_prop
  unfold dampScalar
  exact Real.continuous_exp.measurable.comp h1

theorem dampScalar_aesm (ξ : ES) {μ : Measure ℝ} :
    AEStronglyMeasurable (dampScalar ξ) μ := by
  have h1 : AEStronglyMeasurable (fun s : ℝ => -((1 : ℝ) * ‖ξ‖ ^ 2 * (1 - s))) μ := by
    fun_prop
  unfold dampScalar
  exact Real.continuous_exp.comp_aestronglyMeasurable h1

/-- The window-`m` source amplitude, constant in the integration variable. -/
noncomputable def econst (a : ℝ) (m : ℕ) (ξ : ES) : ℝ :=
  rawVal a m ξ * (1 - ξ 0 ^ 2 / ‖ξ‖ ^ 2)

theorem econst_nonneg (a : ℝ) (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) :
    (0 : ℝ) ≤ econst a m ξ := by
  unfold econst
  refine mul_nonneg (rawVal_nonneg a m ξ (ballW_coord0_nonneg hξ)) ?_
  by_cases hz : ‖ξ‖ ^ 2 = (0 : ℝ)
  · rw [hz]
    simp
  · have hpos : (0 : ℝ) < ‖ξ‖ ^ 2 :=
      lt_of_not_ge fun h => hz (le_antisymm h (sq_nonneg _))
    have h1 : ξ 0 ^ 2 ≤ ‖ξ‖ ^ 2 := by
      have hle := abs_apply_le_norm (f := ξ) (i := (0 : Fin 3))
      calc ξ 0 ^ 2 = |ξ 0| ^ 2 := by rw [sq_abs]
        _ ≤ ‖ξ‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
    exact sub_nonneg.mpr ((div_le_one hpos).mpr h1)

/-- The real scalar profile of the coordinate-`0` horizon Duhamel integrand:
`dampScalar ξ · econst a m ξ` on `timeE m`, zero elsewhere. -/
noncomputable def duhScalar (a : ℝ) (m : ℕ) (ξ : ES) : ℝ → ℝ :=
  (timeE m).indicator (fun s => dampScalar ξ s * econst a m ξ)

theorem duhScalar_apply {a : ℝ} {m : ℕ} {ξ : ES} (s : ℝ) :
    duhScalar a m ξ s = if s ∈ timeE m then dampScalar ξ s * econst a m ξ else 0 := by
  classical
  unfold duhScalar
  rw [Set.indicator_apply]

theorem duhScalar_measurable (a : ℝ) (m : ℕ) (ξ : ES) :
    Measurable (fun s : ℝ => duhScalar a m ξ s) := by
  classical
  unfold duhScalar
  exact ((dampScalar_measurable ξ).mul measurable_const).indicator (timeE_measurable m)

theorem duhScalar_nonneg (a : ℝ) (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) (s : ℝ) :
    (0 : ℝ) ≤ duhScalar a m ξ s := by
  rw [duhScalar_apply]
  by_cases hs : s ∈ timeE m
  · rw [if_pos hs]
    exact mul_nonneg (dampScalar_nonneg ξ s) (econst_nonneg a m hξ)
  · rw [if_neg hs]

/-- Pointwise bound of the scalar profile by the window-independent source
amplitude: the heat multiplier is at most `1`. -/
theorem duhScalar_le_econst (a : ℝ) (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) (s : ℝ) :
    ‖duhScalar a m ξ s‖ ≤ econst a m ξ := by
  have hecon : (0 : ℝ) ≤ econst a m ξ := econst_nonneg a m hξ
  rw [duhScalar_apply]
  by_cases hsw : s ∈ timeE m
  · rw [if_pos hsw, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (dampScalar_nonneg ξ s) hecon)]
    calc dampScalar ξ s * econst a m ξ ≤ 1 * econst a m ξ :=
        mul_le_mul_of_nonneg_right (dampScalar_le_one (timeE_subset m hsw).2.le) hecon
      _ = econst a m ξ := one_mul _
  · rw [if_neg hsw, norm_zero]
    exact hecon

/-- On the active window of the shell that owns `ξ`, the heat multiplier is
bounded below by `damp`: `(rsh m)² · 4⁻ᵐ` is constant. -/
theorem dampScalar_ge_damp {m : ℕ} {ξ : ES} (hξ : ξ ∈ ballW m) {s : ℝ}
    (hs : s ∈ timeE m) : damp ≤ dampScalar ξ s := by
  obtain ⟨_, _, _, hnorm⟩ := ballW_geometry m hξ
  have h2 : (1 : ℝ) - s ≤ (1 / 4 : ℝ) ^ m := by
    simp only [timeE, tEnd] at hs
    linarith [hs.1]
  have hB : ‖ξ‖ ^ 2 ≤ (25 / 4 : ℝ) * rsh m ^ 2 := by
    have hn0 : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg _
    have h : ‖ξ‖ ^ 2 ≤ ((5 / 2 : ℝ) * rsh m) ^ 2 := pow_le_pow_left₀ hn0 hnorm 2
    rw [show ((5 / 2 : ℝ) * rsh m) ^ 2 = (25 / 4 : ℝ) * rsh m ^ 2 by ring] at h
    exact h
  have h3 : (25 / 4 : ℝ) * rsh m ^ 2 * (1 / 4 : ℝ) ^ m = (6400 : ℝ) := by
    rw [rsh_sq m]
    have hp : (0 : ℝ) < (4 : ℝ) ^ m := pow_pos (by norm_num) m
    have h4 : (1 / 4 : ℝ) ^ m = ((4 : ℝ) ^ m)⁻¹ := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow]
    rw [h4, ← mul_assoc]
    field_simp [hp.ne]
    ring
  have hexp : (1 : ℝ) * ‖ξ‖ ^ 2 * (1 - s) ≤ (6400 : ℝ) := by
    rw [one_mul]
    calc ‖ξ‖ ^ 2 * (1 - s) ≤ ‖ξ‖ ^ 2 * (1 / 4 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ ≤ ((25 / 4 : ℝ) * rsh m ^ 2) * (1 / 4 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hB (pow_nonneg (by norm_num) m)
      _ = (6400 : ℝ) := h3
  unfold damp dampScalar
  refine Real.exp_le_exp.mpr ?_
  linarith [hexp]

/-- Pointwise value of the coordinate-`0` Duhamel integrand on the active
window. -/
theorem heatMode_on_window {a : ℝ} {m : ℕ} {ξ : ES} (hξ : ξ ∈ ballW m) {s : ℝ}
    (hs : s ∈ timeE m) :
    heatMode 1 (1 - s)
      (fun ζ : ES => continuousNavierSource (uu a) (uu a) s ζ (0 : Fin 3)) ξ =
      (dampScalar ξ s * econst a m ξ : ℝ) • Complex.I := by
  unfold heatMode dampScalar econst
  dsimp only
  rw [source_coord0 a hs ξ, nls_single0_val]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The coordinate-`0` horizon Duhamel integrand is the scalar profile times
the fixed unit vector `Complex.I`, at every time. -/
theorem heatMode_duhScalar {a : ℝ} {m : ℕ} {ξ : ES} (hξ : ξ ∈ ballW m) {s : ℝ} :
    heatMode 1 (1 - s)
      (fun ζ : ES => continuousNavierSource (uu a) (uu a) s ζ (0 : Fin 3)) ξ =
      (duhScalar a m ξ s : ℝ) • Complex.I := by
  classical
  by_cases hsw : s ∈ timeE m
  · rw [duhScalar_apply, if_pos hsw]
    exact heatMode_on_window hξ hsw
  · rw [duhScalar_apply, if_neg hsw, zero_smul]
    unfold heatMode
    dsimp only
    rw [continuousNavierSource_uu_uu_zero hξ hsw]
    exact mul_zero _

/-- The coordinate-`0` horizon Duhamel value is the real integral of the
scalar profile, in the direction `Complex.I`. -/
theorem duhamel_duhScalar (a : ℝ) (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) :
    continuousDuhamel 1 (uu a) (uu a) 1 ξ (0 : Fin 3) =
      (∫ s in Icc (0 : ℝ) 1, duhScalar a m ξ s ∂volume) • Complex.I := by
  have hae : (fun s : ℝ =>
      heatMode 1 (1 - s)
        (fun ζ : ES => continuousNavierSource (uu a) (uu a) s ζ (0 : Fin 3)) ξ)
      =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun s : ℝ => (duhScalar a m ξ s : ℝ) • Complex.I :=
    ae_of_all _ (fun s => heatMode_duhScalar hξ)
  show (∫ s in Icc (0 : ℝ) 1,
      heatMode 1 (1 - s)
        (fun ζ : ES => continuousNavierSource (uu a) (uu a) s ζ (0 : Fin 3)) ξ) = _
  rw [integral_congr_ae hae]
  exact integral_smul_const (fun s : ℝ => duhScalar a m ξ s) Complex.I

/-- The coordinate-`0` horizon Duhamel norm IS the scalar horizon integral. -/
theorem norm_duhamel_eq_integral (a : ℝ) (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) :
    ‖continuousDuhamel 1 (uu a) (uu a) 1 ξ (0 : Fin 3)‖ =
      ∫ s in Icc (0 : ℝ) 1, duhScalar a m ξ s ∂volume := by
  rw [duhamel_duhScalar a m hξ]
  simp only [Complex.real_smul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg_of_ae
      (ae_of_all _ (duhScalar_nonneg a m hξ)))]

/-- The horizon scalar integral carries the damping floor times the window
measure. -/
theorem integral_duhScalar_ge (a : ℝ) (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) :
    damp * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * econst a m ξ ≤
      ∫ s in Icc (0 : ℝ) 1, duhScalar a m ξ s ∂volume := by
  classical
  have hsub : timeE m ⊆ Icc (0 : ℝ) 1 := (timeE_subset m).trans Set.Ioo_subset_Icc_self
  have hmeas : MeasurableSet (timeE m) := timeE_measurable m
  have hecon : (0 : ℝ) ≤ econst a m ξ := econst_nonneg a m hξ
  haveI hmu : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hduh_sm : AEStronglyMeasurable (fun s : ℝ => duhScalar a m ξ s)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (duhScalar_measurable a m ξ).aestronglyMeasurable
  have hle' : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)), ‖duhScalar a m ξ s‖ ≤ econst a m ξ :=
    ae_of_all _ (duhScalar_le_econst a m hξ)
  have hduh_int : Integrable (fun s : ℝ => duhScalar a m ξ s)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    Integrable.mono' (integrable_const (econst a m ξ)) hduh_sm hle'
  have hind_nonneg : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      ((timeE m).indicator (fun _ : ℝ => damp * econst a m ξ)) := by
    refine ae_of_all _ (fun s => ?_)
    rw [Set.indicator_apply]
    by_cases hs : s ∈ timeE m
    · rw [if_pos hs]
      exact mul_nonneg damp_nonneg hecon
    · rw [if_neg hs]
      exact le_refl _
  have hle2 : ((timeE m).indicator (fun _ : ℝ => damp * econst a m ξ))
      ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] duhScalar a m ξ := by
    refine ae_of_all _ (fun s => ?_)
    rw [Set.indicator_apply, duhScalar_apply]
    by_cases hsw : s ∈ timeE m
    · rw [if_pos hsw, if_pos hsw]
      exact mul_le_mul_of_nonneg_right (dampScalar_ge_damp hξ hsw) hecon
    · rw [if_neg hsw, if_neg hsw]
  have hind : ∫ s : ℝ, (timeE m).indicator (fun _ : ℝ => damp * econst a m ξ) s
      ∂(volume.restrict (Icc (0 : ℝ) 1))
      = damp * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * econst a m ξ := by
    rw [integral_indicator hmeas, Measure.restrict_restrict_of_subset hsub]
    rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ,
      measure_timeE m, ENNReal.toReal_ofReal (by positivity)]
    ring
  calc damp * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * econst a m ξ
      = ∫ s : ℝ, (timeE m).indicator (fun _ : ℝ => damp * econst a m ξ) s
          ∂(volume.restrict (Icc (0 : ℝ) 1)) := hind.symm
    _ ≤ ∫ s : ℝ, (fun s : ℝ => duhScalar a m ξ s) s
          ∂(volume.restrict (Icc (0 : ℝ) 1)) :=
        integral_mono_of_nonneg hind_nonneg hduh_int hle2
    _ = ∫ s in Icc (0 : ℝ) 1, duhScalar a m ξ s ∂volume := rfl

/-- The `X¹`-weighted horizon Duhamel coordinate-`0` integrand. -/
noncomputable def duhIntegrand (a : ℝ) : ES → ℝ :=
  fun ξ => ‖ξ‖ * ‖continuousDuhamel 1 (uu a) (uu a) 1 ξ (0 : Fin 3)‖

theorem duhIntegrand_nonneg (a : ℝ) (ξ : ES) : (0 : ℝ) ≤ duhIntegrand a ξ :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem econst_eq_norm_source (a : ℝ) (m : ℕ) {ξ : ES} (hξ : ξ ∈ ballW m) :
    econst a m ξ = ‖continuousNavierSource (uu a) (uu a) (tMid m) ξ (0 : Fin 3)‖ :=
  (source_coord0_norm a (tMid_mem_timeE m) (ballW_coord0_nonneg hξ)).symm

/-- Per-shell `X¹` Duhamel mass floor at the horizon time: a positive,
shell-independent constant. -/
noncomputable def DW (a : ℝ) : ℝ := damp * K0 a / muC

theorem K0_nonneg (a : ℝ) : (0 : ℝ) ≤ K0 a := by
  unfold K0
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (by norm_num : (0 : ℝ) ≤ (9 / 25 : ℝ)) (mul_self_nonneg a)) mu38_pos.le) muC_pos.le)
    (by norm_num : (0 : ℝ) ≤ (768 : ℝ))

theorem DW_nonneg (a : ℝ) : (0 : ℝ) ≤ DW a :=
  div_nonneg (mul_nonneg damp_nonneg (K0_nonneg a)) muC_pos.le

theorem DW_pos (a : ℝ) (ha : 0 < a) : (0 : ℝ) < DW a :=
  div_pos (mul_pos damp_pos (K0_pos a ha)) muC_pos

theorem DW_eq (a : ℝ) (m : ℕ) :
    damp * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * K1 a m = DW a := by
  have hm : (muC : ℝ) ≠ 0 := ne_of_gt muC_pos
  have hkey : ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * K1 a m * muC = K0 a := by
    calc ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * K1 a m * muC
        = K1 a m * (muC * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m)) := by ring
      _ = K0 a := K1_measure_eq a m
  have hX : ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * K1 a m = K0 a / muC := by
    rw [← hkey, ← mul_div_assoc', div_self hm, mul_one]
  unfold DW
  calc damp * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * K1 a m
      = damp * (((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * K1 a m) := by ring
    _ = damp * (K0 a / muC) := by rw [hX]
    _ = damp * K0 a / muC := mul_div_assoc' _ _ _

/-- On the output ball of shell `m`, the `X¹`-weighted horizon Duhamel value
dominates `DW a`. -/
theorem duhIntegrand_ballW_ge (a : ℝ) (ha : 0 < a) (m : ℕ) {ξ : ES}
    (hξ : ξ ∈ ballW m) : DW a ≤ duhIntegrand a ξ := by
  unfold duhIntegrand
  have hn : (rsh m : ℝ) ≤ ‖ξ‖ := (ballW_geometry m hξ).1
  have hsrc := norm_source_ge a ha (tMid_mem_timeE m) hξ
  have hne : K1 a m ≤
      ‖continuousNavierSource (uu a) (uu a) (tMid m) ξ (0 : Fin 3)‖ * ‖ξ‖ := by
    unfold K1
    calc (9 / 25 : ℝ) * (a * a) * mu38 * (rsh m) ^ 2
        = ((9 / 25 : ℝ) * (a * a) * mu38 * rsh m) * rsh m := by ring
      _ ≤ ‖continuousNavierSource (uu a) (uu a) (tMid m) ξ (0 : Fin 3)‖ * rsh m :=
          mul_le_mul_of_nonneg_right hsrc (rsh_pos m).le
      _ ≤ ‖continuousNavierSource (uu a) (uu a) (tMid m) ξ (0 : Fin 3)‖ * ‖ξ‖ :=
          mul_le_mul_of_nonneg_left hn (norm_nonneg _)
  have hw : (0 : ℝ) ≤ (3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m := by positivity
  have hd : ‖continuousDuhamel 1 (uu a) (uu a) 1 ξ (0 : Fin 3)‖
      = ∫ s in Icc (0 : ℝ) 1, duhScalar a m ξ s ∂volume :=
    norm_duhamel_eq_integral a m hξ
  have hi : damp * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * econst a m ξ
      ≤ ∫ s in Icc (0 : ℝ) 1, duhScalar a m ξ s ∂volume :=
    integral_duhScalar_ge a m hξ
  have he : econst a m ξ =
      ‖continuousNavierSource (uu a) (uu a) (tMid m) ξ (0 : Fin 3)‖ :=
    econst_eq_norm_source a m hξ
  calc DW a = damp * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) * K1 a m := (DW_eq a m).symm
    _ ≤ damp * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) *
        (‖continuousNavierSource (uu a) (uu a) (tMid m) ξ (0 : Fin 3)‖ * ‖ξ‖) :=
        mul_le_mul_of_nonneg_left hne (mul_nonneg damp_nonneg hw)
    _ = ‖ξ‖ * (damp * ((3 / 4 : ℝ) * (1 / 4 : ℝ) ^ m) *
          ‖continuousNavierSource (uu a) (uu a) (tMid m) ξ (0 : Fin 3)‖) := by ring
    _ ≤ ‖ξ‖ * ‖continuousDuhamel 1 (uu a) (uu a) 1 ξ (0 : Fin 3)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [hd, ← he]
        exact hi

/-- Pointwise: the sum over the first `N` output balls is dominated by the
horizon `X¹` Duhamel integrand. The balls are pairwise disjoint, so at most
one term is nonzero. -/
theorem duhIntegrand_sum_le (a : ℝ) (ha : 0 < a) (N : ℕ) (ξ : ES) :
    ∑ m ∈ Finset.range N, ENNReal.ofReal (DW a) *
        (ballW m).indicator (fun _ : ES => (1 : ENNReal)) ξ ≤
      ENNReal.ofReal ‖duhIntegrand a ξ‖ := by
  classical
  by_cases h : ∃ m, m ∈ Finset.range N ∧ ξ ∈ ballW m
  · obtain ⟨m, hmN, hξW⟩ := h
    have hnotin : ∀ k : ℕ, k ≠ m → ¬(ξ ∈ ballW k) := by
      intro k hkm hξk
      have hd : dist ((2 : ℝ) • eta m) ((2 : ℝ) • eta k)
          ≤ dist ((2 : ℝ) • eta m) ξ + dist ξ ((2 : ℝ) • eta k) := dist_triangle _ _ _
      have hsep : dist ((2 : ℝ) • eta m) ((2 : ℝ) • eta k)
          = ‖(2 : ℝ) • eta m - (2 : ℝ) • eta k‖ := dist_eq_norm _ _
      have h1 : dist ((2 : ℝ) • eta m) ξ < 1 / 2 := by
        rw [dist_comm]
        exact (mem_ballW m ξ).mp hξW
      have h2 : dist ξ ((2 : ℝ) • eta k) < 1 / 2 := (mem_ballW k ξ).mp hξk
      linarith [ballW_separated (Ne.symm hkm), hd, hsep, h1, h2]
    have hge : ENNReal.ofReal (DW a) ≤ ENNReal.ofReal ‖duhIntegrand a ξ‖ := by
      rw [Real.norm_of_nonneg (duhIntegrand_nonneg a ξ)]
      exact ENNReal.ofReal_le_ofReal (duhIntegrand_ballW_ge a ha m hξW)
    have hfun : (fun k => ENNReal.ofReal (DW a) *
        (ballW k).indicator (fun _ : ES => (1 : ENNReal)) ξ) =
        fun k => if m = k then ENNReal.ofReal (DW a) else 0 := by
      funext k
      by_cases hkm : k = m
      · subst hkm
        rw [Set.indicator_apply]
        simp [hξW]
      · have hn : ¬(ξ ∈ ballW k) := hnotin k hkm
        rw [Set.indicator_apply, if_neg hn, mul_zero,
          if_neg (fun hh : m = k => hkm hh.symm)]
    rw [hfun]
    have hcollapse : (∑ k ∈ Finset.range N, if m = k then ENNReal.ofReal (DW a) else 0) =
        ENNReal.ofReal (DW a) := by
      rw [Finset.sum_ite_eq (s := Finset.range N) (a := m)
          (b := fun _ => ENNReal.ofReal (DW a)), if_pos hmN]
    rw [hcollapse]
    exact hge
  · have hzero : ∀ k ∈ Finset.range N, ENNReal.ofReal (DW a) *
        (ballW k).indicator (fun _ : ES => (1 : ENNReal)) ξ = 0 := by
      intro k hk
      have hn : ¬(ξ ∈ ballW k) := fun hc => h ⟨k, hk, hc⟩
      rw [Set.indicator_apply]
      simp [hn]
    rw [Finset.sum_eq_zero hzero]
    exact bot_le

/-- The `lintegral` of the shell-`m` ball lower function is the constant
`damp · K0 a`. -/
theorem ballW_lintegral (a : ℝ) (m : ℕ) :
    ∫⁻ ξ : ES, ENNReal.ofReal (DW a) *
        (ballW m).indicator (fun _ : ES => (1 : ENNReal)) ξ ∂volume =
      ENNReal.ofReal (damp * K0 a) := by
  have hprod : DW a * muC = damp * K0 a := by
    unfold DW
    field_simp [ne_of_gt muC_pos]
  rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (DW a))
      (measurable_const.indicator (measurableSet_ballW m)),
    MeasureTheory.lintegral_indicator (measurableSet_ballW m)
      (fun _ : ES => (1 : ENNReal)),
    MeasureTheory.setLIntegral_one (ballW m),
    measure_ballW_eq m,
    ← ENNReal.ofReal_mul (DW_nonneg a),
    hprod]

/-- The first `N` output balls contribute `N · damp · K0 a` to the horizon
`X¹` mass. -/
theorem lintegral_duhIntegrand_le (a : ℝ) (ha : 0 < a) (N : ℕ) :
    (N : ENNReal) * ENNReal.ofReal (damp * K0 a) ≤
      ∫⁻ ξ : ES, ENNReal.ofReal ‖duhIntegrand a ξ‖ ∂volume := by
  classical
  have hmeas : ∀ m ∈ Finset.range N,
      Measurable (fun ξ : ES => ENNReal.ofReal (DW a) *
        (ballW m).indicator (fun _ : ES => (1 : ENNReal)) ξ) := by
    intro m _
    exact Measurable.mul measurable_const
      (measurable_const.indicator (measurableSet_ballW m))
  calc (N : ENNReal) * ENNReal.ofReal (damp * K0 a)
      = ∑ m ∈ Finset.range N, ENNReal.ofReal (damp * K0 a) := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
    _ = ∑ m ∈ Finset.range N,
          ∫⁻ ξ : ES, ENNReal.ofReal (DW a) *
            (ballW m).indicator (fun _ : ES => (1 : ENNReal)) ξ ∂volume :=
          (Finset.sum_congr rfl (fun m _ => ballW_lintegral a m)).symm
    _ ≤ ∫⁻ ξ : ES, ∑ m ∈ Finset.range N, ENNReal.ofReal (DW a) *
          (ballW m).indicator (fun _ : ES => (1 : ENNReal)) ξ ∂volume :=
          (MeasureTheory.lintegral_finsetSum' (Finset.range N)
            (fun m hm => (hmeas m hm).aemeasurable)).ge
    _ ≤ ∫⁻ ξ : ES, ENNReal.ofReal ‖duhIntegrand a ξ‖ ∂volume :=
          MeasureTheory.lintegral_mono (duhIntegrand_sum_le a ha N)

/-- The horizon `X¹` Duhamel mass of the cascade diverges. -/
theorem lintegral_duhIntegrand_eq_top (a : ℝ) (ha : 0 < a) :
    ∫⁻ ξ : ES, ENNReal.ofReal ‖duhIntegrand a ξ‖ ∂volume = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le (fun r => ?_)
  obtain ⟨N, hN⟩ := exists_nat_gt ((r : ℝ) / (damp * K0 a))
  have hD : (0 : ℝ) < damp * K0 a := mul_pos damp_pos (K0_pos a ha)
  have heq : (N : ENNReal) * ENNReal.ofReal (damp * K0 a) =
      ENNReal.ofReal ((N : ℝ) * (damp * K0 a)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    simp
  have hr : (r : ENNReal) ≤ (N : ENNReal) * ENNReal.ofReal (damp * K0 a) := by
    rw [heq, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (((div_lt_iff₀ hD).1 hN).le)
  exact le_trans hr (lintegral_duhIntegrand_le a ha N)

theorem not_integrable_duhIntegrand (a : ℝ) (ha : 0 < a) :
    ¬ Integrable (duhIntegrand a) volume := by
  intro h
  have hf := h.hasFiniteIntegral
  rw [MeasureTheory.hasFiniteIntegral_iff_norm, lintegral_duhIntegrand_eq_top a ha] at hf
  exact lt_irrefl ⊤ hf

/-! ## S3: transport to the completed box's mild image -/

theorem cascadeBox_fst (ρ : ℝ) (hρ : 0 < ρ) :
    (cascadeBox ρ hρ).1 = cascadeCarrier ρ hρ := rfl

theorem duhamel_eq_representative (ρ : ℝ) (hρ : 0 < ρ) (ξ : ES) :
    continuousDuhamel 1 (uu (boxAmplitude ρ)) (uu (boxAmplitude ρ)) 1 ξ =
      continuousDuhamel (1 : ℝ)
        (everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ))
        (everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ)) 1 ξ :=
  continuousDuhamel_congr_ae_on_horizon 1 1 _ _
    (cascade_ae_everywhereRepresentative ρ hρ) 1
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) ξ

/-- At the zero datum the free heat term vanishes, so the mild image at the
horizon IS the Duhamel term of the cascade representative. -/
theorem mildImage_eq_duhamel (ρ : ℝ) (hρ : 0 < ρ) (ξ : ES) (i : Fin 3) :
    mildImage 1 zero_lt_one (0 : ES → ComplexSpace)
      (everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ)) 1 ξ i =
      continuousDuhamel 1 (uu (boxAmplitude ρ)) (uu (boxAmplitude ρ)) 1 ξ i := by
  have hzero : ∀ (ν t : ℝ) (ξ : ES),
      heatVec ν t (0 : ES → ComplexSpace) ξ = 0 := by
    intro ν t ξ
    ext j
    simp [heatVec, heatMode]
  have h1ν : ((1 : ℝ≥0) : ℝ) = (1 : ℝ) := by norm_num
  unfold mildImage ContinuousLeiLinSelfMap.continuousMildImage
  rw [hzero, zero_add, h1ν, duhamel_eq_representative ρ hρ ξ]

/-- **The `X¹` moment of the cascade mild image fails at `t = 1`.** -/
theorem not_integrable_mildImageX1_horizon (ρ : ℝ) (hρ : 0 < ρ) :
    ¬ Integrable (fun ξ : ES => ‖ξ‖ * ‖mildImage 1 zero_lt_one
        (0 : ES → ComplexSpace)
        (everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ)) 1 ξ (0 : Fin 3)‖)
      volume := by
  intro h
  have hcong : (fun ξ : ES => ‖ξ‖ * ‖mildImage 1 zero_lt_one (0 : ES → ComplexSpace)
      (everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ)) 1 ξ (0 : Fin 3)‖)
      =ᵐ[volume] duhIntegrand (boxAmplitude ρ) := by
    refine ae_of_all _ (fun ξ => ?_)
    show ‖ξ‖ * ‖mildImage 1 zero_lt_one (0 : ES → ComplexSpace)
        (everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ)) 1 ξ (0 : Fin 3)‖ = _
    rw [mildImage_eq_duhamel ρ hρ ξ (0 : Fin 3)]
    unfold duhIntegrand
    rfl
  exact not_integrable_duhIntegrand (boxAmplitude ρ) (boxAmplitude_pos hρ)
    (h.congr hcong)

/-! ## S4: the typed negative for leaves 2c and 2e -/

/-- The datum `a = 0` satisfies every side condition
`MildAssemblyTimeLeaves` demands of a datum, so the obstruction below is not
an artefact of an inadmissible input. -/
theorem zero_datum_admissible (R : ℝ) (hR : (0 : ℝ) ≤ R) :
    (∀ i : Fin 3, AEStronglyMeasurable
        (fun ξ : ES => (0 : ES → ComplexSpace) ξ i) volume) ∧
    (∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖(0 : ES → ComplexSpace) ξ i‖)) ∧
    (∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖(0 : ES → ComplexSpace) ξ i‖)) ∧
    coordinateXm1Mass (0 : ES → ComplexSpace) ≤ R := by
  have hzero : ∀ i : Fin 3, (fun ξ : ES => ‖ξ‖⁻¹ * ‖(0 : ES → ComplexSpace) ξ i‖) =
      fun _ : ES => (0 : ℝ) := by
    intro i
    funext ξ
    simp
  have hzero1 : ∀ i : Fin 3, (fun ξ : ES => ‖ξ‖ * ‖(0 : ES → ComplexSpace) ξ i‖) =
      fun _ : ES => (0 : ℝ) := by
    intro i
    funext ξ
    simp
  refine ⟨fun i => aestronglyMeasurable_const, ?_, ?_, ?_⟩
  · intro i
    rw [hzero i]
    exact integrable_zero_fun
  · intro i
    rw [hzero1 i]
    exact integrable_zero_fun
  · have hmass : coordinateXm1Mass (0 : ES → ComplexSpace) = 0 := by
      unfold coordinateXm1Mass normXm1
      refine Finset.sum_eq_zero (fun i _ => ?_)
      simp only [Pi.zero_apply, norm_zero, mul_zero, integral_zero]
    rw [hmass]
    exact hR

/-- **Typed negative, box-specialised.** For every radius `ρ > 0` the
every-time `X¹` integrability of the mild image of the cascade box fails: the
proposition supplied to the constructor of leaf 2e is false at `t = 1`. -/
theorem not_mildTimeLeaf_hmX1_cascade (ρ : ℝ) (hρ : 0 < ρ) :
    ¬ ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ *
        ‖mildImage 1 zero_lt_one (0 : ES → ComplexSpace)
          (everywhereRawRepresentative 1 1 (cascadeBox ρ hρ).1) t ξ i‖) := by
  intro h
  have hcar : (cascadeBox ρ hρ).1 = cascadeCarrier ρ hρ := cascadeBox_fst ρ hρ
  rw [hcar] at h
  exact not_integrable_mildImageX1_horizon ρ hρ
    (h 1 (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (0 : Fin 3))

/-- **Typed negative, in the literal residual shape.** At `(ν, T) = (1, 1)`
the every-time reading of leaf `hmX1` (2c) of `MildAssemblyTimeLeaves` — the
residual quoted verbatim in `docs/OPEN_FRONTIER_MAP.md` — is FALSE: for every
`R > 0` the universal statement over `ActualLinkedBox 1 1 (2 * R) (2 * R)`
fails already at the admissible zero datum, at the horizon time `t = 1`, in
coordinate `0`. -/
theorem not_mildTimeLeaf_hmX1_everyTime (R : ℝ) (hR : (0 : ℝ) < R) :
    ¬ ∀ x : ActualLinkedBox 1 1 (2 * R) (2 * R), ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin 3,
        Integrable (fun ξ : ES => ‖ξ‖ * ‖mildImage 1 zero_lt_one
          (0 : ES → ComplexSpace) (everywhereRawRepresentative 1 1 x.1) t ξ i‖) := by
  intro h
  have hρ : (0 : ℝ) < 2 * R := by linarith
  exact not_mildTimeLeaf_hmX1_cascade (2 * R) hρ
    (fun t ht i => h (cascadeBox (2 * R) hρ) t ht i)

/-- **Leaf 2e is blocked behind a false premise.** The constructor obligation
of `hmX1Time` is the every-time leaf 2c of the horizon-truncated mild image.
For the cascade box that obligation is unsatisfiable: at `t = 1`, where
`mildImageIcc` agrees with `mildImage`, the truncated image is not
`X¹`-integrable. -/
theorem mildTimeLeaf_hmX1Time_obstruction (ρ : ℝ) (hρ : 0 < ρ) :
    ¬ ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ *
        ‖mildImageIcc 1 zero_lt_one 1 (0 : ES → ComplexSpace)
          (everywhereRawRepresentative 1 1 (cascadeBox ρ hρ).1) t ξ i‖) := by
  intro h
  have hcar : (cascadeBox ρ hρ).1 = cascadeCarrier ρ hρ := cascadeBox_fst ρ hρ
  have h1 := h 1 (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (0 : Fin 3)
  rw [hcar] at h1
  have hcong : (fun ξ : ES => ‖ξ‖ * ‖mildImageIcc 1 zero_lt_one 1
      (0 : ES → ComplexSpace) (everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ))
      1 ξ (0 : Fin 3)‖)
      =ᵐ[volume] (fun ξ : ES => ‖ξ‖ * ‖mildImage 1 zero_lt_one (0 : ES → ComplexSpace)
        (everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ)) 1 ξ (0 : Fin 3)‖) := by
    refine ae_of_all _ (fun ξ => ?_)
    exact congrArg (fun z : ComplexSpace => ‖ξ‖ * ‖z (0 : Fin 3)‖)
      (mildImageIcc_of_mem 1 zero_lt_one 1 (0 : ES → ComplexSpace)
        (everywhereRawRepresentative 1 1 (cascadeCarrier ρ hρ)) 1
        (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) ξ)
  exact not_integrable_mildImageX1_horizon ρ hρ (h1.congr hcong)

#check @not_mildTimeLeaf_hmX1_everyTime
#print axioms not_mildTimeLeaf_hmX1_everyTime
#check @mildTimeLeaf_hmX1Time_obstruction
#print axioms mildTimeLeaf_hmX1Time_obstruction
#check @not_integrable_mildImageX1_horizon
#print axioms not_integrable_mildImageX1_horizon

end Navier.Analysis.MildTimeLeafX1CascadeFalsification
