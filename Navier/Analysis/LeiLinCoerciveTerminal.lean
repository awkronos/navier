import Navier.Analysis.LeiLinBilinear
import Navier.Analysis.LeiLinTimeMixed
import Navier.Analysis.CriticalMildBoundedContinuation
import Navier.Analysis.CriticalMildWeightedBanach
import Navier.Analysis.CriticalMildSeries

/-!
# Coercive critical-norm control of the mild terminal bound

`GlobalRegularityCrownCore` records that the heat/Duhamel scalar recurrence
cannot preserve a fixed positive critical-norm radius.  This module supplies
the replacement quantity: the Lei–Lin mixed critical norm

  `𝒬_ν(f) = ‖f‖_{𝒳^{-1}} + ν ‖f‖_{𝒳¹}`,

augmented by zero-mode mass.  That quantity coercively dominates the
inhomogeneous `WeightedLatticeBanach` norm used by the mild charts, and
therefore constructs `CriticalMildTerminalNormBound` from a mixed terminal
bound — without using the disproved fixed-radius recurrence.

No claim is made that the mixed bound holds for arbitrary large data.  This is
the coercive bridge for `navier.bounded-chain-direct-limit`, not a
global-regularity theorem.

Reference: Z. Lei and F. Lin, CPAM 64 (2011) 1297–1304.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.LeiLinCoerciveTerminal

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildBoundedContinuation
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinBilinear
open Navier.Analysis.LeiLinTimeMixed

/-- Homogeneous mode size `|k|` on the lattice carrier. -/
def latticeModeSize (m : LatticeMode) : ℝ :=
  ‖complexFrequency (latticeFrequency m)‖

theorem latticeModeSize_nonneg (m : LatticeMode) : 0 ≤ latticeModeSize m :=
  norm_nonneg _

theorem latticeModeSize_zero : latticeModeSize 0 = 0 := by
  unfold latticeModeSize
  rw [norm_eq_zero]
  ext i
  fin_cases i <;> simp [latticeFrequency, complexFrequency_apply]

theorem latticeModeWeight_eq_one_add_size (m : LatticeMode) :
    latticeModeWeight m = 1 + latticeModeSize m :=
  rfl

/-- Physical coefficient amplitudes of a weighted Banach field. -/
def weightedAmplitude (u : WeightedLatticeBanach) (m : LatticeMode) : ℝ :=
  complexEuclideanNorm (weightedLatticeCoefficient u m)

theorem weightedAmplitude_nonneg (u : WeightedLatticeBanach) (m : LatticeMode) :
    0 ≤ weightedAmplitude u m :=
  norm_nonneg _

theorem norm_apply_eq_weight_mul_amplitude (u : WeightedLatticeBanach)
    (m : LatticeMode) :
    ‖u m‖ = (1 + latticeModeSize m) * weightedAmplitude u m := by
  have h := (latticeWeightedAmplitude_coefficient u m).symm
  simpa [weightedAmplitude, latticeWeightedAmplitude,
    latticeModeWeight_eq_one_add_size] using h

theorem summable_norm_weighted (u : WeightedLatticeBanach) :
    Summable fun m : LatticeMode => ‖u m‖ := by
  simpa using u.2.summable

theorem norm_eq_tsum_norm (u : WeightedLatticeBanach) :
    ‖u‖ = ∑' m : LatticeMode, ‖u m‖ :=
  (tsum_latticeWeightedAmplitude_coefficient u).symm.trans <| by
    simp [latticeWeightedAmplitude_coefficient]

/-- The inhomogeneous CriticalMild norm splits as `𝒳⁰ + 𝒳¹`. -/
theorem norm_eq_normX0_add_normX1 (u : WeightedLatticeBanach) :
    ‖u‖ =
      normX0 (weightedAmplitude u) +
        normX1 latticeModeSize (weightedAmplitude u) := by
  set f := weightedAmplitude u
  have hterm : ∀ m,
      ‖u m‖ = |f m| + latticeModeSize m * |f m| := by
    intro m
    have ha := weightedAmplitude_nonneg u m
    rw [norm_apply_eq_weight_mul_amplitude u m, abs_of_nonneg ha]
    ring
  have hs := summable_norm_weighted u
  have hs0 : Summable fun m => |f m| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun m => by
        have ht := hterm m
        have hm := mul_nonneg (latticeModeSize_nonneg m) (abs_nonneg (f m))
        linarith [norm_nonneg (u m)]) hs
  have hs1 : Summable fun m => latticeModeSize m * |f m| :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (latticeModeSize_nonneg m) (abs_nonneg _))
      (fun m => by
        have ht := hterm m
        linarith [abs_nonneg (f m), norm_nonneg (u m)]) hs
  calc ‖u‖
      = ∑' m, ‖u m‖ := norm_eq_tsum_norm u
    _ = ∑' m, (|f m| + latticeModeSize m * |f m|) := tsum_congr hterm
    _ = (∑' m, |f m|) + ∑' m, latticeModeSize m * |f m| :=
        Summable.tsum_add hs0 hs1
    _ = normX0 f + normX1 latticeModeSize f := rfl

/-- Explicit coercivity factor from AM-GM against the mixed norm. -/
def coerciveFactor (ν : ℝ) : ℝ :=
  1 / (2 * Real.sqrt ν) + 1 / ν

theorem coerciveFactor_pos {ν : ℝ} (hν : 0 < ν) : 0 < coerciveFactor ν := by
  unfold coerciveFactor
  have : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  positivity

/-- Published constant `max(1, C(ν))`, so zero-mode mass is absorbed. -/
def coerciveConstant (ν : ℝ) : ℝ :=
  max 1 (coerciveFactor ν)

theorem one_le_coerciveConstant (ν : ℝ) : 1 ≤ coerciveConstant ν :=
  le_max_left _ _

theorem coerciveFactor_le_coerciveConstant (ν : ℝ) :
    coerciveFactor ν ≤ coerciveConstant ν :=
  le_max_right _ _

theorem coerciveConstant_pos {ν : ℝ} (_hν : 0 < ν) : 0 < coerciveConstant ν :=
  lt_of_lt_of_le zero_lt_one (one_le_coerciveConstant ν)

/-- Helper: `√(A B) ≤ (A + ν B)/(2 √ν)`. -/
theorem sqrt_mul_le_mixed_div {ν A B : ℝ} (hν : 0 < ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A * B) ≤ (A + ν * B) / (2 * Real.sqrt ν) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hstep := sqrt_mul_le_add_div_two hA (mul_nonneg hν.le hB)
  have hmul : Real.sqrt (A * (ν * B)) = Real.sqrt (A * B) * Real.sqrt ν := by
    have hnn : 0 ≤ A * B := mul_nonneg hA hB
    rw [show A * (ν * B) = (A * B) * ν by ring, Real.sqrt_mul hnn]
  have : Real.sqrt (A * B) * Real.sqrt ν ≤ (A + ν * B) / 2 := by
    simpa [hmul] using hstep
  exact (le_div_iff₀ (mul_pos (by norm_num) hs)).2 (by nlinarith)

/-- **Coercive estimate** for mean-zero amplitude families. -/
theorem normX0_add_normX1_le_mixed {ν : ℝ} {σ f : LatticeMode → ℝ}
    (hν : 0 < ν) (hσ : ∀ k, 0 ≤ σ k)
    (hz : ∀ k, σ k = 0 → f k = 0)
    (h0 : Summable fun k => |f k|)
    (hm : InW (fun k => (σ k)⁻¹) f) (hp : InW σ f) :
    normX0 f + normX1 σ f ≤
      coerciveFactor ν * (normXm1 σ f + ν * normX1 σ f) := by
  have hA := normXm1_nonneg hσ f
  have hB := normX1_nonneg hσ f
  set Q := normXm1 σ f + ν * normX1 σ f
  have hX0 : normX0 f ≤ Q / (2 * Real.sqrt ν) := by
    have h1 := normX0_le_sqrt hσ hz h0 hm hp
    have h2 := sqrt_mul_le_mixed_div hν hA hB
    exact h1.trans h2
  have hX1 : normX1 σ f ≤ Q / ν :=
    (le_div_iff₀ hν).2 (by dsimp [Q]; linarith [hA])
  have hsum :
      normX0 f + normX1 σ f ≤
        Q / (2 * Real.sqrt ν) + Q / ν :=
    add_le_add hX0 hX1
  have hfactor :
      Q / (2 * Real.sqrt ν) + Q / ν =
        coerciveFactor ν * Q := by
    unfold coerciveFactor
    field_simp
  exact hsum.trans_eq hfactor

/-- Mode size vanishes only at the zero lattice mode. -/
theorem latticeModeSize_eq_zero_iff (m : LatticeMode) :
    latticeModeSize m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have hz : complexFrequency (latticeFrequency m) = 0 := (norm_eq_zero).1 h
    have h0 : (m.1 : ℝ) = 0 := by
      have := congrArg (fun v : ComplexE3 => (v 0).re) hz
      simpa [complexFrequency_apply, latticeFrequency, Pi.zero_apply, Complex.zero_re] using this
    have h1 : (m.2.1 : ℝ) = 0 := by
      have := congrArg (fun v : ComplexE3 => (v 1).re) hz
      simpa [complexFrequency_apply, latticeFrequency, Pi.zero_apply, Complex.zero_re] using this
    have h2 : (m.2.2 : ℝ) = 0 := by
      have := congrArg (fun v : ComplexE3 => (v 2).re) hz
      simpa [complexFrequency_apply, latticeFrequency, Pi.zero_apply, Complex.zero_re] using this
    refine Prod.ext (Int.cast_eq_zero.mp h0)
      (Prod.ext (Int.cast_eq_zero.mp h1) (Int.cast_eq_zero.mp h2))
  · intro h
    subst h
    exact latticeModeSize_zero

/-- The lattice mode size of any nonzero mode is at least `1`: distinct
integer lattice points are separated by at least unit Euclidean distance. -/
theorem one_le_latticeModeSize_of_ne_zero {m : LatticeMode} (hm : m ≠ 0) :
    1 ≤ latticeModeSize m := by
  have hsq : latticeModeSize m ^ 2 =
      (m.1 : ℝ) ^ 2 + (m.2.1 : ℝ) ^ 2 + (m.2.2 : ℝ) ^ 2 := by
    unfold latticeModeSize
    rw [EuclideanSpace.norm_sq_eq]
    simp [complexFrequency_apply, latticeFrequency, Fin.sum_univ_three,
      RCLike.norm_ofReal, sq_abs]
  have hone : (1 : ℝ) ≤
      (m.1 : ℝ) ^ 2 + (m.2.1 : ℝ) ^ 2 + (m.2.2 : ℝ) ^ 2 := by
    rcases show m.1 ≠ 0 ∨ m.2.1 ≠ 0 ∨ m.2.2 ≠ 0 by
        by_contra h
        push_neg at h
        exact hm (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
      with h1 | h1 | h1
    · have : (1 : ℝ) ≤ (m.1 : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ m.1 ^ 2 := by
          have := Int.one_le_abs h1
          nlinarith [sq_abs m.1]
        exact_mod_cast this
      nlinarith [sq_nonneg (m.2.1 : ℝ), sq_nonneg (m.2.2 : ℝ)]
    · have : (1 : ℝ) ≤ (m.2.1 : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ m.2.1 ^ 2 := by
          have := Int.one_le_abs h1
          nlinarith [sq_abs m.2.1]
        exact_mod_cast this
      nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2.2 : ℝ)]
    · have : (1 : ℝ) ≤ (m.2.2 : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ m.2.2 ^ 2 := by
          have := Int.one_le_abs h1
          nlinarith [sq_abs m.2.2]
        exact_mod_cast this
      nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2.1 : ℝ)]
  nlinarith [latticeModeSize_nonneg m, hsq, hone]

/-- Every physical mode amplitude family is unconditionally `𝒳¹`-summable:
the lattice weight `1 + |k|` already dominates `|k|` in the ambient
`WeightedLatticeBanach` norm, so no extra membership hypothesis is needed. -/
theorem InW_latticeModeSize (u : WeightedLatticeBanach) :
    InW latticeModeSize (weightedAmplitude u) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (latticeModeSize_nonneg k) (abs_nonneg _))
    (fun k => ?_) (summable_norm_weighted u)
  have ha := weightedAmplitude_nonneg u k
  rw [norm_apply_eq_weight_mul_amplitude u k, abs_of_nonneg ha]
  nlinarith [latticeModeSize_nonneg k]

/-- The `𝒳¹` part of the physical amplitude is 1-Lipschitz with respect to
the completed inhomogeneous weighted-lattice norm. -/
theorem normX1_weightedAmplitude_le_add_norm_sub
    (u v : WeightedLatticeBanach) :
    normX1 latticeModeSize (weightedAmplitude u) ≤
      normX1 latticeModeSize (weightedAmplitude v) + ‖u - v‖ := by
  have hu := InW_latticeModeSize u
  have hv := InW_latticeModeSize v
  have hd := summable_norm_weighted (u - v)
  have hpoint : ∀ m : LatticeMode,
      latticeModeSize m * |weightedAmplitude u m| ≤
        latticeModeSize m * |weightedAmplitude v m| + ‖(u - v) m‖ := by
    intro m
    have hσ := latticeModeSize_nonneg m
    have hau := weightedAmplitude_nonneg u m
    have hav := weightedAmplitude_nonneg v m
    rw [abs_of_nonneg hau, abs_of_nonneg hav]
    by_cases huv : weightedAmplitude u m ≤ weightedAmplitude v m
    · have hleft : latticeModeSize m * weightedAmplitude u m ≤
          latticeModeSize m * weightedAmplitude v m :=
        mul_le_mul_of_nonneg_left huv hσ
      exact hleft.trans (le_add_of_nonneg_right (norm_nonneg _))
    · have hdiff : 0 ≤ weightedAmplitude u m - weightedAmplitude v m :=
        by linarith [lt_of_not_ge huv]
      have hcoord := norm_sub_norm_le (u m) (v m)
      rw [norm_apply_eq_weight_mul_amplitude u m,
        norm_apply_eq_weight_mul_amplitude v m] at hcoord
      have hscale : latticeModeSize m *
            (weightedAmplitude u m - weightedAmplitude v m) ≤
          (1 + latticeModeSize m) *
            (weightedAmplitude u m - weightedAmplitude v m) := by
        nlinarith
      have hcarrier : (1 + latticeModeSize m) *
            (weightedAmplitude u m - weightedAmplitude v m) ≤ ‖(u - v) m‖ := by
        calc
          (1 + latticeModeSize m) *
              (weightedAmplitude u m - weightedAmplitude v m) =
            (1 + latticeModeSize m) * weightedAmplitude u m -
              (1 + latticeModeSize m) * weightedAmplitude v m := by ring
          _ ≤ ‖(u - v) m‖ := by simpa using hcoord
      nlinarith
  calc
    normX1 latticeModeSize (weightedAmplitude u) ≤
        ∑' m : LatticeMode,
          (latticeModeSize m * |weightedAmplitude v m| + ‖(u - v) m‖) :=
      hu.tsum_le_tsum hpoint (hv.add hd)
    _ = normX1 latticeModeSize (weightedAmplitude v) + ‖u - v‖ := by
      rw [hv.tsum_add hd, norm_eq_tsum_norm]
      rfl

/-- **Backward `𝒳¹` modulus for an actual mild trajectory, reduced to the
linear heat increment.**  The nonlinear part contributes the explicit
`2 R² / √ν` square-root constant; no qualitative common-interval remainder
survives the restart identity. -/
theorem normX1_shifted_trajectory_le_add_sqrt
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R L t r : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (huR : ∀ s ∈ Set.Ioc (0 : ℝ) (t + r), ‖u s‖ ≤ R)
    (hmild_t : u t = criticalMildImage ν hν u₀ u hu t ht)
    (hmild_tr : u (t + r) =
      criticalMildImage ν hν u₀ u hu (t + r) (add_nonneg ht hr))
    (hheat : ‖CriticalMildHeatFlow.weightedHeatFlow ν r hν.le hr (u t) - u t‖ ≤
      L * Real.sqrt r) :
    normX1 latticeModeSize (weightedAmplitude (u (t + r))) ≤
      normX1 latticeModeSize (weightedAmplitude (u t)) +
        (L + 2 * R ^ 2 / Real.sqrt ν) * Real.sqrt r := by
  calc
    normX1 latticeModeSize (weightedAmplitude (u (t + r))) ≤
        normX1 latticeModeSize (weightedAmplitude (u t)) + ‖u (t + r) - u t‖ :=
      normX1_weightedAmplitude_le_add_norm_sub _ _
    _ ≤ normX1 latticeModeSize (weightedAmplitude (u t)) +
        (L + 2 * R ^ 2 / Real.sqrt ν) * Real.sqrt r := by
      exact add_le_add le_rfl
        (CriticalMildQuantitativeRestart.norm_shifted_trajectory_sub_le_sqrt
          ν hν u₀ u huc hu hR ht hr huR hmild_t hmild_tr hheat)

/-- The actual mild `𝒳¹` modulus obtained from the honest half-generator
moment of the earlier endpoint. -/
theorem normX1_shifted_trajectory_le_add_sqrt_of_halfGeneratorMoment
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t r : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (huR : ∀ s ∈ Set.Ioc (0 : ℝ) (t + r), ‖u s‖ ≤ R)
    (hmild_t : u t = criticalMildImage ν hν u₀ u hu t ht)
    (hmild_tr : u (t + r) =
      criticalMildImage ν hν u₀ u hu (t + r) (add_nonneg ht hr))
    (hhalf : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u t m‖) :
    normX1 latticeModeSize (weightedAmplitude (u (t + r))) ≤
      normX1 latticeModeSize (weightedAmplitude (u t)) +
        (Real.sqrt ν * heatHalfGeneratorMoment (u t) +
          2 * R ^ 2 / Real.sqrt ν) * Real.sqrt r := by
  apply normX1_shifted_trajectory_le_add_sqrt
    ν hν u₀ u huc hu hR ht hr huR hmild_t hmild_tr
  exact norm_weightedHeatFlow_sub_le_sqrt_mul_halfGeneratorMoment
    ν r hν.le hr (u t) (hu t) hhalf

/-- **Terminal `𝒳¹` control from the smallest complete smoothing interface.**

On one trailing window, assume only the actual mild equation, a radius bound,
an integrable `𝒳¹` mass `A`, and a uniform bound `H` on the one-extra-mode
half-generator moment.  Then the terminal sampler yields the explicit constant
produced by the heat and Duhamel estimates. -/
theorem terminal_X1_le_of_trailingMass_and_halfGeneratorMoment
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R H T δ A : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hT : 0 ≤ T) (hδ : 0 < δ) (hδT : δ ≤ T)
    (huR : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖u s‖ ≤ R)
    (hmild : ∀ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T),
      u s = criticalMildImage ν hν u₀ u hu s hs.1)
    (hhalf : ∀ s ∈ Set.Icc (T - δ) T,
      Summable fun m : LatticeMode =>
        ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖)
    (hHbound : ∀ s ∈ Set.Icc (T - δ) T,
      heatHalfGeneratorMoment (u s) ≤ H)
    (hint : IntervalIntegrable
      (fun s => normX1 latticeModeSize (weightedAmplitude (u s)))
      MeasureTheory.volume (T - δ) T)
    (hmass : (∫ s in (T - δ)..T,
      normX1 latticeModeSize (weightedAmplitude (u s))) ≤ A) :
    normX1 latticeModeSize (weightedAmplitude (u T)) ≤
      A / δ + (Real.sqrt ν * H + 2 * R ^ 2 / Real.sqrt ν) * Real.sqrt δ := by
  apply terminal_X1_le_of_backward_sqrt_modulus hδ
    (add_nonneg (mul_nonneg (Real.sqrt_nonneg ν) hH)
      (by positivity : 0 ≤ 2 * R ^ 2 / Real.sqrt ν)) hint
  · intro s hs
    have hs0 : 0 ≤ s := by linarith [hs.1]
    have hr : 0 ≤ T - s := sub_nonneg.mpr hs.2
    have hsT : s + (T - s) = T := by ring
    have hstep := normX1_shifted_trajectory_le_add_sqrt_of_halfGeneratorMoment
      ν hν u₀ u huc hu hR hs0 hr
      (by simpa [hsT] using huR)
      (hmild s ⟨hs0, hs.2⟩)
      (by simpa [hsT] using hmild T ⟨hT, le_rfl⟩)
      (hhalf s hs)
    rw [hsT] at hstep
    refine hstep.trans ?_
    have hcoef :
        Real.sqrt ν * heatHalfGeneratorMoment (u s) + 2 * R ^ 2 / Real.sqrt ν ≤
          Real.sqrt ν * H + 2 * R ^ 2 / Real.sqrt ν := by
      gcongr
      exact hHbound s hs
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (T - s)))
  · exact hmass

/-- Every physical mode amplitude family is unconditionally `𝒳^{-1}`-summable:
the inverse weight is bounded by `1` off the zero mode (lattice separation),
and vanishes at the zero mode. -/
theorem InW_inv_latticeModeSize (u : WeightedLatticeBanach) :
    InW (fun k => (latticeModeSize k)⁻¹) (weightedAmplitude u) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (inv_nonneg.mpr (latticeModeSize_nonneg k)) (abs_nonneg _))
    (fun k => ?_) (summable_norm_weighted u)
  have ha := weightedAmplitude_nonneg u k
  rw [norm_apply_eq_weight_mul_amplitude u k, abs_of_nonneg ha]
  by_cases hk : k = 0
  · subst hk
    simpa [latticeModeSize_zero] using ha
  · have hge := one_le_latticeModeSize_of_ne_zero hk
    have hinv : (latticeModeSize k)⁻¹ ≤ 1 :=
      (inv_le_one_iff₀).2 (Or.inr hge)
    have hw : (1 : ℝ) ≤ 1 + latticeModeSize k := by
      linarith [latticeModeSize_nonneg k]
    nlinarith [mul_le_mul_of_nonneg_right hinv ha,
      mul_le_mul_of_nonneg_right hw ha]

/-- Mixed Lei–Lin quantity, including zero-mode mass. -/
def mixedCriticalQty (ν : ℝ) (u : WeightedLatticeBanach) : ℝ :=
  weightedAmplitude u 0 +
    normXm1 latticeModeSize (weightedAmplitude u) +
      ν * normX1 latticeModeSize (weightedAmplitude u)

theorem mixedCriticalQty_nonneg {ν : ℝ} (hν : 0 ≤ ν) (u : WeightedLatticeBanach) :
    0 ≤ mixedCriticalQty ν u := by
  unfold mixedCriticalQty
  linarith [weightedAmplitude_nonneg u 0,
    normXm1_nonneg latticeModeSize_nonneg (weightedAmplitude u),
    mul_nonneg hν (normX1_nonneg latticeModeSize_nonneg (weightedAmplitude u))]

/-- **Coercive control carrier** — the terminal mixed quantity scaled by the
coercive constant.  This is the single scalar a mild terminal bound controls;
`norm_weightedLattice_le_of_mixed` rewrites the critical norm as this carrier. -/
def coerciveControlFunctional (ν : ℝ) (u : WeightedLatticeBanach) : ℝ :=
  coerciveConstant ν * mixedCriticalQty ν u

theorem coerciveControlFunctional_nonneg {ν : ℝ} (hν : 0 < ν) (u : WeightedLatticeBanach) :
    0 ≤ coerciveControlFunctional ν u := by
  unfold coerciveControlFunctional
  exact mul_nonneg (coerciveConstant_pos hν).le (mixedCriticalQty_nonneg hν.le u)

/-- Zero-mode-killed amplitude family. -/
def amplitudeOffZero (u : WeightedLatticeBanach) (k : LatticeMode) : ℝ :=
  if k = 0 then 0 else weightedAmplitude u k

theorem summable_amplitude (u : WeightedLatticeBanach) :
    Summable fun k => |weightedAmplitude u k| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) ?_ (summable_norm_weighted u)
  intro m
  have ha := weightedAmplitude_nonneg u m
  have hw : 1 ≤ 1 + latticeModeSize m := by linarith [latticeModeSize_nonneg m]
  have hnorm := norm_apply_eq_weight_mul_amplitude u m
  rw [hnorm, abs_of_nonneg ha]
  nlinarith [mul_nonneg (zero_le_one.trans hw) ha]

theorem summable_amplitudeOffZero (u : WeightedLatticeBanach) :
    Summable fun k => |amplitudeOffZero u k| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) ?_ (summable_amplitude u)
  intro k
  by_cases hk : k = 0
  · simp [amplitudeOffZero, hk]
  · simp [amplitudeOffZero, hk]

theorem InW_Xm1_offZero (u : WeightedLatticeBanach)
    (hm : InW (fun k => (latticeModeSize k)⁻¹) (weightedAmplitude u)) :
    InW (fun k => (latticeModeSize k)⁻¹) (amplitudeOffZero u) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (inv_nonneg.mpr (latticeModeSize_nonneg k)) (abs_nonneg _))
    ?_ hm
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [amplitudeOffZero, latticeModeSize_zero]
  · simp [amplitudeOffZero, hk]

theorem InW_X1_offZero (u : WeightedLatticeBanach)
    (hp : InW latticeModeSize (weightedAmplitude u)) :
    InW latticeModeSize (amplitudeOffZero u) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (latticeModeSize_nonneg k) (abs_nonneg _)) ?_ hp
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [amplitudeOffZero, latticeModeSize_zero]
  · simp [amplitudeOffZero, hk]

theorem amplitudeOffZero_meanZero (u : WeightedLatticeBanach) :
    ∀ k, latticeModeSize k = 0 → amplitudeOffZero u k = 0 := by
  intro k hk
  have hk0 : k = 0 := (latticeModeSize_eq_zero_iff k).1 hk
  simp [amplitudeOffZero, hk0]

theorem normX0_split (u : WeightedLatticeBanach) :
    normX0 (weightedAmplitude u) =
      weightedAmplitude u 0 + normX0 (amplitudeOffZero u) := by
  set f := weightedAmplitude u
  set f' := amplitudeOffZero u
  have hs0 : Summable fun k : LatticeMode => if k = 0 then |f 0| else (0 : ℝ) :=
    summable_of_ne_finset_zero (s := ({0} : Finset LatticeMode))
      (fun k hk => by simp at hk; simp [hk])
  have hs' := summable_amplitudeOffZero u
  have hpt : ∀ k, |f k| = (if k = 0 then |f 0| else 0) + |f' k| := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [f', amplitudeOffZero]
    · simp [f, f', amplitudeOffZero, hk]
  have hsum :
      (∑' k, |f k|) =
        (∑' k : LatticeMode, (if k = 0 then |f 0| else (0:ℝ))) + ∑' k, |f' k| := by
    rw [← Summable.tsum_add hs0 hs']
    exact tsum_congr hpt
  have hsingle :
      (∑' k : LatticeMode, (if k = 0 then |f 0| else (0:ℝ))) = |f 0| := by
    rw [tsum_eq_single (0 : LatticeMode) (fun k hk => by simp [hk])]
    simp
  have ha : |f 0| = f 0 := abs_of_nonneg (weightedAmplitude_nonneg u 0)
  simp [normX0, hsum, ha, f, f']

theorem normX1_offZero (u : WeightedLatticeBanach) :
    normX1 latticeModeSize (weightedAmplitude u) =
      normX1 latticeModeSize (amplitudeOffZero u) := by
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [amplitudeOffZero, latticeModeSize_zero]
  · simp [amplitudeOffZero, hk]

theorem normXm1_offZero (u : WeightedLatticeBanach) :
    normXm1 latticeModeSize (weightedAmplitude u) =
      normXm1 latticeModeSize (amplitudeOffZero u) := by
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [amplitudeOffZero, latticeModeSize_zero]
  · simp [amplitudeOffZero, hk]

/-- **CriticalMild norm controlled by the mixed coercive quantity.**
Unconditional: both `𝒳¹` and `𝒳^{-1}` membership of the amplitude family
follow automatically from `u : WeightedLatticeBanach` via
`InW_latticeModeSize` / `InW_inv_latticeModeSize`, so no side hypothesis on
`u` is needed beyond viscosity positivity. -/
theorem norm_weightedLattice_le_of_mixed {ν : ℝ} (hν : 0 < ν)
    (u : WeightedLatticeBanach) :
    ‖u‖ ≤ coerciveConstant ν * mixedCriticalQty ν u := by
  have hm := InW_inv_latticeModeSize u
  have hp := InW_latticeModeSize u
  set f := weightedAmplitude u
  set f' := amplitudeOffZero u
  have hσ : ∀ k, 0 ≤ latticeModeSize k := latticeModeSize_nonneg
  have hOff :=
    normX0_add_normX1_le_mixed (ν := ν) (σ := latticeModeSize) (f := f')
      hν hσ (amplitudeOffZero_meanZero u) (summable_amplitudeOffZero u)
      (InW_Xm1_offZero u hm) (InW_X1_offZero u hp)
  have hnorm := norm_eq_normX0_add_normX1 u
  have hX0 := normX0_split u
  have hX1 := normX1_offZero u
  have hXm1 := normXm1_offZero u
  have hC1 := one_le_coerciveConstant ν
  have hCf := coerciveFactor_le_coerciveConstant ν
  have hfnn : 0 ≤ f 0 := weightedAmplitude_nonneg u 0
  have hQnn : 0 ≤
      normXm1 latticeModeSize f' + ν * normX1 latticeModeSize f' :=
    add_nonneg (normXm1_nonneg hσ f')
      (mul_nonneg hν.le (normX1_nonneg hσ f'))
  have hmix : mixedCriticalQty ν u =
      f 0 + normXm1 latticeModeSize f' + ν * normX1 latticeModeSize f' := by
    unfold mixedCriticalQty
    rw [hXm1, hX1]
  calc ‖u‖
      = normX0 f + normX1 latticeModeSize f := hnorm
    _ = f 0 + (normX0 f' + normX1 latticeModeSize f') := by
        rw [hX0, hX1]; ring
    _ ≤ f 0 + coerciveFactor ν *
          (normXm1 latticeModeSize f' + ν * normX1 latticeModeSize f') := by
        linarith [hOff]
    _ ≤ coerciveConstant ν * f 0 +
          coerciveConstant ν *
            (normXm1 latticeModeSize f' + ν * normX1 latticeModeSize f') := by
        have h1 : f 0 ≤ coerciveConstant ν * f 0 := by
          nlinarith [hC1, hfnn]
        have h2 :
            coerciveFactor ν *
                (normXm1 latticeModeSize f' + ν * normX1 latticeModeSize f') ≤
              coerciveConstant ν *
                (normXm1 latticeModeSize f' + ν * normX1 latticeModeSize f') :=
          mul_le_mul_of_nonneg_right hCf hQnn
        linarith
    _ = coerciveConstant ν * mixedCriticalQty ν u := by
        rw [hmix]; ring

theorem norm_weightedLattice_le_coerciveControlFunctional {ν : ℝ} (hν : 0 < ν)
    (u : WeightedLatticeBanach) :
    ‖u‖ ≤ coerciveControlFunctional ν u := by
  unfold coerciveControlFunctional
  exact norm_weightedLattice_le_of_mixed hν u

/-- Every finite original-data mild chart has terminal mixed critical quantity
at most `K`.  This is the scientific hypothesis replacing the disproved
fixed-radius recurrence.  The `𝒳¹`/`𝒳^{-1}` membership side conditions from
earlier drafts are dropped: they hold unconditionally for every
`WeightedLatticeBanach` element (`InW_latticeModeSize`,
`InW_inv_latticeModeSize`), so this is the sharp remaining hypothesis. -/
def CriticalMildMixedTerminalBound (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (K : ℝ) : Prop :=
  ∀ {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R),
    (∀ τ : Set.Icc (0 : ℝ) T,
      u.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) →
    mixedCriticalQty ν (u.1 ⟨T, ⟨hT, le_rfl⟩⟩) ≤ K

theorem coerciveControlFunctional_le_of_mixedTerminalBound
    {ν : ℝ} (hν : 0 < ν) (a : WeightedLatticeBanach) (K : ℝ)
    (hmixed : CriticalMildMixedTerminalBound ν hν a K)
    {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R)
    (hmild : ∀ τ : Set.Icc (0 : ℝ) T,
      u.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) :
    coerciveControlFunctional ν (u.1 ⟨T, ⟨hT, le_rfl⟩⟩) ≤ coerciveConstant ν * K := by
  unfold coerciveControlFunctional
  exact mul_le_mul_of_nonneg_left (hmixed hT u hmild) (coerciveConstant_pos hν).le

/-- **Construction of the terminal CriticalMild bound from mixed control.**

Under `CriticalMildMixedTerminalBound`, the coercive estimate yields
`CriticalMildTerminalNormBound` at radius `C(ν)·K`. -/
theorem criticalMildTerminalNormBound_of_mixed
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (K : ℝ)
    (_hK : 0 ≤ K)
    (hmixed : CriticalMildMixedTerminalBound ν hν a K) :
    CriticalMildTerminalNormBound ν hν a (coerciveConstant ν * K) := by
  intro T R hT u hmild
  have hqty := hmixed hT u hmild
  have hbound := norm_weightedLattice_le_of_mixed hν (u.1 ⟨T, ⟨hT, le_rfl⟩⟩)
  exact hbound.trans
    (mul_le_mul_of_nonneg_left hqty (coerciveConstant_pos hν).le)

/-- A mixed terminal control closes the bounded-chain continuity consumer once
the initial datum lies in its induced coercive radius. -/
theorem continuous_bounded_global_mild_on_nonneg_of_mixedTerminalBound
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (K : ℝ)
    (hK : 0 ≤ K) (ha : ‖a‖ ≤ coerciveConstant ν * K)
    (hmixed : CriticalMildMixedTerminalBound ν hν a K) :
    Continuous (fun t : Set.Ici (0 : ℝ) =>
      (boundedCoherentChain ν hν a (coerciveConstant ν * K)
        (mul_nonneg (coerciveConstant_pos hν).le hK) ha
        (criticalMildTerminalNormBound_of_mixed ν hν a K hK hmixed)).totalExtension t.1) :=
  continuous_bounded_global_mild_on_nonneg_of_terminalNormBound
    ν hν a (coerciveConstant ν * K)
    (mul_nonneg (coerciveConstant_pos hν).le hK) ha
    (criticalMildTerminalNormBound_of_mixed ν hν a K hK hmixed)

end Navier.Analysis.LeiLinCoerciveTerminal

#print axioms Navier.Analysis.LeiLinCoerciveTerminal.norm_eq_normX0_add_normX1
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.one_le_latticeModeSize_of_ne_zero
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.InW_latticeModeSize
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.InW_inv_latticeModeSize
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.normX1_weightedAmplitude_le_add_norm_sub
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.normX1_shifted_trajectory_le_add_sqrt
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.normX1_shifted_trajectory_le_add_sqrt_of_halfGeneratorMoment
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.terminal_X1_le_of_trailingMass_and_halfGeneratorMoment
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.normX0_add_normX1_le_mixed
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.norm_weightedLattice_le_of_mixed
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.criticalMildTerminalNormBound_of_mixed
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.continuous_bounded_global_mild_on_nonneg_of_mixedTerminalBound
