import Navier.Analysis.LeiLinBilinear
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
open Navier.Analysis.CriticalMildBoundedContinuation
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinBilinear

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

/-- **CriticalMild norm controlled by the mixed coercive quantity.** -/
theorem norm_weightedLattice_le_of_mixed {ν : ℝ} (hν : 0 < ν)
    (u : WeightedLatticeBanach)
    (hm : InW (fun k => (latticeModeSize k)⁻¹) (weightedAmplitude u))
    (hp : InW latticeModeSize (weightedAmplitude u)) :
    ‖u‖ ≤ coerciveConstant ν * mixedCriticalQty ν u := by
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

/-- Every finite original-data mild chart has terminal mixed critical quantity
at most `K`.  This is the scientific hypothesis replacing the disproved
fixed-radius recurrence. -/
def CriticalMildMixedTerminalBound (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (K : ℝ) : Prop :=
  ∀ {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R),
    (∀ τ : Set.Icc (0 : ℝ) T,
      u.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) →
    (InW (fun k => (latticeModeSize k)⁻¹) (weightedAmplitude (u.1 ⟨T, ⟨hT, le_rfl⟩⟩)) ∧
      InW latticeModeSize (weightedAmplitude (u.1 ⟨T, ⟨hT, le_rfl⟩⟩)) ∧
      mixedCriticalQty ν (u.1 ⟨T, ⟨hT, le_rfl⟩⟩) ≤ K)

/-- **Construction of the terminal CriticalMild bound from mixed control.**

Under `CriticalMildMixedTerminalBound`, the coercive estimate yields
`CriticalMildTerminalNormBound` at radius `C(ν)·K`. -/
theorem criticalMildTerminalNormBound_of_mixed
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (K : ℝ)
    (_hK : 0 ≤ K)
    (hmixed : CriticalMildMixedTerminalBound ν hν a K) :
    CriticalMildTerminalNormBound ν hν a (coerciveConstant ν * K) := by
  intro T R hT u hmild
  obtain ⟨hm, hp, hqty⟩ := hmixed hT u hmild
  have hbound :=
    norm_weightedLattice_le_of_mixed hν (u.1 ⟨T, ⟨hT, le_rfl⟩⟩) hm hp
  exact hbound.trans
    (mul_le_mul_of_nonneg_left hqty (coerciveConstant_pos hν).le)

end Navier.Analysis.LeiLinCoerciveTerminal

#print axioms Navier.Analysis.LeiLinCoerciveTerminal.norm_eq_normX0_add_normX1
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.normX0_add_normX1_le_mixed
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.norm_weightedLattice_le_of_mixed
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.criticalMildTerminalNormBound_of_mixed
