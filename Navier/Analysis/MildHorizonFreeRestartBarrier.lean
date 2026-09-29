import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.Norm
import Navier.Analysis.ContinuousLeiLinSpace

/-!
# The mild-box barrier: X⁻¹ ∩ X¹ membership never bounds the X² restart leg

**Mission (W31-N02).**  Produce `HorizonIndependentRestart N`
(`Navier.Analysis.RestartPaste`) with `h = h(ν, M)` horizon-independent on the
whole-space mild-solution carrier, or a carrier-bound stagnation report naming
the blocking field.  This module delivers the measured half of that report as
checked mathematics.

**Measured carrier state.**  The continuous Lei--Lin mild fixed point
`ContinuousLeiLinMildFixedPoint.actual_existsUnique_mildFixedPoint` is ALREADY
horizon-free: its horizon `T` enters only through `0 ≤ T`, and the admissible
norm contraction is uniform in `T`.  The requested numeric-budget transport of
a restricted horizon recurrence therefore degenerates — there is no horizon
dependence left to remove on the mild side.  What blocks the plain-form
producer on the mild carrier is the *record*, not the horizon:
`Navier.Analysis.WholeSpaceRestartX2BudgetWiring` names the `SourceX2Budget`
legs as not supplied by the linked-box record
`ContinuousLeiLinActualSlots.linkedAdmissibleBoxSet`, whose two slots
(`Xm1TimeSlot`, `ViscousX1TimeSlot`) control the per-time `X⁻¹` and viscous
`X¹` quantities.  The budget's third leg is

```lean
∀ s j, Integrable (fun η : ES => ‖η‖ ^ 2 * ‖v s η j‖)
```

— a weight-degree-2 obligation, while the record carries no slot of
weight degree ≥ 2.

**What this module proves.**  A checked separation upgrading that comment:
the radial profile `mildBarrierProfile` (supported off the unit ball, tail
`‖ξ‖⁻⁵` in dimension 3) has finite `X⁻¹` and finite `X¹` quantities
(`integrable_barrier_Xm1`, `integrable_barrier_X1`), while its `X²` weight is
not integrable:

`∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2 * ‖mildBarrierProfile ξ‖) ∂volume = ⊤`

(`lintegral_barrier_X2_eq_top`, `not_integrable_barrier_X2`).  The
time-constant trajectory corollary `constant_trajectory_fails_hv2` kills the
`SourceX2Budget` third leg for this trajectory, and
`exists_slots_below_radii_hv2_fails` shows the barrier for ARBITRARY radii:
below any `B1, B2 > 0` there is a datum whose per-coordinate `X⁻¹` and `X¹`
integrals are bounded by them while `hv2` fails.  No choice of the record's
two radii determines the `X²` leg: the blocking field is the weight degree of
`linkedAdmissibleBoxSet`, not the horizon.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ENNReal Topology Filter
open scoped NNReal BigOperators

namespace Navier.Analysis.MildHorizonFreeRestartBarrier

open Navier.Analysis.ContinuousLeiLinSpace

/-! ## The barrier profile -/

/-- The region where the barrier profile lives: outside the closed unit ball. -/
def supportSet : Set ES :=
  {ξ : ES | (1 : ℝ) < ‖ξ‖}

theorem measurableSet_supportSet : MeasurableSet supportSet :=
  measurableSet_lt measurable_const continuous_norm.measurable

/-- The scalar tail profile: `‖ξ‖⁻⁵` off the unit ball, `0` inside. -/
def mildBarrierScalar (ξ : ES) : ℝ :=
  supportSet.indicator (fun ξ => 1 / ‖ξ‖ ^ (5 : ℕ)) ξ

@[simp]
theorem mildBarrierScalar_apply (ξ : ES) :
    mildBarrierScalar ξ = if (1 : ℝ) < ‖ξ‖ then 1 / ‖ξ‖ ^ (5 : ℕ) else 0 := by
  simp [mildBarrierScalar, supportSet, Set.indicator_apply]

private theorem mildBarrierScalar_nonneg (ξ : ES) : 0 ≤ mildBarrierScalar ξ := by
  rw [mildBarrierScalar_apply]
  split <;> positivity

theorem measurable_mildBarrierScalar : Measurable mildBarrierScalar := by
  have h : Measurable fun ξ : ES => 1 / ‖ξ‖ ^ (5 : ℕ) :=
    measurable_const.div ((continuous_norm.pow 5).measurable)
  exact h.indicator measurableSet_supportSet

/-- The ℂ-valued profile consumed by the mild carrier. -/
def mildBarrierProfile (ξ : ES) : ℂ :=
  (mildBarrierScalar ξ : ℂ)

theorem norm_mildBarrierProfile (ξ : ES) :
    ‖mildBarrierProfile ξ‖ = mildBarrierScalar ξ := by
  show ‖(mildBarrierScalar ξ : ℂ)‖ = mildBarrierScalar ξ
  exact Complex.norm_of_nonneg (mildBarrierScalar_nonneg ξ)

/-- The time-constant vector trajectory built from the profile: every Fourier
coordinate equals the profile. -/
def mildBarrierVec (ξ : ES) : ComplexSpace :=
  fun _ => mildBarrierProfile ξ

/-! ## Dyadic shells covering the region `1 ≤ ‖ξ‖` -/

/-- The outward dyadic shell `2^k ≤ ‖ξ‖ < 2^(k+1)`. -/
private def bShell (k : ℕ) : Set ES :=
  Metric.ball 0 ((2 : ℝ) ^ (k + 1)) ∩ {ξ : ES | (2 : ℝ) ^ k ≤ ‖ξ‖}

theorem measurableSet_bShell (k : ℕ) : MeasurableSet (bShell k) :=
  Metric.isOpen_ball.measurableSet.inter
    (measurableSet_le measurable_const continuous_norm.measurable)

private theorem bShell_norm_lt {k : ℕ} {x : ES} (hx : x ∈ bShell k) :
    ‖x‖ < (2 : ℝ) ^ (k + 1) := by
  have h1 := hx.1
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h1
  exact h1

private theorem bShell_norm_le {k : ℕ} {x : ES} (hx : x ∈ bShell k) :
    (2 : ℝ) ^ k ≤ ‖x‖ := hx.2

theorem bShell_disjoint : Pairwise (Function.onFun Disjoint bShell) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun z hzi hzj => ?_
  rcases lt_or_gt_of_ne hij with h | h
  · have hpow : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [bShell_norm_lt hzi, bShell_norm_le hzj]
  · have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [bShell_norm_lt hzj, bShell_norm_le hzi]

theorem iUnion_bShell : (⋃ k, bShell k) = {ξ : ES | (1 : ℝ) ≤ ‖ξ‖} := by
  classical
  apply Set.Subset.antisymm
  · rw [iUnion_subset_iff]
    intro k x hx
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le k)
      simpa using this
    exact le_trans h1 (bShell_norm_le hx)
  · intro x hx
    have hle1 : (1 : ℝ) ≤ ‖x‖ := hx
    obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos ‖x‖ one_pos
    rw [show (1 : ℝ) + 1 = 2 from one_add_one_eq_two] at hm
    have hex : ∃ n : ℕ, ‖x‖ < (2 : ℝ) ^ n := ⟨m, hm⟩
    have hspec : ‖x‖ < (2 : ℝ) ^ Nat.find hex := Nat.find_spec hex
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · rw [h, pow_zero] at hspec
        linarith [hle1]
      · exact h
    let k := Nat.find hex - 1
    have hklt : k < Nat.find hex := by omega
    have hnot : ¬ (‖x‖ < (2 : ℝ) ^ k) := Nat.find_min hex hklt
    have hle : (2 : ℝ) ^ k ≤ ‖x‖ := by linarith
    have hup : ‖x‖ < (2 : ℝ) ^ (k + 1) := by
      have hkeq : k + 1 = Nat.find hex := by omega
      rw [hkeq]
      exact hspec
    refine mem_iUnion.mpr ⟨k, ?_⟩
    simpa [bShell, Metric.mem_ball, dist_eq_norm, sub_zero] using ⟨hup, hle⟩

/-! ## Pointwise shell bounds for the `X⁻¹` and `X¹` weights -/

private theorem barrier_Xm1_on_shell {k : ℕ} {x : ES} (hx : x ∈ bShell k) :
    ‖x‖⁻¹ * mildBarrierScalar x ≤ (1 : ℝ) / (2 : ℝ) ^ (6 * k) := by
  rw [mildBarrierScalar_apply]
  rcases lt_or_ge (1 : ℝ) ‖x‖ with hlt | hge
  · rw [if_pos hlt]
    have hnorm : 0 < ‖(x : ES)‖ := lt_trans (by norm_num : (0 : ℝ) < 1) hlt
    have hstep : ‖x‖⁻¹ * (1 / ‖x‖ ^ (5 : ℕ)) = 1 / ‖x‖ ^ (6 : ℕ) := by
      field_simp [pow_ne_zero 5 (ne_of_gt hnorm), pow_ne_zero 6 (ne_of_gt hnorm)]
    have hle : ((2 : ℝ) ^ k) ^ (6 : ℕ) ≤ ‖x‖ ^ (6 : ℕ) :=
      pow_le_pow_left₀ (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) k))
        (bShell_norm_le hx) 6
    calc ‖x‖⁻¹ * (1 / ‖x‖ ^ (5 : ℕ)) = 1 / ‖x‖ ^ (6 : ℕ) := hstep
      _ ≤ 1 / ((2 : ℝ) ^ k) ^ 6 :=
        one_div_le_one_div_of_le
          (pow_pos (pow_pos (by norm_num : (0 : ℝ) < 2) k) 6) hle
      _ = 1 / (2 : ℝ) ^ (6 * k) := by rw [← pow_mul, Nat.mul_comm k 6]
  · rw [if_neg (fun h => lt_irrefl (1 : ℝ) (lt_of_lt_of_le h hge))]
    simp

private theorem barrier_X1_on_shell {k : ℕ} {x : ES} (hx : x ∈ bShell k) :
    ‖x‖ * mildBarrierScalar x ≤ (1 : ℝ) / (2 : ℝ) ^ (4 * k) := by
  rw [mildBarrierScalar_apply]
  rcases lt_or_ge (1 : ℝ) ‖x‖ with hlt | hge
  · rw [if_pos hlt]
    have hnorm : 0 < ‖(x : ES)‖ := lt_trans (by norm_num : (0 : ℝ) < 1) hlt
    have hstep : ‖x‖ * (1 / ‖x‖ ^ (5 : ℕ)) = 1 / ‖x‖ ^ (4 : ℕ) := by
      field_simp [pow_ne_zero 5 (ne_of_gt hnorm), pow_ne_zero 4 (ne_of_gt hnorm)]
    have hle : ((2 : ℝ) ^ k) ^ (4 : ℕ) ≤ ‖x‖ ^ (4 : ℕ) :=
      pow_le_pow_left₀ (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) k))
        (bShell_norm_le hx) 4
    calc ‖x‖ * (1 / ‖x‖ ^ (5 : ℕ)) = 1 / ‖x‖ ^ (4 : ℕ) := hstep
      _ ≤ 1 / ((2 : ℝ) ^ k) ^ 4 :=
        one_div_le_one_div_of_le
          (pow_pos (pow_pos (by norm_num : (0 : ℝ) < 2) k) 4) hle
      _ = 1 / (2 : ℝ) ^ (4 * k) := by rw [← pow_mul, Nat.mul_comm k 4]
  · rw [if_neg (fun h => lt_irrefl (1 : ℝ) (lt_of_lt_of_le h hge))]
    simp

/-! ## The unit-ball volume constant -/

private def V3 : ℝ≥0∞ := volume (Metric.ball (0 : ES) 1)

private theorem V3_eq :
    V3 = ENNReal.ofReal (Real.sqrt Real.pi ^ (3 : ℕ) /
      Real.Gamma ((((3 : ℕ) : ℝ) / 2) + 1)) := by
  show volume (Metric.ball (0 : ES) 1) = _
  rw [EuclideanSpace.volume_ball (Fin 3) (0 : ES) 1]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]

private theorem V3_pos : 0 < V3 := by
  rw [V3_eq, ENNReal.ofReal_pos]
  have harg : (((3 : ℕ) : ℝ) / 2) + 1 = (5 : ℝ) / 2 := by norm_num
  have hg : Real.Gamma ((5 : ℝ) / 2) = 3 * Real.sqrt Real.pi / 4 := by
    have := Real.Gamma_nat_add_half 2
    norm_num at this ⊢
    exact this
  rw [harg, hg]
  positivity

private theorem V3_lt_top : V3 < ⊤ := by
  rw [V3_eq]
  exact ENNReal.ofReal_lt_top

private theorem volume_ball_eq (x : ES) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (r ^ (3 : ℕ)) * V3 := by
  calc volume (Metric.ball x r)
      = ENNReal.ofReal r ^ Fintype.card (Fin 3) *
          ENNReal.ofReal (Real.sqrt Real.pi ^ Fintype.card (Fin 3) /
            Real.Gamma ((Fintype.card (Fin 3) : ℝ) / 2 + 1)) :=
        EuclideanSpace.volume_ball (Fin 3) x r
    _ = ENNReal.ofReal (r ^ (3 : ℕ)) *
          ENNReal.ofReal (Real.sqrt Real.pi ^ Fintype.card (Fin 3) /
            Real.Gamma ((Fintype.card (Fin 3) : ℝ) / 2 + 1)) := by
        simp only [Fintype.card_fin]
        rw [← ENNReal.ofReal_pow hr]
    _ = ENNReal.ofReal (r ^ (3 : ℕ)) * V3 := by
        simp only [Fintype.card_fin, V3_eq]

private theorem volume_bShell_le (k : ℕ) :
    volume (bShell k) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 * k + 3)) * V3 := by
  calc volume (bShell k) ≤ volume (Metric.ball (0 : ES) ((2 : ℝ) ^ (k + 1))) :=
        measure_mono (fun z hz => hz.1)
    _ = ENNReal.ofReal (((2 : ℝ) ^ (k + 1)) ^ (3 : ℕ)) * V3 :=
        volume_ball_eq 0 (by positivity)
    _ = ENNReal.ofReal ((2 : ℝ) ^ (3 * k + 3)) * V3 := by
        congr 1
        rw [← pow_mul]
        congr 1
        ring

/-! ## Shell algebra identities -/

private theorem barrier_Xm1_shell_alg (k : ℕ) :
    (1 / (2 : ℝ) ^ (6 * k)) * (2 : ℝ) ^ (3 * k + 3) = (8 : ℝ) * ((1 / 8 : ℝ) ^ k) := by
  have h6 : (2 : ℝ) ^ (6 * k) = (2 : ℝ) ^ (3 * k) * (2 : ℝ) ^ (3 * k) := by
    rw [show (6 * k : ℕ) = 3 * k + 3 * k from by ring, pow_add]
  have h3 : (2 : ℝ) ^ (3 * k + 3) = (2 : ℝ) ^ (3 * k) * 8 := by
    rw [pow_add]
    norm_num
  have hdiv : ((1 / 8 : ℝ) ^ k) = 1 / (8 : ℝ) ^ k := by
    rw [div_pow, one_pow]
  have h8 : (8 : ℝ) ^ k = (2 : ℝ) ^ (3 * k) := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, pow_mul]
  rw [h6, h3, hdiv, h8]
  field_simp [show ((2 : ℝ) ^ (3 * k)) ≠ 0 by positivity]

private theorem barrier_X1_shell_alg (k : ℕ) :
    (1 / (2 : ℝ) ^ (4 * k)) * (2 : ℝ) ^ (3 * k + 3) = (8 : ℝ) * ((1 / 2 : ℝ) ^ k) := by
  have h4 : (2 : ℝ) ^ (4 * k) = ((2 : ℝ) ^ k) ^ (4 : ℕ) := by
    rw [show (4 * k : ℕ) = k * 4 from by ring, ← pow_mul]
  have h3 : (2 : ℝ) ^ (3 * k + 3) = ((2 : ℝ) ^ k) ^ (3 : ℕ) * 8 := by
    rw [pow_add, show (3 * k : ℕ) = k * 3 from by ring, ← pow_mul]
    norm_num
  have hdiv : ((1 / 2 : ℝ) ^ k) = 1 / (2 : ℝ) ^ k := by
    rw [div_pow, one_pow]
  rw [h4, h3, hdiv]
  field_simp [show ((2 : ℝ) ^ k) ≠ 0 by positivity]

/-! ## `X⁻¹` and `X¹` finiteness -/

private theorem lintegral_barrier_Xm1_le :
    (∫⁻ ξ : ES, ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume) ≤
      ENNReal.ofReal (64 / 7) * V3 := by
  have hmeas : MeasurableSet (⋃ k, bShell k) :=
    MeasurableSet.iUnion (fun k => measurableSet_bShell k)
  have hsuppC : ∀ ξ : ES, ξ ∉ ⋃ k, bShell k →
      ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) = 0 := by
    intro ξ hξ
    have hnorm : ‖ξ‖ < 1 :=
      not_le.mp (by simpa [iUnion_bShell, Set.mem_setOf_eq] using hξ)
    rw [mildBarrierScalar_apply,
      if_neg (fun h => lt_irrefl (1 : ℝ) (lt_of_lt_of_le h (le_of_lt hnorm)))]
    simp
  calc (∫⁻ ξ : ES, ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume)
      = ∫⁻ ξ in univ, ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume := by
        rw [← setLIntegral_univ]
    _ = ∫⁻ ξ in (⋃ k, bShell k) ∪ (⋃ k, bShell k)ᶜ,
          ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume := by
        rw [Set.union_compl_self]
    _ = (∫⁻ ξ in ⋃ k, bShell k, ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume) +
          ∫⁻ ξ in (⋃ k, bShell k)ᶜ, ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume :=
        lintegral_union hmeas.compl disjoint_compl_right
    _ = (∫⁻ ξ in ⋃ k, bShell k, ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume) + 0 := by
        rw [setLIntegral_congr_fun hmeas.compl hsuppC]
        simp
    _ = ∫⁻ ξ in ⋃ k, bShell k, ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume :=
        add_zero _
    _ = ∑' k, ∫⁻ ξ in bShell k, ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume :=
        lintegral_iUnion (fun k => measurableSet_bShell k) bShell_disjoint _
    _ ≤ ∑' k, (ENNReal.ofReal (1 / (2 : ℝ) ^ (6 * k)) *
          ENNReal.ofReal ((2 : ℝ) ^ (3 * k + 3)) * V3) := by
        apply ENNReal.tsum_le_tsum
        intro k
        calc ∫⁻ ξ in bShell k, ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume
            ≤ ∫⁻ _ in bShell k, ENNReal.ofReal (1 / (2 : ℝ) ^ (6 * k)) ∂volume :=
              setLIntegral_mono measurable_const fun _z hz =>
                ENNReal.ofReal_le_ofReal (barrier_Xm1_on_shell hz)
          _ = ENNReal.ofReal (1 / (2 : ℝ) ^ (6 * k)) * volume (bShell k) :=
              setLIntegral_const _ _
          _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ (6 * k)) *
                (ENNReal.ofReal ((2 : ℝ) ^ (3 * k + 3)) * V3) :=
              mul_le_mul_of_nonneg_left (volume_bShell_le k) zero_le
          _ = ENNReal.ofReal (1 / (2 : ℝ) ^ (6 * k)) *
                ENNReal.ofReal ((2 : ℝ) ^ (3 * k + 3)) * V3 := (mul_assoc _ _ _).symm
    _ = (∑' k : ℕ, ENNReal.ofReal ((8 : ℝ) * ((1 / 8 : ℝ) ^ k))) * V3 := by
        rw [ENNReal.tsum_mul_right]
        have hpoint : (fun k : ℕ => ENNReal.ofReal (1 / (2 : ℝ) ^ (6 * k)) *
            ENNReal.ofReal ((2 : ℝ) ^ (3 * k + 3))) =
            (fun k : ℕ => ENNReal.ofReal ((8 : ℝ) * ((1 / 8 : ℝ) ^ k))) := by
          funext k
          rw [← ENNReal.ofReal_mul (by positivity), barrier_Xm1_shell_alg k]
        rw [hpoint]
    _ ≤ ENNReal.ofReal (64 / 7) * V3 := by
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        have hsumm : Summable fun k : ℕ => (8 : ℝ) * ((1 / 8 : ℝ) ^ k) :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm]
        rw [tsum_mul_left]
        rw [(hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 8 : ℝ))
          (by norm_num : ((1 / 8 : ℝ) < 1))).tsum_eq]
        norm_num

private theorem lintegral_barrier_X1_le :
    (∫⁻ ξ : ES, ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume) ≤
      ENNReal.ofReal (16 : ℝ) * V3 := by
  have hmeas : MeasurableSet (⋃ k, bShell k) :=
    MeasurableSet.iUnion (fun k => measurableSet_bShell k)
  have hsuppC : ∀ ξ : ES, ξ ∉ ⋃ k, bShell k →
      ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) = 0 := by
    intro ξ hξ
    have hnorm : ‖ξ‖ < 1 :=
      not_le.mp (by simpa [iUnion_bShell, Set.mem_setOf_eq] using hξ)
    rw [mildBarrierScalar_apply,
      if_neg (fun h => lt_irrefl (1 : ℝ) (lt_of_lt_of_le h (le_of_lt hnorm)))]
    simp
  calc (∫⁻ ξ : ES, ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume)
      = ∫⁻ ξ in univ, ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume := by
        rw [← setLIntegral_univ]
    _ = ∫⁻ ξ in (⋃ k, bShell k) ∪ (⋃ k, bShell k)ᶜ,
          ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume := by
        rw [Set.union_compl_self]
    _ = (∫⁻ ξ in ⋃ k, bShell k, ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume) +
          ∫⁻ ξ in (⋃ k, bShell k)ᶜ, ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume :=
        lintegral_union hmeas.compl disjoint_compl_right
    _ = (∫⁻ ξ in ⋃ k, bShell k, ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume) + 0 := by
        rw [setLIntegral_congr_fun hmeas.compl hsuppC]
        simp
    _ = ∫⁻ ξ in ⋃ k, bShell k, ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume :=
        add_zero _
    _ = ∑' k, ∫⁻ ξ in bShell k, ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume :=
        lintegral_iUnion (fun k => measurableSet_bShell k) bShell_disjoint _
    _ ≤ ∑' k, (ENNReal.ofReal (1 / (2 : ℝ) ^ (4 * k)) *
          ENNReal.ofReal ((2 : ℝ) ^ (3 * k + 3)) * V3) := by
        apply ENNReal.tsum_le_tsum
        intro k
        calc ∫⁻ ξ in bShell k, ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume
            ≤ ∫⁻ _ in bShell k, ENNReal.ofReal (1 / (2 : ℝ) ^ (4 * k)) ∂volume :=
              setLIntegral_mono measurable_const fun _z hz =>
                ENNReal.ofReal_le_ofReal (barrier_X1_on_shell hz)
          _ = ENNReal.ofReal (1 / (2 : ℝ) ^ (4 * k)) * volume (bShell k) :=
              setLIntegral_const _ _
          _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ (4 * k)) *
                (ENNReal.ofReal ((2 : ℝ) ^ (3 * k + 3)) * V3) :=
              mul_le_mul_of_nonneg_left (volume_bShell_le k) zero_le
          _ = ENNReal.ofReal (1 / (2 : ℝ) ^ (4 * k)) *
                ENNReal.ofReal ((2 : ℝ) ^ (3 * k + 3)) * V3 := (mul_assoc _ _ _).symm
    _ = (∑' k : ℕ, ENNReal.ofReal ((8 : ℝ) * ((1 / 2 : ℝ) ^ k))) * V3 := by
        rw [ENNReal.tsum_mul_right]
        have hpoint : (fun k : ℕ => ENNReal.ofReal (1 / (2 : ℝ) ^ (4 * k)) *
            ENNReal.ofReal ((2 : ℝ) ^ (3 * k + 3))) =
            (fun k : ℕ => ENNReal.ofReal ((8 : ℝ) * ((1 / 2 : ℝ) ^ k))) := by
          funext k
          rw [← ENNReal.ofReal_mul (by positivity), barrier_X1_shell_alg k]
        rw [hpoint]
    _ ≤ ENNReal.ofReal (16 : ℝ) * V3 := by
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        have hsumm : Summable fun k : ℕ => (8 : ℝ) * ((1 / 2 : ℝ) ^ k) :=
          summable_geometric_two.mul_left _
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm]
        rw [tsum_mul_left]
        rw [tsum_geometric_two]
        norm_num

theorem lintegral_barrier_Xm1_lt_top :
    (∫⁻ ξ : ES, ENNReal.ofReal (‖ξ‖⁻¹ * mildBarrierScalar ξ) ∂volume) < ⊤ :=
  lt_of_le_of_lt lintegral_barrier_Xm1_le
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top V3_lt_top)

theorem lintegral_barrier_X1_lt_top :
    (∫⁻ ξ : ES, ENNReal.ofReal (‖ξ‖ * mildBarrierScalar ξ) ∂volume) < ⊤ :=
  lt_of_le_of_lt lintegral_barrier_X1_le
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top V3_lt_top)

/-- The barrier profile has finite `X⁻¹` quantity. -/
theorem integrable_barrier_Xm1 :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖mildBarrierProfile ξ‖) volume := by
  have hfi : HasFiniteIntegral (fun ξ : ES => ‖ξ‖⁻¹ * mildBarrierScalar ξ) volume := by
    rw [hasFiniteIntegral_iff_ofReal
      (ae_of_all _ (fun ξ => mul_nonneg (inv_nonneg.2 (norm_nonneg _))
        (mildBarrierScalar_nonneg ξ)))]
    exact lintegral_barrier_Xm1_lt_top
  have hscalar : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * mildBarrierScalar ξ) volume :=
    ⟨(continuous_norm.measurable.inv.mul measurable_mildBarrierScalar).aestronglyMeasurable,
      hfi⟩
  convert hscalar using 1 with ξ
  · funext ξ
    simp only [norm_mildBarrierProfile]

/-- The barrier profile has finite `X¹` quantity. -/
theorem integrable_barrier_X1 :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖mildBarrierProfile ξ‖) volume := by
  have hfi : HasFiniteIntegral (fun ξ : ES => ‖ξ‖ * mildBarrierScalar ξ) volume := by
    rw [hasFiniteIntegral_iff_ofReal
      (ae_of_all _ (fun ξ => mul_nonneg (norm_nonneg _)
        (mildBarrierScalar_nonneg ξ)))]
    exact lintegral_barrier_X1_lt_top
  have hscalar : Integrable (fun ξ : ES => ‖ξ‖ * mildBarrierScalar ξ) volume :=
    ⟨(continuous_norm.measurable.mul measurable_mildBarrierScalar).aestronglyMeasurable, hfi⟩
  convert hscalar using 1 with ξ
  · funext ξ
    simp only [norm_mildBarrierProfile]

/-! ## The `X²` leg: divergence -/

private def X2Integrand (ξ : ES) : ℝ≥0∞ :=
  ENNReal.ofReal (‖ξ‖ ^ (2 : ℕ) * mildBarrierScalar ξ)

private theorem X2Integrand_apply (ξ : ES) :
    X2Integrand ξ = ENNReal.ofReal (‖ξ‖ ^ (2 : ℕ) * mildBarrierScalar ξ) := rfl

private theorem measurable_X2Integrand : Measurable X2Integrand := by
  refine ENNReal.measurable_ofReal.comp ?_
  exact ((continuous_norm.pow 2).measurable.mul measurable_mildBarrierScalar)

private def barrierCenter (j : ℕ) : ES :=
  EuclideanSpace.single (0 : Fin 3) ((3 / 2 : ℝ) * (2 : ℝ) ^ j)

private def barrierRadius (j : ℕ) : ℝ := (2 : ℝ) ^ j / 16

private theorem norm_barrierCenter (j : ℕ) :
    ‖barrierCenter j‖ = (3 / 2 : ℝ) * (2 : ℝ) ^ j := by
  show ‖EuclideanSpace.single (0 : Fin 3) ((3 / 2 : ℝ) * (2 : ℝ) ^ j)‖ = _
  rw [EuclideanSpace.norm_single, Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity)

private theorem barrierRadius_pos (j : ℕ) : 0 < barrierRadius j :=
  div_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j) (by norm_num : (0 : ℝ) < 16)

private theorem norm_sub_swap (x y : ES) : ‖x - y‖ = ‖y - x‖ := by
  rw [← norm_neg, neg_sub]

private theorem barrierBall_norm_lower (j : ℕ) {y : ES}
    (hy : y ∈ Metric.ball (barrierCenter j) (barrierRadius j)) :
    (23 / 16 : ℝ) * (2 : ℝ) ^ j < ‖y‖ := by
  have hnorm : ‖y - barrierCenter j‖ < barrierRadius j := hy
  have h1 : ‖barrierCenter j‖ ≤ ‖y‖ + ‖y - barrierCenter j‖ := by
    calc ‖barrierCenter j‖ = ‖y + (barrierCenter j - y)‖ :=
          congrArg (fun z : ES => ‖z‖) (by rw [add_comm, sub_add_cancel])
      _ ≤ ‖y‖ + ‖barrierCenter j - y‖ := norm_add_le _ _
      _ = ‖y‖ + ‖y - barrierCenter j‖ := by rw [norm_sub_swap]
  rw [norm_barrierCenter] at h1
  have h2 : (3 / 2 : ℝ) * (2 : ℝ) ^ j - barrierRadius j =
      (23 / 16 : ℝ) * (2 : ℝ) ^ j := by
    show (3 / 2 : ℝ) * (2 : ℝ) ^ j - (2 : ℝ) ^ j / 16 = (23 / 16 : ℝ) * (2 : ℝ) ^ j
    ring
  linarith

private theorem barrierBall_subset_bShell (j : ℕ) {y : ES}
    (hy : y ∈ Metric.ball (barrierCenter j) (barrierRadius j)) : y ∈ bShell j := by
  have hnorm : ‖y - barrierCenter j‖ < barrierRadius j := hy
  constructor
  · show ‖y - (0 : ES)‖ < (2 : ℝ) ^ (j + 1)
    rw [sub_zero]
    have h1 : ‖y‖ ≤ ‖y - barrierCenter j‖ + ‖barrierCenter j‖ := by
      calc ‖y‖ = ‖(y - barrierCenter j) + barrierCenter j‖ :=
            congrArg (fun z : ES => ‖z‖) (sub_add_cancel y (barrierCenter j)).symm
        _ ≤ ‖y - barrierCenter j‖ + ‖barrierCenter j‖ := norm_add_le _ _
    have h2 : ‖y - barrierCenter j‖ + ‖barrierCenter j‖ <
        barrierRadius j + (3 / 2 : ℝ) * (2 : ℝ) ^ j := by
      linarith [hnorm, norm_barrierCenter j]
    have h3 : barrierRadius j + (3 / 2 : ℝ) * (2 : ℝ) ^ j < (2 : ℝ) ^ (j + 1) := by
      have h31 : barrierRadius j + (3 / 2 : ℝ) * (2 : ℝ) ^ j =
          (25 / 16 : ℝ) * (2 : ℝ) ^ j := by
        show (2 : ℝ) ^ j / 16 + (3 / 2 : ℝ) * (2 : ℝ) ^ j = (25 / 16 : ℝ) * (2 : ℝ) ^ j
        ring
      rw [h31]
      have h32 : (25 / 16 : ℝ) * (2 : ℝ) ^ j < (2 : ℝ) ^ j * 2 := by
        rw [mul_comm]
        exact mul_lt_mul_of_pos_left (by norm_num : (25 / 16 : ℝ) < 2)
          (pow_pos (by norm_num : (0 : ℝ) < 2) j)
      rw [pow_succ]
      exact h32
    exact lt_trans (lt_of_le_of_lt h1 h2) h3
  · have hlow := barrierBall_norm_lower j hy
    have hstep : (2 : ℝ) ^ j ≤ (23 / 16 : ℝ) * (2 : ℝ) ^ j := by
      have hc : (1 : ℝ) ≤ 23 / 16 := by norm_num
      have h := mul_le_mul_of_nonneg_right hc
        (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) j))
      simpa using h
    exact le_of_lt (lt_of_le_of_lt hstep hlow)

private theorem measurableSet_barrierBall (j : ℕ) :
    MeasurableSet (Metric.ball (barrierCenter j) (barrierRadius j)) :=
  Metric.isOpen_ball.measurableSet

private def c0 : ℝ≥0∞ := ENNReal.ofReal (1 / (25 : ℝ) ^ (3 : ℕ)) * V3

private theorem c0_ne_zero : c0 ≠ 0 :=
  mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) (ne_of_gt V3_pos)

private theorem c0_lt_top : c0 ≠ ⊤ :=
  (ENNReal.mul_lt_top ENNReal.ofReal_lt_top V3_lt_top).ne

private theorem barrierBall_integral_ge_c0 (j : ℕ) :
    c0 ≤ ∫⁻ y in Metric.ball (barrierCenter j) (barrierRadius j), X2Integrand y ∂volume := by
  have h_point : ∀ y ∈ Metric.ball (barrierCenter j) (barrierRadius j),
      ENNReal.ofReal (1 / (25 * barrierRadius j) ^ (3 : ℕ)) ≤ X2Integrand y := by
    intro y hy
    have h1lt : (1 : ℝ) < ‖y‖ := by
      have t1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le j)
        simpa using h
      have hlow : (23 / 16 : ℝ) * (2 : ℝ) ^ j < ‖y‖ := barrierBall_norm_lower j hy
      have hstep : (23 / 16 : ℝ) * (1 : ℝ) ≤ (23 / 16 : ℝ) * (2 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left t1 (by norm_num : (0 : ℝ) ≤ 23 / 16)
      nlinarith
    have hnorm : 0 < ‖(y : ES)‖ := by positivity
    have hc : ‖y - barrierCenter j‖ < barrierRadius j := hy
    have hUpper : ‖y‖ < 25 * barrierRadius j := by
      have h1 : ‖y‖ ≤ ‖y - barrierCenter j‖ + ‖barrierCenter j‖ := by
        calc ‖y‖ = ‖(y - barrierCenter j) + barrierCenter j‖ :=
              congrArg (fun z : ES => ‖z‖) (sub_add_cancel y (barrierCenter j)).symm
          _ ≤ ‖y - barrierCenter j‖ + ‖barrierCenter j‖ := norm_add_le _ _
      have hcen : ‖barrierCenter j‖ = 24 * barrierRadius j := by
        rw [norm_barrierCenter]
        show (3 / 2 : ℝ) * (2 : ℝ) ^ j = 24 * ((2 : ℝ) ^ j / 16)
        ring
      nlinarith [barrierRadius_pos j]
    rw [X2Integrand_apply, mildBarrierScalar_apply, if_pos h1lt]
    refine ENNReal.ofReal_le_ofReal ?_
    have hEq : ‖y‖ ^ (2 : ℕ) * (1 / ‖y‖ ^ (5 : ℕ)) = 1 / ‖y‖ ^ (3 : ℕ) := by
      field_simp [pow_ne_zero 5 (ne_of_gt hnorm), pow_ne_zero 3 (ne_of_gt hnorm)]
    rw [hEq]
    exact one_div_le_one_div_of_le (pow_pos hnorm 3)
      (pow_le_pow_left₀ (le_of_lt hnorm) (le_of_lt hUpper) 3)
  have hvol : volume (Metric.ball (barrierCenter j) (barrierRadius j)) =
      ENNReal.ofReal (barrierRadius j ^ (3 : ℕ)) * V3 :=
    volume_ball_eq _ (le_of_lt (barrierRadius_pos j))
  have halg : (1 / (25 * barrierRadius j) ^ (3 : ℕ)) * barrierRadius j ^ (3 : ℕ) =
      1 / (25 : ℝ) ^ (3 : ℕ) := by
    rw [mul_pow]
    field_simp [ne_of_gt (barrierRadius_pos j), (by norm_num : (25 : ℝ) ≠ 0)]
  have hw : (0 : ℝ) ≤ 1 / (25 * barrierRadius j) ^ (3 : ℕ) :=
    one_div_nonneg.mpr (pow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 25)
      (le_of_lt (barrierRadius_pos j))) (3 : ℕ))
  have hsplit : ENNReal.ofReal (1 / (25 * barrierRadius j) ^ (3 : ℕ)) *
      ENNReal.ofReal (barrierRadius j ^ (3 : ℕ)) =
      ENNReal.ofReal (1 / (25 : ℝ) ^ (3 : ℕ)) := by
    rw [← ENNReal.ofReal_mul hw, halg]
  have heq : c0 = ENNReal.ofReal (1 / (25 * barrierRadius j) ^ (3 : ℕ)) *
      volume (Metric.ball (barrierCenter j) (barrierRadius j)) := by
    show ENNReal.ofReal (1 / (25 : ℝ) ^ (3 : ℕ)) * V3 = _
    rw [← hsplit, mul_assoc, ← hvol]
  calc c0 = ENNReal.ofReal (1 / (25 * barrierRadius j) ^ (3 : ℕ)) *
        volume (Metric.ball (barrierCenter j) (barrierRadius j)) := heq
    _ = ∫⁻ y in Metric.ball (barrierCenter j) (barrierRadius j),
          ENNReal.ofReal (1 / (25 * barrierRadius j) ^ (3 : ℕ)) ∂volume :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in Metric.ball (barrierCenter j) (barrierRadius j), X2Integrand y ∂volume :=
        setLIntegral_mono measurable_X2Integrand h_point

theorem lintegral_barrier_X2_eq_top :
    (∫⁻ ξ : ES, X2Integrand ξ ∂volume) = ⊤ := by
  by_contra hne
  have hlt : (∫⁻ ξ : ES, X2Integrand ξ ∂volume) < ⊤ := lt_top_iff_ne_top.mpr hne
  have hN : ∀ N : ℕ, (N : ℕ) • c0 ≤ ∫⁻ ξ : ES, X2Integrand ξ ∂volume := by
    intro N
    have hpw : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
        (fun j : ℕ => Metric.ball (barrierCenter j) (barrierRadius j)) := by
      intro i _ j _ hij
      refine Set.disjoint_left.mpr fun y hy1 hy2 => ?_
      have h1 : y ∈ bShell i := barrierBall_subset_bShell i hy1
      have h2 : y ∈ bShell j := barrierBall_subset_bShell j hy2
      exact Set.disjoint_left.mp (bShell_disjoint hij) h1 h2
    let hU : Set ES := ⋃ j ∈ Finset.range N,
      Metric.ball (barrierCenter j) (barrierRadius j)
    have hsum : (N : ℕ) • c0 =
        Finset.sum (Finset.range N) (fun _ : ℕ => c0) := by
      simp [Finset.sum_const, Finset.card_range]
    have hle' : Finset.sum (Finset.range N) (fun _ : ℕ => c0) ≤
        Finset.sum (Finset.range N) (fun j : ℕ =>
          ∫⁻ y in Metric.ball (barrierCenter j) (barrierRadius j),
            X2Integrand y ∂volume) :=
      Finset.sum_le_sum (fun j _ => barrierBall_integral_ge_c0 j)
    have hib : Finset.sum (Finset.range N) (fun j : ℕ =>
          ∫⁻ y in Metric.ball (barrierCenter j) (barrierRadius j),
            X2Integrand y ∂volume) =
        ∫⁻ y in hU, X2Integrand y ∂volume :=
      (lintegral_biUnion_finset hpw
        (fun b _ => measurableSet_barrierBall b) X2Integrand).symm
    have hmono : ∫⁻ y in hU, X2Integrand y ∂volume ≤
        ∫⁻ y in (univ : Set ES), X2Integrand y ∂volume :=
      lintegral_mono_set (Set.subset_univ hU)
    calc (N : ℕ) • c0
        = Finset.sum (Finset.range N) (fun _ : ℕ => c0) := hsum
      _ ≤ Finset.sum (Finset.range N) (fun j : ℕ =>
            ∫⁻ y in Metric.ball (barrierCenter j) (barrierRadius j),
              X2Integrand y ∂volume) := hle'
      _ = ∫⁻ y in hU, X2Integrand y ∂volume := hib
      _ ≤ ∫⁻ y in (univ : Set ES), X2Integrand y ∂volume := hmono
      _ = ∫⁻ ξ : ES, X2Integrand ξ ∂volume := setLIntegral_univ _
  obtain ⟨N, hN'⟩ := exists_nat_gt ((∫⁻ ξ : ES, X2Integrand ξ ∂volume).toReal / c0.toReal)
  have hc0 : (0 : ℝ) < c0.toReal := ENNReal.toReal_pos c0_ne_zero c0_lt_top
  have hNlt : ((N : ℕ) • c0) < ⊤ := lt_of_le_of_lt (hN N) hlt
  have h1 : ((N : ℕ) • c0).toReal ≤ (∫⁻ ξ : ES, X2Integrand ξ ∂volume).toReal :=
    (ENNReal.toReal_le_toReal hNlt.ne hne).mpr (hN N)
  rw [ENNReal.toReal_nsmul, nsmul_eq_mul] at h1
  have hgt : (∫⁻ ξ : ES, X2Integrand ξ ∂volume).toReal < (N : ℝ) * c0.toReal :=
    (div_lt_iff₀ hc0).mp hN'
  linarith

/-- **The barrier theorem.**  The `X²` weight of the barrier profile is not
integrable: the `hv2` leg of `SourceX2Budget` fails for this datum. -/
theorem not_integrable_barrier_X2 :
    ¬ Integrable (fun ξ : ES => ‖ξ‖ ^ (2 : ℕ) * ‖mildBarrierProfile ξ‖) volume := by
  intro h
  have hfi := h.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal
      (ae_of_all _ (fun ξ => mul_nonneg (pow_nonneg (norm_nonneg _) 2)
        (norm_nonneg _)))] at hfi
  have key : (∫⁻ ξ : ES,
      ENNReal.ofReal (‖ξ‖ ^ (2 : ℕ) * ‖mildBarrierProfile ξ‖) ∂volume) = ⊤ := by
    convert lintegral_barrier_X2_eq_top using 1
    · simp only [X2Integrand, norm_mildBarrierProfile]
  rw [key] at hfi
  exact lt_irrefl (⊤ : ℝ≥0∞) hfi

/-- The time-constant trajectory `mildBarrierVec` has finite `X⁻¹` and finite
`X¹` quantities in every coordinate... -/
theorem constant_trajectory_slots_finite (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖mildBarrierVec ξ i‖) volume ∧
      Integrable (fun ξ : ES => ‖ξ‖ * ‖mildBarrierVec ξ i‖) volume := by
  constructor
  · simpa [mildBarrierVec] using integrable_barrier_Xm1
  · simpa [mildBarrierVec] using integrable_barrier_X1

/-- ...but its `hv2` leg fails: this is exactly the `SourceX2Budget` third-leg
shape `∀ s j, Integrable (fun η => ‖η‖ ^ 2 * ‖v s η j‖)` with `s` suppressed
(time-constant trajectory). -/
theorem constant_trajectory_fails_hv2 :
    ¬ ∀ j : Fin 3, Integrable (fun η : ES => ‖η‖ ^ (2 : ℕ) * ‖mildBarrierVec η j‖) volume := by
  intro h
  exact not_integrable_barrier_X2 (h ⟨0, by omega⟩)

/-- **No positive scale repairs the gap.**  At scale `B ≠ 0` the `X²` weight of
the scaled profile is still non-integrable. -/
theorem not_integrable_barrier_X2_at_scale (B : ℝ) (hB : B ≠ 0) :
    ¬ Integrable (fun ξ : ES => ‖ξ‖ ^ (2 : ℕ) * ‖(B : ℂ) * mildBarrierProfile ξ‖) volume := by
  intro h
  have hBc : (B : ℂ) ≠ 0 := by simpa using hB
  have hfi := h.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal
      (ae_of_all _ (fun ξ => mul_nonneg (pow_nonneg (norm_nonneg _) 2)
        (norm_nonneg _)))] at hfi
  have key : (∫⁻ ξ : ES,
      ENNReal.ofReal (‖ξ‖ ^ (2 : ℕ) * ‖(B : ℂ) * mildBarrierProfile ξ‖) ∂volume) = ⊤ := by
    have hmul : (fun ξ : ES =>
        ENNReal.ofReal (‖ξ‖ ^ (2 : ℕ) * ‖(B : ℂ) * mildBarrierProfile ξ‖)) =
        (fun ξ : ES => ENNReal.ofReal ‖(B : ℂ)‖ * X2Integrand ξ) := by
      funext ξ
      rw [X2Integrand_apply, norm_mul (B : ℂ) (mildBarrierProfile ξ),
        norm_mildBarrierProfile, ← ENNReal.ofReal_mul (norm_nonneg _)]
      congr 1
      ring
    rw [hmul, lintegral_const_mul _ measurable_X2Integrand,
      lintegral_barrier_X2_eq_top]
    refine ENNReal.mul_eq_top.mpr (Or.inl ⟨?_, rfl⟩)
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hBc))
  rw [key] at hfi
  exact lt_irrefl (⊤ : ℝ≥0∞) hfi

/-! ## The radii-independent barrier -/

private theorem integral_barrier_Xm1_le :
    ∫ ξ : ES, ‖ξ‖⁻¹ * mildBarrierScalar ξ ∂volume ≤
      (ENNReal.ofReal (64 / 7) * V3).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun ξ => mul_nonneg (inv_nonneg.2 (norm_nonneg _))
      (mildBarrierScalar_nonneg ξ)))
    ((continuous_norm.measurable.inv.mul measurable_mildBarrierScalar).aestronglyMeasurable)]
  exact (ENNReal.toReal_le_toReal lintegral_barrier_Xm1_lt_top.ne
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top V3_lt_top).ne).mpr
      lintegral_barrier_Xm1_le

private theorem integral_barrier_X1_le :
    ∫ ξ : ES, ‖ξ‖ * mildBarrierScalar ξ ∂volume ≤
      (ENNReal.ofReal (16 : ℝ) * V3).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun ξ => mul_nonneg (norm_nonneg _) (mildBarrierScalar_nonneg ξ)))
    ((continuous_norm.measurable.mul measurable_mildBarrierScalar).aestronglyMeasurable)]
  exact (ENNReal.toReal_le_toReal lintegral_barrier_X1_lt_top.ne
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top V3_lt_top).ne).mpr
      lintegral_barrier_X1_le

/-- **The radii theorem.**  For any box radii `B1, B2 > 0` there is a datum
whose per-coordinate `X⁻¹` and `X¹` integrals are bounded by them while the
`X²` (`hv2`) leg fails.  No choice of the linked-box record's two radii
determines the `SourceX2Budget` third leg. -/
theorem exists_slots_below_radii_hv2_fails (B1 B2 : ℝ) (hB1 : 0 < B1) (hB2 : 0 < B2) :
    ∃ v : ES → ComplexSpace,
      (∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖v ξ i‖) volume) ∧
        (∀ i : Fin 3, ∫ ξ : ES, ‖ξ‖⁻¹ * ‖v ξ i‖ ∂volume ≤ B1) ∧
        (∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖v ξ i‖) volume) ∧
        (∀ i : Fin 3, ∫ ξ : ES, ‖ξ‖ * ‖v ξ i‖ ∂volume ≤ B2) ∧
        ¬ ∀ j : Fin 3, Integrable (fun η : ES => ‖η‖ ^ (2 : ℕ) * ‖v η j‖) volume := by
  let A1 := (ENNReal.ofReal (64 / 7) * V3).toReal
  let A2 := (ENNReal.ofReal (16 : ℝ) * V3).toReal
  have hA1 : 0 ≤ A1 := ENNReal.toReal_nonneg
  have hA2 : 0 ≤ A2 := ENNReal.toReal_nonneg
  let B := min (B1 / (A1 + 1)) (B2 / (A2 + 1))
  have hBpos : 0 < B :=
    lt_min (div_pos hB1 (by linarith)) (div_pos hB2 (by linarith))
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hB1' : B * (A1 + 1) ≤ B1 :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < A1 + 1)).mp (min_le_left _ _)
  have hB2' : B * (A2 + 1) ≤ B2 :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < A2 + 1)).mp (min_le_right _ _)
  have hBnorm : ‖(B : ℂ)‖ = B := Complex.norm_of_nonneg (le_of_lt hBpos)
  have hI1 : ∫ ξ : ES, ‖ξ‖⁻¹ * mildBarrierScalar ξ ∂volume ≤ A1 :=
    integral_barrier_Xm1_le
  have hI2 : ∫ ξ : ES, ‖ξ‖ * mildBarrierScalar ξ ∂volume ≤ A2 :=
    integral_barrier_X1_le
  have hxm1_eq : (fun ξ : ES => ‖ξ‖⁻¹ * ‖(B : ℂ) * mildBarrierProfile ξ‖) =
      (fun ξ => B * (‖ξ‖⁻¹ * ‖mildBarrierProfile ξ‖)) := by
    funext ξ
    rw [norm_mul (B : ℂ) (mildBarrierProfile ξ), hBnorm]
    ring
  have hx1_eq : (fun ξ : ES => ‖ξ‖ * ‖(B : ℂ) * mildBarrierProfile ξ‖) =
      (fun ξ => B * (‖ξ‖ * ‖mildBarrierProfile ξ‖)) := by
    funext ξ
    rw [norm_mul (B : ℂ) (mildBarrierProfile ξ), hBnorm]
    ring
  refine ⟨fun ξ => fun _ => (B : ℂ) * mildBarrierProfile ξ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖(B : ℂ) * mildBarrierProfile ξ‖) volume
    rw [hxm1_eq]
    exact Integrable.smul B integrable_barrier_Xm1
  · intro i
    show ∫ ξ : ES, ‖ξ‖⁻¹ * ‖(B : ℂ) * mildBarrierProfile ξ‖ ∂volume ≤ B1
    rw [hxm1_eq, integral_const_mul B]
    calc B * ∫ ξ : ES, ‖ξ‖⁻¹ * ‖mildBarrierProfile ξ‖ ∂volume
        = B * ∫ ξ : ES, ‖ξ‖⁻¹ * mildBarrierScalar ξ ∂volume := by
            congr 1; simp only [norm_mildBarrierProfile]
      _ ≤ B * A1 := mul_le_mul_of_nonneg_left hI1 (le_of_lt hBpos)
      _ ≤ B * (A1 + 1) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
              (le_of_lt hBpos)
      _ ≤ B1 := hB1'
  · intro i
    show Integrable (fun ξ : ES => ‖ξ‖ * ‖(B : ℂ) * mildBarrierProfile ξ‖) volume
    rw [hx1_eq]
    exact Integrable.smul B integrable_barrier_X1
  · intro i
    show ∫ ξ : ES, ‖ξ‖ * ‖(B : ℂ) * mildBarrierProfile ξ‖ ∂volume ≤ B2
    rw [hx1_eq, integral_const_mul B]
    calc B * ∫ ξ : ES, ‖ξ‖ * ‖mildBarrierProfile ξ‖ ∂volume
        = B * ∫ ξ : ES, ‖ξ‖ * mildBarrierScalar ξ ∂volume := by
            congr 1; simp only [norm_mildBarrierProfile]
      _ ≤ B * A2 := mul_le_mul_of_nonneg_left hI2 (le_of_lt hBpos)
      _ ≤ B * (A2 + 1) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
              (le_of_lt hBpos)
      _ ≤ B2 := hB2'
  · intro h
    exact not_integrable_barrier_X2_at_scale B hBne (h ⟨0, by omega⟩)

end Navier.Analysis.MildHorizonFreeRestartBarrier

#print axioms Navier.Analysis.MildHorizonFreeRestartBarrier.lintegral_barrier_X2_eq_top
#print axioms Navier.Analysis.MildHorizonFreeRestartBarrier.not_integrable_barrier_X2
#print axioms Navier.Analysis.MildHorizonFreeRestartBarrier.integrable_barrier_Xm1
#print axioms Navier.Analysis.MildHorizonFreeRestartBarrier.integrable_barrier_X1
#print axioms Navier.Analysis.MildHorizonFreeRestartBarrier.constant_trajectory_fails_hv2
#print axioms Navier.Analysis.MildHorizonFreeRestartBarrier.not_integrable_barrier_X2_at_scale
#print axioms Navier.Analysis.MildHorizonFreeRestartBarrier.exists_slots_below_radii_hv2_fails
