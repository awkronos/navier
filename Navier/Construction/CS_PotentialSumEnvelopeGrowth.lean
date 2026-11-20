/-
Lane MATH-NAVIER-1120 (2026-11-20).

# T1 without `hnum`: low stages may grow like a negative power of `q`

`CSPotentialSumEnvelope.potentialSum_negPower_envelope` asks the finitely many
low stages `j < M` for CONSTANT jet bounds `K j m` on the whole estimate domain
`S`.  `CSPotentialSumEnvelope.lowStageTable_le` produces those constants only
under `hnum : 0 ≤ g j - L m`, and `Construction.HnumFalsification` proves that
at the selected estimates witness `hnum` is false (`gainSel 1 / 2 < 1 ≤
lossSel m`).  So the constant-table route is dead at the actual schedule.

The constant table is stronger than the envelope needs: the conclusion already
allows a factor `q ^ (-β)`.  This module proves the envelope with the low
stages bounded by `K j m * q x ^ (-β₀)` (a fixed nonnegative growth exponent
`β₀`, only on the sublevel `q x ≤ 1`), and then discharges that hypothesis from
`CutStageBounds` alone, with NO numerical gain-against-loss condition:
a stage with `1 ≤ j` has jets `≤ (1/2)^j q^(g j - L m)` and
`g j ≥ 0` gives `g j - L m ≥ -L m`, so `q^(g j - L m) ≤ q^(-β₀)` for `q ≤ 1`
as soon as `L m ≤ β₀`.

The coverage side condition `hcov` (each low row sits inside the stage-bound
range `m ≤ j + 2`) is kept; it is automatic at the consumer's ceiling `M = 2`.
-/
import Navier.Construction.CS_PotentialSumEnvelope

set_option autoImplicit false
noncomputable section

namespace Navier.Construction.CSPotentialSumEnvelopeGrowth

open Set Filter Function Topology
open scoped BigOperators ContDiff
open Navier.Construction.CSPotentialSumEnvelope

private theorem nat_le_infty' (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Frozen prefix with low stages allowed to grow like `q ^ (-β₀)`. -/
theorem partialPotential_prefix_sum_growth
    {a : ℕ → ℝ}
    {q : E → ℝ} {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    (hq : ContDiffOn ℝ ∞ q U) (hqpos : ∀ x ∈ S, 0 < q x)
    {A : ℕ → E → V} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    {g L : ℕ → ℝ} (hgpos : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hb : DiagonalJetBounds.CutStageBounds a q
      (CutStageEstimates.positiveStages A) g L S)
    (M : ℕ) (K : ℕ → ℕ → ℝ) (β₀ : ℝ)
    (hK : ∀ j m, j < M → m ≤ M → ∀ x ∈ S, q x ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (SolenoidalDiagonal.cutStage a q (CutStageEstimates.positiveStages A) j) x‖ ≤
        K j m * q x ^ (-β₀))
    (J : ℕ) (hJgeM : M ≤ J) (β : ℝ) (hβ0 : β₀ ≤ β) (hLβ : ∀ m ≤ M, L m ≤ β)
    (m : ℕ) (hm : m ≤ M) (x : E) (hx : x ∈ S) (hq1 : q x ≤ 1) :
    ‖iteratedFDeriv ℝ m
        (fun y => SolenoidalDiagonal.partialPotential a q
          (CutStageEstimates.positiveStages A) (J + 1) y) x‖ ≤
      ((∑ j ∈ Finset.range M, ∑ k ∈ Finset.range (M + 1), |K j k|) +
        (J + 1 : ℝ)) * q x ^ (-β) := by
  let A' : ℕ → E → V := CutStageEstimates.positiveStages A
  let Cterm : ℝ := ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range (M + 1), |K j k|
  have hxU : x ∈ U := hSU hx
  have hqx : 0 < q x := hqpos x hx
  have hqAt : ContDiffAt ℝ ∞ q x := hq.contDiffAt (hU.mem_nhds hxU)
  have hA'At : ∀ j, ContDiffAt ℝ ∞ (A' j) x :=
    fun j => (CutStageEstimates.positiveStages_smooth hA j).contDiffAt (hU.mem_nhds hxU)
  have hFAt : ∀ j, ContDiffAt ℝ ∞ (SolenoidalDiagonal.cutStage a q A' j) x :=
    fun j => SolenoidalDiagonal.cutStage_contDiffAt hqAt hA'At j
  have hpf : iteratedFDeriv ℝ m
      (fun y => SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x =
      ∑ j ∈ Finset.range (J + 1), iteratedFDeriv ℝ m
        (SolenoidalDiagonal.cutStage a q A' j) x := by
    show iteratedFDeriv ℝ m (fun y => ∑ j ∈ Finset.range (J + 1),
      SolenoidalDiagonal.cutStage a q A' j y) x = _
    exact finite_sum_jet hFAt (J + 1) m
  have hrp0 : q x ^ (-β₀) ≤ q x ^ (-β) :=
    Real.rpow_le_rpow_of_exponent_ge hqx hq1 (by linarith)
  rw [hpf]
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : M ≤ J + 1)]
  have hlow : ∑ j ∈ Finset.range M,
      ‖iteratedFDeriv ℝ m (SolenoidalDiagonal.cutStage a q A' j) x‖ ≤ Cterm * q x ^ (-β) := by
    calc ∑ j ∈ Finset.range M, ‖iteratedFDeriv ℝ m (SolenoidalDiagonal.cutStage a q A' j) x‖
        ≤ ∑ j ∈ Finset.range M, (∑ k ∈ Finset.range (M + 1), |K j k|) * q x ^ (-β) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hKle : K j m ≤ ∑ k ∈ Finset.range (M + 1), |K j k| :=
            (le_abs_self (K j m)).trans
              (Finset.single_le_sum (f := fun k => |K j k|) (fun k _ => abs_nonneg _)
                (Finset.mem_range.mpr (by omega : m < M + 1)))
          have hK0 : 0 ≤ K j m * q x ^ (-β₀) := by
            have := (norm_nonneg _).trans (hK j m (Finset.mem_range.mp hj) hm x hx hq1)
            exact this
          have hKnn : 0 ≤ K j m := by
            by_contra hneg
            push_neg at hneg
            have := mul_neg_of_neg_of_pos hneg (Real.rpow_pos_of_pos hqx (-β₀))
            linarith
          calc ‖iteratedFDeriv ℝ m (SolenoidalDiagonal.cutStage a q A' j) x‖
              ≤ K j m * q x ^ (-β₀) := hK j m (Finset.mem_range.mp hj) hm x hx hq1
            _ ≤ K j m * q x ^ (-β) := mul_le_mul_of_nonneg_left hrp0 hKnn
            _ ≤ (∑ k ∈ Finset.range (M + 1), |K j k|) * q x ^ (-β) :=
                mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg hqx.le _)
      _ = Cterm * q x ^ (-β) := by rw [← Finset.sum_mul]
  have hhigh : ∑ j ∈ Finset.Ico M (J + 1),
      ‖iteratedFDeriv ℝ m (SolenoidalDiagonal.cutStage a q A' j) x‖ ≤
      (J + 1 : ℝ) * q x ^ (-β) := by
    have hterm : ∀ j ∈ Finset.Ico M (J + 1),
        ‖iteratedFDeriv ℝ m (SolenoidalDiagonal.cutStage a q A' j) x‖ ≤ q x ^ (-β) := by
      intro j hj
      have hjM : M ≤ j := (Finset.mem_Ico.mp hj).1
      by_cases hj0 : j = 0
      · subst hj0
        have hz : (fun y => SolenoidalDiagonal.cutStage a q A' 0 y) = fun _ => (0 : V) := by
          funext y
          show SmoothCutoffs.scaledCutoff (a 0) (q y) • A' 0 y = 0
          have hzero_stage : A' 0 = 0 := CutStageEstimates.positiveStages_zero A
          rw [hzero_stage]
          simp
        have hjet : iteratedFDeriv ℝ m (fun y =>
            SolenoidalDiagonal.cutStage a q A' 0 y) x = 0 := by
          rw [hz, iteratedFDeriv_fun_zero, Pi.zero_apply]
        rw [hjet, norm_zero]
        exact Real.rpow_nonneg hqx.le (-β)
      · have hj1 : (1 : ℕ) ≤ j := by omega
        have hj2 : m ≤ j + 2 := by omega
        have hge : -β ≤ g j - L m := by
          have hgj : (0 : ℝ) ≤ g j := hgpos j hj1
          linarith [hLβ m hm]
        have hrp : q x ^ (g j - L m) ≤ q x ^ (-β) :=
          Real.rpow_le_rpow_of_exponent_ge hqx hq1 hge
        calc ‖iteratedFDeriv ℝ m (SolenoidalDiagonal.cutStage a q A' j) x‖
            ≤ (1 / 2 : ℝ) ^ j * q x ^ (g j - L m) := hb j hj1 m hj2 x hx
          _ ≤ (1 / 2 : ℝ) ^ j * q x ^ (-β) :=
              mul_le_mul_of_nonneg_left hrp (pow_nonneg (by norm_num) j)
          _ ≤ 1 * q x ^ (-β) :=
              mul_le_mul_of_nonneg_right
                (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
                  (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.zero_le j))
                (Real.rpow_nonneg hqx.le _)
          _ = q x ^ (-β) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hcard : (Finset.Ico M (J + 1)).card ≤ J + 1 := by
      rw [Nat.card_Ico]; omega
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.rpow_nonneg hqx.le _)
  calc _ ≤ Cterm * q x ^ (-β) + (J + 1 : ℝ) * q x ^ (-β) := add_le_add hlow hhigh
    _ = (Cterm + (J + 1 : ℝ)) * q x ^ (-β) := by ring

/-- **T1 envelope with growing low stages.** -/
theorem potentialSum_negPower_envelope_growth
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (ha1 : ∀ j, (1 : ℝ) ≤ a j)
    {q : E → ℝ} {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    (hq : ContDiffOn ℝ ∞ q U) (hqpos : ∀ x ∈ S, 0 < q x)
    {A : ℕ → E → V} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    {g L : ℕ → ℝ} (hg : Monotone g) (hgtop : Tendsto g atTop atTop)
    (hgpos : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hb : DiagonalJetBounds.CutStageBounds a q
      (CutStageEstimates.positiveStages A) g L S)
    (M : ℕ) (K : ℕ → ℕ → ℝ) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀)
    (hK : ∀ j m, j < M → m ≤ M → ∀ x ∈ S, q x ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (SolenoidalDiagonal.cutStage a q (CutStageEstimates.positiveStages A) j) x‖ ≤
        K j m * q x ^ (-β₀)) :
    ∃ C β : ℝ, 0 < C ∧ 0 ≤ β ∧ ∀ m ≤ M, ∀ x ∈ S,
      ‖iteratedFDeriv ℝ m
        (SolenoidalDiagonal.potentialSum a q (CutStageEstimates.positiveStages A)) x‖ ≤
        C * q x ^ (-β) := by
  obtain ⟨J, _hJmin, hJgeM, hgain⟩ :=
    DiagonalJetBounds.exists_prefix_gain g L hgtop M 0 0
  let β : ℝ := β₀ + ∑ m ∈ Finset.range (M + 1), |L m|
  have hSum0 : 0 ≤ ∑ m ∈ Finset.range (M + 1), |L m| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hβ : 0 ≤ β := by positivity
  have hβ0 : β₀ ≤ β := by simp only [β]; linarith
  have hLβ : ∀ m ≤ M, L m ≤ β := by
    intro m hm
    have hsum : |L m| ≤ ∑ k ∈ Finset.range (M + 1), |L k| :=
      Finset.single_le_sum (f := fun k => |L k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega : m < M + 1))
    calc L m ≤ |L m| := le_abs_self _
      _ ≤ _ := hsum
      _ ≤ β := by simp only [β]; linarith
  let Cterm : ℝ := ∑ j ∈ Finset.range M, ∑ m ∈ Finset.range (M + 1), |K j m|
  have hCterm0 : 0 ≤ Cterm :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  let C : ℝ := 1 + Cterm + (J + 2 : ℝ) + (1 / 2 : ℝ) ^ J
  have hC : 0 < C := by positivity
  refine ⟨C, β, hC, hβ, ?_⟩
  intro m hm x hx
  let A' : ℕ → E → V := CutStageEstimates.positiveStages A
  have hxU : x ∈ U := hSU hx
  have hqx : 0 < q x := hqpos x hx
  have hqAt : ContDiffAt ℝ ∞ q x := hq.contDiffAt (hU.mem_nhds hxU)
  have hA'At : ∀ j, ContDiffAt ℝ ∞ (A' j) x :=
    fun j => (CutStageEstimates.positiveStages_smooth hA j).contDiffAt (hU.mem_nhds hxU)
  have hFAt : ∀ j, ContDiffAt ℝ ∞ (SolenoidalDiagonal.cutStage a q A' j) x :=
    fun j => SolenoidalDiagonal.cutStage_contDiffAt hqAt hA'At j
  by_cases hq1 : q x ≤ 1
  · have hsm : ContDiffAt ℝ ∞ (fun y => SolenoidalDiagonal.potentialSum a q A' y) x :=
      SolenoidalDiagonal.potentialSum_contDiffAt ha hqx hqAt hA'At
    have hpr : ContDiffAt ℝ ∞
        (fun y => SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x := by
      show ContDiffAt ℝ ∞ (fun y => ∑ j ∈ Finset.range (J + 1),
        SolenoidalDiagonal.cutStage a q A' j y) x
      exact ContDiffAt.sum (fun j _ => hFAt j)
    have htail : ‖iteratedFDeriv ℝ m
        (fun y => SolenoidalDiagonal.potentialSum a q A' y -
          SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x‖ ≤ (1 / 2 : ℝ) ^ J :=
      potentialSum_tail_jet_sub ha hU hSU hq hqpos hA hg hb M J hJgeM hgain m hm x hx hq1
    have hprefix := partialPotential_prefix_sum_growth hU hSU hq hqpos hA hgpos hb M K β₀ hK
      J hJgeM β hβ0 hLβ m hm x hx hq1
    have hsub : iteratedFDeriv ℝ m (fun y => SolenoidalDiagonal.potentialSum a q A' y) x =
        iteratedFDeriv ℝ m (fun y => SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x +
          iteratedFDeriv ℝ m (fun y =>
            SolenoidalDiagonal.potentialSum a q A' y -
              SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x := by
      rw [fun_iteratedFDeriv_sub_apply (hsm.of_le (nat_le_infty' m))
        (hpr.of_le (nat_le_infty' m))]
      abel
    have hone : (1 : ℝ) ≤ q x ^ (-β) := by
      have h0 : q x ^ (0 : ℝ) ≤ q x ^ (-β) :=
        Real.rpow_le_rpow_of_exponent_ge hqx hq1 (by linarith [hβ])
      rwa [Real.rpow_zero] at h0
    have hmul_le {k : ℝ} (hk0 : 0 ≤ k) : k ≤ k * q x ^ (-β) := by
      have := mul_le_mul_of_nonneg_left hone hk0
      rwa [mul_one] at this
    calc ‖iteratedFDeriv ℝ m (fun y => SolenoidalDiagonal.potentialSum a q A' y) x‖
        = ‖iteratedFDeriv ℝ m (fun y => SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x +
            iteratedFDeriv ℝ m (fun y =>
              SolenoidalDiagonal.potentialSum a q A' y -
                SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x‖ := by rw [hsub]
      _ ≤ ‖iteratedFDeriv ℝ m
            (fun y => SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x‖ +
            ‖iteratedFDeriv ℝ m (fun y => SolenoidalDiagonal.potentialSum a q A' y -
              SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x‖ := norm_add_le _ _
      _ ≤ (Cterm + (J + 1 : ℝ)) * q x ^ (-β) + (1 / 2 : ℝ) ^ J := add_le_add hprefix htail
      _ ≤ (Cterm + (J + 1 : ℝ)) * q x ^ (-β) + (1 / 2 : ℝ) ^ J * q x ^ (-β) :=
          add_le_add (le_refl _) (hmul_le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) J))
      _ = ((1 / 2 : ℝ) ^ J + Cterm + (J + 1 : ℝ)) * q x ^ (-β) := by ring
      _ ≤ C * q x ^ (-β) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hqx.le _)
          show (1 / 2 : ℝ) ^ J + Cterm + (J + 1 : ℝ) ≤
            1 + Cterm + (J + 2 : ℝ) + (1 / 2 : ℝ) ^ J
          linarith
  · have hgt : (1 : ℝ) < q x := lt_of_not_ge hq1
    have hjet : iteratedFDeriv ℝ m (fun y => SolenoidalDiagonal.potentialSum a q A' y) x = 0 :=
      potentialSum_large_scale_vanishing_sub ha1 hU hSU hq x hx hgt m
    rw [hjet, norm_zero]
    exact mul_nonneg (le_of_lt hC) (Real.rpow_nonneg hqx.le _)

/-- **The envelope from `CutStageBounds` alone, no `hnum`.**  Only the coverage
condition `hcov` remains (automatic at `M = 2`). -/
theorem potentialSum_negPower_envelope_of_cutBounds_free
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (ha1 : ∀ j, (1 : ℝ) ≤ a j)
    {q : E → ℝ} {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    (hq : ContDiffOn ℝ ∞ q U) (hqpos : ∀ x ∈ S, 0 < q x)
    {A : ℕ → E → V} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    {g L : ℕ → ℝ} (hg : Monotone g) (hgtop : Tendsto g atTop atTop)
    (hgpos : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hb : DiagonalJetBounds.CutStageBounds a q
      (CutStageEstimates.positiveStages A) g L S)
    (M : ℕ) (hcov : ∀ j, 1 ≤ j → j < M → M ≤ j + 2) :
    ∃ C β : ℝ, 0 < C ∧ 0 ≤ β ∧ ∀ m ≤ M, ∀ x ∈ S,
      ‖iteratedFDeriv ℝ m
        (SolenoidalDiagonal.potentialSum a q (CutStageEstimates.positiveStages A)) x‖ ≤
        C * q x ^ (-β) := by
  let β₀ : ℝ := ∑ m ∈ Finset.range (M + 1), |L m|
  have hβ₀ : 0 ≤ β₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hLβ : ∀ m ≤ M, L m ≤ β₀ := by
    intro m hm
    exact (le_abs_self (L m)).trans
      (Finset.single_le_sum (f := fun k => |L k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega : m < M + 1)))
  refine potentialSum_negPower_envelope_growth ha ha1 hU hSU hq hqpos hA hg hgtop hgpos hb M
    (fun j _ => if j = 0 then (0 : ℝ) else (1 / 2 : ℝ) ^ j) β₀ hβ₀ ?_
  intro j m hjM hmM x hx hq1
  have hqx : 0 < q x := hqpos x hx
  by_cases hj0 : j = 0
  · subst hj0
    have hzero : SolenoidalDiagonal.cutStage a q (CutStageEstimates.positiveStages A) 0 =
        fun _ => (0 : V) := by
      funext y
      show SmoothCutoffs.scaledCutoff (a 0) (q y) • CutStageEstimates.positiveStages A 0 y = 0
      rw [CutStageEstimates.positiveStages_zero A]
      simp
    rw [hzero, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    simp
  · have hj1 : 1 ≤ j := by omega
    have hm2 : m ≤ j + 2 := hmM.trans (hcov j hj1 hjM)
    have hge : -β₀ ≤ g j - L m := by linarith [hgpos j hj1, hLβ m hmM]
    have hrp : q x ^ (g j - L m) ≤ q x ^ (-β₀) :=
      Real.rpow_le_rpow_of_exponent_ge hqx hq1 hge
    simp only [hj0, if_false]
    exact (hb j hj1 m hm2 x hx).trans
      (mul_le_mul_of_nonneg_left hrp (pow_nonneg (by norm_num) j))

#print axioms Navier.Construction.CSPotentialSumEnvelopeGrowth.partialPotential_prefix_sum_growth
#print axioms Navier.Construction.CSPotentialSumEnvelopeGrowth.potentialSum_negPower_envelope_growth
#print axioms Navier.Construction.CSPotentialSumEnvelopeGrowth.potentialSum_negPower_envelope_of_cutBounds_free

end Navier.Construction.CSPotentialSumEnvelopeGrowth
