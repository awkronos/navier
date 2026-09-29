/-
Original work, lane W30-NCS1-0929 (2026-09-28/29).

# T1 — schedule summation of the diagonal cut-stage bounds

`docs/OPEN_FRONTIER_MAP.md` (BKM row) and `Analysis/BKMProfileEnvelope.lean`
(`## Exact surviving proposition (OPEN)`) record the surviving work for the
selected compact candidate as five named transports; transport 1 is the
positive-stage sum bound: "the per-stage `RawStageBounds` exist; the schedule
summation over `j` does not". The faithful endpoint
`Analysis.BKMEnvAxis.vorticityRateBound_sel_of_polyUpper` consumes the
polynomial upper envelope `hup`, whose Construction-side input is exactly
this summation (consumed further by the curl transport at order `m = 1`).

This module lands the first missing primitive, decomposed (Fano saturation
rule, `lean4.md` §6.4.c) into three named sub-keystones plus the assembly:

* `potentialSum_tail_jet_sub` — the tail beyond the frozen prefix `J` is
  bounded by `2^(-J)` at every jet order `m ≤ M` (via
  `DiagonalJetBounds.norm_tsum_sub_prefix_jet_le` and the prefix-gain
  inequality `0 ≤ g (J + 1) - L m`).
* `partialPotential_prefix_sum_sub` — the finite prefix splits at `M` into
  the explicit low-stage table `K` (summed into `Cterm`) and the geometric
  `CutStageBounds` range `M ≤ j ≤ J`, each stage absorbed by `q x ^ (-β)`.
* `potentialSum_large_scale_vanishing_sub` — for `q x > 1` every cutoff
  scale satisfies `1 / a j ≤ 1 < q x`, so the whole sum vanishes on a
  neighborhood and every jet at `x` is exactly `0` (equation-level, not a
  convention: `SmoothCutoffs.scaledCutoff_zero_of_inv_le`, `tsum_congr`,
  `iteratedFDeriv_eventuallyEq`).

`potentialSum_negPower_envelope` assembles them into one negative-power
envelope

    ‖iteratedFDeriv ℝ m (potentialSum a q (positiveStages A)) x‖ ≤ C * q x ^ (-β)

for every derivative ceiling `m ≤ M`, uniformly over the estimate domain `S`,
and `potentialSum_negPower_envelope_physical` specializes it to the actual
`physicalQ` similarity coordinate on the preterminal domain.

Numerical budget discipline (`research-mathematics.md` §3, F2/F6 defense):
the budget is frozen before any summation argument and contains no geometric
object — `J` comes from `DiagonalJetBounds.exists_prefix_gain`, a pure
inequality `0 ≤ g (J + 1) - L m` with `M ≤ J`; `β` is the finite sum of
`|L m|` over `m ≤ M`; `C` is the explicit sum `1 + Cterm + (J + 2) + 2^(-J)`
with `Cterm` the low-stage sup-bound table. There is no induction on the
stages and no induction hypothesis assumes the assembled field.

Nothing downstream is made unconditional: this is the transport itself. The
stage-0 bound (T2), the curl transport at `m = 1` (T3), and the cut plus
activation sup reduction (T4) remain the named consumers.
-/
import Navier.Construction.SolenoidalDiagonal
import Navier.Construction.CutStageEstimates
import Navier.Construction.DiagonalJetBounds
import Navier.Construction.PhysicalWaveSum

set_option autoImplicit false
noncomputable section

namespace Navier.Construction.CSPotentialSumEnvelope

open Set Filter Function Topology
open scoped BigOperators ContDiff

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The jets of a finite diagonal prefix are the finite sum of the stage
jets. (`DiagonalJetBounds.finite_sum_jet` is private; this is the public
copy the summation transport needs.) -/
theorem finite_sum_jet {F : ℕ → E → V} {x : E}
    (hF : ∀ j, ContDiffAt ℝ ∞ (F j) x) (K m : ℕ) :
    iteratedFDeriv ℝ m (fun y => ∑ j ∈ Finset.range K, F j y) x =
      ∑ j ∈ Finset.range K, iteratedFDeriv ℝ m (F j) x := by
  have hs : ∀ j ∈ Finset.range K, ContDiffWithinAt ℝ m (F j) univ x := by
    intro j _
    exact ((hF j).of_le (nat_le_infty m)).contDiffWithinAt
  simpa only [iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ x) hs

/-- **(T1 sub-keystone 1 — tail.)** Beyond the frozen prefix length `J`
(the gain `0 ≤ g (J + 1) - L m` at the ceiling), every jet of the actual
tsum minus the prefix is at most `2^(-J)` on the sublevel `q x ≤ 1`. -/
theorem potentialSum_tail_jet_sub
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    (hq : ContDiffOn ℝ ∞ q U) (hqpos : ∀ x ∈ S, 0 < q x)
    {A : ℕ → E → V} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    {g L : ℕ → ℝ} (hg : Monotone g)
    (hb : DiagonalJetBounds.CutStageBounds a q
      (CutStageEstimates.positiveStages A) g L S)
    (M J : ℕ) (hJgeM : M ≤ J) (hgain : ∀ m ≤ M, (0 : ℝ) ≤ g (J + 1) - L m)
    (m : ℕ) (hm : m ≤ M) (x : E) (hx : x ∈ S) (hq1 : q x ≤ 1) :
    ‖iteratedFDeriv ℝ m
        (fun y => SolenoidalDiagonal.potentialSum a q
            (CutStageEstimates.positiveStages A) y -
          SolenoidalDiagonal.partialPotential a q
            (CutStageEstimates.positiveStages A) (J + 1) y) x‖ ≤
      (1 / 2 : ℝ) ^ J := by
  let A' : ℕ → E → V := CutStageEstimates.positiveStages A
  have hxU : x ∈ U := hSU hx
  have hqx : 0 < q x := hqpos x hx
  have hqAt : ContDiffAt ℝ ∞ q x := hq.contDiffAt (hU.mem_nhds hxU)
  have hA'At : ∀ j, ContDiffAt ℝ ∞ (A' j) x :=
    fun j => (CutStageEstimates.positiveStages_smooth hA j).contDiffAt (hU.mem_nhds hxU)
  have hFAt : ∀ j, ContDiffAt ℝ ∞ (SolenoidalDiagonal.cutStage a q A' j) x :=
    fun j => SolenoidalDiagonal.cutStage_contDiffAt hqAt hA'At j
  obtain ⟨N, hzero⟩ :=
    SolenoidalDiagonal.eventually_zero_tail ha hqAt.continuousAt hqx A'
  have hexp : q x ^ (g (J + 1) - L m) ≤ 1 := by
    rw [← Real.rpow_zero (q x)]
    exact Real.rpow_le_rpow_of_exponent_ge hqx hq1 (hgain m hm)
  show ‖iteratedFDeriv ℝ m (fun y => (∑' j : ℕ, SolenoidalDiagonal.cutStage a q A' j y) -
      ∑ j ∈ Finset.range (J + 1), SolenoidalDiagonal.cutStage a q A' j y) x‖ ≤ (1 / 2 : ℝ) ^ J
  refine (DiagonalJetBounds.norm_tsum_sub_prefix_jet_le ⟨N, hzero⟩ hFAt
    g hg (L m) (q x) hqx hq1 J m ?_).trans ?_
  · intro j hj
    exact hb j (by omega) m (by omega) x hx
  · exact (mul_le_mul_of_nonneg_left hexp
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) J)).trans (le_of_eq (mul_one _))

/-- **(T1 sub-keystone 2 — frozen prefix.)** The prefix of length `J + 1`
splits at the ceiling `M`: the low stages `j < M` are absorbed by the
explicit table `K` (double sum `Cterm`), the stages `M ≤ j ≤ J` by the
geometric bounds, each at most `q x ^ (-β)` whenever `L m ≤ β` for the
ceiling `m ≤ M`. -/
theorem partialPotential_prefix_sum_sub
    {a : ℕ → ℝ}
    {q : E → ℝ} {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    (hq : ContDiffOn ℝ ∞ q U) (hqpos : ∀ x ∈ S, 0 < q x)
    {A : ℕ → E → V} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    {g L : ℕ → ℝ} (hgpos : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hb : DiagonalJetBounds.CutStageBounds a q
      (CutStageEstimates.positiveStages A) g L S)
    (M : ℕ) (K : ℕ → ℕ → ℝ)
    (hK : ∀ j m, j < M → m ≤ M → ∀ x ∈ S,
      ‖iteratedFDeriv ℝ m
        (SolenoidalDiagonal.cutStage a q (CutStageEstimates.positiveStages A) j) x‖ ≤ K j m)
    (J : ℕ) (hJgeM : M ≤ J) (β : ℝ) (hLβ : ∀ m ≤ M, L m ≤ β)
    (m : ℕ) (hm : m ≤ M) (x : E) (hx : x ∈ S) (hq1 : q x ≤ 1) :
    ‖iteratedFDeriv ℝ m
        (fun y => SolenoidalDiagonal.partialPotential a q
          (CutStageEstimates.positiveStages A) (J + 1) y) x‖ ≤
      (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range (M + 1), |K j k|) +
        (J + 1 : ℝ) * q x ^ (-β) := by
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
  rw [hpf]
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : M ≤ J + 1)]
  refine add_le_add ?_ ?_
  · calc ∑ j ∈ Finset.range M, ‖iteratedFDeriv ℝ m (SolenoidalDiagonal.cutStage a q A' j) x‖
        ≤ ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range (M + 1), |K j k| :=
            Finset.sum_le_sum fun j hj =>
              (hK j m (Finset.mem_range.mp hj) hm x hx).trans
                ((le_abs_self (K j m)).trans
                  (Finset.single_le_sum (f := fun k => |K j k|) (fun k _ => abs_nonneg _)
                    (Finset.mem_range.mpr (by omega : m < M + 1))))
      _ = Cterm := rfl
  · refine (Finset.sum_le_sum (g := fun _ => q x ^ (-β)) ?_).trans ?_
    · intro j hj
      have hjM : M ≤ j := (Finset.mem_Ico.mp hj).1
      by_cases hj0 : j = 0
      · subst hj0
        have hz : (fun y => SolenoidalDiagonal.cutStage a q A' 0 y) = fun _ => (0 : V) := by
          funext y
          show SmoothCutoffs.scaledCutoff (a 0) (q y) • A' 0 y = 0
          have hzero_stage : A' 0 = 0 :=
            CutStageEstimates.positiveStages_zero A
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
    · have hnon : 0 ≤ ∑ j ∈ Finset.range M, q x ^ (-β) :=
          Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg hqx.le _)
      have hsplit : ∑ j ∈ Finset.range (J + 1), q x ^ (-β)
          = ∑ j ∈ Finset.range M, q x ^ (-β)
              + ∑ j ∈ Finset.Ico M (J + 1), q x ^ (-β) := by
          rw [← Finset.sum_range_add_sum_Ico _ (by omega : M ≤ J + 1)]
      exact (le_add_of_nonneg_left hnon).trans
        ((le_of_eq hsplit.symm).trans
          (le_of_eq (by rw [Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]; norm_cast)))

/-- **(T1 sub-keystone 3 — large scales.)** Off the sublevel `q > 1` every
scale satisfies `1 / a j ≤ 1 < q x`, so each cutoff — and with it the whole
sum — vanishes on a whole neighborhood of `x`; consequently every jet at `x`
is exactly `0`. -/
theorem potentialSum_large_scale_vanishing_sub
    {a : ℕ → ℝ} (ha1 : ∀ j, (1 : ℝ) ≤ a j)
    {q : E → ℝ} {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    (hq : ContDiffOn ℝ ∞ q U)
    {A : ℕ → E → V}
    (x : E) (hx : x ∈ S) (hgt : (1 : ℝ) < q x) (m : ℕ) :
    iteratedFDeriv ℝ m
      (fun y => SolenoidalDiagonal.potentialSum a q
        (CutStageEstimates.positiveStages A) y) x = 0 := by
  let A' : ℕ → E → V := CutStageEstimates.positiveStages A
  have hxU : x ∈ U := hSU hx
  have hqAt : ContDiffAt ℝ ∞ q x := hq.contDiffAt (hU.mem_nhds hxU)
  have heq : (fun y => SolenoidalDiagonal.potentialSum a q A' y) =ᶠ[𝓝 x]
      (fun _ => (0 : V)) := by
    filter_upwards [hqAt.continuousAt
      (IsOpen.mem_nhds isOpen_Ioi (Set.mem_Ioi.mpr hgt))] with y hy
    show SolenoidalDiagonal.potentialSum a q A' y = 0
    show (∑' j : ℕ, SolenoidalDiagonal.cutStage a q A' j y) = 0
    have hzy : ∀ j : ℕ, SolenoidalDiagonal.cutStage a q A' j y = 0 := by
      intro j
      have haj : (1 : ℝ) ≤ a j := ha1 j
      have h0 : (0 : ℝ) < a j := by linarith
      have hinv : 1 / a j < q y := by
        calc (1 : ℝ) / a j ≤ 1 / 1 :=
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) haj
          _ = 1 := div_one 1
          _ < q y := hy
      have hz := SmoothCutoffs.scaledCutoff_zero_of_inv_le h0 hinv.le
      simp only [SolenoidalDiagonal.cutStage, hz, zero_smul]
    rw [tsum_congr hzy, tsum_zero]
  have h : iteratedFDeriv ℝ m (fun y => SolenoidalDiagonal.potentialSum a q A' y) x =
      iteratedFDeriv ℝ m (fun _ => (0 : V)) x :=
    (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq heq m).self_of_nhds
  rw [h, iteratedFDeriv_fun_zero, Pi.zero_apply]

/-- **(T1 — schedule summation.)** From the geometric diagonal stage bounds
over the estimate domain `S` alone (no global-openness of the bounds), the
actual positive-stage diagonal sum satisfies one negative-power envelope for
every derivative ceiling `m ≤ M`, uniformly over `S`: there are constants
`0 < C` and `0 ≤ β` with

    ‖iteratedFDeriv ℝ m (potentialSum a q (positiveStages A)) x‖ ≤ C * q x ^ (-β)

for all `m ≤ M`, `x ∈ S`. The finitely many stages whose derivative budget
`j + 2` falls below the ceiling are absorbed by the explicit table `K`
(pointwise sup bounds of their `m`-jets on `S`); every other prefix stage and
the whole tail come from `CutStageBounds` plus the prefix-gain inequality
`0 ≤ g (J + 1) - L m`. Off the sublevel `q > 1` the sum vanishes identically
in a neighborhood because every cutoff scale satisfies `1 / a j ≤ 1`. -/
theorem potentialSum_negPower_envelope
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (ha1 : ∀ j, (1 : ℝ) ≤ a j)
    {q : E → ℝ} {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    (hq : ContDiffOn ℝ ∞ q U) (hqpos : ∀ x ∈ S, 0 < q x)
    {A : ℕ → E → V} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    {g L : ℕ → ℝ} (hg : Monotone g) (hgtop : Tendsto g atTop atTop)
    (hgpos : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hb : DiagonalJetBounds.CutStageBounds a q
      (CutStageEstimates.positiveStages A) g L S)
    (M : ℕ) (K : ℕ → ℕ → ℝ)
    (hK : ∀ j m, j < M → m ≤ M → ∀ x ∈ S,
      ‖iteratedFDeriv ℝ m
        (SolenoidalDiagonal.cutStage a q (CutStageEstimates.positiveStages A) j) x‖ ≤ K j m) :
    ∃ C β : ℝ, 0 < C ∧ 0 ≤ β ∧ ∀ m ≤ M, ∀ x ∈ S,
      ‖iteratedFDeriv ℝ m
        (SolenoidalDiagonal.potentialSum a q (CutStageEstimates.positiveStages A)) x‖ ≤
        C * q x ^ (-β) := by
  -- Frozen numerical budget: no stage induction, no assembled object.
  obtain ⟨J, _hJmin, hJgeM, hgain⟩ :=
    DiagonalJetBounds.exists_prefix_gain g L hgtop M 0 0
  let β : ℝ := ∑ m ∈ Finset.range (M + 1), |L m|
  have hβ : 0 ≤ β := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hLβ : ∀ m ≤ M, L m ≤ β := by
    intro m hm
    have hsum : |L m| ≤ ∑ k ∈ Finset.range (M + 1), |L k| :=
      Finset.single_le_sum (f := fun k => |L k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega : m < M + 1))
    calc L m ≤ |L m| := le_abs_self _
      _ ≤ β := hsum
  let Cterm : ℝ := ∑ j ∈ Finset.range M, ∑ m ∈ Finset.range (M + 1), |K j m|
  let C : ℝ := 1 + Cterm + (J + 2 : ℝ) + (1 / 2 : ℝ) ^ J
  have hC : 0 < C := by
    show (0 : ℝ) < 1 + (∑ j ∈ Finset.range M, ∑ m ∈ Finset.range (M + 1), |K j m|) +
      (J + 2 : ℝ) + (1 / 2 : ℝ) ^ J
    positivity
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
  · -- Small-scale branch: tail plus frozen-prefix summation.
    have hsm : ContDiffAt ℝ ∞ (fun y => SolenoidalDiagonal.potentialSum a q A' y) x :=
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
    have hprefix : ‖iteratedFDeriv ℝ m
        (fun y => SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x‖ ≤
        Cterm + (J + 1 : ℝ) * q x ^ (-β) :=
      partialPotential_prefix_sum_sub hU hSU hq hqpos hA hgpos hb M K hK J hJgeM β hLβ
        m hm x hx hq1
    have hCterm0 : 0 ≤ Cterm :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hsub : iteratedFDeriv ℝ m (fun y => SolenoidalDiagonal.potentialSum a q A' y) x =
        iteratedFDeriv ℝ m (fun y => SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x +
          iteratedFDeriv ℝ m (fun y =>
            SolenoidalDiagonal.potentialSum a q A' y -
              SolenoidalDiagonal.partialPotential a q A' (J + 1) y) x := by
      rw [fun_iteratedFDeriv_sub_apply (hsm.of_le (nat_le_infty m))
        (hpr.of_le (nat_le_infty m))]
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
      _ ≤ (Cterm + (J + 1 : ℝ) * q x ^ (-β)) + (1 / 2 : ℝ) ^ J := add_le_add hprefix htail
      _ ≤ (Cterm * q x ^ (-β) + (J + 1 : ℝ) * q x ^ (-β)) +
          (1 / 2 : ℝ) ^ J * q x ^ (-β) :=
          add_le_add (add_le_add (hmul_le hCterm0) (le_refl _))
            (hmul_le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) J))
      _ = ((1 / 2 : ℝ) ^ J + Cterm + (J + 1 : ℝ)) * q x ^ (-β) := by ring
      _ ≤ C * q x ^ (-β) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hqx.le _)
          show (1 / 2 : ℝ) ^ J + (∑ j ∈ Finset.range M, ∑ m ∈ Finset.range (M + 1), |K j m|) +
              (J + 1 : ℝ) ≤
            1 + (∑ j ∈ Finset.range M, ∑ m ∈ Finset.range (M + 1), |K j m|) +
              (J + 2 : ℝ) + (1 / 2 : ℝ) ^ J
          linarith
  · -- Large-scale branch: the whole sum vanishes in a neighborhood of `x`.
    have hgt : (1 : ℝ) < q x := lt_of_not_ge hq1
    have hjet : iteratedFDeriv ℝ m (fun y => SolenoidalDiagonal.potentialSum a q A' y) x = 0 :=
      potentialSum_large_scale_vanishing_sub ha1 hU hSU hq x hx hgt m
    rw [hjet, norm_zero]
    exact mul_nonneg (le_of_lt hC) (Real.rpow_nonneg hqx.le _)

/-- **(T1 at the physical similarity coordinate.)** The same summation for
the actual `physicalQ h` coordinate on the preterminal spacetime domain, at
an actual natural-valued schedule. This is the format the stage machinery of
`MixedDiagonalSchedule` and the cut-candidate assembly emit, so the curl
transport (T3) can consume it directly at order `m = 1`. -/
theorem potentialSum_negPower_envelope_physical
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℕ} (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop)
    (ha1 : ∀ j, 0 < a j)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set ProblemStatement.SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A : ℕ → ProblemStatement.SpaceTime → V}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) PhysicalWaveSum.preterminal)
    {g L : ℕ → ℝ} (hg : Monotone g) (hgtop : Tendsto g atTop atTop)
    (hgpos : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hb : DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A) g L S)
    (M : ℕ) (K : ℕ → ℕ → ℝ)
    (hK : ∀ j m, j < M → m ≤ M → ∀ x ∈ S,
      ‖iteratedFDeriv ℝ m (SolenoidalDiagonal.cutStage (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A) j) x‖ ≤ K j m) :
    ∃ C β : ℝ, 0 < C ∧ 0 ≤ β ∧ ∀ m ≤ M, ∀ x ∈ S,
      ‖iteratedFDeriv ℝ m (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A)) x‖ ≤
        C * PhysicalWaveSum.physicalQ h x ^ (-β) :=
  potentialSum_negPower_envelope
    (E := ProblemStatement.SpaceTime)
    (a := fun j => (a j : ℝ))
    (q := PhysicalWaveSum.physicalQ h)
    (U := PhysicalWaveSum.preterminal)
    ha (fun j => by exact_mod_cast ha1 j)
    PhysicalWaveSum.preterminal_open hS
    (fun w hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt)
    (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 (hS hw))
    hA hg hgtop hgpos hb M K hK

#print axioms Navier.Construction.CSPotentialSumEnvelope.finite_sum_jet
#print axioms Navier.Construction.CSPotentialSumEnvelope.potentialSum_tail_jet_sub
#print axioms Navier.Construction.CSPotentialSumEnvelope.partialPotential_prefix_sum_sub
#print axioms Navier.Construction.CSPotentialSumEnvelope.potentialSum_large_scale_vanishing_sub
#print axioms Navier.Construction.CSPotentialSumEnvelope.potentialSum_negPower_envelope
#print axioms Navier.Construction.CSPotentialSumEnvelope.potentialSum_negPower_envelope_physical

end Navier.Construction.CSPotentialSumEnvelope
