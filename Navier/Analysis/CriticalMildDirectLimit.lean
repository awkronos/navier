import Navier.Analysis.CriticalMildCompatibleSuccessor

/-!
# Direct-limit carrier for a compatible critical mild chain

This is finite-stage coherence infrastructure only.  It defines values on the
literal union of reached closed intervals; it does not establish unboundedness
of that union or a solution beyond it.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildDirectLimit

open Set Filter MeasureTheory
open scoped Topology
open Navier
open Navier.Analysis.CriticalMildCompatibleSuccessor
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildRestrictionCompatibility
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildWeightedBanach

/-- The literal union of all finite closed horizons in the compatible chain. -/
structure CriticalMildCoherentChain (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) where
  horizon : ℕ → ℝ
  radius : ℕ → ℝ
  horizon_nonneg : ∀ n, 0 ≤ horizon n
  path : ∀ n, CriticalMildPathBall (horizon n) (radius n)
  mild : ∀ n (τ : Icc (0 : ℝ) (horizon n)),
    (path n).1 τ = criticalMildImage ν hν a
      (criticalMildPathExtension (horizon n) (horizon_nonneg n) (path n).1)
      (criticalMildPathBallExtension_divergenceFree (horizon_nonneg n) (path n)) τ.1 τ.2.1
  horizon_mono : Monotone horizon
  pairwise : ∀ {m n : ℕ} (hmn : m ≤ n),
    criticalMildPathRestrict (horizon_mono hmn) (path n).1 = (path m).1
  strict_local_extension : ∀ n, horizon n < horizon (n + 1)

namespace CriticalMildCoherentChain

def domain {ν : ℝ} {hν : 0 < ν} {a : WeightedLatticeBanach}
    (C : CriticalMildCoherentChain ν hν a) : Set ℝ :=
  {t | ∃ n : ℕ, t ∈ Icc (0 : ℝ) (C.horizon n)}

def index {ν : ℝ} {hν : 0 < ν} {a : WeightedLatticeBanach}
    (C : CriticalMildCoherentChain ν hν a) (t : ℝ) (ht : t ∈ C.domain) : ℕ :=
  Classical.choose ht

theorem index_spec {ν : ℝ} {hν : 0 < ν} {a : WeightedLatticeBanach}
    (C : CriticalMildCoherentChain ν hν a) (t : ℝ) (ht : t ∈ C.domain) :
    t ∈ Icc (0 : ℝ) (C.horizon (C.index t ht)) :=
  Classical.choose_spec ht

def value {ν : ℝ} {hν : 0 < ν} {a : WeightedLatticeBanach}
    (C : CriticalMildCoherentChain ν hν a) (t : ℝ) (ht : t ∈ C.domain) :
    WeightedLatticeBanach :=
  (C.path (C.index t ht)).1 ⟨t, C.index_spec t ht⟩

theorem value_eq_stage {ν : ℝ} {hν : 0 < ν} {a : WeightedLatticeBanach}
    (C : CriticalMildCoherentChain ν hν a) {t : ℝ} (ht : t ∈ C.domain)
    (n : ℕ) (hn : t ∈ Icc (0 : ℝ) (C.horizon n)) :
    C.value t ht = (C.path n).1 ⟨t, hn⟩ := by
  let k := C.index t ht
  have hk := C.index_spec t ht
  change (C.path k).1 ⟨t, hk⟩ = _
  rcases le_total k n with hkn | hnk
  · have hpair := C.pairwise hkn
    rw [← hpair]
    rfl
  · have hpair := C.pairwise hnk
    have happ := ContinuousMap.congr_fun hpair ⟨t, hn⟩
    simpa [criticalMildPathRestrict, criticalMildTimeInclusion] using happ

def totalExtension {ν : ℝ} {hν : 0 < ν} {a : WeightedLatticeBanach}
    (C : CriticalMildCoherentChain ν hν a) : ℝ → WeightedLatticeBanach := by
  classical
  exact fun t => if ht : t ∈ C.domain then C.value t ht else 0

theorem totalExtension_divergenceFree {ν : ℝ} {hν : 0 < ν} {a : WeightedLatticeBanach}
    (C : CriticalMildCoherentChain ν hν a) (t : ℝ) :
    LatticeDivergenceFree (C.totalExtension t) := by
  classical
  by_cases ht : t ∈ C.domain
  · rw [totalExtension, dif_pos ht]
    have hdom := ht
    obtain ⟨n, hn⟩ := ht
    rw [C.value_eq_stage hdom n hn]
    exact criticalMildPathBall_divergenceFree (C.path n) ⟨t, hn⟩
  · rw [totalExtension, dif_neg ht]
    unfold LatticeDivergenceFree
    intro m
    simp [weightedLatticeCoefficient, ComplexLerayNorm.complexEuclideanPoint]

theorem totalExtension_eq_stage {ν : ℝ} {hν : 0 < ν} {a : WeightedLatticeBanach}
    (C : CriticalMildCoherentChain ν hν a) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (C.horizon n)) :
    C.totalExtension t = (C.path n).1 ⟨t, ht⟩ := by
  classical
  have hdom : t ∈ C.domain := ⟨n, ht⟩
  rw [totalExtension, dif_pos hdom]
  exact C.value_eq_stage hdom n ht

theorem pathIntegrand_totalExtension_eq_stage {ν : ℝ} {hν : 0 < ν}
    {a : WeightedLatticeBanach} (C : CriticalMildCoherentChain ν hν a) (n : ℕ)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) (C.horizon n)) (hs : s ∈ Ioc (0 : ℝ) t) :
    criticalMildPathIntegrand ν hν (C.totalExtension)
      (C.totalExtension_divergenceFree) t s =
      criticalMildPathIntegrand ν hν
        (criticalMildPathExtension (C.horizon n) (C.horizon_nonneg n) (C.path n).1)
        (criticalMildPathBallExtension_divergenceFree (C.horizon_nonneg n) (C.path n)) t s := by
  have hsIcc : s ∈ Icc (0 : ℝ) (C.horizon n) :=
    ⟨hs.1.le, le_trans hs.2 ht.2⟩
  have heq := C.totalExtension_eq_stage n hsIcc
  have hstage := criticalMildPathExtension_apply (C.horizon n) (C.horizon_nonneg n)
    (C.path n).1 hsIcc
  unfold criticalMildPathIntegrand
  congr 1
  · exact heq.trans hstage.symm
  · exact heq.trans hstage.symm

theorem duhamel_totalExtension_eq_stage {ν : ℝ} {hν : 0 < ν}
    {a : WeightedLatticeBanach} (C : CriticalMildCoherentChain ν hν a) (n : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (C.horizon n)) :
    criticalMildDuhamel ν hν C.totalExtension C.totalExtension_divergenceFree t =
      criticalMildDuhamel ν hν
        (criticalMildPathExtension (C.horizon n) (C.horizon_nonneg n) (C.path n).1)
        (criticalMildPathBallExtension_divergenceFree (C.horizon_nonneg n) (C.path n)) t := by
  unfold criticalMildDuhamel
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact C.pathIntegrand_totalExtension_eq_stage n ht hs

theorem value_satisfies_original_mild {ν : ℝ} {hν : 0 < ν}
    {a : WeightedLatticeBanach} (C : CriticalMildCoherentChain ν hν a)
    {t : ℝ} (ht : t ∈ C.domain) (ht0 : 0 ≤ t) :
    C.value t ht = criticalMildImage ν hν a C.totalExtension
      C.totalExtension_divergenceFree t ht0 := by
  have hdom := ht
  obtain ⟨n, htn⟩ := ht
  rw [C.value_eq_stage hdom n htn]
  rw [C.mild n ⟨t, htn⟩]
  unfold criticalMildImage
  rw [C.duhamel_totalExtension_eq_stage n htn]

def CofinalLifespan {ν : ℝ} {hν : 0 < ν} {a : WeightedLatticeBanach}
    (C : CriticalMildCoherentChain ν hν a) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ∈ C.domain

theorem totalExtension_satisfies_mild_of_cofinal {ν : ℝ} {hν : 0 < ν}
    {a : WeightedLatticeBanach} (C : CriticalMildCoherentChain ν hν a)
    (hcofinal : C.CofinalLifespan) : ∀ t : ℝ, ∀ ht : 0 ≤ t,
      C.totalExtension t = criticalMildImage ν hν a C.totalExtension
        C.totalExtension_divergenceFree t ht := by
  intro t ht
  have hdom := hcofinal t ht
  rw [totalExtension, dif_pos hdom]
  exact C.value_satisfies_original_mild hdom ht

/-- If a coherent chain reaches every nonnegative time, its total extension
is continuous on the nonnegative-time subtype.  This makes no assertion about
the zero branch on negative times. -/
theorem continuous_totalExtension_on_nonneg_of_cofinal {ν : ℝ} {hν : 0 < ν}
    {a : WeightedLatticeBanach} (C : CriticalMildCoherentChain ν hν a)
    (hcofinal : C.CofinalLifespan) :
    Continuous (fun t : Ici (0 : ℝ) => C.totalExtension t.1) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨n, hxn⟩ := hcofinal x.1 x.2
  have hnext := C.strict_local_extension n
  let ε : ℝ := (C.horizon (n + 1) - x.1) / 2
  have hε : 0 < ε := by
    have hmargin : 0 < C.horizon (n + 1) - x.1 := by
      linarith [hxn.2, hnext]
    dsimp [ε]
    positivity
  apply ContinuousAt.congr_of_eventuallyEq
    ((continuous_criticalMildPathExtension _ (C.horizon_nonneg (n + 1))
      (C.path (n + 1)).1).comp continuous_subtype_val).continuousAt
  refine Metric.eventually_nhds_iff.2 ⟨ε, hε, ?_⟩
  intro y hy
  have hysucc : y.1 ≤ C.horizon (n + 1) := by
    have habs : |y.1 - x.1| < ε := by
      change dist y.1 x.1 < ε at hy
      simpa [Real.dist_eq] using hy
    dsimp [ε] at habs
    have hupper := (abs_lt.mp habs).2
    have hxnext : x.1 < C.horizon (n + 1) := lt_of_le_of_lt hxn.2 hnext
    have hhalf : (C.horizon (n + 1) - x.1) / 2 <
        C.horizon (n + 1) - x.1 := half_lt_self (sub_pos.mpr hxnext)
    have hyGap : y.1 - x.1 < C.horizon (n + 1) - x.1 := lt_trans hupper hhalf
    linarith
  have hyIcc : y.1 ∈ Icc (0 : ℝ) (C.horizon (n + 1)) := ⟨y.2, hysucc⟩
  change C.totalExtension y.1 =
    criticalMildPathExtension (C.horizon (n + 1))
      (C.horizon_nonneg (n + 1)) (C.path (n + 1)).1 y.1
  rw [C.totalExtension_eq_stage (n + 1) hyIcc]
  rw [criticalMildPathExtension_apply _ (C.horizon_nonneg (n + 1)) _ hyIcc]

end CriticalMildCoherentChain

end Navier.Analysis.CriticalMildDirectLimit

#print axioms Navier.Analysis.CriticalMildDirectLimit.CriticalMildCoherentChain.value_eq_stage
#print axioms Navier.Analysis.CriticalMildDirectLimit.CriticalMildCoherentChain.continuous_totalExtension_on_nonneg_of_cofinal
