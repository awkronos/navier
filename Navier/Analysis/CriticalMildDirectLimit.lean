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
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildRestrictionCompatibility
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildWeightedBanach

/-- The literal union of all finite closed horizons in the compatible chain. -/
def criticalMildChainDomain (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) : Set ℝ :=
  {t | ∃ n : ℕ, t ∈ Icc (0 : ℝ) (criticalMildCompatibleChain ν hν a n).horizon}

/-- A chosen chain index witnessing that a time belongs to the finite union. -/
def criticalMildChainIndex (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (t : ℝ) (ht : t ∈ criticalMildChainDomain ν hν a) : ℕ :=
  Classical.choose ht

theorem criticalMildChainIndex_spec (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (t : ℝ) (ht : t ∈ criticalMildChainDomain ν hν a) :
    t ∈ Icc (0 : ℝ) (criticalMildCompatibleChain ν hν a
      (criticalMildChainIndex ν hν a t ht)).horizon :=
  Classical.choose_spec ht

/-- The direct-limit value, initially written using an arbitrary witnessing
index.  The independence theorem below shows that this choice is immaterial. -/
def criticalMildChainValue (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (t : ℝ) (ht : t ∈ criticalMildChainDomain ν hν a) : WeightedLatticeBanach :=
  (criticalMildCompatibleChain ν hν a (criticalMildChainIndex ν hν a t ht)).path.1
    ⟨t, criticalMildChainIndex_spec ν hν a t ht⟩

/-- Any chain stage containing a time gives the same direct-limit value. -/
theorem criticalMildChainValue_eq_stage
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) {t : ℝ}
    (ht : t ∈ criticalMildChainDomain ν hν a) (n : ℕ)
    (hn : t ∈ Icc (0 : ℝ) (criticalMildCompatibleChain ν hν a n).horizon) :
    criticalMildChainValue ν hν a t ht =
      (criticalMildCompatibleChain ν hν a n).path.1 ⟨t, hn⟩ := by
  let k := criticalMildChainIndex ν hν a t ht
  have hk := criticalMildChainIndex_spec ν hν a t ht
  change (criticalMildCompatibleChain ν hν a k).path.1 ⟨t, hk⟩ = _
  rcases le_total k n with hkn | hnk
  · have hpair := criticalMildCompatibleChain_pairwise ν hν a hkn
    rw [← hpair]
    rfl
  · have hpair := criticalMildCompatibleChain_pairwise ν hν a hnk
    have happ := ContinuousMap.congr_fun hpair ⟨t, hn⟩
    simpa [criticalMildPathRestrict, criticalMildTimeInclusion] using happ

/-- The direct-limit value is divergence free at every reached time. -/
theorem criticalMildChainValue_divergenceFree
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) {t : ℝ}
    (ht : t ∈ criticalMildChainDomain ν hν a) :
    LatticeDivergenceFree (criticalMildChainValue ν hν a t ht) := by
  let n := criticalMildChainIndex ν hν a t ht
  have hn := criticalMildChainIndex_spec ν hν a t ht
  rw [criticalMildChainValue_eq_stage ν hν a ht n hn]
  exact criticalMildPathBall_divergenceFree
    (criticalMildCompatibleChain ν hν a n).path ⟨t, hn⟩

/-- The direct-limit path as a function on the union-domain subtype. -/
def criticalMildChainPath (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    criticalMildChainDomain ν hν a → WeightedLatticeBanach :=
  fun t => criticalMildChainValue ν hν a t.1 t.2

/-- A total representative of the union path, set to zero outside the literal
union-domain.  The zero branch is only an integration carrier; no equation is
asserted there. -/
def criticalMildChainTotalExtension (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    ℝ → WeightedLatticeBanach := by
  classical
  exact fun t => if ht : t ∈ criticalMildChainDomain ν hν a then
    criticalMildChainValue ν hν a t ht else 0

theorem criticalMildChainTotalExtension_divergenceFree
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (t : ℝ) :
    LatticeDivergenceFree (criticalMildChainTotalExtension ν hν a t) := by
  classical
  by_cases ht : t ∈ criticalMildChainDomain ν hν a
  · rw [criticalMildChainTotalExtension, dif_pos ht]
    exact criticalMildChainValue_divergenceFree ν hν a ht
  · rw [criticalMildChainTotalExtension, dif_neg ht]
    unfold LatticeDivergenceFree
    intro m
    simp [weightedLatticeCoefficient, ComplexLerayNorm.complexEuclideanPoint]

/-- On every reached stage interval, the total representative is exactly that
stage's path. -/
theorem criticalMildChainTotalExtension_eq_stage
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (criticalMildCompatibleChain ν hν a n).horizon) :
    criticalMildChainTotalExtension ν hν a t =
      (criticalMildCompatibleChain ν hν a n).path.1 ⟨t, ht⟩ := by
  classical
  have hdom : t ∈ criticalMildChainDomain ν hν a := ⟨n, ht⟩
  rw [criticalMildChainTotalExtension, dif_pos hdom]
  exact criticalMildChainValue_eq_stage ν hν a hdom n ht

/-- The nonlinear integrands agree on the actual integration interval of any
containing stage. -/
theorem criticalMildPathIntegrand_totalExtension_eq_stage
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (n : ℕ)
    {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (criticalMildCompatibleChain ν hν a n).horizon)
    (hs : s ∈ Ioc (0 : ℝ) t) :
    criticalMildPathIntegrand ν hν (criticalMildChainTotalExtension ν hν a)
      (criticalMildChainTotalExtension_divergenceFree ν hν a) t s =
      criticalMildPathIntegrand ν hν
        (criticalMildPathExtension
          (criticalMildCompatibleChain ν hν a n).horizon
          (criticalMildCompatibleChain ν hν a n).horizon_nonneg
          (criticalMildCompatibleChain ν hν a n).path.1)
        (criticalMildPathBallExtension_divergenceFree
          (criticalMildCompatibleChain ν hν a n).horizon_nonneg
          (criticalMildCompatibleChain ν hν a n).path) t s := by
  have hsIcc : s ∈ Icc (0 : ℝ)
      (criticalMildCompatibleChain ν hν a n).horizon :=
    ⟨hs.1.le, le_trans hs.2 ht.2⟩
  have heq := criticalMildChainTotalExtension_eq_stage ν hν a n hsIcc
  have hstage := criticalMildPathExtension_apply
    (criticalMildCompatibleChain ν hν a n).horizon
    (criticalMildCompatibleChain ν hν a n).horizon_nonneg
    (criticalMildCompatibleChain ν hν a n).path.1 hsIcc
  unfold criticalMildPathIntegrand
  congr 1
  · exact heq.trans hstage.symm
  · exact heq.trans hstage.symm

/-- The literal Duhamel integral of the total union extension agrees with
every stage containing its observation time. -/
theorem criticalMildDuhamel_totalExtension_eq_stage
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (criticalMildCompatibleChain ν hν a n).horizon) :
    criticalMildDuhamel ν hν (criticalMildChainTotalExtension ν hν a)
      (criticalMildChainTotalExtension_divergenceFree ν hν a) t =
      criticalMildDuhamel ν hν
        (criticalMildPathExtension
          (criticalMildCompatibleChain ν hν a n).horizon
          (criticalMildCompatibleChain ν hν a n).horizon_nonneg
          (criticalMildCompatibleChain ν hν a n).path.1)
        (criticalMildPathBallExtension_divergenceFree
          (criticalMildCompatibleChain ν hν a n).horizon_nonneg
          (criticalMildCompatibleChain ν hν a n).path) t := by
  unfold criticalMildDuhamel
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact criticalMildPathIntegrand_totalExtension_eq_stage ν hν a n ht hs


/-- Locally, a union-domain value is represented by the canonical extension
of one strict successor stage. -/
theorem criticalMildChainPath_eventually_eq_successorExtension
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (x : criticalMildChainDomain ν hν a) :
    ∃ n : ℕ, ∀ᶠ y in 𝓝 x,
      criticalMildChainPath ν hν a y =
        criticalMildPathExtension
          (criticalMildCompatibleChain ν hν a (n + 1)).horizon
          (criticalMildCompatibleChain ν hν a (n + 1)).horizon_nonneg
          (criticalMildCompatibleChain ν hν a (n + 1)).path.1 y.1 := by
  obtain ⟨n, hxn⟩ := x.2
  obtain ⟨hnext, _⟩ := criticalMildCompatibleChain_adjacent ν hν a n
  let ε : ℝ := ((criticalMildCompatibleChain ν hν a (n + 1)).horizon - x.1) / 2
  have hε : 0 < ε := by
    have hmargin : 0 <
        (criticalMildCompatibleChain ν hν a (n + 1)).horizon - x.1 := by
      linarith [hxn.2, hnext]
    dsimp [ε]
    linarith [hmargin]
  refine ⟨n, Metric.eventually_nhds_iff.2 ⟨ε, hε, ?_⟩⟩
  intro y hy
  have hy0 : 0 ≤ y.1 := by
    obtain ⟨k, hyk⟩ := y.2
    exact hyk.1
  have hysucc : y.1 ≤ (criticalMildCompatibleChain ν hν a (n + 1)).horizon := by
    have habs : |y.1 - x.1| < ε := by
      change dist y.1 x.1 < ε at hy
      simpa [Real.dist_eq] using hy
    dsimp [ε] at habs
    have hupper := (abs_lt.mp habs).2
    have hmargin : 0 <
        (criticalMildCompatibleChain ν hν a (n + 1)).horizon - x.1 := by
      dsimp [ε] at hε
      linarith
    linarith
  have hyIcc : y.1 ∈ Icc (0 : ℝ)
      (criticalMildCompatibleChain ν hν a (n + 1)).horizon := ⟨hy0, hysucc⟩
  change criticalMildChainValue ν hν a y.1 y.2 = _
  rw [criticalMildChainValue_eq_stage ν hν a y.2 (n + 1) hyIcc]
  rw [criticalMildPathExtension_apply _
    (criticalMildCompatibleChain ν hν a (n + 1)).horizon_nonneg _ hyIcc]

/-- The choice-independent direct-limit path is continuous on its literal
union-domain subtype. -/
theorem continuous_criticalMildChainPath
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    Continuous (criticalMildChainPath ν hν a) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨n, hevent⟩ := criticalMildChainPath_eventually_eq_successorExtension ν hν a x
  apply ContinuousAt.congr_of_eventuallyEq
    ((continuous_criticalMildPathExtension _
      (criticalMildCompatibleChain ν hν a (n + 1)).horizon_nonneg
      (criticalMildCompatibleChain ν hν a (n + 1)).path.1).comp
        continuous_subtype_val).continuousAt hevent

end Navier.Analysis.CriticalMildDirectLimit

#print axioms Navier.Analysis.CriticalMildDirectLimit.criticalMildChainValue_eq_stage
#print axioms Navier.Analysis.CriticalMildDirectLimit.criticalMildChainValue_divergenceFree
#print axioms Navier.Analysis.CriticalMildDirectLimit.continuous_criticalMildChainPath
#print axioms Navier.Analysis.CriticalMildDirectLimit.criticalMildPathIntegrand_totalExtension_eq_stage
#print axioms Navier.Analysis.CriticalMildDirectLimit.criticalMildDuhamel_totalExtension_eq_stage
