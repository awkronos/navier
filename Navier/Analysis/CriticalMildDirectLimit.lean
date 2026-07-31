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

open Set
open Navier
open Navier.Analysis.CriticalMildCompatibleSuccessor
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildRestrictionCompatibility
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

end Navier.Analysis.CriticalMildDirectLimit

#print axioms Navier.Analysis.CriticalMildDirectLimit.criticalMildChainValue_eq_stage
#print axioms Navier.Analysis.CriticalMildDirectLimit.criticalMildChainValue_divergenceFree
