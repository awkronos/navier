import Navier.Analysis.CriticalMildRestart

/-!
# Terminal-data restart for the critical mild ball

The restart radius is deliberately fresh data.  No estimate here identifies a
new radius with the radius of an earlier trajectory.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildRestartFixedPoint

open Set
open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildRestart
open Navier.Analysis.CriticalMildSelfMap

/-- The terminal datum of a local trajectory, viewed in the completed carrier. -/
def criticalMildPathTerminalData
    {T R : ℝ} (u : CriticalMildPathBall T R) (t : Icc (0 : ℝ) T) :
    WeightedLatticeBanach := u.1 t

/-- The original fixed-point trajectory satisfies the restart identity at any
later point inside its closed horizon. -/
theorem criticalMildRestartImage_eq_fixedPoint_trajectory
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (u : CriticalMildPathBall T R)
    (htraj : ∀ τ : Icc (0 : ℝ) T,
      u.1 τ = criticalMildImage ν hν u₀
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1)
    {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (htr : t + r ≤ T) :
    criticalMildRestartImage ν hν
      (criticalMildPathExtension T hT u.1)
      (criticalMildPathBallExtension_divergenceFree hT u) t r hr =
        criticalMildPathExtension T hT u.1 (t + r) := by
  have htmem : t ∈ Icc (0 : ℝ) T :=
    ⟨ht, le_trans (le_add_of_nonneg_right hr) htr⟩
  have htrmem : t + r ∈ Icc (0 : ℝ) T := ⟨add_nonneg ht hr, htr⟩
  have hmild_t : criticalMildPathExtension T hT u.1 t =
      criticalMildImage ν hν u₀ (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) t ht := by
    rw [criticalMildPathExtension_apply T hT u.1 htmem]
    exact htraj ⟨t, htmem⟩
  have hmild_tr : criticalMildPathExtension T hT u.1 (t + r) =
      criticalMildImage ν hν u₀ (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) (t + r)
          (add_nonneg ht hr) := by
    rw [criticalMildPathExtension_apply T hT u.1 htrmem]
    exact htraj ⟨t + r, htrmem⟩
  exact criticalMildRestartImage_eq_shifted_trajectory
    ν hν u₀ (criticalMildPathExtension T hT u.1)
    (continuous_criticalMildPathExtension T hT u.1)
    (criticalMildPathBallExtension_divergenceFree hT u) hR ht hr
    (fun s hs => criticalMildPathBallExtension_norm_le hT u s)
    hmild_t hmild_tr

/-- The terminal-data local mild map preserves its explicitly chosen
subsequent radius ball. -/
def criticalMildTerminalRestartBallImage
    (ν : ℝ) (hν : 0 < ν)
    {T R S R' : ℝ} (u : CriticalMildPathBall T R)
    (t : Icc (0 : ℝ) T)
    (hS : 0 ≤ S) (hR' : 0 ≤ R')
    (hbudget : ‖criticalMildPathTerminalData u t‖ +
      (2 * Real.sqrt S / Real.sqrt ν) * R' ^ 2 ≤ R') :
    CriticalMildPathBall S R' → CriticalMildPathBall S R' :=
  criticalMildPathBallImage ν hν (criticalMildPathTerminalData u t)
    hS hR' hbudget

/-- Under fresh explicit radius and smallness hypotheses, terminal data has a
unique fixed point in the subsequent local ball. -/
theorem existsUnique_criticalMildTerminalRestart_fixedPoint
    (ν : ℝ) (hν : 0 < ν)
    {T R S R' : ℝ} (u : CriticalMildPathBall T R)
    (t : Icc (0 : ℝ) T)
    (hS : 0 ≤ S) (hR' : 0 ≤ R')
    (hbudget : ‖criticalMildPathTerminalData u t‖ +
      (2 * Real.sqrt S / Real.sqrt ν) * R' ^ 2 ≤ R')
    (hcontr : (4 * Real.sqrt S / Real.sqrt ν) * R' < 1) :
    ∃! v : CriticalMildPathBall S R',
      Function.IsFixedPt
        (criticalMildTerminalRestartBallImage ν hν u t hS hR' hbudget) v := by
  change ∃! v : CriticalMildPathBall S R', Function.IsFixedPt
    (criticalMildPathBallImage ν hν (criticalMildPathTerminalData u t)
      hS hR' hbudget) v
  obtain ⟨v, hv⟩ := exists_criticalMildPathBall_fixedPoint
    ν hν (criticalMildPathTerminalData u t) hS hR' hbudget hcontr
  refine ⟨v, ?_, ?_⟩
  · exact hv
  · intro w hw
    exact criticalMildPathBall_fixedPoint_unique
      ν hν (criticalMildPathTerminalData u t) hS hR' hbudget hcontr hw hv

/-- The unique subsequent fixed point is an actual terminal-data local mild
trajectory on its own explicitly supplied radius ball. -/
theorem exists_criticalMildTerminalRestart_trajectory
    (ν : ℝ) (hν : 0 < ν)
    {T R S R' : ℝ} (u : CriticalMildPathBall T R)
    (t : Icc (0 : ℝ) T)
    (hS : 0 ≤ S) (hR' : 0 ≤ R')
    (hbudget : ‖criticalMildPathTerminalData u t‖ +
      (2 * Real.sqrt S / Real.sqrt ν) * R' ^ 2 ≤ R')
    (hcontr : (4 * Real.sqrt S / Real.sqrt ν) * R' < 1) :
    ∃ v : CriticalMildPathBall S R',
      ∀ σ : Icc (0 : ℝ) S,
        v.1 σ = criticalMildImage ν hν (criticalMildPathTerminalData u t)
          (criticalMildPathExtension S hS v.1)
          (criticalMildPathBallExtension_divergenceFree hS v) σ.1 σ.2.1 := by
  exact exists_criticalMild_trajectory
    ν hν (criticalMildPathTerminalData u t) hS hR' hbudget hcontr

end Navier.Analysis.CriticalMildRestartFixedPoint

#print axioms Navier.Analysis.CriticalMildRestartFixedPoint.criticalMildRestartImage_eq_fixedPoint_trajectory
#print axioms Navier.Analysis.CriticalMildRestartFixedPoint.existsUnique_criticalMildTerminalRestart_fixedPoint
#print axioms Navier.Analysis.CriticalMildRestartFixedPoint.exists_criticalMildTerminalRestart_trajectory
