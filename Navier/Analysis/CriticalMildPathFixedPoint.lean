import Navier.Analysis.CriticalMildImageObservationContinuity
import Navier.Analysis.CriticalMildPathContraction

/-!
# Critical mild path-space fixed-point carrier

The local path carrier is the complete continuous-map space on `Icc 0 T`.
For use by the existing literal Duhamel estimates, its canonical `IccExtend`
clamp supplies a globally continuous representative without extra data.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildPathFixedPoint

open Set Topology
open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathContraction

/-- The complete local carrier used for a critical mild fixed point. -/
abbrev CriticalMildPath (T : ℝ) := WeightedMildPath T

/-- The canonical globally continuous representative of a local path, constant
outside the closed time interval through the order projection onto `Icc 0 T`. -/
def criticalMildPathExtension
    (T : ℝ) (hT : 0 ≤ T) (u : CriticalMildPath T) :
    ℝ → WeightedLatticeBanach :=
  IccExtend hT u

theorem continuous_criticalMildPathExtension
    (T : ℝ) (hT : 0 ≤ T) (u : CriticalMildPath T) :
    Continuous (criticalMildPathExtension T hT u) := by
  exact u.continuous.Icc_extend'

theorem criticalMildPathExtension_apply
    (T : ℝ) (hT : 0 ≤ T) (u : CriticalMildPath T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    criticalMildPathExtension T hT u t = u ⟨t, ht⟩ := by
  exact IccExtend_of_mem hT u ht

/-- The radius/divergence-free local ball, represented as a subtype of the
complete continuous path carrier. -/
def CriticalMildPathBall (T R : ℝ) :=
  {u : CriticalMildPath T //
    ∀ t : Icc (0 : ℝ) T,
      LatticeDivergenceFree (u t) ∧ ‖u t‖ ≤ R}

theorem criticalMildPathBall_divergenceFree
    {T R : ℝ} (u : CriticalMildPathBall T R) (t : Icc (0 : ℝ) T) :
    LatticeDivergenceFree (u.1 t) :=
  (u.2 t).1

theorem criticalMildPathBall_norm_le
    {T R : ℝ} (u : CriticalMildPathBall T R) (t : Icc (0 : ℝ) T) :
    ‖u.1 t‖ ≤ R :=
  (u.2 t).2

end Navier.Analysis.CriticalMildPathFixedPoint

#print axioms Navier.Analysis.CriticalMildPathFixedPoint.continuous_criticalMildPathExtension
#print axioms Navier.Analysis.CriticalMildPathFixedPoint.criticalMildPathExtension_apply
