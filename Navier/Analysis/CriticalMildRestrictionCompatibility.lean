import Navier.Analysis.CriticalMildLocalSelection

/-!
# Restriction compatibility for critical mild paths

This module proves that constructed compatible finite-horizon mild paths
restrict correctly. The direct-limit construction uses this compatibility
in `CriticalMildDirectLimit`.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildRestrictionCompatibility

open MeasureTheory Set
open Navier
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildLocalSelection
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildWeightedBanach

/-- The inclusion of the earlier closed time interval into a later one. -/
def criticalMildTimeInclusion {T T' : ℝ} (hTT' : T ≤ T') :
    Icc (0 : ℝ) T → Icc (0 : ℝ) T' :=
  fun τ => ⟨τ.1, ⟨τ.2.1, le_trans τ.2.2 hTT'⟩⟩

theorem continuous_criticalMildTimeInclusion {T T' : ℝ} (hTT' : T ≤ T') :
    Continuous (criticalMildTimeInclusion hTT') := by
  apply Continuous.subtype_mk continuous_subtype_val

/-- Restrict a continuous critical mild path to an earlier horizon. -/
def criticalMildPathRestrict {T T' : ℝ} (hTT' : T ≤ T')
    (u : CriticalMildPath T') : CriticalMildPath T :=
  u.comp ⟨criticalMildTimeInclusion hTT', continuous_criticalMildTimeInclusion hTT'⟩

@[simp] theorem criticalMildPathRestrict_apply {T T' : ℝ} (hTT' : T ≤ T')
    (u : CriticalMildPath T') (τ : Icc (0 : ℝ) T) :
    criticalMildPathRestrict hTT' u τ = u (criticalMildTimeInclusion hTT' τ) := rfl

/-- Restricting along two nested time inclusions is the same underlying path
as restricting once along their composite inclusion. -/
theorem criticalMildPathRestrict_trans {T₀ T₁ T₂ : ℝ}
    (h₀₁ : T₀ ≤ T₁) (h₁₂ : T₁ ≤ T₂) (u : CriticalMildPath T₂) :
    criticalMildPathRestrict h₀₁ (criticalMildPathRestrict h₁₂ u) =
      criticalMildPathRestrict (le_trans h₀₁ h₁₂) u := by
  apply ContinuousMap.ext
  intro τ
  rfl

/-- Restriction preserves the divergence-free and radius constraints. -/
def criticalMildPathBallRestrict {T T' R : ℝ} (hTT' : T ≤ T')
    (u : CriticalMildPathBall T' R) : CriticalMildPathBall T R :=
  ⟨criticalMildPathRestrict hTT' u.1, fun τ => u.2 (criticalMildTimeInclusion hTT' τ)⟩

@[simp] theorem criticalMildPathBallRestrict_apply {T T' R : ℝ} (hTT' : T ≤ T')
    (u : CriticalMildPathBall T' R) (τ : Icc (0 : ℝ) T) :
    (criticalMildPathBallRestrict hTT' u).1 τ = u.1 (criticalMildTimeInclusion hTT' τ) := rfl

/-- The restriction inherits divergence freedom pointwise. -/
theorem criticalMildPathBallRestrict_divergenceFree {T T' R : ℝ} (hTT' : T ≤ T')
    (u : CriticalMildPathBall T' R) (τ : Icc (0 : ℝ) T) :
    LatticeDivergenceFree ((criticalMildPathBallRestrict hTT' u).1 τ) :=
  (criticalMildPathBallRestrict hTT' u).2 τ |>.1

/-- The restriction inherits exactly the same radius bound. -/
theorem criticalMildPathBallRestrict_norm_le {T T' R : ℝ} (hTT' : T ≤ T')
    (u : CriticalMildPathBall T' R) (τ : Icc (0 : ℝ) T) :
    ‖(criticalMildPathBallRestrict hTT' u).1 τ‖ ≤ R :=
  (criticalMildPathBallRestrict hTT' u).2 τ |>.2

/-- On the earlier interval, the canonical extensions of a path and its
restriction agree pointwise. -/
theorem criticalMildPathExtension_restrict_eq {T T' : ℝ} (hT : 0 ≤ T)
    (hT' : 0 ≤ T') (hTT' : T ≤ T') (u : CriticalMildPath T')
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    criticalMildPathExtension T hT (criticalMildPathRestrict hTT' u) s =
      criticalMildPathExtension T' hT' u s := by
  rw [criticalMildPathExtension_apply T hT _ hs,
    criticalMildPathExtension_apply T' hT' u ⟨hs.1, le_trans hs.2 hTT'⟩]
  rfl

/-- At an observation time in the earlier interval, the literal Duhamel
integral is unchanged by restriction: its domain is exactly `(0, τ]`. -/
theorem criticalMildDuhamel_restrict_eq
    (ν : ℝ) (hν : 0 < ν) {T T' R : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (hTT' : T ≤ T') (u : CriticalMildPathBall T' R) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) :
    criticalMildDuhamel ν hν
      (criticalMildPathExtension T hT (criticalMildPathBallRestrict hTT' u).1)
      (criticalMildPathBallExtension_divergenceFree hT
        (criticalMildPathBallRestrict hTT' u)) τ =
      criticalMildDuhamel ν hν (criticalMildPathExtension T' hT' u.1)
        (criticalMildPathBallExtension_divergenceFree hT' u) τ := by
  unfold criticalMildDuhamel
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, le_trans hs.2 hτ.2⟩
  have hext : criticalMildPathExtension T hT
      (criticalMildPathBallRestrict hTT' u).1 s =
      criticalMildPathExtension T' hT' u.1 s := by
    simpa [criticalMildPathBallRestrict] using
      (criticalMildPathExtension_restrict_eq hT hT' hTT' u.1 hsT)
  unfold criticalMildPathIntegrand
  simpa only [hext]

/-- The original-data mild equation restricts to every earlier horizon. -/
theorem criticalMildPathBallRestrict_satisfies_original_mild
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    {T T' R : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') (hTT' : T ≤ T')
    (u : CriticalMildPathBall T' R)
    (hu : ∀ τ : Icc (0 : ℝ) T',
      u.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension T' hT' u.1)
        (criticalMildPathBallExtension_divergenceFree hT' u) τ.1 τ.2.1)
    (τ : Icc (0 : ℝ) T) :
    (criticalMildPathBallRestrict hTT' u).1 τ = criticalMildImage ν hν a
      (criticalMildPathExtension T hT (criticalMildPathBallRestrict hTT' u).1)
      (criticalMildPathBallExtension_divergenceFree hT
        (criticalMildPathBallRestrict hTT' u)) τ.1 τ.2.1 := by
  rw [criticalMildPathBallRestrict_apply]
  rw [hu (criticalMildTimeInclusion hTT' τ)]
  change weightedHeatFlow ν τ.1 hν.le τ.2.1 a +
      criticalMildDuhamel ν hν (criticalMildPathExtension T' hT' u.1)
        (criticalMildPathBallExtension_divergenceFree hT' u) τ.1 = _
  unfold criticalMildImage
  rw [criticalMildDuhamel_restrict_eq ν hν hT hT' hTT' u τ.2]

/-- The exact compatibility contract required before constructing a direct
limit from an increasing family of finite-horizon mild paths.  This contract
does not construct the family or its limit. -/
structure CriticalMildIncreasingCompatibility
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) where
  horizon : ℕ → ℝ
  horizon_nonneg : ∀ n, 0 ≤ horizon n
  horizon_strictMono : StrictMono horizon
  pathRadius : ℕ → ℝ
  path : ∀ n, CriticalMildPathBall (horizon n) (pathRadius n)
  mild : ∀ n, ∀ τ : Icc (0 : ℝ) (horizon n),
    (path n).1 τ = criticalMildImage ν hν a
      (criticalMildPathExtension (horizon n) (horizon_nonneg n) (path n).1)
      (criticalMildPathBallExtension_divergenceFree (horizon_nonneg n) (path n))
      τ.1 τ.2.1
  restrict_compatible : ∀ {m n : ℕ} (hmn : m < n),
    criticalMildPathRestrict (le_of_lt (horizon_strictMono hmn))
      (path n).1 = (path m).1

end Navier.Analysis.CriticalMildRestrictionCompatibility

#print axioms Navier.Analysis.CriticalMildRestrictionCompatibility.criticalMildDuhamel_restrict_eq
#print axioms Navier.Analysis.CriticalMildRestrictionCompatibility.criticalMildPathBallRestrict_satisfies_original_mild
