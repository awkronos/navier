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
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildPathContraction
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildObservationContinuity

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

/-- Clamping a local path to the real line does not increase its native
uniform path distance. -/
theorem norm_criticalMildPathExtension_sub_le
    (T : ℝ) (hT : 0 ≤ T) (u v : CriticalMildPath T) (s : ℝ) :
    ‖criticalMildPathExtension T hT u s - criticalMildPathExtension T hT v s‖ ≤
      ‖u - v‖ := by
  change ‖u (projIcc (0 : ℝ) T hT s) - v (projIcc (0 : ℝ) T hT s)‖ ≤ ‖u - v‖
  rw [← ContinuousMap.sub_apply]
  exact norm_weightedMildPath_eval_le T (u - v) _

/-- The radius/divergence-free local ball, represented as a subtype of the
complete continuous path carrier. -/
abbrev CriticalMildPathBall (T R : ℝ) :=
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

/-- The divergence-free radius predicate is closed in the uniform metric on
continuous paths: it is an intersection of coordinate equalizers and norm
sublevel sets at each time. -/
theorem isClosed_criticalMildPathBall (T R : ℝ) :
    IsClosed {u : CriticalMildPath T |
      ∀ t : Icc (0 : ℝ) T,
        LatticeDivergenceFree (u t) ∧ ‖u t‖ ≤ R} := by
  rw [show {u : CriticalMildPath T | ∀ t : Icc (0 : ℝ) T,
      LatticeDivergenceFree (u t) ∧ ‖u t‖ ≤ R} =
      ⋂ t : Icc (0 : ℝ) T,
        (⋂ m : LatticeMode, {u | latticeDivergenceCLM m (u t) = 0}) ∩
          {u | ‖u t‖ ≤ R} by
      ext u
      simp only [mem_setOf_eq, mem_iInter, mem_inter_iff]
      constructor
      · intro hu t
        exact ⟨fun m => hu t |>.1 m, hu t |>.2⟩
      · intro hu t
        exact ⟨fun m => hu t |>.1 m, hu t |>.2⟩]
  apply isClosed_iInter
  intro t
  apply IsClosed.inter
  · apply isClosed_iInter
    intro m
    exact isClosed_eq
      ((latticeDivergenceCLM m).continuous.comp (continuous_eval_const t))
      continuous_const
  · exact isClosed_le
      (continuous_norm.comp (continuous_eval_const t)) continuous_const

instance criticalMildPathBall_isClosed (T R : ℝ) :
    IsClosed ({u : CriticalMildPath T |
      ∀ t : Icc (0 : ℝ) T,
        LatticeDivergenceFree (u t) ∧ ‖u t‖ ≤ R} : Set (CriticalMildPath T)) :=
  isClosed_criticalMildPathBall T R

instance criticalMildPathBall_completeSpace (T R : ℝ) :
    CompleteSpace (CriticalMildPathBall T R) := by
  change CompleteSpace ↑{u : CriticalMildPath T |
    ∀ t : Icc (0 : ℝ) T,
      LatticeDivergenceFree (u t) ∧ ‖u t‖ ≤ R}
  infer_instance

theorem criticalMildPathBallExtension_divergenceFree
    {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R) (s : ℝ) :
    LatticeDivergenceFree (criticalMildPathExtension T hT u.1 s) := by
  let p : CriticalMildPath T := u.1
  change LatticeDivergenceFree (p (projIcc (0 : ℝ) T hT s))
  exact criticalMildPathBall_divergenceFree u _

theorem criticalMildPathBallExtension_norm_le
    {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R) (s : ℝ) :
    ‖criticalMildPathExtension T hT u.1 s‖ ≤ R := by
  let p : CriticalMildPath T := u.1
  change ‖p (projIcc (0 : ℝ) T hT s)‖ ≤ R
  exact criticalMildPathBall_norm_le u _

/-- At the zero endpoint, the full mild image is continuous along any closed
nonnegative horizon.  The linear and nonlinear terms are composed through the
nonnegative-time subtype separately. -/
theorem continuousAt_criticalMildImage_zero_on_Icc
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (huR : ∀ s, ‖u s‖ ≤ R) :
    ContinuousAt (fun τ : Icc (0 : ℝ) T =>
      criticalMildImage ν hν u₀ u hu τ.1 τ.2.1) ⟨0, ⟨le_rfl, hT⟩⟩ := by
  let time : Icc (0 : ℝ) T → NNReal := fun τ => ⟨τ.1, τ.2.1⟩
  have htime0 : Filter.Tendsto time (𝓝 ⟨0, ⟨le_rfl, hT⟩⟩) (𝓝 0) := by
    have htime : Continuous time :=
      continuous_subtype_val.subtype_mk fun τ => τ.2.1
    convert htime.continuousAt using 1
    rfl
  have hheat := (continuous_weightedHeatFlow_nnreal ν hν.le u₀).continuousAt (x := 0)
  have hduhamel := tendsto_criticalMildDuhamel_nnreal_zero ν hν u huc hu hR huR
  have hsum : Filter.Tendsto
    (fun τ : Icc (0 : ℝ) T =>
      weightedHeatFlow ν τ.1 hν.le τ.2.1 u₀ + criticalMildDuhamel ν hν u hu τ.1)
    (𝓝 ⟨0, ⟨le_rfl, hT⟩⟩)
    (𝓝 (weightedHeatFlow ν 0 hν.le le_rfl u₀ + 0))
    := by
      have hheat' := Filter.Tendsto.comp hheat htime0
      have hduhamel' := Filter.Tendsto.comp hduhamel htime0
      convert Filter.Tendsto.add hheat' hduhamel' using 1
      · funext σ
        congr
      · simp [time]
  simpa [ContinuousAt, criticalMildImage, criticalMildDuhamel] using hsum

/-- The full image is continuous on the closed local horizon: the zero branch
uses the preceding endpoint lemma and every other point uses positive-time
observation continuity. -/
theorem continuous_criticalMildImage_on_Icc
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (huR : ∀ s, ‖u s‖ ≤ R) :
    Continuous fun τ : Icc (0 : ℝ) T =>
      criticalMildImage ν hν u₀ u hu τ.1 τ.2.1 := by
  rw [continuous_iff_continuousAt]
  intro τ
  rcases eq_or_lt_of_le τ.2.1 with hzero | hpos
  · have hτ : τ = ⟨0, ⟨le_rfl, hT⟩⟩ := Subtype.ext hzero.symm
    rw [hτ]
    exact continuousAt_criticalMildImage_zero_on_Icc
      ν hν u₀ u huc hu hR hT huR
  · unfold criticalMildImage
    apply ContinuousAt.add
    · let time : Icc (0 : ℝ) T → NNReal := fun σ => ⟨σ.1, σ.2.1⟩
      have htime : Continuous time :=
        continuous_subtype_val.subtype_mk fun σ => σ.2.1
      have hheat := (continuous_weightedHeatFlow_nnreal ν hν.le u₀).continuousAt
        (x := time τ)
      have hcomp := Filter.Tendsto.comp hheat htime.continuousAt
      change Filter.Tendsto
        (fun σ : Icc (0 : ℝ) T => weightedHeatFlow ν σ.1 hν.le σ.2.1 u₀)
        (𝓝 τ) (𝓝 (weightedHeatFlow ν τ.1 hν.le τ.2.1 u₀))
      convert hcomp using 1
      · funext σ
        congr
      · congr
    · exact (tendsto_criticalMildDuhamel_observation ν hν u huc hu hR hpos huR).comp
        continuous_subtype_val.continuousAt

/-- The actual mild map packaged as an endomap of the divergence-free radius
ball. -/
def criticalMildPathBallImage
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbudget : ‖u₀‖ + (2 * Real.sqrt T / Real.sqrt ν) * R ^ 2 ≤ R)
    (u : CriticalMildPathBall T R) : CriticalMildPathBall T R := by
  let p : CriticalMildPath T := u.1
  let ext : ℝ → WeightedLatticeBanach := criticalMildPathExtension T hT p
  have hextc : Continuous ext := continuous_criticalMildPathExtension T hT p
  have hextdf : ∀ s, LatticeDivergenceFree (ext s) := by
    intro s
    exact criticalMildPathBallExtension_divergenceFree hT u s
  have hextR : ∀ s, ‖ext s‖ ≤ R := by
    intro s
    exact criticalMildPathBallExtension_norm_le hT u s
  refine ⟨⟨fun τ => criticalMildImage ν hν u₀ ext hextdf τ.1 τ.2.1, ?_⟩, ?_⟩
  · exact continuous_criticalMildImage_on_Icc ν hν u₀ ext hextc hextdf hR hT hextR
  · intro τ
    constructor
    · exact criticalMildImage_divergenceFree ν hν u₀ ext hextc hextdf hR τ.2.1
        (fun s hs => hextR s)
    · exact norm_criticalMildImage_le_radius ν hν u₀ ext hextc hextdf hR τ.2.1 τ.2.2
        (fun s hs => hextR s) hbudget

/-- Uniform path-norm Lipschitz estimate for the local mild ball endomap. -/
theorem norm_criticalMildPathBallImage_sub_le
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbudget : ‖u₀‖ + (2 * Real.sqrt T / Real.sqrt ν) * R ^ 2 ≤ R)
    (u v : CriticalMildPathBall T R) :
    ‖(criticalMildPathBallImage ν hν u₀ hT hR hbudget u).1 -
        (criticalMildPathBallImage ν hν u₀ hT hR hbudget v).1‖ ≤
      (4 * Real.sqrt T / Real.sqrt ν) * R * ‖u.1 - v.1‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro τ
  let pu : CriticalMildPath T := u.1
  let pv : CriticalMildPath T := v.1
  let eu : ℝ → WeightedLatticeBanach := criticalMildPathExtension T hT pu
  let ev : ℝ → WeightedLatticeBanach := criticalMildPathExtension T hT pv
  have heuc : Continuous eu := continuous_criticalMildPathExtension T hT pu
  have hevc : Continuous ev := continuous_criticalMildPathExtension T hT pv
  have heudf : ∀ s, LatticeDivergenceFree (eu s) := by
    intro s
    exact criticalMildPathBallExtension_divergenceFree hT u s
  have hevdf : ∀ s, LatticeDivergenceFree (ev s) := by
    intro s
    exact criticalMildPathBallExtension_divergenceFree hT v s
  have heuR : ∀ s, ‖eu s‖ ≤ R := by
    intro s
    exact criticalMildPathBallExtension_norm_le hT u s
  have hevR : ∀ s, ‖ev s‖ ≤ R := by
    intro s
    exact criticalMildPathBallExtension_norm_le hT v s
  have hD : ∀ s, ‖eu s - ev s‖ ≤ ‖u.1 - v.1‖ := by
    intro s
    exact norm_criticalMildPathExtension_sub_le T hT pu pv s
  have hpoint := norm_criticalMildImage_sub_le ν hν u₀ eu ev heuc hevc heudf hevdf
    hR (norm_nonneg _) τ.2.1 (fun s hs => heuR s) (fun s hs => hevR s)
    (fun s hs => hD s)
  have hsqrt : Real.sqrt τ.1 ≤ Real.sqrt T := Real.sqrt_le_sqrt τ.2.2
  have hcoef : 0 ≤ (4 / Real.sqrt ν) * R * ‖u.1 - v.1‖ := by positivity
  change ‖criticalMildImage ν hν u₀ eu heudf τ.1 τ.2.1 -
      criticalMildImage ν hν u₀ ev hevdf τ.1 τ.2.1‖ ≤ _
  calc
    ‖criticalMildImage ν hν u₀ eu heudf τ.1 τ.2.1 -
        criticalMildImage ν hν u₀ ev hevdf τ.1 τ.2.1‖ ≤
        (4 * Real.sqrt τ.1 / Real.sqrt ν) * R * ‖u.1 - v.1‖ := hpoint
    _ = ((4 / Real.sqrt ν) * R * ‖u.1 - v.1‖) * Real.sqrt τ.1 := by ring
    _ ≤ ((4 / Real.sqrt ν) * R * ‖u.1 - v.1‖) * Real.sqrt T :=
      mul_le_mul_of_nonneg_left hsqrt hcoef
    _ = (4 * Real.sqrt T / Real.sqrt ν) * R * ‖u.1 - v.1‖ := by ring

end Navier.Analysis.CriticalMildPathFixedPoint

#print axioms Navier.Analysis.CriticalMildPathFixedPoint.continuous_criticalMildPathExtension
#print axioms Navier.Analysis.CriticalMildPathFixedPoint.criticalMildPathExtension_apply
