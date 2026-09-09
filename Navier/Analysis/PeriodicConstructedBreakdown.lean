import Navier.Analysis.EuclideanPDETransport
import Navier.Analysis.ViscosityEndpoints
import Navier.Construction.ActualCandidateAssembly
import Navier.Construction.CandidateConsequences

/-!
# The constructed periodic breakdown endpoint

The selected construction is already a unit-periodic Euclidean lift.  This
module transports that lift through the coordinate identity to the official
native carrier.  No spatial periodization of the compact whole-space
extraction is needed: doing so would require a new pressure and same-force
comparison argument, whereas the selected periodic candidate already carries
exactly those data.
-/

set_option autoImplicit false
noncomputable section

open scoped ContDiff Topology Pointwise

namespace Navier.Analysis.PeriodicConstructedBreakdown

open Set Filter
open Navier
open Navier.Analysis.EuclideanPDETransport
open Navier.Construction.ProblemStatement

private theorem nativeFutureJet_periodic {f : ForceField}
    (hp : SpatiallyPeriodicForce f) (m : ℕ) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ∀ i : Fin 3,
      iteratedFDerivWithin ℝ m (fun z : ℝ × Space => f z.1 z.2)
        nonnegativeSpacetime (t, x + basisVector i) =
      iteratedFDerivWithin ℝ m (fun z : ℝ × Space => f z.1 z.2)
        nonnegativeSpacetime (t, x) := by
  intro t ht x i
  have he : Set.EqOn
      (fun z : ℝ × Space => (fun w : ℝ × Space => f w.1 w.2)
        (z + (0, basisVector i)))
      (fun z : ℝ × Space => f z.1 z.2) nonnegativeSpacetime := by
    rintro ⟨s, y⟩ hz
    simpa only [Prod.mk_add_mk, add_zero] using hp s hz.1 y i
  have hc := iteratedFDerivWithin_congr (𝕜 := ℝ) he
    (show (t, x) ∈ nonnegativeSpacetime from ⟨ht, Set.mem_univ _⟩) m
  have hs := iteratedFDerivWithin_comp_add_right (𝕜 := ℝ)
    (f := fun z : ℝ × Space => f z.1 z.2)
    (s := nonnegativeSpacetime) m (0, basisVector i) (t, x)
  have htranslate : ((0, basisVector i) : ℝ × Space) +ᵥ nonnegativeSpacetime =
      nonnegativeSpacetime := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [nonnegativeSpacetime] using hw
    · intro hz
      refine ⟨z - (0, basisVector i), ?_, ?_⟩
      · simpa [nonnegativeSpacetime] using hz
      · simp
  rw [htranslate] at hs
  simpa only [Prod.mk_add_mk, add_zero] using hs.symm.trans hc

/-- Smooth, unit-periodic forcing with a uniform terminal time automatically
has every official half-space jet bounded by every polynomial time weight. -/
theorem periodicForcedDataRapidDecay_of_smooth_periodic_timeSupport
    {f : ForceField} (hsmooth : SmoothForceOnNonnegativeTime f)
    (hperiodic : SpatiallyPeriodicForce f) {T : ℝ}
    (htime : ∀ t : ℝ, T ≤ t → ∀ x : Space, f t x = 0) :
    PeriodicForcedDataRapidDecay f := by
  refine ⟨hperiodic, hsmooth, ?_⟩
  intro n K
  let J := fun z : ℝ × Space =>
    iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
      nonnegativeSpacetime z
  have hJ : ContinuousOn J nonnegativeSpacetime :=
    hsmooth.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top)
      ((uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ)
  -- Use the construction's compact fundamental-cell lemma with the actual jet
  -- as codomain; only the domain is re-presented through `toNative`.
  let H := fun z : Navier.Construction.ProblemStatement.SpaceTime =>
    J (z.1, toNative z.2)
  have hHcont : ContinuousOn H
      (Icc (0 : ℝ) (T + 1) ×ˢ (Set.univ : Set Navier.Construction.ProblemStatement.Space)) := by
    apply hJ.comp spacetimeToNative_contDiff.continuous.continuousOn
    intro z hz
    exact ⟨hz.1.1, Set.mem_univ _⟩
  have hHperiodic : UnitSpatialPeriodsOn (Icc (0 : ℝ) (T + 1)) H := by
    intro t ht x i
    change J (t, toNative (x + coordinateVector i)) = J (t, toNative x)
    rw [show coordinateVector i = eBasisVector i by rfl, map_add, toNative_eBasisVector]
    exact nativeFutureJet_periodic hperiodic n t ht.1 (toNative x) i
  obtain ⟨M, hM, hbound⟩ :=
    Navier.Construction.MaximalLifespan.periodic_bound_on_slab hHcont hHperiodic
  refine ⟨max (M * (1 + (T + 1)) ^ K) 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hsmall : t ≤ T + 1
  · have hb := hbound t ⟨ht, hsmall⟩ (toEuclidean x)
    have hweight : (1 + t) ^ K ≤ (1 + (T + 1)) ^ K := by
      exact pow_le_pow_left₀ (by linarith) (by linarith) K
    calc
      (1 + t) ^ K * ‖J (t, x)‖ ≤
          (1 + (T + 1)) ^ K * M :=
        mul_le_mul hweight hb (norm_nonneg _) (pow_nonneg (by linarith) K)
      _ = M * (1 + (T + 1)) ^ K := by ring
      _ ≤ max (M * (1 + (T + 1)) ^ K) 0 := le_max_left _ _
  · have htT : T < t := by linarith
    have he : (fun z : ℝ × Space => f z.1 z.2) =ᶠ[𝓝[nonnegativeSpacetime] (t, x)]
        (fun _ => 0) := by
      have hn : {z : ℝ × Space | T < z.1} ∈ 𝓝 (t, x) :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds htT
      filter_upwards [mem_nhdsWithin_of_mem_nhds hn] with z hz
      exact htime z.1 hz.le z.2
    have hz : J (t, x) = 0 := by
      simpa [J] using he.iteratedFDerivWithin_eq (htime t htT.le x) n (𝕜 := ℝ)
    change (1 + t) ^ K * ‖J (t, x)‖ ≤ _
    rw [hz, norm_zero, mul_zero]
    exact le_max_right _ _

private theorem nativeForce_periodic {f : EVelocityField}
    (hf : UnitSpatialPeriodsOn (Ici (0 : ℝ)) f) :
    SpatiallyPeriodicForce (nativeForce f) := by
  intro t ht x i
  simp only [nativeForce]
  rw [map_add, toEuclidean_basisVector]
  exact congrArg toNative (hf t ht (toEuclidean x) i)

private theorem nativeForce_timeSupport {f : EVelocityField} {T : ℝ}
    (hf : ∀ t : ℝ, T ≤ t → ∀ x : ESpace, f (t, x) = 0) :
    ∀ t : ℝ, T ≤ t → ∀ x : Space, nativeForce f t x = 0 :=
  nativeForce_futureTimeSupport hf

def toConstructionGlobalSolutionOne
    {f : EVelocityField} {v : VelocityEvolution} {p : PressureEvolution}
    (sol : IsPeriodicClassicalSolution 1 (nativeForce f) 0 v p) :
    Navier.Construction.ComparatorBridge.GlobalSolutionOne f
      (euclideanVelocity v) (euclideanPressure p) where
  velocity_smooth := euclideanVelocity_smoothOnNonnegativeTime sol.velocity_smooth
  pressure_smooth := euclideanPressure_smoothOnNonnegativeTime sol.pressure_smooth
  velocity_periodic := by
    intro t ht x i
    apply toNative.injective
    simp only [euclideanVelocity]
    rw [show coordinateVector i = eBasisVector i by rfl, map_add, toNative_eBasisVector]
    simpa [euclideanVelocity] using sol.velocity_periodic t ht (toNative x) i
  pressure_periodic := by
    intro t ht x i
    simp only [euclideanPressure]
    rw [show coordinateVector i = eBasisVector i by rfl, map_add, toNative_eBasisVector]
    simpa [euclideanPressure] using sol.pressure_periodic t ht (toNative x) i
  initial_velocity := by intro x; simp [euclideanVelocity, sol.initial_condition]
  divergence_free := by
    intro t ht x
    have hs := eFutureSpatialSlice_contDiff
      (euclideanVelocity_smoothOnNonnegativeTime sol.velocity_smooth) ht
    have hd := divergence_nativeVelocity (euclideanVelocity v)
      (x := x) (hs.differentiable (by simp) x)
    rw [nativeVelocity_euclideanVelocity] at hd
    exact hd.symm.trans (sol.incompressible t ht (toNative x))
  navier_stokes := by
    intro t ht x
    have hs := eFutureSpatialSlice_contDiff
      (euclideanVelocity_smoothOnNonnegativeTime sol.velocity_smooth) ht.le
    have hps := eFuturePressureSlice_contDiff
      (euclideanPressure_smoothOnNonnegativeTime sol.pressure_smooth) ht.le
    have htime := eFutureTimeSlice_differentiableAt
      (euclideanVelocity_smoothOnNonnegativeTime sol.velocity_smooth) ht x
    have ht' := timeDerivative_nativeVelocity_of_pos (euclideanVelocity v) ht x htime
    have hc := convection_nativeVelocity (euclideanVelocity v)
      (x := x) (hs.differentiable (by simp) x)
    have hl := laplacian_nativeVelocity (euclideanVelocity v) (x := x) hs
    have hp' := pressureGradient_nativePressure (euclideanPressure p) (x := x)
      (hps.differentiable (by simp) x)
    change eTimeDerivative (euclideanVelocity v) t x +
      eConvection (euclideanVelocity v) t x -
      eLaplacian (euclideanVelocity v) t x +
      ePressureGradient (euclideanPressure p) t x = f (t, x)
    apply toNative.injective
    simp only [map_add, map_sub]
    rw [← ht', ← hc, ← hl, ← hp', ← nativeForce_value f t x]
    simp only [nativeVelocity_euclideanVelocity, nativePressure_euclideanPressure]
    have he := sol.equation t ht.le (toNative x)
    rw [he]
    simp only [one_smul]
    abel

/-- Any actual selected-style periodic candidate with its globally smooth
forcing inhabits the exact viscosity-one official D surface. -/
theorem periodicBreakdownAtViscosityOne_of_candidate
    {u : EVelocityField} {p : EPressureField} {f : EVelocityField}
    (h : CandidateProperties u p f) :
    Navier.Analysis.ViscosityEndpoints.PeriodicBreakdownAtViscosityOne := by
  refine ⟨0, ?_, nativeForce f, ?_, ?_⟩
  · exact ⟨contDiff_const, fun x => by simp [staticDivergence], fun x i => rfl⟩
  · obtain ⟨T, _hT, htime⟩ := h.force_time_support
    exact periodicForcedDataRapidDecay_of_smooth_periodic_timeSupport
      (nativeForce_smoothOnNonnegativeTime h.force_smooth)
      (nativeForce_periodic h.force_periodic) (nativeForce_timeSupport htime)
  · rintro ⟨v, q, hglobal⟩
    let hg := toConstructionGlobalSolutionOne hglobal
    exact Navier.Construction.MaximalLifespan.candidate_excludes_global_solution h
      hg.velocity_smooth hg.pressure_smooth hg.velocity_periodic hg.pressure_periodic
      hg.initial_velocity hg.divergence_free hg.navier_stokes

/-- The repository's selected explicit periodic construction inhabits the
original all-positive-viscosity breakdown alternative D. -/
theorem periodicBreakdown : ProblemStatements.PeriodicBreakdown := by
  apply Navier.Analysis.ViscosityEndpoints.periodicBreakdown_iff_atViscosityOne.mpr
  obtain ⟨a, _, ea, eb, ep, f, hcandidate, _⟩ :=
    Navier.Construction.ActualCandidateAssembly.selected_witness
  exact periodicBreakdownAtViscosityOne_of_candidate hcandidate

end Navier.Analysis.PeriodicConstructedBreakdown
