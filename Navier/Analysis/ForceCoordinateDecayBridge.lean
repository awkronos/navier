import Navier.Analysis.ForceCoordinateBridge

/-!
# Decay transport from force coordinates to Fréchet bundles

`Breakdown.OfficialCDEncoding` fixes a typed coordinate convention: each
coordinate derivative is an iterated within-Fréchet derivative evaluated on a
list of the time/spatial coordinate directions.  The finite expansion in
`ForceCoordinateBridge` makes that convention equivalent to the bundle decay
used by the formal C/D surfaces, once the surface's existing smoothness and
periodicity fields are retained.

This is deliberately a typed adapter, not an assertion that this convention
already matches every possible textual multi-index partial-derivative syntax.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ForceCoordinateDecayBridge

open Navier
open Navier.Analysis.ForceCoordinateBridge
open Navier.Breakdown.OfficialCDEncoding

/-- The periodic typed-coordinate decay predicate supplies the bundle-decay
field of `PeriodicForcedDataRapidDecay`. -/
theorem periodicCoordinatewiseForceDecay_implies_bundleDecay
    {f : ForceField} (hf : PeriodicCoordinatewiseForceDecay f) :
    ∀ (n K : ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        (1 + t) ^ K * ‖iteratedFDerivWithin ℝ n
          (fun z : ℝ × Space => f z.1 z.2)
          nonnegativeSpacetime (t, x)‖ ≤ C := by
  intro n K
  obtain ⟨C, hC, hbound⟩ :=
    exists_weighted_iteratedFDerivWithin_opNorm_bound f n
      (fun t _x => (1 + t) ^ K)
      (fun t ht _x => pow_nonneg (by linarith) K)
      (fun axes component => hf n K axes component)
  refine ⟨(Fintype.card (Fin n → Option (Fin 3)) : ℝ) * C,
    mul_nonneg (by positivity) hC, ?_⟩
  exact hbound

/-- With the periodicity and half-space smoothness fields already required by
the official predicate, its typed coordinate formulation is equivalent to the
Fréchet-bundle formulation. -/
theorem periodicForcedDataRapidDecay_iff_typedCoordinatewise
    (f : ForceField) :
    PeriodicForcedDataRapidDecay f ↔
      SpatiallyPeriodicForce f ∧ SmoothForceOnNonnegativeTime f ∧
        PeriodicCoordinatewiseForceDecay f := by
  constructor
  · intro hf
    exact ⟨hf.1, hf.2.1,
      periodicForcedDataRapidDecay_implies_coordinatewise hf⟩
  · rintro ⟨hperiodic, hsmooth, hcoordinate⟩
    exact ⟨hperiodic, hsmooth,
      periodicCoordinatewiseForceDecay_implies_bundleDecay hcoordinate⟩

/-- The whole-space typed-coordinate decay predicate supplies the bundle-decay
field of `ForcedDataRapidDecay`; its Euclidean weight dominates the inherited
spatial norm weight used by the formal surface. -/
theorem wholeSpaceCoordinatewiseForceDecay_implies_bundleDecay
    {f : ForceField} (hf : WholeSpaceCoordinatewiseForceDecay f) :
    ∀ (n K : ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        (1 + ‖x‖ + t) ^ K * ‖iteratedFDerivWithin ℝ n
          (fun z : ℝ × Space => f z.1 z.2)
          nonnegativeSpacetime (t, x)‖ ≤ C := by
  intro n K
  obtain ⟨C, hC, hbound⟩ :=
    exists_weighted_iteratedFDerivWithin_opNorm_bound f n
      (fun t x => (1 + euclideanNorm x + t) ^ K)
      (fun t ht x => pow_nonneg (by
        have : 0 ≤ euclideanNorm x := by
          dsimp [euclideanNorm]
          positivity
        linarith) K)
      (fun axes component => hf n K axes component)
  refine ⟨(Fintype.card (Fin n → Option (Fin 3)) : ℝ) * C,
    mul_nonneg (by positivity) hC, ?_⟩
  intro t ht x
  have hbase : 0 ≤ 1 + ‖x‖ + t := by linarith [norm_nonneg x]
  have hweight : 1 + ‖x‖ + t ≤ 1 + euclideanNorm x + t := by
    linarith [norm_le_euclideanNorm x]
  have hpow := pow_le_pow_left₀ hbase hweight K
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans (hbound t ht x)

/-- With the existing half-space smoothness field retained, the whole-space
typed-coordinate predicate is equivalent to the Fréchet-bundle force-decay
predicate. -/
theorem forcedDataRapidDecay_iff_typedCoordinatewise
    (f : ForceField) :
    ForcedDataRapidDecay f ↔
      SmoothForceOnNonnegativeTime f ∧ WholeSpaceCoordinatewiseForceDecay f := by
  constructor
  · intro hf
    exact ⟨hf.1, forcedDataRapidDecay_implies_coordinatewise hf⟩
  · rintro ⟨hsmooth, hcoordinate⟩
    exact ⟨hsmooth, wholeSpaceCoordinatewiseForceDecay_implies_bundleDecay hcoordinate⟩

end Navier.Analysis.ForceCoordinateDecayBridge
