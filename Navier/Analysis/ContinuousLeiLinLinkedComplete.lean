import Mathlib.Analysis.Normed.Lp.ProdLp
import Navier.Analysis.ContinuousLeiLinBanachContraction

/-!
# A complete linked carrier for the continuous Lei--Lin iteration

The estimate
`ContinuousLeiLinBanachContraction.admissibleNorm_continuousMildImage_sub_le_banach`
uses the sum metric

`sup_t X⁻¹(u - v) + ν * ∫ X¹(u - v)`.

The ordinary product metric is the maximum of its two coordinate distances;
passing through it would lose a factor two and turn the proved `3/4` bound
into a non-contraction.  `WithLp 1` instead equips the two slots with exactly
their sum distance.  The second slot below is therefore understood to carry
the viscosity-weighted norm `ν * ∫ X¹`; the viscosity is part of that slot's
norm, rather than an additional scalar in the product construction.

The two Banach slots cannot be used as an unrestricted product: their elements
must describe the same spacetime trajectory.  We enforce this by taking the
equalizer of two continuous linear realization maps into a common trajectory
space.  This equalizer is closed, hence complete.  Intersecting it with the
two coordinate norm balls gives the complete admissible box used by the
self-map estimates.

The final theorem applies Banach's fixed-point theorem on that box.  Its input
is the genuine coordinate contraction inequality, not a trajectory-existence
hypothesis.  For the Navier--Stokes mild map, the remaining analytic input is
now precise: construct the two weighted Banach slots and continuous linear
realization maps, then lift `continuousMildImage` to the linked box using the
already proved self-map and contraction estimates.

Pólya's `FixedPointBanach` strategy at revision
`698dfdc0d3b402f47887adf276ba48bea8f862f9` has exactly the final fixed-point
shape.  This project has no Pólya dependency, so the theorem below uses the
same Mathlib `ContractingWith` API directly.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal
open Navier.Analysis.ContinuousLeiLinAdmissibleContraction

namespace Navier.Analysis.ContinuousLeiLinLinkedComplete

/-- The `L¹` product of the `X⁻¹` slot and the viscosity-weighted `X¹` slot.
Its distance is the sum of the two coordinate distances. -/
abbrev AdmissiblePair (Xm1Slot X1WeightedSlot : Type*) :=
  WithLp 1 (Xm1Slot × X1WeightedSlot)

section LinkedCarrier

variable {Xm1Slot X1WeightedSlot CommonTrajectory : Type*}
variable [NormedAddCommGroup Xm1Slot] [NormedSpace ℝ Xm1Slot]
variable [NormedAddCommGroup X1WeightedSlot] [NormedSpace ℝ X1WeightedSlot]
variable [NormedAddCommGroup CommonTrajectory] [NormedSpace ℝ CommonTrajectory]

/-- Pairs whose two Banach-space representatives realize the same trajectory. -/
def linkedAdmissibleSet
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory) :
    Set (AdmissiblePair Xm1Slot X1WeightedSlot) :=
  {u | realizeXm1 u.fst = realizeX1 u.snd}

/-- The faithful two-norm carrier: an `L¹` product together with the proof that
both coordinate representatives describe one common trajectory. -/
def LinkedAdmissibleCarrier
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory) :=
  linkedAdmissibleSet realizeXm1 realizeX1

/-- Linkage is a closed condition because both realization maps are continuous. -/
theorem linkedAdmissibleSet_isClosed
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory) :
    IsClosed (linkedAdmissibleSet realizeXm1 realizeX1) := by
  exact isClosed_eq
    (realizeXm1.continuous.comp
      (WithLp.continuous_fst (1 : ENNReal) Xm1Slot X1WeightedSlot))
    (realizeX1.continuous.comp
      (WithLp.continuous_snd (1 : ENNReal) Xm1Slot X1WeightedSlot))

/-- A closed equalizer of two realization maps between Banach slots is complete. -/
instance linkedAdmissibleCarrierComplete
    [CompleteSpace Xm1Slot] [CompleteSpace X1WeightedSlot]
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory) :
    CompleteSpace (LinkedAdmissibleCarrier realizeXm1 realizeX1) :=
  (linkedAdmissibleSet_isClosed realizeXm1 realizeX1).completeSpace_coe

/-- The two zero representatives define a canonical linked trajectory. -/
def linkedAdmissibleZero
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory) :
    LinkedAdmissibleCarrier realizeXm1 realizeX1 :=
  ⟨0, by
    change realizeXm1 0 = realizeX1 0
    simp⟩

/-- The zero representatives are linked, so the carrier is nonempty. -/
instance linkedAdmissibleCarrierNonempty
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory) :
    Nonempty (LinkedAdmissibleCarrier realizeXm1 realizeX1) :=
  ⟨linkedAdmissibleZero realizeXm1 realizeX1⟩

/-- The carrier distance is exactly the admissible sum distance. -/
theorem linkedAdmissibleCarrier_dist_eq
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory)
    (u v : LinkedAdmissibleCarrier realizeXm1 realizeX1) :
    dist u v = dist u.1.fst v.1.fst + dist u.1.snd v.1.snd := by
  rw [Subtype.dist_eq, WithLp.prod_dist_eq_of_L1]

/-- Exact transport from the two slot distances to the admissible norm used by
`admissibleNorm_continuousMildImage_sub_le_banach`.  The second equality is the
load-bearing realization of viscosity weighting in the `X¹` slot. -/
theorem linkedAdmissibleCarrier_dist_eq_admissibleNorm
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory)
    (u v : LinkedAdmissibleCarrier realizeXm1 realizeX1)
    (ν A B : ℝ)
    (hXm1 : dist u.1.fst v.1.fst = A)
    (hX1Weighted : dist u.1.snd v.1.snd = ν * B) :
    dist u v = admissibleNorm ν A B := by
  rw [linkedAdmissibleCarrier_dist_eq, hXm1, hX1Weighted]
  rfl

/-- The coordinatewise closed admissible box inside the linked carrier.  In
the Navier application its radii are the self-map budgets for the `X⁻¹` and
viscosity-weighted `X¹` slots. -/
def linkedAdmissibleBoxSet
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory)
    (xm1Radius x1WeightedRadius : ℝ) :
    Set (LinkedAdmissibleCarrier realizeXm1 realizeX1) :=
  {u | ‖u.1.fst‖ ≤ xm1Radius ∧ ‖u.1.snd‖ ≤ x1WeightedRadius}

/-- The coordinatewise admissible box is closed. -/
theorem linkedAdmissibleBoxSet_isClosed
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory)
    (xm1Radius x1WeightedRadius : ℝ) :
    IsClosed (linkedAdmissibleBoxSet realizeXm1 realizeX1
      xm1Radius x1WeightedRadius) := by
  have hval : Continuous (fun u : LinkedAdmissibleCarrier realizeXm1 realizeX1 => u.1) :=
    continuous_subtype_val
  have hfst : Continuous
      (fun u : LinkedAdmissibleCarrier realizeXm1 realizeX1 => u.1.fst) :=
    (WithLp.continuous_fst (1 : ENNReal) Xm1Slot X1WeightedSlot).comp hval
  have hsnd : Continuous
      (fun u : LinkedAdmissibleCarrier realizeXm1 realizeX1 => u.1.snd) :=
    (WithLp.continuous_snd (1 : ENNReal) Xm1Slot X1WeightedSlot).comp hval
  exact (isClosed_le hfst.norm continuous_const).inter
    (isClosed_le hsnd.norm continuous_const)

/-- The complete admissible box on which the mild map acts. -/
def LinkedAdmissibleBox
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory)
    (xm1Radius x1WeightedRadius : ℝ) :=
  linkedAdmissibleBoxSet realizeXm1 realizeX1 xm1Radius x1WeightedRadius

/-- Closed coordinate bounds preserve completeness of the linked carrier. -/
instance linkedAdmissibleBoxComplete
    [CompleteSpace Xm1Slot] [CompleteSpace X1WeightedSlot]
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory)
    (xm1Radius x1WeightedRadius : ℝ) :
    CompleteSpace (LinkedAdmissibleBox realizeXm1 realizeX1
      xm1Radius x1WeightedRadius) :=
  (linkedAdmissibleBoxSet_isClosed realizeXm1 realizeX1
    xm1Radius x1WeightedRadius).completeSpace_coe

/-- The box distance remains exactly the sum of its coordinate distances. -/
theorem linkedAdmissibleBox_dist_eq
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory)
    (xm1Radius x1WeightedRadius : ℝ)
    (u v : LinkedAdmissibleBox realizeXm1 realizeX1
      xm1Radius x1WeightedRadius) :
    dist u v = dist u.1.1.fst v.1.1.fst + dist u.1.1.snd v.1.1.snd := by
  rw [Subtype.dist_eq, linkedAdmissibleCarrier_dist_eq]

/-- A coordinate sum estimate is exactly a `ContractingWith` certificate on
the admissible box; there is no loss through a maximum-product metric. -/
theorem contractingWith_of_coordinate_sum
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory)
    (xm1Radius x1WeightedRadius : ℝ)
    (Φ : LinkedAdmissibleBox realizeXm1 realizeX1
      xm1Radius x1WeightedRadius →
      LinkedAdmissibleBox realizeXm1 realizeX1
        xm1Radius x1WeightedRadius)
    (K : ℝ≥0) (hK : K < 1)
    (hΦ : ∀ u v,
      dist (Φ u).1.1.fst (Φ v).1.1.fst +
          dist (Φ u).1.1.snd (Φ v).1.1.snd ≤
        (K : ℝ) * (dist u.1.1.fst v.1.1.fst +
          dist u.1.1.snd v.1.1.snd)) :
    ContractingWith K Φ := by
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  simpa only [linkedAdmissibleBox_dist_eq] using hΦ u v

/-- Banach's theorem on the complete linked admissible box.  The radii only
supply its canonical zero element; the map is already a self-map by its type,
and the coordinate estimate supplies the strict contraction. -/
theorem existsUnique_fixedPoint_of_coordinate_sum
    [CompleteSpace Xm1Slot] [CompleteSpace X1WeightedSlot]
    (realizeXm1 : Xm1Slot →L[ℝ] CommonTrajectory)
    (realizeX1 : X1WeightedSlot →L[ℝ] CommonTrajectory)
    (xm1Radius x1WeightedRadius : ℝ)
    (hxm1Radius : 0 ≤ xm1Radius)
    (hx1WeightedRadius : 0 ≤ x1WeightedRadius)
    (Φ : LinkedAdmissibleBox realizeXm1 realizeX1
      xm1Radius x1WeightedRadius →
      LinkedAdmissibleBox realizeXm1 realizeX1
        xm1Radius x1WeightedRadius)
    (K : ℝ≥0) (hK : K < 1)
    (hΦ : ∀ u v,
      dist (Φ u).1.1.fst (Φ v).1.1.fst +
          dist (Φ u).1.1.snd (Φ v).1.1.snd ≤
        (K : ℝ) * (dist u.1.1.fst v.1.1.fst +
          dist u.1.1.snd v.1.1.snd)) :
    ∃ x, Φ x = x ∧ ∀ y, Φ y = y → y = x := by
  let _ : Nonempty (LinkedAdmissibleBox realizeXm1 realizeX1
      xm1Radius x1WeightedRadius) :=
    ⟨⟨linkedAdmissibleZero realizeXm1 realizeX1, by
      constructor
      · simpa [linkedAdmissibleZero] using hxm1Radius
      · simpa [linkedAdmissibleZero] using hx1WeightedRadius⟩⟩
  have hContract : ContractingWith K Φ :=
    contractingWith_of_coordinate_sum realizeXm1 realizeX1
      xm1Radius x1WeightedRadius Φ K hK hΦ
  refine ⟨hContract.fixedPoint Φ, hContract.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact hContract.fixedPoint_unique hy

end LinkedCarrier

end Navier.Analysis.ContinuousLeiLinLinkedComplete

#print axioms Navier.Analysis.ContinuousLeiLinLinkedComplete.linkedAdmissibleCarrier_dist_eq
#print axioms Navier.Analysis.ContinuousLeiLinLinkedComplete.linkedAdmissibleCarrier_dist_eq_admissibleNorm
#print axioms Navier.Analysis.ContinuousLeiLinLinkedComplete.linkedAdmissibleBoxSet_isClosed
#print axioms Navier.Analysis.ContinuousLeiLinLinkedComplete.contractingWith_of_coordinate_sum
#print axioms Navier.Analysis.ContinuousLeiLinLinkedComplete.existsUnique_fixedPoint_of_coordinate_sum
