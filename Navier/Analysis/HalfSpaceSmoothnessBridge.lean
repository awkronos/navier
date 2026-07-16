import Navier.Problem

/-!
# Half-space smoothness bridge

`Navier/Problem.lean` encodes Fefferman's `u, p ∈ C^∞(ℝ³ × [0,∞))` with
Mathlib's within-set smoothness `ContDiffOn ℝ ∞` on the closed half-space
`Set.Ici 0 ×ˢ Set.univ`.  This file records the provable content of the
`halfSpaceSmoothnessEquivalence` residual and reduces its one genuinely open
direction to a single named classical extension property.

**Established here.**
1. Restrictions of globally smooth spacetime fields are within-smooth
   (`halfSpaceSmooth_of_contDiff`), and more generally any field agreeing on
   the half-space with a globally smooth extension is within-smooth
   (`halfSpaceSmooth_of_extension`).
2. A within-smooth field is genuinely smooth at every interior time
   (`contDiffAt_of_halfSpaceSmooth_of_pos`).
3. The classical reading of `C^∞` up to the boundary holds: every iterated
   within-derivative of a within-smooth field is continuous on the whole
   closed half-space (`continuousOn_iteratedFDerivWithin_of_halfSpaceSmooth`).

**Reduced to a named leaf.**  The converse representation — every
within-smooth field on the closed half-space is the restriction of a globally
smooth field — is Seeley's extension theorem (R. T. Seeley, *Extension of
C^∞ functions defined in a half space*, Proc. Amer. Math. Soc. 15 (1964),
625–626; est. ~600 LOC: dyadic reflection series, uniform convergence of all
derivatives).  It is recorded as the named property `SeeleyExtensionProperty`;
`halfSpaceSmooth_iff_extension_of_seeley` shows that property is exactly what
closes the residual.  No equivalence is asserted unconditionally.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.HalfSpaceSmoothnessBridge

open Navier
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The joint spacetime map of a time-indexed field. -/
def jointMap (g : ℝ → Space → E) : ℝ × Space → E :=
  fun z => g z.1 z.2

/-- Within-smoothness on the closed nonnegative-time half-space, the common
shape of `SmoothVelocityOnNonnegativeTime` and
`SmoothPressureOnNonnegativeTime`. -/
def HalfSpaceSmooth (g : ℝ → Space → E) : Prop :=
  ContDiffOn ℝ ∞ (jointMap g) ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set Space))

/-- The velocity predicate is literally half-space smoothness. -/
theorem smoothVelocityOnNonnegativeTime_iff_halfSpaceSmooth
    (u : VelocityEvolution) :
    SmoothVelocityOnNonnegativeTime u ↔ HalfSpaceSmooth u :=
  Iff.rfl

/-- The pressure predicate is literally half-space smoothness. -/
theorem smoothPressureOnNonnegativeTime_iff_halfSpaceSmooth
    (p : PressureEvolution) :
    SmoothPressureOnNonnegativeTime p ↔ HalfSpaceSmooth p :=
  Iff.rfl

/-- A globally smooth spacetime field is within-smooth on the half-space. -/
theorem halfSpaceSmooth_of_contDiff {g : ℝ → Space → E}
    (hg : ContDiff ℝ ∞ (jointMap g)) : HalfSpaceSmooth g :=
  hg.contDiffOn

/-- A globally smooth extension witness for a field on nonnegative time. -/
structure HalfSpaceSmoothExtension (g : ℝ → Space → E) where
  /-- The globally defined spacetime extension. -/
  extension : ℝ × Space → E
  /-- The extension is smooth on all of spacetime. -/
  smooth : ContDiff ℝ ∞ extension
  /-- The extension agrees with the field on nonnegative time. -/
  agrees : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, extension (t, x) = g t x

/-- Restriction direction of the residual: any field admitting a globally
smooth extension is within-smooth on the closed half-space. -/
theorem halfSpaceSmooth_of_extension {g : ℝ → Space → E}
    (w : HalfSpaceSmoothExtension g) : HalfSpaceSmooth g := by
  refine (w.smooth.contDiffOn (s := (Set.Ici (0 : ℝ)) ×ˢ
    (Set.univ : Set Space))).congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact (w.agrees t ht x).symm

/-- Interior regularity: a within-smooth field is genuinely smooth at every
strictly positive time. -/
theorem contDiffAt_of_halfSpaceSmooth_of_pos {g : ℝ → Space → E}
    (hg : HalfSpaceSmooth g) {t : ℝ} (ht : 0 < t) (x : Space) :
    ContDiffAt ℝ ∞ (jointMap g) (t, x) := by
  refine hg.contDiffAt ?_
  have h1 : Set.Ici (0 : ℝ) ∈ nhds t := Ici_mem_nhds ht
  have h2 : (Set.univ : Set Space) ∈ nhds x := Filter.univ_mem
  simpa using prod_mem_nhds h1 h2

/-- The closed half-space is a set of unique differentiability. -/
theorem uniqueDiffOn_halfSpace :
    UniqueDiffOn ℝ ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set Space)) :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

/-- Classical `C^∞`-up-to-the-boundary clause: every iterated
within-derivative of a within-smooth field is continuous on the whole closed
half-space, boundary included. -/
theorem continuousOn_iteratedFDerivWithin_of_halfSpaceSmooth
    {g : ℝ → Space → E} (hg : HalfSpaceSmooth g) (n : ℕ) :
    ContinuousOn
      (iteratedFDerivWithin ℝ n (jointMap g)
        ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set Space)))
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set Space)) :=
  hg.continuousOn_iteratedFDerivWithin
    (by exact_mod_cast le_top) uniqueDiffOn_halfSpace

/-- **Named leaf (Seeley 1964).**  Every within-smooth field on the closed
nonnegative-time half-space extends to a globally smooth spacetime field.
Reference: R. T. Seeley, Proc. Amer. Math. Soc. 15 (1964), 625–626.
Estimated ~600 LOC; dependencies: geometric reflection series
`Σ aₖ φ(bₖ t) g(-bₖ t, x)`, uniform convergence of all iterated derivatives,
and a smooth cutoff.  This is a definition of the open property, not an
assertion of it. -/
def SeeleyExtensionProperty : Prop :=
  ∀ (E' : Type) (_ : NormedAddCommGroup E') (_ : NormedSpace ℝ E')
    (g : ℝ → Space → E'), HalfSpaceSmooth g → Nonempty (HalfSpaceSmoothExtension g)

/-- The `halfSpaceSmoothnessEquivalence` residual closes exactly under the
named Seeley extension property: given it, within-smoothness on the closed
half-space is equivalent to being the restriction of a globally smooth
field. -/
theorem halfSpaceSmooth_iff_extension_of_seeley
    (hS : SeeleyExtensionProperty)
    {E' : Type} [inst1 : NormedAddCommGroup E'] [inst2 : NormedSpace ℝ E']
    (g : ℝ → Space → E') :
    HalfSpaceSmooth g ↔ Nonempty (HalfSpaceSmoothExtension g) := by
  constructor
  · exact fun hg => hS E' inst1 inst2 g hg
  · rintro ⟨w⟩
    exact halfSpaceSmooth_of_extension w

end Navier.Analysis.HalfSpaceSmoothnessBridge
