import Navier.Analysis.SeeleyGlue

/-!
# Seeley synthesis — the extension property, established

The reflection-series machinery (`SeeleyReflection`), the infinite moment
identities (`SeeleyMoments`), and the cutoff/glueing layer (`SeeleyGlue`)
assemble into Seeley's extension theorem: every within-smooth field on the
closed nonnegative-time half-space is the restriction of a globally smooth
spacetime field.

This leaf realizes `SeeleyExtensionProperty` — declared in
`HalfSpaceSmoothnessBridge` as the named open property — from
`SeeleyGlue.seeley_extension`, and derives the unconditional half-space
smoothness equivalence `halfSpaceSmooth_iff_extension`.

Reference: R. T. Seeley, "Extension of C^∞ functions defined in a half
space", Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

noncomputable section

namespace Navier.Analysis.HalfSpaceSmoothnessBridge

/-- **Seeley's extension theorem** (Seeley 1964): the extension property
holds — within-smooth fields on the closed half-space extend to globally
smooth spacetime fields.  Realized by the reflection series
`∑ₖ seeleyA k · seeleyPhi(−2^k t) · g(−2^k t, x)` glued across `t = 0`
(`SeeleyGlue.seeley_extension`). -/
theorem seeleyExtensionProperty_holds : SeeleyExtensionProperty :=
  fun E' i1 i2 g hg => @SeeleyGlue.seeley_extension E' i1 i2 g hg

/-- **The half-space smoothness equivalence** (unconditional): a field is
within-smooth on the closed nonnegative-time half-space iff it is the
restriction of a globally smooth spacetime field. -/
theorem halfSpaceSmooth_iff_extension
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : ℝ → Space → E') :
    HalfSpaceSmooth g ↔ Nonempty (HalfSpaceSmoothExtension g) :=
  halfSpaceSmooth_iff_extension_of_seeley seeleyExtensionProperty_holds g

end Navier.Analysis.HalfSpaceSmoothnessBridge
