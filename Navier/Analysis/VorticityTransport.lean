import Navier.Analysis.CurlIdentities

/-!
# Vorticity transport: strictly-lower leaves for the curl of Navier–Stokes

The vorticity transport equation `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω`
(Majda–Bertozzi (1.33)) is the curl of the momentum equation.  Its
formalization decomposes into:

1. **Slice bridge** (`contDiffAt_spatial_slice`): joint `C^∞` on the closed
   nonnegative-time half-space gives full Fréchet smoothness of every
   nonnegative-time spatial slice — the slice direction is interior, so no
   one-sided derivative survives into spatial smoothness.  Every Clairaut
   step of the transport derivation consumes this bridge.
2. **Pressure leaf** (`staticCurl_pressureGradient_eq_zero`): the curl of
   the pressure gradient vanishes, Identity 1 of `CurlIdentities` applied to
   the pressure slice.
3. **Force leaf** (`staticCurl_zero`): the curl of the identically zero
   force field vanishes.

Residual leaves (named here, attacked down the list): curl–`∂ₜ`
commutation (time–space Clairaut on the half-space, `fderivWithin`
boundary layer), curl–Δ commutation (third-order spatial Clairaut), the
convection identity `∇×((u·∇)u) = (u·∇)ω − (ω·∇)u` under `div u = div ω = 0`
(Identity 2), then final assembly.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff

namespace Navier.Analysis.VorticityTransport

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.CurlIdentities

/-- **Spatial-slice smoothness bridge.**  Joint `C^∞` regularity of an
evolution on the closed nonnegative-time half-space `Ici 0 ×ˢ univ`
restricts to full Fréchet `C^∞` regularity of every nonnegative-time
spatial slice: for fixed `t ≥ 0` the map `y ↦ (t, y)` lands inside the
constraint set, so `ContDiffWithinAt` composed with the slice embedding
upgrades to `ContDiffAt` on the whole space. -/
theorem contDiffAt_spatial_slice {β : Type*} [NormedAddCommGroup β]
    [NormedSpace ℝ β] {F : ℝ → Space → β}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Space => F z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    ContDiffAt ℝ ∞ (F t) x := by
  have hmem : (t, x) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ :=
    Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht, Set.mem_univ x⟩
  have hG : ContDiffWithinAt ℝ ∞ (fun z : ℝ × Space => F z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, x) := hF (t, x) hmem
  have he : ContDiffWithinAt ℝ ∞ (fun y : Space => (t, y)) Set.univ x :=
    (contDiffAt_const.prodMk contDiffAt_id).contDiffWithinAt
  have hmaps : Set.MapsTo (fun y : Space => (t, y)) Set.univ
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro y _
    exact Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht, Set.mem_univ y⟩
  have hcomp := ContDiffWithinAt.comp x hG he hmaps
  rw [show ((fun z : ℝ × Space => F z.1 z.2) ∘ (fun y : Space => (t, y))) =
      F t from rfl] at hcomp
  exact hcomp.contDiffAt Filter.univ_mem

/-- **Pressure leaf.**  The curl of the pressure gradient vanishes at every
nonnegative time: Identity 1 (`staticCurl_staticGradient_eq_zero`) applied
to the spatial pressure slice.  This kills the pressure term in the curl of
the momentum equation. -/
theorem staticCurl_pressureGradient_eq_zero (p : PressureEvolution)
    (hp : SmoothPressureOnNonnegativeTime p) {t : ℝ} (ht : 0 ≤ t)
    (x : Space) :
    staticCurl (fun y => pressureGradient p t y) x = 0 := by
  have h2 : ContDiffAt ℝ 2 (p t) x :=
    (contDiffAt_spatial_slice hp ht x).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [show (fun y => pressureGradient p t y) =
      (fun y => staticGradient (p t) y) from rfl]
  exact staticCurl_staticGradient_eq_zero (p t) x h2

/-- **Force leaf.**  The curl of the identically zero velocity field
vanishes.  Covers the unforced (`zeroForce`) term of statement A. -/
theorem staticCurl_zero (x : Space) :
    staticCurl (fun _ : Space => (0 : Space)) x = 0 := by
  simp [staticCurl]

/-- **Third-order Clairaut swap (scalar core).**  For a `C^3` scalar field
the coordinate third derivative `∂ⱼ∂ᵢ∂ᵢ g` equals `∂ᵢ∂ᵢ∂ⱼ g`: first swap the
outer `∂ⱼ` past the adjacent `∂ᵢ` (second-order Clairaut on the `C^2` field
`∂ᵢ g`), then swap the remaining adjacent pair `∂ⱼ∂ᵢ` pointwise everywhere
(second-order Clairaut on `g`) and differentiate the resulting function
equality.  This is the analytic core of `curl ∘ Δ = Δ ∘ curl` and of the
viscous term of the vorticity transport equation. -/
theorem thirdDeriv_swap (g : Space → ℝ) (hg : ContDiff ℝ 3 g)
    (x : Space) (i j : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ g z (basisVector i)) y
        (basisVector i)) x (basisVector j) =
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ g z (basisVector j)) y
        (basisVector i)) x (basisVector i) := by
  have hG2 : ContDiffAt ℝ 2 (fun z => fderiv ℝ g z (basisVector i)) x := by
    have h2 : ContDiffAt ℝ 2 (fderiv ℝ g) x :=
      (hg.contDiffAt).fderiv_right (by norm_num)
    exact ((ContinuousLinearMap.apply ℝ ℝ
      (basisVector i)).contDiff).contDiffAt.comp x h2
  have hstep1 : fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ g z
        (basisVector i)) y (basisVector j)) x (basisVector i) =
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ g z (basisVector i)) y
        (basisVector i)) x (basisVector j) :=
    ContDiffAt.hasSymmetricMixedPartialAt hG2 i j
  rw [← hstep1]
  have hswap : ∀ y : Space,
      fderiv ℝ (fun z => fderiv ℝ g z (basisVector i)) y (basisVector j) =
        fderiv ℝ (fun z => fderiv ℝ g z (basisVector j)) y (basisVector i) :=
    fun y => ContDiffAt.hasSymmetricMixedPartialAt
      ((hg.contDiffAt).of_le (by norm_num)) j i
  rw [show (fun y => fderiv ℝ (fun z => fderiv ℝ g z (basisVector i)) y
        (basisVector j)) =
      (fun y => fderiv ℝ (fun z => fderiv ℝ g z (basisVector j)) y
        (basisVector i)) from funext hswap]

end Navier.Analysis.VorticityTransport
