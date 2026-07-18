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

4. **Viscous leaf** (`staticCurl_laplacian_comm`,
   `staticCurl_laplacian_evolution_comm`): `∇ × Δw = Δ(∇ × w)` for `C^3`
   fields, and on every nonnegative-time slice of a smooth evolution
   `∇ × Δu(t) = Δω(t)` — third-order spatial Clairaut via
   `thirdDeriv_swap`, with private local copies of the `CurlIdentities`
   cross-product chain-rule leaves.

Residual leaves (named here, attacked down the list): curl–`∂ₜ`
commutation (time–space Clairaut on the half-space, `fderivWithin`
boundary layer), the convection identity `∇×((u·∇)u) = (u·∇)ω − (ω·∇)u`
under `div u = div ω = 0` (Identity 2), then final assembly.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff Matrix

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


/-- Component bridge (local copy of the `CurlIdentities` private lemma):
the `j`-th component of the Fréchet derivative of a velocity field equals
the Fréchet derivative of the `j`-th scalar component function. -/
private theorem fderiv_apply_component
    (w : VelocityField) (x : Space)
    (hw : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => w y k) x)
    (h : Space) (j : Fin 3) :
    (fderiv ℝ w x h) j = fderiv ℝ (fun y => w y j) x h := by
  have hpi' := fderiv_pi (𝕜 := ℝ) (E := Space) (x := x)
    (φ := fun k : Fin 3 => fun y : Space => w y k) hw
  rw [show (fun y : Space => fun k : Fin 3 => w y k) = w from rfl] at hpi'
  rw [hpi']
  rfl

/-- Eval-CLM bridge: the derivative of `z ↦ fderiv u z a` at `y` in
direction `b` is the second Fréchet derivative applied to `b` then `a`.
This is the `hg` subproof of the `CurlIdentities` cross-summand chain rule,
factored out for reuse. -/
private theorem fderiv_fderiv_apply_eq (u : VelocityField) (y : Space)
    (a b : Space) (hu : DifferentiableAt ℝ (fderiv ℝ u) y) :
    fderiv ℝ (fun z => fderiv ℝ u z a) y b =
      (fderiv ℝ (fderiv ℝ u) y b) a := by
  let T : (Space →L[ℝ] Space) →L[ℝ] Space := ContinuousLinearMap.apply ℝ Space a
  have hcomp := (HasFDerivAt.comp y T.hasFDerivAt hu.hasFDerivAt).fderiv
  change (fderiv ℝ (⇑T ∘ fderiv ℝ u) y) b = ((fderiv ℝ (fderiv ℝ u) y) b) a
  rw [hcomp]
  rfl

/-- Chain-rule leaf (local copy of the `CurlIdentities` private lemma): the
derivative of the `i`-th cross-product summand of `staticCurl` factors
through the linear cross-product and the eval-CLM bridge. -/
private theorem fderiv_cross_basisVector_apply
    (u : VelocityField) (x h : Space) (i : Fin 3)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    fderiv ℝ (fun y => basisVector i ⨯₃ fderiv ℝ u y (basisVector i)) x h =
      basisVector i ⨯₃ ((fderiv ℝ (fderiv ℝ u) x h) (basisVector i)) := by
  let L : Space →ₗ[ℝ] Space := crossProduct (basisVector i)
  have hg : fderiv ℝ (fun y => fderiv ℝ u y (basisVector i)) x h =
      (fderiv ℝ (fderiv ℝ u) x h) (basisVector i) :=
    fderiv_fderiv_apply_eq u x (basisVector i) h hu
  have hdg : DifferentiableAt ℝ (fun y => fderiv ℝ u y (basisVector i)) x := by
    have heq : (fun y => fderiv ℝ u y (basisVector i)) =
      (ContinuousLinearMap.apply ℝ Space (basisVector i) ∘ fderiv ℝ u) := rfl
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ Space (basisVector i)).differentiableAt.comp x hu
  have hL : HasFDerivAt (fun w => L w) L.toContinuousLinearMap
      (fderiv ℝ u x (basisVector i)) :=
    L.toContinuousLinearMap.hasFDerivAt
  have hcomp := (HasFDerivAt.comp x hL hdg.hasFDerivAt).fderiv
  change (fderiv ℝ ((fun w => L w) ∘ (fun y => fderiv ℝ u y (basisVector i))) x) h = _
  rw [hcomp]
  change L ((fderiv ℝ (fun y => fderiv ℝ u y (basisVector i)) x) h) = _
  rw [hg]

/-- Each summand of `staticCurl u` is differentiable at `x` when `fderiv u`
is (local copy of the `CurlIdentities` private lemma). -/
private theorem differentiableAt_staticCurl_summand
    (u : VelocityField) (x : Space) (i : Fin 3)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    DifferentiableAt ℝ (fun y => basisVector i ⨯₃ fderiv ℝ u y (basisVector i)) x := by
  let L : Space →ₗ[ℝ] Space := crossProduct (basisVector i)
  have hdg : DifferentiableAt ℝ (fun y => fderiv ℝ u y (basisVector i)) x := by
    have heq : (fun y => fderiv ℝ u y (basisVector i)) =
      (ContinuousLinearMap.apply ℝ Space (basisVector i) ∘ fderiv ℝ u) := rfl
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ Space (basisVector i)).differentiableAt.comp x hu
  have heq : (fun y => basisVector i ⨯₃ fderiv ℝ u y (basisVector i)) =
    (L.toContinuousLinearMap ∘ (fun y => fderiv ℝ u y (basisVector i))) := rfl
  rw [heq]
  exact L.toContinuousLinearMap.differentiableAt.comp x hdg

/-- Differentiability of a cross product with a constant first factor. -/
private theorem differentiableAt_cross_const (a : Space) (F : Space → Space)
    (x : Space) (hF : DifferentiableAt ℝ F x) :
    DifferentiableAt ℝ (fun y => a ⨯₃ F y) x := by
  let L : Space →ₗ[ℝ] Space := crossProduct a
  have heq : (fun y => a ⨯₃ F y) = (L.toContinuousLinearMap ∘ F) := rfl
  rw [heq]
  exact L.toContinuousLinearMap.differentiableAt.comp x hF

/-- The derivative of `y ↦ a ⨯₃ F y` with constant first factor is the
cross product of `a` with the derivative of `F`. -/
private theorem fderiv_cross_const (a : Space) (F : Space → Space)
    (x h : Space) (hF : DifferentiableAt ℝ F x) :
    fderiv ℝ (fun y => a ⨯₃ F y) x h = a ⨯₃ (fderiv ℝ F x h) := by
  let L : Space →ₗ[ℝ] Space := crossProduct a
  have hL : HasFDerivAt (fun w => L w) L.toContinuousLinearMap (F x) :=
    L.toContinuousLinearMap.hasFDerivAt
  have hcomp := (HasFDerivAt.comp x hL hF.hasFDerivAt).fderiv
  change (fderiv ℝ ((fun w => L w) ∘ F) x) h = L (fderiv ℝ F x h)
  rw [hcomp]
  rfl

/-- **Curl–Laplacian commutation (static form).**  For a `C^3` velocity
field, `∇ × Δw = Δ(∇ × w)` pointwise: both sides expand into third-order
coordinate derivatives and close by the scalar Clairaut swap
`thirdDeriv_swap` componentwise plus finite-sum reindexing.  Viscous-term
identity of the vorticity transport derivation (Majda–Bertozzi §1.3, used
in (1.33)). -/
theorem staticCurl_laplacian_comm (w : VelocityField) (x : Space)
    (hw : ContDiff ℝ 3 w) :
    staticCurl (fun y => ∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) y (basisVector i)) x =
      ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (staticCurl w) y (basisVector i)) x
        (basisVector i) := by
  have hw2f : ContDiff ℝ 2 (fderiv ℝ w) := hw.fderiv_right (by norm_num)
  have hwf : ∀ y : Space, DifferentiableAt ℝ (fderiv ℝ w) y :=
    fun y => (hw2f.contDiffAt).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hwk : ∀ k : Fin 3, ContDiff ℝ 3 (fun z => w z k) :=
    fun k => contDiff_pi.mp hw k
  have hwd : ∀ (z : Space) (k : Fin 3), DifferentiableAt ℝ (fun z' => w z' k) z :=
    fun z k => (hwk k).differentiable (by norm_num : (3 : WithTop ℕ∞) ≠ 0) z
  have hF : ∀ i : Fin 3, ContDiff ℝ 2 (fun z => fderiv ℝ w z (basisVector i)) :=
    fun i => ((ContinuousLinearMap.apply ℝ Space (basisVector i)).contDiff).comp hw2f
  have hFd : ∀ (i : Fin 3) (y : Space) (k : Fin 3),
      DifferentiableAt ℝ (fun z => (fderiv ℝ w z (basisVector i)) k) y :=
    fun i y k => differentiableAt_pi.mp
      ((hF i).differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) y) k
  have hF1 : ∀ i : Fin 3,
      ContDiff ℝ 1 (fderiv ℝ (fun z => fderiv ℝ w z (basisVector i))) :=
    fun i => (hF i).fderiv_right (by norm_num)
  have hff : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ w)) := hw2f.fderiv_right (by norm_num)
  have hS1 : ∀ i : Fin 3, ContDiff ℝ 1
      (fun y => fderiv ℝ (fderiv ℝ w) y (basisVector i)) := by
    intro i
    let T : (Space →L[ℝ] (Space →L[ℝ] Space)) →L[ℝ] (Space →L[ℝ] Space) :=
      ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (basisVector i)
    exact (T.contDiff).comp hff
  have hS' : ∀ i j : Fin 3, ContDiff ℝ 1
      (fun y => (fderiv ℝ (fderiv ℝ w) y (basisVector i)) (basisVector j)) := by
    intro i j
    let T : (Space →L[ℝ] Space) →L[ℝ] Space :=
      ContinuousLinearMap.apply ℝ Space (basisVector j)
    exact (T.contDiff).comp (hS1 i)
  have hD : ∀ i : Fin 3, DifferentiableAt ℝ
      (fun y => fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) y
        (basisVector i)) x :=
    fun i => (ContinuousLinearMap.apply ℝ Space (basisVector i)).differentiableAt.comp x
      ((hF1 i).contDiffAt.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0))
  have hLHS : ∀ j : Fin 3,
      fderiv ℝ (fun y => ∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) y (basisVector i)) x
        (basisVector j) =
        ∑ i : Fin 3, fderiv ℝ (fun y =>
          fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) y (basisVector i)) x
          (basisVector j) := by
    intro j
    rw [fderiv_fun_sum (fun i _ => hD i)]
    rfl
  have hInner : ∀ (y : Space) (i : Fin 3),
      fderiv ℝ (staticCurl w) y (basisVector i) =
        ∑ j : Fin 3, basisVector j ⨯₃
          ((fderiv ℝ (fderiv ℝ w) y (basisVector i)) (basisVector j)) := by
    intro y i
    change (fderiv ℝ (∑ j : Fin 3,
        (fun z => basisVector j ⨯₃ fderiv ℝ w z (basisVector j))) y)
      (basisVector i) = _
    rw [fderiv_sum (fun j _ => differentiableAt_staticCurl_summand w y j (hwf y))]
    change (∑ j : Fin 3, (fderiv ℝ
        (fun z => basisVector j ⨯₃ fderiv ℝ w z (basisVector j)) y)
      (basisVector i)) = _
    exact Finset.sum_congr rfl (fun j _ =>
      fderiv_cross_basisVector_apply w y (basisVector i) j (hwf y))
  have hE : ∀ i j : Fin 3, DifferentiableAt ℝ
      (fun y => fderiv ℝ (fun z => fderiv ℝ w z (basisVector j)) y
        (basisVector i)) x :=
    fun i j => (ContinuousLinearMap.apply ℝ Space (basisVector i)).differentiableAt.comp x
      ((hF1 j).contDiffAt.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0))
  have hTU : ∀ i j : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) y
          (basisVector i)) x (basisVector j) =
        fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ w) y (basisVector i))
          (basisVector j)) x (basisVector i) := by
    intro i j
    rw [show (fun y => (fderiv ℝ (fderiv ℝ w) y (basisVector i))
          (basisVector j)) =
        (fun y => fderiv ℝ (fun z => fderiv ℝ w z (basisVector j)) y
          (basisVector i)) from
      funext (fun y => (fderiv_fderiv_apply_eq w y (basisVector j)
        (basisVector i) (hwf y)).symm)]
    ext k
    rw [fderiv_apply_component _ x (fun k' => differentiableAt_pi.mp (hD i) k')
        (basisVector j) k,
      fderiv_apply_component _ x (fun k' => differentiableAt_pi.mp (hE i j) k')
        (basisVector i) k]
    rw [show (fun y => (fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) y
          (basisVector i)) k) =
        (fun y => fderiv ℝ (fun z => (fderiv ℝ w z (basisVector i)) k) y
          (basisVector i)) from
      funext (fun y => fderiv_apply_component _ y (fun k' => hFd i y k')
        (basisVector i) k)]
    rw [show (fun y => (fderiv ℝ (fun z => fderiv ℝ w z (basisVector j)) y
          (basisVector i)) k) =
        (fun y => fderiv ℝ (fun z => (fderiv ℝ w z (basisVector j)) k) y
          (basisVector i)) from
      funext (fun y => fderiv_apply_component _ y (fun k' => hFd j y k')
        (basisVector i) k)]
    rw [show (fun z => (fderiv ℝ w z (basisVector i)) k) =
        (fun z => fderiv ℝ (fun z' => w z' k) z (basisVector i)) from
      funext (fun z => fderiv_apply_component w z (fun k' => hwd z k')
        (basisVector i) k)]
    rw [show (fun z => (fderiv ℝ w z (basisVector j)) k) =
        (fun z => fderiv ℝ (fun z' => w z' k) z (basisVector j)) from
      funext (fun z => fderiv_apply_component w z (fun k' => hwd z k')
        (basisVector j) k)]
    exact thirdDeriv_swap (fun z' => w z' k) (hwk k) x i j
  have hOuter : ∀ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (staticCurl w) y (basisVector i)) x
        (basisVector i) =
        ∑ j : Fin 3, basisVector j ⨯₃
          (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ w) y (basisVector i))
            (basisVector j)) x (basisVector i)) := by
    intro i
    rw [show (fun y => fderiv ℝ (staticCurl w) y (basisVector i)) =
        (fun y => ∑ j : Fin 3, basisVector j ⨯₃
          ((fderiv ℝ (fderiv ℝ w) y (basisVector i)) (basisVector j))) from
      funext (fun y => hInner y i)]
    rw [fderiv_fun_sum (fun j _ => differentiableAt_cross_const _ _ x
      ((hS' i j).contDiffAt.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)))]
    change (∑ j : Fin 3, (fderiv ℝ (fun y => basisVector j ⨯₃
        ((fderiv ℝ (fderiv ℝ w) y (basisVector i)) (basisVector j))) x)
      (basisVector i)) = _
    exact Finset.sum_congr rfl (fun j _ => fderiv_cross_const _ _ x _
      ((hS' i j).contDiffAt.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)))
  calc staticCurl (fun y => ∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) y (basisVector i)) x
      = ∑ j : Fin 3, basisVector j ⨯₃ (∑ i : Fin 3,
          fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) y
            (basisVector i)) x (basisVector j)) := by
        rw [staticCurl]
        exact Finset.sum_congr rfl (fun j _ =>
          congrArg (crossProduct (basisVector j)) (hLHS j))
    _ = ∑ j : Fin 3, ∑ i : Fin 3, basisVector j ⨯₃
          (fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) y
            (basisVector i)) x (basisVector j)) :=
        Finset.sum_congr rfl (fun j _ =>
          map_sum (crossProduct (basisVector j)) _ Finset.univ)
    _ = ∑ j : Fin 3, ∑ i : Fin 3, basisVector j ⨯₃
          (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ w) y (basisVector i))
            (basisVector j)) x (basisVector i)) :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ =>
          congrArg (crossProduct (basisVector j)) (hTU i j)))
    _ = ∑ i : Fin 3, ∑ j : Fin 3, basisVector j ⨯₃
          (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ w) y (basisVector i))
            (basisVector j)) x (basisVector i)) :=
        Finset.sum_comm
    _ = ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (staticCurl w) y (basisVector i)) x
          (basisVector i) :=
        Finset.sum_congr rfl (fun i _ => (hOuter i).symm)

/-- **Curl–Laplacian commutation (evolution form).**  On a smooth velocity
evolution, `∇ × Δu(t) = Δω(t)` at every nonnegative time `t`: the spatial
slice is `C^∞` by `contDiffAt_spatial_slice`, so the static commutation
applies to `w := u t`.  This is the viscous term of the vorticity
transport equation `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω`. -/
theorem staticCurl_laplacian_evolution_comm (u : VelocityEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    staticCurl (fun y => laplacian u t y) x =
      laplacian (fun s => vorticity u s) t x := by
  have hw3 : ContDiff ℝ 3 (u t) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact (contDiffAt_spatial_slice hu ht y).of_le
      (WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  have hmain := staticCurl_laplacian_comm (u t) x hw3
  rw [show (fun y => laplacian u t y) = (fun y => ∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (u t) z (basisVector i)) y (basisVector i)) from rfl]
  rw [show laplacian (fun s => vorticity u s) t x = ∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (staticCurl (u t)) y (basisVector i)) x
        (basisVector i) from rfl]
  exact hmain

end Navier.Analysis.VorticityTransport
