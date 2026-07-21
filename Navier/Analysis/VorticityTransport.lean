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

/-!
### Time–space Clairaut: the curl commutes with `∂ₜ`

`timeDerivative` is one-sided (`fderivWithin` on `Set.Ici 0`), so
`∇ × ∂ₜu = ∂ₜ(∇ × u)` is a boundary-layer statement.  Both mixed
partials are directional evaluations of the joint second
within-derivative of `z ↦ u z.1 z.2` on `Set.Ici 0 ×ˢ Set.univ`, and
they agree by `ContDiffWithinAt.isSymmSndFDerivWithinAt`.  The slice
embeddings `s ↦ (s, y)` and `y ↦ (t, y)` transport within-derivatives
of the joint function to the one-sided time derivative and the full
spatial derivative respectively; the spatial direction is interior,
the time direction sits at the unique-differentiability point of
`Set.Ici 0`.
-/

/-- **Time-slice bridge.**  The one-sided time derivative of a jointly
smooth evolution equals the joint within-derivative along `(1, 0)`.
Generic in the codomain so scalar components and full vectors share one
proof. -/
private theorem fderivWithin_time_slice_apply {β : Type*} [NormedAddCommGroup β]
    [NormedSpace ℝ β] {F : ℝ → Space → β}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Space => F z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) (y : Space) :
    fderivWithin ℝ (fun s => F s y) (Set.Ici 0) t 1 =
      fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, y) (1, 0) := by
  have hmem : (t, y) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ :=
    Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht, Set.mem_univ y⟩
  have hG : HasFDerivWithinAt (fun z : ℝ × Space => F z.1 z.2)
      (fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, y))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, y) :=
    ((hF (t, y) hmem).differentiableWithinAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)).hasFDerivWithinAt
  have hι : HasFDerivAt (fun s : ℝ => (s, y))
      (ContinuousLinearMap.inl ℝ ℝ Space) t := hasFDerivAt_prodMk_left t y
  have hmaps : Set.MapsTo (fun s : ℝ => (s, y)) (Set.Ici 0)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun s hs =>
    Set.mem_prod.mpr ⟨hs, Set.mem_univ y⟩
  have hcomp := HasFDerivWithinAt.comp t hG hι.hasFDerivWithinAt hmaps
  rw [show ((fun z : ℝ × Space => F z.1 z.2) ∘ (fun s : ℝ => (s, y))) =
      (fun s => F s y) from rfl] at hcomp
  rw [hcomp.fderivWithin ((uniqueDiffOn_Ici 0) t (Set.mem_Ici.mpr ht)),
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- **Space-slice bridge.**  The full spatial derivative of a
nonnegative-time slice equals the joint within-derivative along
`(0, v)`. -/
private theorem fderiv_space_slice_apply {β : Type*} [NormedAddCommGroup β]
    [NormedSpace ℝ β] {F : ℝ → Space → β}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Space => F z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs : 0 ≤ s) (x v : Space) :
    fderiv ℝ (F s) x v =
      fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) (s, x) (0, v) := by
  have hmem : (s, x) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ :=
    Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hs, Set.mem_univ x⟩
  have hG : HasFDerivWithinAt (fun z : ℝ × Space => F z.1 z.2)
      (fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) (s, x))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) (s, x) :=
    ((hF (s, x) hmem).differentiableWithinAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)).hasFDerivWithinAt
  have hκ : HasFDerivAt (fun y : Space => (s, y))
      (ContinuousLinearMap.inr ℝ ℝ Space) x := hasFDerivAt_prodMk_right s x
  have hmaps : Set.MapsTo (fun y : Space => (s, y)) Set.univ
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun y _ =>
    Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hs, Set.mem_univ y⟩
  have hcomp := HasFDerivWithinAt.comp x hG hκ.hasFDerivWithinAt hmaps
  rw [show ((fun z : ℝ × Space => F z.1 z.2) ∘ (fun y : Space => (s, y))) =
      F s from rfl] at hcomp
  have hAt : HasFDerivAt (F s)
      ((fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) (s, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
    hcomp.hasFDerivAt Filter.univ_mem
  rw [hAt.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- **Eval bridge.**  The within-derivative of an evaluated
within-derivative field is the second within-derivative evaluated in
the other order: `D(Dg(v))(w) = D²g(w)(v)`. -/
private theorem fderivWithin_eval_apply {β : Type*} [NormedAddCommGroup β]
    [NormedSpace ℝ β] {g : ℝ × Space → β} {S : Set (ℝ × Space)}
    {z : ℝ × Space}
    (hg : DifferentiableWithinAt ℝ (fderivWithin ℝ g S) S z)
    (hs : UniqueDiffWithinAt ℝ S z) (v w : ℝ × Space) :
    fderivWithin ℝ (fun z' => fderivWithin ℝ g S z' v) S z w =
      fderivWithin ℝ (fderivWithin ℝ g S) S z w v := by
  let T : ((ℝ × Space) →L[ℝ] β) →L[ℝ] β :=
    ContinuousLinearMap.apply ℝ β v
  have hT : HasFDerivWithinAt
      (fun z' => fderivWithin ℝ g S z' v)
      (T.comp (fderivWithin ℝ (fderivWithin ℝ g S) S z)) S z := by
    have hcomp := HasFDerivWithinAt.comp z T.hasFDerivWithinAt
      hg.hasFDerivWithinAt (fun z' _ => Set.mem_univ _)
    rw [show (T ∘ (fderivWithin ℝ g S)) =
        (fun z' => fderivWithin ℝ g S z' v) from rfl] at hcomp
    exact hcomp
  have hfw := hT.fderivWithin hs
  calc fderivWithin ℝ (fun z' => fderivWithin ℝ g S z' v) S z w
      = (T.comp (fderivWithin ℝ (fderivWithin ℝ g S) S z)) w := by rw [hfw]
    _ = fderivWithin ℝ (fderivWithin ℝ g S) S z w v := rfl

/-- The time curve `s ↦ u s y` is differentiable within `Set.Ici 0` at
every `t ≥ 0`. -/
private theorem differentiableWithinAt_time_curve (u : VelocityEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u) {t : ℝ} (ht : 0 ≤ t) (y : Space) :
    DifferentiableWithinAt ℝ (fun s => u s y) (Set.Ici 0) t := by
  have hmem : (t, y) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ :=
    Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht, Set.mem_univ y⟩
  have hG : DifferentiableWithinAt ℝ (fun z : ℝ × Space => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, y) :=
    (hu (t, y) hmem).differentiableWithinAt (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hmaps : Set.MapsTo (fun s : ℝ => (s, y)) (Set.Ici 0)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun s hs =>
    Set.mem_prod.mpr ⟨hs, Set.mem_univ y⟩
  have hcomp := hG.comp t
    (hasFDerivAt_prodMk_left t y).hasFDerivWithinAt.differentiableWithinAt hmaps
  rw [show ((fun z : ℝ × Space => u z.1 z.2) ∘ (fun s : ℝ => (s, y))) =
      (fun s => u s y) from rfl] at hcomp
  exact hcomp

/-- **Component bridge within.**  The `k`-th component of the one-sided
time derivative of a vector curve is the one-sided time derivative of
the `k`-th component. -/
private theorem fderivWithin_component_apply (w : ℝ → Space) (t : ℝ)
    (ht : 0 ≤ t) (hw : DifferentiableWithinAt ℝ w (Set.Ici 0) t) (k : Fin 3) :
    (fderivWithin ℝ w (Set.Ici 0) t 1) k =
      fderivWithin ℝ (fun s => w s k) (Set.Ici 0) t 1 := by
  have h := fderivWithin_apply hw ((uniqueDiffOn_Ici 0) t (Set.mem_Ici.mpr ht)) k
  rw [h, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- The spatial derivative field `s ↦ fderiv ℝ (u s) x (eᵢ)` is
differentiable within `Set.Ici 0` at `t ≥ 0`: on the half-line it
agrees with the joint within-derivative along `(0, eᵢ)` pulled back
along the time curve. -/
private theorem differentiableWithinAt_spaceDeriv_curve (u : VelocityEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u) {t : ℝ} (ht : 0 ≤ t) (x : Space)
    (i : Fin 3) :
    DifferentiableWithinAt ℝ (fun s => fderiv ℝ (u s) x (basisVector i))
      (Set.Ici 0) t := by
  set S : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ Set.univ with hSdef
  set G : ℝ × Space → Space := fun z => u z.1 z.2 with hGdef
  have hUD : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hz : (t, x) ∈ S := Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht, Set.mem_univ x⟩
  have hg2 : ContDiffWithinAt ℝ ∞ G S (t, x) := hu (t, x) hz
  have hDg : DifferentiableWithinAt ℝ (fderivWithin ℝ G S) S (t, x) :=
    (hg2.fderivWithin_right hUD (by decide) hz).differentiableWithinAt one_ne_zero
  have hH : DifferentiableWithinAt ℝ
      (fun z' => fderivWithin ℝ G S z' ((0, basisVector i) : ℝ × Space))
      S (t, x) := by
    let T : ((ℝ × Space) →L[ℝ] Space) →L[ℝ] Space :=
      ContinuousLinearMap.apply ℝ Space ((0, basisVector i) : ℝ × Space)
    have hcomp := DifferentiableWithinAt.comp (t, x)
      (T.differentiableAt).differentiableWithinAt hDg (fun z' _ => Set.mem_univ _)
    rw [show (T ∘ (fderivWithin ℝ G S)) =
        (fun z' => fderivWithin ℝ G S z' ((0, basisVector i) : ℝ × Space))
        from rfl] at hcomp
    exact hcomp
  have hmaps : Set.MapsTo (fun s : ℝ => (s, x)) (Set.Ici 0) S := fun s hs =>
    Set.mem_prod.mpr ⟨hs, Set.mem_univ x⟩
  have hcomp := hH.comp t
    (hasFDerivAt_prodMk_left t x).hasFDerivWithinAt.differentiableWithinAt hmaps
  rw [show ((fun z' => fderivWithin ℝ G S z' (0, basisVector i)) ∘
      (fun s : ℝ => (s, x))) =
      (fun s => fderivWithin ℝ G S (s, x) (0, basisVector i)) from rfl] at hcomp
  refine hcomp.congr (fun s hs => ?_) ?_
  · exact fderiv_space_slice_apply hu (Set.mem_Ici.mp hs) x (basisVector i)
  · exact fderiv_space_slice_apply hu ht x (basisVector i)

/-- Each component of the (one-sided) time-derivative field is spatially
differentiable: it is the joint within-derivative along `(1, 0)` pulled
back along the space curve, an interior direction. -/
private theorem differentiableAt_timeDeriv_component (u : VelocityEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u) {t : ℝ} (ht : 0 ≤ t) (x : Space)
    (k : Fin 3) :
    DifferentiableAt ℝ (fun y => fderivWithin ℝ (fun s => u s y k)
      (Set.Ici 0) t 1) x := by
  set S : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ Set.univ with hSdef
  set g : ℝ × Space → ℝ := fun z => u z.1 z.2 k with hgdef
  have hUD : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hz : (t, x) ∈ S := Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht, Set.mem_univ x⟩
  have hgc : ContDiffOn ℝ ∞ g S := contDiffOn_pi.mp hu k
  have hg2 : ContDiffWithinAt ℝ ∞ g S (t, x) := hgc (t, x) hz
  have hDg : DifferentiableWithinAt ℝ (fderivWithin ℝ g S) S (t, x) :=
    (hg2.fderivWithin_right hUD (by decide) hz).differentiableWithinAt one_ne_zero
  have hH : DifferentiableWithinAt ℝ
      (fun z' => fderivWithin ℝ g S z' ((1, 0) : ℝ × Space)) S (t, x) := by
    let T : ((ℝ × Space) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × Space)
    have hcomp := DifferentiableWithinAt.comp (t, x)
      (T.differentiableAt).differentiableWithinAt hDg (fun z' _ => Set.mem_univ _)
    rw [show (T ∘ (fderivWithin ℝ g S)) =
        (fun z' => fderivWithin ℝ g S z' ((1, 0) : ℝ × Space)) from rfl] at hcomp
    exact hcomp
  have hmaps : Set.MapsTo (fun y : Space => (t, y)) Set.univ S := fun y _ =>
    Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht, Set.mem_univ y⟩
  have hcomp := hH.comp x
    (hasFDerivAt_prodMk_right t x).hasFDerivWithinAt.differentiableWithinAt hmaps
  rw [show ((fun z' => fderivWithin ℝ g S z' (1, 0)) ∘
      (fun y : Space => (t, y))) =
      (fun y => fderivWithin ℝ g S (t, y) (1, 0)) from rfl] at hcomp
  have hAt : DifferentiableAt ℝ (fun y => fderivWithin ℝ g S (t, y) (1, 0)) x :=
    hcomp.differentiableAt Filter.univ_mem
  have heq : (fun y => fderivWithin ℝ (fun s => u s y k) (Set.Ici 0) t 1)
      = (fun y => fderivWithin ℝ g S (t, y) (1, 0)) :=
    funext fun y =>
      fderivWithin_time_slice_apply (F := fun s y => u s y k) hgc ht y
  rw [heq]; exact hAt

/-- **Time–space Clairaut (scalar).**  For a smooth velocity evolution,
the spatial derivative of the (one-sided) time derivative equals the
(one-sided) time derivative of the spatial derivative, componentwise.
Both sides are the joint second within-derivative of the component
function `z ↦ u z.1 z.2 k` on the half-space, evaluated along
`((0, v), (1, 0))` in the two orders; they agree by symmetry of the
second within-derivative on a unique-differentiability domain. -/
private theorem timeDeriv_spaceDeriv_comm_scalar (u : VelocityEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u) {t : ℝ} (ht : 0 ≤ t) (x v : Space)
    (k : Fin 3) :
    fderiv ℝ (fun y => fderivWithin ℝ (fun s => u s y k) (Set.Ici 0) t 1) x v =
      fderivWithin ℝ (fun s => fderiv ℝ (fun y => u s y k) x v)
        (Set.Ici 0) t 1 := by
  set S : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ Set.univ with hSdef
  set g : ℝ × Space → ℝ := fun z => u z.1 z.2 k with hgdef
  have hUD : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hz : (t, x) ∈ S := Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht, Set.mem_univ x⟩
  have hgc : ContDiffOn ℝ ∞ g S := contDiffOn_pi.mp hu k
  have hg2 : ContDiffWithinAt ℝ ∞ g S (t, x) := hgc (t, x) hz
  have hcl : (t, x) ∈ closure (interior S) := by
    have hint : interior S = Set.Ioi (0 : ℝ) ×ˢ Set.univ := by
      rw [hSdef, interior_prod_eq, interior_Ici, interior_univ]
    rw [hint, closure_prod_eq, closure_Ioi, closure_univ]
    exact hz
  have hSymm : IsSymmSndFDerivWithinAt ℝ g S (t, x) :=
    hg2.isSymmSndFDerivWithinAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; decide) hUD hcl hz
  have hDg : DifferentiableWithinAt ℝ (fderivWithin ℝ g S) S (t, x) :=
    (hg2.fderivWithin_right hUD (by decide) hz).differentiableWithinAt one_ne_zero
  have hT : ∀ w : ℝ × Space, DifferentiableWithinAt ℝ
      (fun z' => fderivWithin ℝ g S z' w) S (t, x) := by
    intro w
    let T : ((ℝ × Space) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ w
    have hcomp := DifferentiableWithinAt.comp (t, x)
      (T.differentiableAt).differentiableWithinAt hDg (fun z' _ => Set.mem_univ _)
    rw [show (T ∘ (fderivWithin ℝ g S)) =
        (fun z' => fderivWithin ℝ g S z' w) from rfl] at hcomp
    exact hcomp
  have hLHSfun : (fun y => fderivWithin ℝ (fun s => u s y k) (Set.Ici 0) t 1)
      = (fun y => fderivWithin ℝ g S (t, y) (1, 0)) :=
    funext fun y =>
      fderivWithin_time_slice_apply (F := fun s y => u s y k) hgc ht y
  have hLchain : HasFDerivAt (fun y => fderivWithin ℝ g S (t, y) (1, 0))
      ((fderivWithin ℝ (fun z' => fderivWithin ℝ g S z' (1, 0)) S (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
    have hκ : HasFDerivAt (fun y : Space => (t, y))
        (ContinuousLinearMap.inr ℝ ℝ Space) x := hasFDerivAt_prodMk_right t x
    have hmaps : Set.MapsTo (fun y : Space => (t, y)) Set.univ S := fun y _ =>
      Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht, Set.mem_univ y⟩
    have hcomp := HasFDerivWithinAt.comp x (hT ((1, 0) : ℝ × Space)).hasFDerivWithinAt
      hκ.hasFDerivWithinAt hmaps
    rw [show ((fun z' => fderivWithin ℝ g S z' ((1, 0) : ℝ × Space)) ∘
        (fun y : Space => (t, y))) =
        (fun y => fderivWithin ℝ g S (t, y) ((1, 0) : ℝ × Space)) from rfl] at hcomp
    exact hcomp.hasFDerivAt Filter.univ_mem
  have hLHS : fderiv ℝ (fun y => fderivWithin ℝ (fun s => u s y k)
        (Set.Ici 0) t 1) x v
      = fderivWithin ℝ (fderivWithin ℝ g S) S (t, x) (0, v) (1, 0) := by
    rw [hLHSfun, hLchain.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]
    exact fderivWithin_eval_apply hDg (hUD (t, x) hz) (1, 0) (0, v)
  have hRinner : ∀ s : ℝ, 0 ≤ s → fderiv ℝ (fun y => u s y k) x v
      = fderivWithin ℝ g S (s, x) (0, v) := fun s hs =>
    fderiv_space_slice_apply (F := fun s y => u s y k) hgc hs x v
  have hRHSfun : Set.EqOn (fun s => fderiv ℝ (fun y => u s y k) x v)
      (fun s => fderivWithin ℝ g S (s, x) (0, v)) (Set.Ici 0) :=
    fun s hs => hRinner s (Set.mem_Ici.mp hs)
  have hRchain : HasFDerivWithinAt
      (fun s => fderivWithin ℝ g S (s, x) (0, v))
      ((fderivWithin ℝ (fun z' => fderivWithin ℝ g S z' (0, v)) S (t, x)).comp
        (ContinuousLinearMap.inl ℝ ℝ Space)) (Set.Ici 0) t := by
    have hι : HasFDerivAt (fun s : ℝ => (s, x))
        (ContinuousLinearMap.inl ℝ ℝ Space) t := hasFDerivAt_prodMk_left t x
    have hmaps : Set.MapsTo (fun s : ℝ => (s, x)) (Set.Ici 0) S := fun s hs =>
      Set.mem_prod.mpr ⟨hs, Set.mem_univ x⟩
    have hcomp := HasFDerivWithinAt.comp t (hT ((0, v) : ℝ × Space)).hasFDerivWithinAt
      hι.hasFDerivWithinAt hmaps
    rw [show ((fun z' => fderivWithin ℝ g S z' ((0, v) : ℝ × Space)) ∘
        (fun s : ℝ => (s, x))) =
        (fun s => fderivWithin ℝ g S (s, x) ((0, v) : ℝ × Space)) from rfl] at hcomp
    exact hcomp
  have hRHS : fderivWithin ℝ (fun s => fderiv ℝ (fun y => u s y k) x v)
        (Set.Ici 0) t 1
      = fderivWithin ℝ (fderivWithin ℝ g S) S (t, x) (1, 0) (0, v) := by
    rw [fderivWithin_congr hRHSfun (hRinner t ht)]
    rw [(hRchain.fderivWithin ((uniqueDiffOn_Ici 0) t (Set.mem_Ici.mpr ht))),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    exact fderivWithin_eval_apply hDg (hUD (t, x) hz) (0, v) (1, 0)
  rw [hLHS, hRHS]
  exact hSymm (0, v) (1, 0)

/-- **Within cross-const.**  The one-sided time derivative of
`s ↦ a ⨯₃ G s` is `a ⨯₃` the one-sided time derivative of `G`. -/
private theorem fderivWithin_cross_const_apply (a : Space) (G : ℝ → Space)
    {t : ℝ} (ht : 0 ≤ t) (hG : DifferentiableWithinAt ℝ G (Set.Ici 0) t) :
    fderivWithin ℝ (fun s => a ⨯₃ G s) (Set.Ici 0) t 1 =
      a ⨯₃ (fderivWithin ℝ G (Set.Ici 0) t 1) := by
  let L : Space →ₗ[ℝ] Space := crossProduct a
  have key : fderivWithin ℝ (fun s => a ⨯₃ G s) (Set.Ici 0) t =
      L.toContinuousLinearMap.comp (fderivWithin ℝ G (Set.Ici 0) t) := by
    have hcomp : HasFDerivWithinAt ((fun w => L w) ∘ G)
        (L.toContinuousLinearMap.comp (fderivWithin ℝ G (Set.Ici 0) t))
        (Set.Ici 0) t :=
      HasFDerivWithinAt.comp t L.toContinuousLinearMap.hasFDerivWithinAt
        hG.hasFDerivWithinAt (fun s _ => Set.mem_univ _)
    rw [show ((fun w => L w) ∘ G) = (fun s => a ⨯₃ G s) from rfl] at hcomp
    exact hcomp.fderivWithin ((uniqueDiffOn_Ici 0) t (Set.mem_Ici.mpr ht))
  rw [key, ContinuousLinearMap.comp_apply]
  rfl

/-- **Time leaf.**  The curl commutes with the (one-sided) time
derivative on the nonnegative-time half-space: `∇ × ∂ₜu = ∂ₜω`.  Both
sides expand to sums of `eᵢ ⨯₃` applied to mixed time–space derivatives
of the components, which agree by the scalar Clairaut leaf
`timeDeriv_spaceDeriv_comm_scalar`. -/
theorem staticCurl_timeDerivative_comm (u : VelocityEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    staticCurl (fun y => timeDerivative u t y) x =
      timeDerivative (fun s => vorticity u s) t x := by
  have hsum : ∀ w : VelocityField, staticCurl w x =
      ∑ i, basisVector i ⨯₃ (fderiv ℝ w x (basisVector i)) := fun w => rfl
  rw [hsum]
  show (∑ i, basisVector i ⨯₃ (fderiv ℝ (fun y => timeDerivative u t y) x
      (basisVector i))) =
      fderivWithin ℝ (fun s => staticCurl (u s) x) (Set.Ici 0) t 1
  rw [show (fun s => staticCurl (u s) x) =
      (fun s => ∑ i, basisVector i ⨯₃ (fderiv ℝ (u s) x (basisVector i)))
      from funext fun s => hsum (u s)]
  have hD : ∀ i : Fin 3, DifferentiableWithinAt ℝ
      (fun s => fderiv ℝ (u s) x (basisVector i)) (Set.Ici 0) t :=
    fun i => differentiableWithinAt_spaceDeriv_curve u hu ht x i
  have hsumD : ∀ i : Fin 3, DifferentiableWithinAt ℝ
      (fun s => basisVector i ⨯₃ (fderiv ℝ (u s) x (basisVector i)))
      (Set.Ici 0) t := by
    intro i
    have hc := DifferentiableAt.comp_differentiableWithinAt t
      ((crossProduct (basisVector i)).toContinuousLinearMap).differentiableAt (hD i)
    rw [show ((crossProduct (basisVector i)).toContinuousLinearMap ∘
        (fun s => fderiv ℝ (u s) x (basisVector i))) =
        (fun s => basisVector i ⨯₃ (fderiv ℝ (u s) x (basisVector i)))
        from rfl] at hc
    exact hc
  rw [fderivWithin_fun_sum ((uniqueDiffOn_Ici 0) t (Set.mem_Ici.mpr ht))
    (fun i _ => hsumD i), sum_apply]
  rw [show (∑ i, fderivWithin ℝ (fun s =>
        basisVector i ⨯₃ (fderiv ℝ (u s) x (basisVector i))) (Set.Ici 0) t 1) =
      (∑ i, basisVector i ⨯₃ (fderivWithin ℝ (fun s =>
        fderiv ℝ (u s) x (basisVector i)) (Set.Ici 0) t 1)) from
    Finset.sum_congr rfl fun i _ =>
      fderivWithin_cross_const_apply (basisVector i)
        (fun s => fderiv ℝ (u s) x (basisVector i)) ht (hD i)]
  have hDd : ∀ k : Fin 3, DifferentiableAt ℝ
      (fun y => (fderivWithin ℝ (fun s => u s y) (Set.Ici 0) t 1) k) x := by
    intro k
    have heq : (fun y => (fderivWithin ℝ (fun s => u s y) (Set.Ici 0) t 1) k) =
        (fun y => fderivWithin ℝ (fun s => u s y k) (Set.Ici 0) t 1) :=
      funext fun y => fderivWithin_component_apply _ t ht
        (differentiableWithinAt_time_curve u hu ht y) k
    rw [heq]
    exact differentiableAt_timeDeriv_component u hu ht x k
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  funext k
  have hcomp1 : (fderiv ℝ (fun y => timeDerivative u t y) x (basisVector i)) k
      = fderiv ℝ (fun y => timeDerivative u t y k) x (basisVector i) :=
    fderiv_apply_component _ x (fun k' => hDd k') _ k
  have hFeq : (fun y => timeDerivative u t y k) =
      (fun y => fderivWithin ℝ (fun s => u s y k) (Set.Ici 0) t 1) :=
    funext fun y => fderivWithin_component_apply _ t ht
      (differentiableWithinAt_time_curve u hu ht y) k
  have hcomp2 : fderiv ℝ (fun y => timeDerivative u t y k) x (basisVector i)
      = fderivWithin ℝ (fun s => fderiv ℝ (fun y => u s y k) x
          (basisVector i)) (Set.Ici 0) t 1 := by
    rw [hFeq]
    exact timeDeriv_spaceDeriv_comm_scalar u hu ht x (basisVector i) k
  have hcomp3 : (fderivWithin ℝ (fun s => fderiv ℝ (u s) x (basisVector i))
        (Set.Ici 0) t 1) k
      = fderivWithin ℝ (fun s => fderiv ℝ (fun y => u s y k) x
          (basisVector i)) (Set.Ici 0) t 1 := by
    rw [fderivWithin_component_apply _ t ht (hD i) k]
    have hfun : fderivWithin ℝ (fun s => (fderiv ℝ (u s) x (basisVector i)) k)
          (Set.Ici 0) t =
        fderivWithin ℝ (fun s => fderiv ℝ (fun y => u s y k) x (basisVector i))
          (Set.Ici 0) t := by
      apply fderivWithin_congr
      · intro s hs
        exact fderiv_apply_component _ x (fun k' =>
          differentiableAt_pi.mp ((contDiffAt_spatial_slice hu
            (Set.mem_Ici.mp hs) x).differentiableAt (by decide)) k') _ k
      · exact fderiv_apply_component _ x (fun k' =>
          differentiableAt_pi.mp ((contDiffAt_spatial_slice hu ht
            x).differentiableAt (by decide)) k') _ k
    rw [hfun]
  rw [hcomp1, hcomp2, hcomp3]



/-!
### Curl linearity and the partial vorticity transport identity

Curl is linear on pointwise sums / differences / scalar multiples at a point
of joint differentiability.  Combined with the three commutation leaves above,
the curl of the (unforced) Navier–Stokes momentum equation reduces to
`∂ₜω + curl(convection u t) = ν • Δω` pointwise: the pressure-gradient term
dies (`curl ∘ ∇ = 0`), `∂ₜ` commutes past `curl`, and `Δ` commutes past `curl`.
The remaining leaf for the full Majda–Bertozzi (1.33) transport PDE
`∂ₜω + (u·∇)ω = (ω·∇)u + νΔω` is the convection–curl identity
`curl((u·∇)u) = (u·∇)ω − (ω·∇)u`, valid under `div u = div ω = 0`.
-/

/-- Curl of a pointwise sum at a joint-differentiability point. -/
private theorem staticCurl_add_field (a b : VelocityField) (x : Space)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    staticCurl (fun y => a y + b y) x = staticCurl a x + staticCurl b x := by
  unfold staticCurl
  rw [show (fun y => a y + b y) = (a + b) from rfl, fderiv_add ha hb]
  simp only [add_apply, Finset.sum_add_distrib, LinearMap.map_add]

/-- Curl of a pointwise difference at a joint-differentiability point. -/
private theorem staticCurl_sub_field (a b : VelocityField) (x : Space)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    staticCurl (fun y => a y - b y) x = staticCurl a x - staticCurl b x := by
  unfold staticCurl
  rw [show (fun y => a y - b y) = (a - b) from rfl, fderiv_sub ha hb]
  simp only [sub_apply, Finset.sum_sub_distrib, LinearMap.map_sub]

/-- Curl of a pointwise scalar multiple at a differentiability point. -/
private theorem staticCurl_smul_field (c : ℝ) (a : VelocityField) (x : Space)
    (ha : DifferentiableAt ℝ a x) :
    staticCurl (fun y => c • a y) x = c • staticCurl a x := by
  unfold staticCurl
  rw [show (fun y => c • a y) = (c • a) from rfl, fderiv_const_smul ha]
  simp only [smul_apply, LinearMap.map_smul, Finset.smul_sum]

/- **Curl of the unforced momentum equation = partial vorticity transport.**
At every nonnegative time `t` and every spatial point `x` along a classical
solution, taking the spatial curl of the momentum equation
`∂ₜu + (u·∇)u = νΔu − ∇p`, killing the pressure-gradient term by
`staticCurl_pressureGradient_eq_zero`, commuting `∂ₜ` past `curl` via
`staticCurl_timeDerivative_comm`, and commuting `Δ` past `curl` via
`staticCurl_laplacian_evolution_comm` gives

  `∂ₜω + curl((u·∇)u) = ν • Δω`.

The remaining leaf for the full Majda–Bertozzi (1.33) transport PDE
`∂ₜω + (u·∇)ω = (ω·∇)u + νΔω` is the convection–curl identity
`curl((u·∇)u) = (u·∇)ω − (ω·∇)u`, valid under `div u = div ω = 0`.
Reference: Majda–Bertozzi, *Vorticity and Incompressible Flow*, §1.3, (1.33). -/
theorem curl_of_momentum_eq_partial_vorticity_transport
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    timeDerivative (fun s => vorticity u s) t x +
      staticCurl (fun y => convection u t y) x =
      ν • laplacian (fun s => vorticity u s) t x := by
  -- Spatial slices are C^∞ at x
  have huA : ContDiffAt ℝ ∞ (u t) x :=
    contDiffAt_spatial_slice hsol.velocity_smooth ht x
  have hpA : ContDiffAt ℝ ∞ (p t) x :=
    contDiffAt_spatial_slice hsol.pressure_smooth ht x
  have huAfd : ContDiffAt ℝ ∞ (fderiv ℝ (u t)) x := huA.fderiv_right (by simp)
  -- Differentiability of the four Fréchet-smooth component fields at x
  have hD_time : DifferentiableAt ℝ (fun y => timeDerivative u t y) x := by
    apply differentiableAt_pi.mpr
    intro k
    have heq : (fun y => timeDerivative u t y k) =
        (fun y => fderivWithin ℝ (fun s => u s y k) (Set.Ici 0) t 1) := by
      funext y
      exact fderivWithin_component_apply (fun s => u s y) t ht
        (differentiableWithinAt_time_curve u hsol.velocity_smooth ht y) k
    rw [heq]
    exact differentiableAt_timeDeriv_component u hsol.velocity_smooth ht x k
  have hD_conv : DifferentiableAt ℝ (fun y => convection u t y) x :=
    (huAfd.clm_apply huA).differentiableAt (by decide)
  have hD_pg : DifferentiableAt ℝ (fun y => pressureGradient p t y) x := by
    have hpfd : ContDiffAt ℝ ∞ (fderiv ℝ (p t)) x := hpA.fderiv_right (by simp)
    rw [show (fun y => pressureGradient p t y) =
        (fun y i => fderiv ℝ (p t) y (basisVector i)) from rfl]
    apply differentiableAt_pi.mpr
    intro i
    exact ((ContinuousLinearMap.apply ℝ ℝ (basisVector i)).contDiff.contDiffAt).comp x hpfd |>.differentiableAt
      (by decide)
  have hD_lap : DifferentiableAt ℝ (laplacian u t) x := by
    rw [show (laplacian u t : VelocityField) =
        (∑ i : Fin 3, fun y =>
          fderiv ℝ (fun z => fderiv ℝ (u t) z (basisVector i)) y (basisVector i))
      from by ext y; simp only [laplacian, Finset.sum_apply]]
    apply DifferentiableAt.sum
    intro i hi
    have hg : ContDiffAt ℝ ∞
        (fun z => fderiv ℝ (u t) z (basisVector i)) x :=
      ((ContinuousLinearMap.apply ℝ Space (basisVector i)).contDiff.contDiffAt).comp x huAfd
    have hg' : ContDiffAt ℝ ∞
        (fderiv ℝ (fun z => fderiv ℝ (u t) z (basisVector i))) x :=
      hg.fderiv_right (by simp)
    have hg'eval : ContDiffAt ℝ ∞
        (fun y => fderiv ℝ (fun z => fderiv ℝ (u t) z (basisVector i)) y
          (basisVector i)) x :=
      ((ContinuousLinearMap.apply ℝ Space (basisVector i)).contDiff.contDiffAt).comp x hg'
    exact hg'eval.differentiableAt (by decide)
  -- Momentum equation (unforced: zeroForce = 0)
  have hMom : ∀ y : Space,
      timeDerivative u t y + convection u t y =
        ν • laplacian u t y - pressureGradient p t y := by
    intro y
    have h := hsol.equation t ht y
    simp only [zeroForce, add_zero] at h
    exact h
  -- Apply staticCurl to both sides of the momentum equation at x
  have hCurl : staticCurl (fun y => timeDerivative u t y + convection u t y) x =
      staticCurl (fun y => ν • laplacian u t y - pressureGradient p t y) x := by
    congr 1
    funext y
    exact hMom y
  -- Split LHS via curl linearity, then commute ∂ₜ past curl
  rw [staticCurl_add_field _ _ _ hD_time hD_conv] at hCurl
  rw [staticCurl_timeDerivative_comm u hsol.velocity_smooth ht x] at hCurl
  -- Split RHS via curl linearity on the smul-and-sub
  have hD_smul_lap : DifferentiableAt ℝ (fun y => ν • laplacian u t y) x := by
    rw [show (fun y => ν • laplacian u t y) = (ν • laplacian u t) from rfl]
    exact hD_lap.const_smul ν
  rw [staticCurl_sub_field (fun y => ν • laplacian u t y)
        (fun y => pressureGradient p t y) x hD_smul_lap hD_pg] at hCurl
  rw [staticCurl_smul_field ν (laplacian u t) x hD_lap] at hCurl
  -- Apply the three commutation leaves
  rw [staticCurl_laplacian_evolution_comm u hsol.velocity_smooth ht x] at hCurl
  rw [staticCurl_pressureGradient_eq_zero p hsol.pressure_smooth ht x] at hCurl
  rw [sub_zero] at hCurl
  exact hCurl



/-- **Reduction of the full vorticity transport PDE to the convection–curl
identity.**  Given the partial transport identity
`curl_of_momentum_eq_partial_vorticity_transport` (the curl of the momentum
equation, with all three Clairaut commutations applied), the full Majda–Bertozzi
(1.33) pointwise vorticity transport PDE
  `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω`
holds at `(t, x)` iff the convection–curl identity
  `curl((u·∇)u) = (u·∇)ω − (ω·∇)u`
holds at `(t, x)`.  The latter is a pure vector-calculus identity under
`div u = div ω = 0` (the `div ω = 0` half is `staticDivergence_staticCurl_eq_zero`;
the `div u = 0` half is the classical-solution incompressibility hypothesis).
The convection–curl identity is the named residual for the full
`Navier.Analysis.Enstrophy.vorticityTransportEquation`. -/
theorem vorticityTransport_eq_partial_and_convection_curl
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    (timeDerivative (fun s => vorticity u s) t x +
        spatialDerivative (fun s => vorticity u s) t x (u t x) =
      spatialDerivative u t x (vorticity u t x) +
        ν • laplacian (fun s => vorticity u s) t x)
    ↔
    (staticCurl (fun y => convection u t y) x =
      spatialDerivative (fun s => vorticity u s) t x (u t x) -
        spatialDerivative u t x (vorticity u t x)) := by
  have hPart := curl_of_momentum_eq_partial_vorticity_transport hsol ht x
  -- hPart : ∂ₜω + staticCurl(convection) = ν • Δω
  -- Target ↔ : (∂ₜω + (u·∇)ω = (ω·∇)u + νΔω) ↔ (staticCurl(conv) = (u·∇)ω - (ω·∇)u)
  -- Substitute ν • Δω = ∂ₜω + staticCurl(conv) from hPart into the target LHS.
  constructor
  · intro h
    have hD : ν • laplacian (fun s => vorticity u s) t x =
        timeDerivative (fun s => vorticity u s) t x +
          staticCurl (fun y => convection u t y) x := hPart.symm
    rw [hD] at h
    linear_combination -h
  · intro h
    rw [h] at hPart
    linear_combination hPart

end Navier.Analysis.VorticityTransport
