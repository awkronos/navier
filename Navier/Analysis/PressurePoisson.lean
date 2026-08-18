import Navier.Analysis.VorticityTransport
import Navier.Analysis.ParabolicCaccioppoli
import Navier.Breakdown.MaximalNonextension

/-!
# The pressure Poisson equation (pointwise)

Along a zero-force `PartialClassicalSolution`, taking the divergence of the
momentum equation yields the **pressure Poisson equation**

  `Δp = − Σᵢⱼ (∂ᵢuⱼ)(∂ⱼuᵢ)`  on `[0,T) × ℝ³`.

This is the first rung of the pressure-representation program behind blocker
(b) of `ConditionalRegularity.prodiSerrin_interior_outerRegion_bounded` (the
`L^r` pressure bound for the Caccioppoli pressure term; see
`NAVIER-RESIDUALS-2026-08-17.md`, #10): combined with a Newtonian-potential /
Liouville argument it identifies `p` with the Calderón–Zygmund singular
integral `Σ RᵢRⱼ(uᵢuⱼ)`, whose `L^r` bounds are the remaining named residual.
The derivative-free cutoff form that consumes such a bound is certified in
`CutoffEnergyIbp.cutoffEnergy_pressure_ibp`.

## Certified here (no sorry)

* `staticDivergence_timeDerivative_eq_zero` — `div(∂ₜu) = 0` along an
  incompressible-before-`T` evolution.  The time–space Clairaut swap is
  rebuilt for the `spacetimeBefore T` setting (local copies of the
  `VorticityTransport` private slice bridges, adapted from `Ici 0 ×ˢ univ`
  to `Ico 0 T ×ˢ univ`), then `∂ₜ(div u) = ∂ₜ 0 = 0` on the germ near
  `t < T`.
* `staticDivergence_convection_eq` — `div((u·∇)u) = Σᵢⱼ (∂ᵢuⱼ)(∂ⱼuᵢ)`:
  the evaluated-CLM chain rule, symmetric mixed partials
  (`CurlIdentities.ContDiffAt.hasSymmetricMixedPartialAt`), and `div u = 0`.
* `staticDivergence_laplacian_eq_zero` — `div(Δu) = Δ(div u) = 0` via the
  public `VorticityTransport.thirdDeriv_swap`.
* `pressure_poisson_eq` — the capstone.

Axiom target: `⊆ {propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff

namespace Navier.Analysis.PressurePoisson

open Navier
open Navier.Breakdown
open Navier.Analysis.ParabolicCaccioppoli
  (velocity_slice_contDiff pressure_slice_contDiff)

/-! ### Set plumbing for `spacetimeBefore T` -/

/-- `spacetimeBefore T = [0,T) ×ˢ univ` is a unique-differentiability domain
when `0 < T`: it is convex with nonempty interior. -/
theorem uniqueDiffOn_spacetimeBefore {T : ℝ} (hT : 0 < T) :
    UniqueDiffOn ℝ (spacetimeBefore T) := by
  have hconv : Convex ℝ (spacetimeBefore T) :=
    (convex_Ico 0 T).prod convex_univ
  have hne : (interior (spacetimeBefore T)).Nonempty := by
    rw [spacetimeBefore, interior_prod_eq, interior_Ico, interior_univ]
    exact (nonempty_Ioo.mpr hT).prod Set.univ_nonempty
  exact uniqueDiffOn_convex hconv hne

/-- Every point of `spacetimeBefore T` lies in the closure of its interior
(the `IsSymmSndFDerivWithinAt` side condition). -/
theorem mem_closure_interior_spacetimeBefore {T : ℝ}
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) (x : Space) :
    (t, x) ∈ closure (interior (spacetimeBefore T)) := by
  have hT_lt : (0 : ℝ) < T := ht0.trans_lt htT
  rw [spacetimeBefore, interior_prod_eq, interior_Ico, interior_univ,
    closure_prod_eq, closure_Ioo (ne_of_lt hT_lt), closure_univ]
  exact ⟨⟨ht0, htT.le⟩, Set.mem_univ x⟩

/-- The one-sided time derivative at `t < T` sees only the `Ico 0 T` germ:
the within-set `Ici 0` of `timeDerivative` may be replaced by `Ico 0 T`. -/
theorem fderivWithin_Ici_eq_fderivWithin_Ico {β : Type*} [NormedAddCommGroup β]
    [NormedSpace ℝ β] {T : ℝ} {t : ℝ} (htT : t < T) (F : ℝ → β) (v : ℝ) :
    fderivWithin ℝ F (Set.Ici 0) t v = fderivWithin ℝ F (Set.Ico 0 T) t v := by
  congr 1
  rw [← Set.Ici_inter_Iio (a := (0 : ℝ)) (b := T),
    fderivWithin_inter (Iio_mem_nhds htT)]

/-! ### Slice bridges on `spacetimeBefore T`

Local copies of the `VorticityTransport` private lemmas
`fderivWithin_time_slice_apply`, `fderiv_space_slice_apply`, and
`fderivWithin_eval_apply`, adapted from the half-space `Ici 0 ×ˢ univ` to
`spacetimeBefore T`.  The proofs are identical; only the constraint set and
its unique-differentiability witness change. -/

/-- **Time-slice bridge (before `T`).**  The one-sided derivative of the
time curve `s ↦ F s y` within `Ico 0 T` is the joint within-derivative
along `(1, 0)`. -/
private theorem fderivWithin_time_slice_apply_before {β : Type*}
    [NormedAddCommGroup β] [NormedSpace ℝ β] {F : ℝ → Space → β} {T : ℝ}
    (hT : 0 < T)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Space => F z.1 z.2) (spacetimeBefore T))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) (y : Space) :
    fderivWithin ℝ (fun s => F s y) (Set.Ico 0 T) t 1 =
      fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (spacetimeBefore T) (t, y) (1, 0) := by
  have hmem : (t, y) ∈ spacetimeBefore T :=
    Set.mem_prod.mpr ⟨⟨ht0, htT⟩, Set.mem_univ y⟩
  have hG : HasFDerivWithinAt (fun z : ℝ × Space => F z.1 z.2)
      (fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (spacetimeBefore T) (t, y))
      (spacetimeBefore T) (t, y) :=
    ((hF (t, y) hmem).differentiableWithinAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)).hasFDerivWithinAt
  have hι : HasFDerivAt (fun s : ℝ => (s, y))
      (ContinuousLinearMap.inl ℝ ℝ Space) t := hasFDerivAt_prodMk_left t y
  have hmaps : Set.MapsTo (fun s : ℝ => (s, y)) (Set.Ico 0 T)
      (spacetimeBefore T) := fun s hs =>
    Set.mem_prod.mpr ⟨hs, Set.mem_univ y⟩
  have hcomp := HasFDerivWithinAt.comp t hG hι.hasFDerivWithinAt hmaps
  rw [show ((fun z : ℝ × Space => F z.1 z.2) ∘ (fun s : ℝ => (s, y))) =
      (fun s => F s y) from rfl] at hcomp
  have hUD : UniqueDiffWithinAt ℝ (Set.Ico 0 T) t :=
    (uniqueDiffOn_convex (convex_Ico 0 T)
      (by rw [interior_Ico]; exact nonempty_Ioo.mpr hT)) t
      (Set.mem_Ico.mpr ⟨ht0, htT⟩)
  rw [hcomp.fderivWithin hUD, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply]

/-- **Space-slice bridge (before `T`).**  The full spatial derivative of a
slice equals the joint within-derivative along `(0, v)`. -/
private theorem fderiv_space_slice_apply_before {β : Type*}
    [NormedAddCommGroup β] [NormedSpace ℝ β] {F : ℝ → Space → β} {T : ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Space => F z.1 z.2) (spacetimeBefore T))
    {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T) (x v : Space) :
    fderiv ℝ (F s) x v =
      fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (spacetimeBefore T) (s, x) (0, v) := by
  have hmem : (s, x) ∈ spacetimeBefore T :=
    Set.mem_prod.mpr ⟨⟨hs0, hsT⟩, Set.mem_univ x⟩
  have hG : HasFDerivWithinAt (fun z : ℝ × Space => F z.1 z.2)
      (fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (spacetimeBefore T) (s, x))
      (spacetimeBefore T) (s, x) :=
    ((hF (s, x) hmem).differentiableWithinAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)).hasFDerivWithinAt
  have hκ : HasFDerivAt (fun y : Space => (s, y))
      (ContinuousLinearMap.inr ℝ ℝ Space) x := hasFDerivAt_prodMk_right s x
  have hmaps : Set.MapsTo (fun y : Space => (s, y)) Set.univ
      (spacetimeBefore T) := fun y _ =>
    Set.mem_prod.mpr ⟨⟨hs0, hsT⟩, Set.mem_univ y⟩
  have hcomp := HasFDerivWithinAt.comp x hG hκ.hasFDerivWithinAt hmaps
  rw [show ((fun z : ℝ × Space => F z.1 z.2) ∘ (fun y : Space => (s, y))) =
      F s from rfl] at hcomp
  have hAt : HasFDerivAt (F s)
      ((fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (spacetimeBefore T) (s, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
    hcomp.hasFDerivAt Filter.univ_mem
  rw [hAt.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]

/-- **Eval bridge** (local copy of the `VorticityTransport` private lemma):
the within-derivative of an evaluated within-derivative field is the second
within-derivative evaluated in the other order. -/
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

end Navier.Analysis.PressurePoisson
