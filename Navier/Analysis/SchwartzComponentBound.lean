import Navier.Problem

/-!
# Componentwise derivative comparison for Schwartz velocity fields

`Space = Fin 3 → ℝ` carries Mathlib's Pi (sup) norm, so each coordinate
projection `ContinuousLinearMap.proj i : Space →L[ℝ] ℝ` is a norm-`≤ 1`
contraction.  Post-composing a Schwartz velocity field with it therefore cannot
increase any iterated Fréchet derivative:

  `‖D^n (uᵢ)(x)‖ ≤ ‖D^n u(x)‖`  for every `i : Fin 3`, `n : ℕ`, `x : Space`.

This is the elementary "component/derivative comparison" step that the scalar
Fourier reduction needs in order to pay for a vector-valued Sobolev norm with
scalar-component Plancherel rungs: the scalar analysis is carried out on
`x ↦ u(x)ᵢ`, while the `H^s` norms in the consumers are built from
`iteratedFDeriv ℝ n (⇑u)`.

## Placement

This file sits **upstream of everything**: it imports only `Navier.Problem`
(for `Space` / `SchwartzVelocity`) and Mathlib, and depends on no other
`Navier.Analysis` module.  It is therefore importable from any point of the
analysis DAG without creating a cycle — in particular from both
`Navier.Analysis.BKMLogBootstrap` and `Navier.Analysis.FourierMajorant`, which
currently stand in an import relation to each other.

## Certified here (no sorry)

* `norm_proj_le_one` — the coordinate projection is a contraction for the Pi
  (sup) norm.
* `norm_iteratedFDeriv_component_le` — the pointwise derivative comparison.
* `integral_normSq_component_le` — its `L²` consequence, with integrability
  hypothesis-carried (the repo convention for majorants).

Reference: the bound is `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`
(Mathlib, `Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`) specialised to
`ContinuousLinearMap.proj`; see also L. Hörmander, *The Analysis of Linear
Partial Differential Operators I*, 2nd ed. Springer 1990, §7.1, for the
Schwartz-seminorm calculus these comparisons feed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.SchwartzComponentBound

open Navier

/-- **The coordinate projection is a contraction (certified, no sorry).**
`Space = Fin 3 → ℝ` carries the Pi (sup) norm, so `|x i| ≤ ‖x‖` and hence
`‖proj i‖ ≤ 1`. -/
theorem norm_proj_le_one (i : Fin 3) :
    ‖(ContinuousLinearMap.proj i : Space →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_le_pi_norm x i

/-- **Componentwise derivative comparison (certified, no sorry).**
For a Schwartz velocity field `u`, every coordinate `i` and every order `n`,

  `‖D^n (x ↦ u(x)ᵢ)(x)‖ ≤ ‖D^n u(x)‖`.

Proof: `x ↦ u(x)ᵢ` is literally `proj i ∘ u`, so
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left` bounds the left side by
`‖proj i‖ · ‖D^n u(x)‖`, and `norm_proj_le_one` removes the factor.

This is what lets a *scalar* Fourier/Plancherel analysis of the components pay
for a *vector-valued* Sobolev norm. -/
theorem norm_iteratedFDeriv_component_le
    (u : SchwartzVelocity) (i : Fin 3) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y : Space => (⇑u) y i) x‖ ≤ ‖iteratedFDeriv ℝ n (⇑u) x‖ := by
  have key := (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
    (f := (⇑u)) (x := x) (n := n) (u.smooth n).contDiffAt le_rfl
  have heq : ((ContinuousLinearMap.proj i : Space →L[ℝ] ℝ) ∘ (⇑u))
      = fun y : Space => (⇑u) y i := rfl
  rw [heq] at key
  refine key.trans ?_
  have h1 := norm_proj_le_one i
  have h2 : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ n (⇑u) x‖ := norm_nonneg _
  nlinarith

/-- **`L²` form of the componentwise comparison (certified, no sorry).**
The order-`n` component energy is dominated by the order-`n` full energy.
Integrability of the two squared-norm integrands is hypothesis-carried, which
is this repo's convention for majorants; both hold for Schwartz `u` by rapid
decay. -/
theorem integral_normSq_component_le
    (u : SchwartzVelocity) (i : Fin 3) (n : ℕ)
    (hcomp : Integrable
      (fun x : Space => ‖iteratedFDeriv ℝ n (fun y : Space => (⇑u) y i) x‖ ^ 2))
    (hfull : Integrable (fun x : Space => ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2)) :
    (∫ x : Space, ‖iteratedFDeriv ℝ n (fun y : Space => (⇑u) y i) x‖ ^ 2)
      ≤ ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 := by
  refine integral_mono hcomp hfull fun x => ?_
  have hle := norm_iteratedFDeriv_component_le u i n x
  have h0 : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ n (fun y : Space => (⇑u) y i) x‖ := norm_nonneg _
  nlinarith

end Navier.Analysis.SchwartzComponentBound

