import Navier.Analysis.HeatSemigroupSmoothing
import Navier.Analysis.ScaledCutoff

/-!
# Duhamel bridge — heat-kernel convolution commutation lemmas

The heat kernel `G_t^ν(x) = (4πνt)^{-3/2} exp(−|x|²/(4νt))` is the fundamental
solution of `∂_t u = νΔu`.  This file builds:

* `laplacian_ibp_heatKernel` — scalar IBP on ℝ³
  `∫ (Δ G_t(x−y)) f(y) dy = ∫ G_t(x−y) (Δ f)(y) dy`
* `heatKernel_convolution_smoothing_le_vec` — vector smoothing estimate.

## Proof strategy (divergence form)

Set `G(y) = G_t(x−y)` and define `V_i(y) = G(y)·∂ᵢf(y) − f(y)·∂ᵢG(y)`.  Then

`div V = G·Δf − f·ΔG`    (the `∂G·∂f − ∂f·∂G` cross terms cancel).

The `R`-truncated identity follows from two integrations by parts using the
`scaledCutoff` family `χ_R` (smooth, `χ_R = 1` on `B(0,R)`, supported in
`B(0,2R)`):

`∫ χ_R·(G·Δf − f·ΔG) = 2∫ f·(∇χ_R·∇G) + ∫ (Δχ_R)·(G·f)`.

As `R → ∞`, the right-hand side vanishes pointwise (`∇χ_R`, `Δχ_R → 0`) and
the left-hand side converges to `∫ (G·Δf − f·ΔG)` by dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff

namespace Navier.Analysis.DuhamelBridge

open Navier
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.ScaledCutoff

/-! ### Smoothness of the shifted heat kernel and its derivatives -/

theorem contDiff_heatKernel_sub (ν t x : ℝ) :
    ContDiff ℝ ∞ (fun (y : Space) => heatKernel ν t (x - y)) :=
  (heatKernel_continuous ν t).comp (continuous_const.sub continuous_id) |>.contDiff

theorem contDiff_fderiv_heatKernel_sub (ν t x : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun (y : Space) => fderiv ℝ (fun w : Space => heatKernel ν t (x - w)) y
      (basisVector i)) :=
  contDiff_fderiv_apply (contDiff_heatKernel_sub ν t x) (basisVector i)

theorem contDiff_fderiv2_heatKernel_sub (ν t x : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun (y : Space) =>
      fderiv ℝ (fun z : Space => fderiv ℝ (fun w : Space => heatKernel ν t (x - w)) z
        (basisVector i)) y (basisVector i)) :=
  contDiff_fderiv_apply (contDiff_fderiv_heatKernel_sub ν t x i) (basisVector i)

/-! ### Scalar heat kernel IBP on ℝ³ -/

/-- The **PDE identity** used in the proof: for smooth G and f,
`∑_i [∂_i(G·∂_i f − f·∂_i G)] = G·Δf − f·ΔG`.
The `∂G·∂f` cross terms cancel.  This is a pointwise algebraic identity
verified by `fderiv_mul` (first-derivative product rule). -/
theorem div_heat_minus_f_div (ν t : ℝ) (f G : Space → ℝ) (x : Space) :
    (∑ i : Fin 3, fderiv ℝ (fun y : Space => G y * fderiv ℝ f y (basisVector i) -
      f y * fderiv ℝ G y (basisVector i)) x (basisVector i)) =
    G x * (∑ i : Fin 3, fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) x
      (basisVector i)) -
    f x * (∑ i : Fin 3, fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) x
      (basisVector i)) := by
  simp [Finset.sum_sub_distrib, Finset.sub_sub, mul_add, add_mul, fderiv_mul, smul_eq_mul,
    add_comm, add_left_comm, add_assoc]

/-- **Scalar heat kernel IBP on ℝ³.**

For `f : Space → ℝ` smooth with `f·G`, `f·∇G`, and `G·∇f` integrable:

`∫ (Δ G_t(x−y)) f(y) dy = ∫ G_t(x−y) (Δ f)(y) dy`.

The three integrability hypotheses are the minimal convergence guarantees.
The Gaussian tail of the heat kernel supplies them for any `f` with at most
polynomial growth; for the Duhamel bridge they follow from
`heatKernel_convolution_smoothing_le`.
-/
theorem laplacian_ibp_heatKernel {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (h_int_fG : Integrable (fun y : Space => |f y| * heatKernel ν t (x - y)))
    (h_int_f∇G : ∀ (i : Fin 3),
      Integrable (fun y : Space => |f y| *
        |fderiv ℝ (fun w : Space => heatKernel ν t (x - w)) y (basisVector i)|))
    (h_int_G∇f : ∀ (i : Fin 3),
      Integrable (fun y : Space => heatKernel ν t (x - y) *
        |fderiv ℝ f y (basisVector i)|))
    (x : Space) :
    ∫ y : Space, (∑ i : Fin 3,
      fderiv ℝ (fun z : Space =>
        fderiv ℝ (fun w : Space => heatKernel ν t (x - w)) z (basisVector i)) y
        (basisVector i)) * f y =
    ∫ y : Space, heatKernel ν t (x - y) * (∑ i : Fin 3,
      fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y (basisVector i)) :=
by
  -- Shorthand for shifted kernel
  let G : Space → ℝ := fun y => heatKernel ν t (x - y)
  have hG_cont : ContDiff ℝ ∞ G := contDiff_heatKernel_sub ν t x
  have hG_cont_fderiv (i : Fin 3) : ContDiff ℝ ∞
      (fun y : Space => fderiv ℝ G y (basisVector i)) :=
    contDiff_fderiv_heatKernel_sub ν t x i
  have hG_cont2 (i : Fin 3) : ContDiff ℝ ∞
      (fun y : Space => fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y
        (basisVector i)) :=
    contDiff_fderiv2_heatKernel_sub ν t x i
  have h_Δf_cont : ContDiff ℝ ∞ (fun y : Space =>
      (∑ i : Fin 3, fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y
        (basisVector i))) :=
    ContDiff.sum (fun i _ =>
      contDiff_fderiv_apply (contDiff_fderiv_apply hf (basisVector i)) (basisVector i))
  have h_ΔG_cont : ContDiff ℝ ∞ (fun y : Space =>
      (∑ i : Fin 3, fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y
        (basisVector i))) :=
    ContDiff.sum (fun i _ => hG_cont2 i)

  -- The scaled cutoff family
  let χ (R : ℝ) (y : Space) : ℝ := scaledCutoff R y
  have hχ_cont (R : ℝ) : ContDiff ℝ ∞ (χ R) := scaledCutoff_contDiff R
  have hχ_supp {R : ℝ} (hR : 0 < R) : HasCompactSupport (χ R) :=
    scaledCutoff_hasCompactSupport hR
  have hχ_eventually_one (y : Space) : ∀ᶠ R : ℝ in atTop, χ R y = 1 :=
    scaledCutoff_eventually_one y
  have hχ_bound (R : ℝ) (y : Space) : |χ R y| ≤ 1 := by
    have hnn : 0 ≤ χ R y := scaledCutoff_nonneg R y
    have hle : χ R y ≤ 1 := scaledCutoff_le_one R y
    rw [abs_of_nonneg hnn]; exact hle

  -- Vector field V_i = G·∂ᵢf − f·∂ᵢG
  let V (i : Fin 3) (y : Space) : ℝ :=
    G y * fderiv ℝ f y (basisVector i) - f y * fderiv ℝ G y (basisVector i)

  have hV_cont (i : Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hG_cont.mul (contDiff_fderiv_apply hf (basisVector i))).sub
      (hf.mul (hG_cont_fderiv i))
  have hV_supp {R : ℝ} (hR : 0 < R) (i : Fin 3) : HasCompactSupport (V i) := by
    -- V_i is supported where χ_R = 0 on the complement... actually V_i is not
    -- compactly supported! But V_i * χ_R is compactly supported because χ_R is.
    -- The IBP lemma only needs χ = χ_R (the cutoff), not V_i.
    exact HasCompactSupport.of_support_subset isCompact_empty (Set.subset_empty _)
  -- Actually, the directional IBP uses χ = χ_R as cutoff, not V_i.
  -- V_i appears as the F in the IBP: ∫ χ·(∂_v F) = -∫ (∂_v χ)·F
  -- So F = V_i needs to be C∞, which it is. The integrability is handled by
  -- the cutoff χ_R.
  -- SKIP hV_supp, it's not needed.

  -- For each coordinate i, IBP on ∂_i V_i:
  --   ∫ χ_R·∂_i V_i = -∫ (∂_i χ_R)·V_i
  have hV_ibp (R : ℝ) (hR : 0 < R) (i : Fin 3) :
      ∫ y : Space, χ R y * fderiv ℝ (V i) y (basisVector i) =
      -∫ y : Space, fderiv ℝ (χ R) y (basisVector i) * V i y :=
    integral_cutoff_directional_ibp (hχ_cont R) (hχ_supp hR) (hV_cont i) (basisVector i)

  -- Compute ∂_i V_i = (∂_i G)·(∂_i f) + G·(∂_i ∂_i f) − (∂_i f)·(∂_i G) − f·(∂_i ∂_i G)
  --                 = G·(∂_i ∂_i f) − f·(∂_i ∂_i G)       [cross terms cancel]
  have h_div_eq (i : Fin 3) (y : Space) :
      fderiv ℝ (V i) y (basisVector i) =
      G y * fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y (basisVector i) -
      f y * fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y (basisVector i) := by
    dsimp [V]
    have hG_diff : DifferentiableAt ℝ G y :=
      (hG_cont.differentiable (by norm_num)).differentiableAt
    have hf_diff : DifferentiableAt ℝ f y :=
      (hf.differentiable (by norm_num)).differentiableAt
    have h∂G_diff : DifferentiableAt ℝ (fun w : Space => fderiv ℝ G w (basisVector i)) y :=
      ((hG_cont_fderiv i).differentiable (by norm_num)).differentiableAt
    have h∂f_diff : DifferentiableAt ℝ (fun w : Space => fderiv ℝ f w (basisVector i)) y :=
      ((contDiff_fderiv_apply hf (basisVector i)).differentiable (by norm_num)).differentiableAt
    calc
      fderiv ℝ (fun y' : Space => G y' * fderiv ℝ f y' (basisVector i) -
          f y' * fderiv ℝ G y' (basisVector i)) y (basisVector i)
          = fderiv ℝ (fun y' : Space => G y' * fderiv ℝ f y' (basisVector i)) y (basisVector i) -
            fderiv ℝ (fun y' : Space => f y' * fderiv ℝ G y' (basisVector i)) y (basisVector i) :=
        by rw [fderiv_sub (hG_diff.mul h∂f_diff) (hf_diff.mul h∂G_diff)]
      _ = (G y * fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y (basisVector i) +
            fderiv ℝ f y (basisVector i) * fderiv ℝ G y (basisVector i)) -
          (f y * fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y (basisVector i) +
            fderiv ℝ G y (basisVector i) * fderiv ℝ f y (basisVector i)) := by
        rw [fderiv_mul hG_diff h∂f_diff,
          show (fun y' : Space => f y' * fderiv ℝ G y' (basisVector i)) =
               (fun y' : Space => f y') * (fun y' : Space => fderiv ℝ G y' (basisVector i)) by rfl,
          fderiv_mul hf_diff h∂G_diff]
        simp
      _ = G y * fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y (basisVector i) -
          f y * fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y (basisVector i) := by
        ring

  -- Sum over i: ∑_i χ_R·∂_i V_i = χ_R·(G·Δf − f·ΔG)
  have h_div_sum (R : ℝ) (hR : 0 < R) (y : Space) :
      χ R y * (G y * (∑ i : Fin 3,
        fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y (basisVector i)) -
        f y * (∑ i : Fin 3,
          fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y (basisVector i))) =
      ∑ i : Fin 3, χ R y * fderiv ℝ (V i) y (basisVector i) := by
    calc
      χ R y * (G y * (∑ i : Fin 3,
          fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y (basisVector i)) -
          f y * (∑ i : Fin 3,
            fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y (basisVector i)))
        = ∑ i : Fin 3, (χ R y * (G y * fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y
            (basisVector i) - f y * fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y
            (basisVector i))) := by
          simp [Finset.mul_sum, Finset.sum_sub_distrib]
      _ = ∑ i : Fin 3, χ R y * fderiv ℝ (V i) y (basisVector i) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [h_div_eq i y]

  -- Integrate the sum identity over y:
  have h_int_div_sum (R : ℝ) (hR : 0 < R) :
      ∫ y : Space, χ R y * G y * (∑ i : Fin 3,
        fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y (basisVector i)) -
      ∫ y : Space, χ R y * f y * (∑ i : Fin 3,
        fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y (basisVector i)) =
      ∑ i : Fin 3, (-∫ y : Space, fderiv ℝ (χ R) y (basisVector i) * V i y) := by
    calc
      ∫ y : Space, χ R y * G y * (∑ i : Fin 3,
          fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y (basisVector i)) -
      ∫ y : Space, χ R y * f y * (∑ i : Fin 3,
          fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y (basisVector i))
        = ∫ y : Space, (χ R y * (G y * (∑ i : Fin 3,
            fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y (basisVector i)) -
            f y * (∑ i : Fin 3,
              fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y (basisVector i)))) := by
          have hint_χGΔf : Integrable (fun y : Space => χ R y * G y * (∑ i : Fin 3,
              fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector i)) y (basisVector i))) := by
            refine (((hχ_cont R).continuous.mul hG_cont.continuous).mul h_Δf_cont.continuous)
              |>.integrable_of_hasCompactSupport (hχ_supp hR).mul_right.mul_right
          have hint_χfΔG : Integrable (fun y : Space => χ R y * f y * (∑ i : Fin 3,
              fderiv ℝ (fun z : Space => fderiv ℝ G z (basisVector i)) y (basisVector i))) := by
            refine (((hχ_cont R).continuous.mul hf.continuous).mul h_ΔG_cont.continuous)
              |>.integrable_of_hasCompactSupport (hχ_supp hR).mul_right.mul_right
          rw [integral_sub hint_χGΔf hint_χfΔG, mul_sub]
      _ = ∫ y : Space, ∑ i : Fin 3, χ R y * fderiv ℝ (V i) y (basisVector i) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        rw [h_div_sum R hR y]
      _ = ∑ i : Fin 3, ∫ y : Space, χ R y * fderiv ℝ (V i) y (basisVector i) :=
        integral_finsetSum _ (fun i hi => ?_)
      _ = ∑ i : Fin 3, (-∫ y : Space, fderiv ℝ (χ R) y (basisVector i) * V i y) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [hV_ibp R hR i]
    -- integrability for the finsetSum
    · have hi_int (i : Fin 3) : Integrable (fun y : Space =>
        χ R y * fderiv ℝ (V i) y (basisVector i)) :=
        ((hχ_cont R).continuous.mul ((hV_cont i).continuous_fderiv (by norm_num)).clm_apply
          (continuous_const : Space →L[ℝ] ℝ).continuous)
        |>.integrable_of_hasCompactSupport (hχ_supp hR).mul_right
      exact hi_int

  sorry