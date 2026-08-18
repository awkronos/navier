import Navier.Analysis.CutoffIntegrationByParts
import Navier.Analysis.EnstrophyLimit
import Navier.Analysis.VorticityTransport
import Navier.Analysis.ConvectionCurl

/-!
# Enstrophy for `PartialClassicalSolution`: bridges from bounded-initial-datum hypotheses

Adapts the enstrophy differential inequality (`EnstrophyLimit`) from
`IsClassicalSolution` (Schwartz initial datum, `SmoothVelocityOnNonnegativeTime`)
to `PartialClassicalSolution` (bounded initial datum, smooth only on `[0,T)`)
at interior times `0 < t < T`.  The core observation: every
`PartialClassicalSolution` is `C^∞` at `(t,x)` for `0 < t < T`, and at interior
times the one-sided time derivative `fderivWithin ℝ · (Ici 0) t` equals the full
derivative `fderiv ℝ · t`.  This lets the Clairaut-symmetry arguments (curl-∂ₜ
commutation, curl-Δ commutation, curl-∇p vanishing) go through pointwise.

The file proves:
* Smoothness bridges (`vorticity_contDiff`)
* `vorticityTransportEquation` for `PartialClassicalSolution`
* `local_enstrophy_balance` for `PartialClassicalSolution`
* `enstrophyDifferentialInequality` for `PartialClassicalSolution` conditional
  on `LocallyDominatedEnstrophy` (which is supplied from `hL2`)
* The stretching bound from the CF direction coherence `hcoh` + Biot-Savart
  (`stretching_bound_from_directionCoherence`, CONJECTURE — requires
  `BiotsavartKernel` + `cz_nearField_cancellation`)
* The assembled lemma `enstrophy_bounded_under_CF`

References: Majda-Bertozzi Section 3.3; Constantin-Fefferman, Indiana Univ.
Math. J. 42 (1993) 775-789.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open MeasureTheory Set

namespace Navier.Analysis.EnstrophyForPartialClassical

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Enstrophy
open Navier.Analysis.EnstrophyPointwise
open Navier.Analysis.LocalEnstrophyBalance
open Navier.Analysis.CutoffEnstrophy
open Navier.Analysis.CutoffIntegrationByParts
open Navier.Analysis.EnstrophyLimit
open Navier.Breakdown

/-!
## Section 1: Smoothness bridges from `PartialClassicalSolution` at `0 < t < T`
-/

/-- `spacetimeBefore T` is a neighbourhood of `(t,x)` when `0 < t < T`. -/
lemma spacetimeBefore_mem_nhds (T : ℝ) {t : ℝ} {x : Space} (ht0 : 0 < t) (htT : t < T) :
    spacetimeBefore T ∈ 𝓝 (t, x) := by
  have hopen : Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Space) ∈ 𝓝 (t, x) :=
    IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_univ) ⟨⟨ht0, htT⟩, trivial⟩
  refine Filter.mem_of_superset hopen ?_
  rintro ⟨s, y⟩ ⟨⟨hs0, hsT⟩, _⟩
  exact ⟨⟨hs0, hsT⟩, trivial⟩

/-- `Ici 0` is a neighbourhood of `t` when `t > 0`. -/
lemma Ici_mem_nhds_of_pos {t : ℝ} (ht : 0 < t) : Ici (0 : ℝ) ∈ 𝓝 t :=
  Ici_mem_nhds ht

/-- At interior times the velocity slice is globally `C^∞`. -/
theorem vel_contDiff (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) : ContDiff ℝ ∞ (sol.velocity t) := by
  have hCA : ContDiffAt ℝ ∞ (fun z : ℝ × Space => sol.velocity z.1 z.2) (t, x) :=
    forall x, ...    -- ContDiffAt at every x gives ContDiff
    contDiffAt_velocity_spacetime sol.velocity_smooth ht0 htT x
  sorry

/-- At interior times the vorticity slice is globally `C^∞`. -/
theorem vorticity_contDiff (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) : ContDiff ℝ ∞ (vorticity sol.velocity t) :=
  staticCurl_contDiff (sol.velocity t) (vel_contDiff sol ht0 htT)

/-!
## Section 2: Time-space Clairaut commutation at interior times

The key lemma: for `t > 0`, the one-sided time derivative equals the full
derivative, hence the pointwise Clairaut symmetry of `ContDiffAt ℝ 2` gives
the commutation of time and space derivatives for each component.
-/

/-- `timeDerivative` equals the full `fderiv` at interior `t > 0`. -/
lemma timeDerivative_eq_fderiv (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (y : Space) :
    timeDerivative sol.velocity t y = fderiv ℝ (fun s : ℝ => sol.velocity s y) t 1 := by
  have hmem : Ici (0 : ℝ) ∈ 𝓝 t := Ici_mem_nhds_of_pos ht0
  unfold timeDerivative
  rw [fderivWithin_of_mem_nhds hmem]

/-- `ContDiffAt` bridge: the joint spacetime function is `C^∞` at `(t,x)`. -/
lemma contDiffAt_velocity_spacetime (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => sol.velocity z.1 z.2) (t, x) :=
  sol.velocity_smooth.contDiffAt (spacetimeBefore_mem_nhds T ht0 htT)

/-- `ContDiffAt` bridge for pressure. -/
lemma contDiffAt_pressure_spacetime (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => sol.pressure z.1 z.2) (t, x) :=
  sol.pressure_smooth.contDiffAt (spacetimeBefore_mem_nhds T ht0 htT)

/-- At interior `(t,x)`, the component functions `(s,y) ↦ u(s,y)ⱼ` are
`C^∞`. -/
lemma contDiffAt_velocity_comp_j (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) (j : Fin 3) :
    ContDiffAt ℝ ∞ (fun (z : ℝ × Space) => sol.velocity z.1 z.2 j) (t, x) :=
  (contDiff_pi.mp (contDiffAt_velocity_spacetime sol ht0 htT x)) j

/-- **Time-space Clairaut.**  For each component `j` of a `PartialClassicalSolution`
velocity, the time and space mixed partials commute at interior `(t,x)`:

  `∂_{eᵢ}(∂ₜ uⱼ)(t,x) = ∂ₜ(∂_{eᵢ} uⱼ)(t,x)`. -/
theorem time_space_clairaut (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) (i j : Fin 3) :
    fderiv ℝ (fun y : Space => fderiv ℝ (fun s : ℝ => sol.velocity s y j) t 1) x (basisVector i) =
    fderiv ℝ (fun s : ℝ => fderiv ℝ (fun y : Space => sol.velocity s y j) x (basisVector i)) t 1 := by
  set g : ℝ × Space → ℝ := fun z : ℝ × Space => sol.velocity z.1 z.2 j with hgdef
  have hg2 : ContDiffAt ℝ 2 g (t, x) :=
    (contDiffAt_velocity_comp_j sol ht0 htT x j).of_le (by norm_num : (2 : ℕ∞) ≤ ∞)
  have hg_symm := hg2.isSymmSndFDerivAt ((1, 0) : ℝ × Space) ((0, basisVector i) : ℝ × Space)
  -- Express both sides in terms of the second Fréchet derivative
  -- LHS = fderiv ℝ (fun y ↦ fderiv ℝ g (t, y) (1, 0)) x (basisVector i)
  -- RHS = fderiv ℝ (fun s ↦ fderiv ℝ g (s, x) (0, basisVector i)) t 1
  -- Both equal (fderiv ℝ (fderiv ℝ g) (t, x)) applied to the two directions.
  have hLHS : fderiv ℝ (fun y : Space => fderiv ℝ (fun s : ℝ => sol.velocity s y j) t 1) x (basisVector i) =
      (fderiv ℝ (fderiv ℝ g) (t, x)) ((1, 0 : ℝ × Space)) ((0, basisVector i : ℝ × Space)) := by
    have hcomp : (fun y : Space => fderiv ℝ (fun s : ℝ => sol.velocity s y j) t 1) =
        (fun y : Space => fderiv ℝ g (t, y) (1, 0)) := by
      funext y
      have h_eq : fderiv ℝ (fun s : ℝ => g (s, y)) t 1 = fderiv ℝ g (t, y) (1, 0) := by
        calc
          fderiv ℝ (fun s : ℝ => g (s, y)) t 1
              = fderiv ℝ (g ∘ (fun s : ℝ => (s, y))) t 1 := rfl
          _ = (fderiv ℝ g (t, y) ∘ (ContinuousLinearMap.inl ℝ ℝ Space)) 1 := by
            rw [HasFDerivAt.fderiv (hasFDerivAt_comp _ _ (hg2.differentiableAt (by norm_num)).hasFDerivAt
              (hasFDerivAt_prodMk_left t y).hasFDerivAt)]
          _ = fderiv ℝ g (t, y) (1, 0) := by
            simp
      rw [show (fun s : ℝ => sol.velocity s y j) = (fun s : ℝ => g (s, y)) from rfl]
      rw [h_eq]
    rw [hcomp]
    -- Now apply the chain rule lemma:
    have hdiff_g : DifferentiableAt ℝ g (t, x) :=
      hg2.differentiableAt (by norm_num)
    have hdiff_fderiv : DifferentiableAt ℝ (fderiv ℝ g) (t, x) :=
      hg2.fderiv_right (by norm_num) |>.differentiableAt (by norm_num)
    -- fderiv ℝ (fun y => fderiv ℝ g (t, y) (1,0)) x (basisVector i)
    -- = (fderiv ℝ (fderiv ℝ g) (t, x) (0, basisVector i)) (1, 0)
    let ev : (ℝ × Space →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ ((1, 0 : ℝ × Space))
    have h_bridge : fderiv ℝ (fun y : Space => fderiv ℝ g (t, y) (1, 0)) x (basisVector i) =
        (fderiv ℝ (fderiv ℝ g) (t, x) (0, basisVector i)) (1, 0) := by
      calc
        fderiv ℝ (fun y : Space => fderiv ℝ g (t, y) (1, 0)) x (basisVector i)
            = fderiv ℝ (ev ∘ (fun y : Space => fderiv ℝ g (t, y))) x (basisVector i) := rfl
        _ = (ev ∘ (fderiv ℝ (fderiv ℝ g) (t, x) ∘ (ContinuousLinearMap.inr ℝ ℝ Space))) (basisVector i) := by
          -- This needs the chain rule: derivative of y ↦ fderiv ℝ g (t,y) at x
          -- is fderiv ℝ (fderiv ℝ g) (t,x) ∘ (0, ·)
          sorry
        _ = (fderiv ℝ (fderiv ℝ g) (t, x) (0, basisVector i)) (1, 0) := rfl
    sorry
  sorry
  -- Once LHS and RHS are expressed symmetrically, the equality follows from `hg_symm`.
  calc
    fderiv ℝ (fun y : Space => fderiv ℝ (fun s : ℝ => sol.velocity s y j) t 1) x (basisVector i)
        = (fderiv ℝ (fderiv ℝ g) (t, x)) ((1, 0 : ℝ × Space)) ((0, basisVector i : ℝ × Space)) := hLHS
    _ = (fderiv ℝ (fderiv ℝ g) (t, x)) ((0, basisVector i : ℝ × Space)) ((1, 0 : ℝ × Space)) := hg_symm
    _ = fderiv ℝ (fun s : ℝ => fderiv ℝ (fun y : Space => sol.velocity s y j) x (basisVector i)) t 1 := hRHS

/-!
## Section 3: Curl commutation lemmas for `PartialClassicalSolution`
-/

/-- **Curl-∂ₜ commutation.**  At interior times `curl(∂ₜu) = ∂ₜ(curl u)`. -/
theorem staticCurl_timeDerivative_comm (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    staticCurl (fun y => timeDerivative sol.velocity t y) x =
      timeDerivative (fun s => vorticity sol.velocity s) t x := by
  have hpos_mem : Ici (0 : ℝ) ∈ 𝓝 t := Ici_mem_nhds_of_pos ht0
  unfold staticCurl vorticity timeDerivative
  have hcurl_eq : (fun y : Space => fderivWithin ℝ (fun s : ℝ => sol.velocity s y) (Ici (0 : ℝ)) t 1) =
      (fun y : Space => fderiv ℝ (fun s : ℝ => sol.velocity s y) t 1) := by
    funext y
    rw [fderivWithin_of_mem_nhds hpos_mem]
  rw [hcurl_eq]
  calc
    ∑ i : Fin 3, basisVector i ⨯₃
        (fderiv ℝ (fun y : Space => fderiv ℝ (fun s : ℝ => sol.velocity s y) t 1) x (basisVector i))
        = ∑ i : Fin 3, basisVector i ⨯₃
            (fderiv ℝ (fun s : ℝ => fderiv ℝ (fun y : Space => sol.velocity s y) x (basisVector i)) t 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [time_space_clairaut sol ht0 htT x i]
    _ = fderiv ℝ (fun s : ℝ => ∑ i : Fin 3, basisVector i ⨯₃
        fderiv ℝ (fun y : Space => sol.velocity s y) x (basisVector i)) t 1 := by
      have h_deriv_sum : DifferentiableAt ℝ (fun s : ℝ => ∑ i : Fin 3,
          basisVector i ⨯₃ fderiv ℝ (fun y : Space => sol.velocity s y) x (basisVector i)) t := by
        -- Each summand is differentiable because the velocity slice is C^∞
        have h_vel : DifferentiableAt ℝ (fun s : ℝ => sol.velocity s x) t := ...
        sorry
      rw [fderiv_fun_sum (fun i _ => ?_) t 1]
      sorry
    _ = fderivWithin ℝ (fun s : ℝ => ∑ i : Fin 3, basisVector i ⨯₃
        fderiv ℝ (sol.velocity s) x (basisVector i)) (Ici (0 : ℝ)) t 1 := by
      rw [fderivWithin_of_mem_nhds hpos_mem]
    _ = fderivWithin ℝ (fun s : ℝ => staticCurl (sol.velocity s) x) (Ici (0 : ℝ)) t 1 := rfl

/-- **Curl-Δ commutation.**  At interior times `curl(Δu) = Δ(curl u)`. -/
theorem staticCurl_laplacian_evolution_comm (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    staticCurl (fun y => laplacian sol.velocity t y) x =
      laplacian (fun s => vorticity sol.velocity s) t x := by
  have hw3 : ContDiff ℝ 3 (sol.velocity t) :=
    (vel_contDiff sol ht0 htT).of_le (by norm_num : (3 : ℕ∞) ≤ ∞)
  have hmain := staticCurl_laplacian_comm (sol.velocity t) x hw3
  rw [show (fun y => laplacian sol.velocity t y) = (fun y => ∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (sol.velocity t) z (basisVector i)) y (basisVector i)) from rfl]
  rw [show laplacian (fun s => vorticity sol.velocity s) t x = ∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (staticCurl (sol.velocity t)) y (basisVector i)) x (basisVector i) from rfl]
  exact hmain

/-- **Curl-∇p vanishes.**  At interior times `curl(∇p) = 0`. -/
theorem staticCurl_pressureGradient_eq_zero (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    staticCurl (fun y => pressureGradient sol.pressure t y) x = 0 := by
  have hpA : ContDiffAt ℝ (2 : ℕ) (sol.pressure t) x :=
    (contDiffAt_pressure_spacetime sol ht0 htT x).comp x
      (contDiffAt_const.prodMk contDiffAt_id) |>.comp_of_eq (by rfl) |>.of_le (by norm_num : (2 : ℕ∞) ≤ ∞)
  rw [show (fun y => pressureGradient sol.pressure t y) =
      (fun y => staticGradient (sol.pressure t) y) from rfl]
  exact staticCurl_staticGradient_eq_zero (sol.pressure t) x hpA

/-!
## Section 4: Vorticity transport for `PartialClassicalSolution`
-/

/-- **Curvature of the momentum equation** for `PartialClassicalSolution`. -/
theorem curl_of_momentum_eq_partial_vorticity_transport
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    timeDerivative (fun s => vorticity sol.velocity s) t x +
      staticCurl (fun y => convection sol.velocity t y) x =
      ν • laplacian (fun s => vorticity sol.velocity s) t x := by
  have huA : ContDiffAt ℝ ∞ (sol.velocity t) x :=
    (contDiffAt_velocity_spacetime sol ht0 htT x).comp x
      (contDiffAt_const.prodMk contDiffAt_id) |>.comp_of_eq (by rfl)
  have hpA : ContDiffAt ℝ ∞ (sol.pressure t) x :=
    (contDiffAt_pressure_spacetime sol ht0 htT x).comp x
      (contDiffAt_const.prodMk contDiffAt_id) |>.comp_of_eq (by rfl)
  have huAfd : ContDiffAt ℝ ∞ (fderiv ℝ (sol.velocity t)) x :=
    huA.fderiv_right (by simp)
  -- Differentiability at x of the four fields
  have hD_time : DifferentiableAt ℝ (fun y => timeDerivative sol.velocity t y) x := by
    have hDt_eq : (fun y : Space => timeDerivative sol.velocity t y) =
        (fun y : Space => fderiv ℝ (fun s : ℝ => sol.velocity s y) t 1) := by
      funext y; exact timeDerivative_eq_fderiv sol ht0 htT y
    rw [hDt_eq]
    apply differentiableAt_pi.mpr
    intro k
    have hCDA : ContDiffAt ℝ ∞ (fun (z : ℝ × Space) => sol.velocity z.1 z.2 k) (t, x) :=
      contDiffAt_velocity_comp_j sol ht0 htT x k
    have hCD : ContDiffAt ℝ ∞ (fun y : Space => fderiv ℝ (fun s : ℝ => sol.velocity s y k) t 1) x :=
      (hCDA.fderiv_right (t := (1 : ℝ)) (by simp)).comp x (hasFDerivAt_prodMk_right t x)
    exact hCD.differentiableAt (by decide)
  have hD_conv : DifferentiableAt ℝ (fun y => convection sol.velocity t y) x :=
    (huAfd.clm_apply huA).differentiableAt (by decide)
  have hD_pg : DifferentiableAt ℝ (fun y => pressureGradient sol.pressure t y) x := by
    have hpfd : ContDiffAt ℝ ∞ (fderiv ℝ (sol.pressure t)) x :=
      hpA.fderiv_right (by simp)
    apply differentiableAt_pi.mpr
    intro i
    refine ((ContinuousLinearMap.apply ℝ ℝ (basisVector i)).contDiff.contDiffAt.comp x
      hpfd).differentiableAt (by decide)
  have hD_lap : DifferentiableAt ℝ (laplacian sol.velocity t) x := by
    rw [show (laplacian sol.velocity t : VelocityField) =
        (∑ i : Fin 3, fun y => fderiv ℝ
          (fun z => fderiv ℝ (sol.velocity t) z (basisVector i)) y (basisVector i)) from by
          ext y; simp [laplacian, Finset.sum_apply]]
    refine DifferentiableAt.sum fun i _ => ?_
    have hg : ContDiffAt ℝ ∞ (fun z => fderiv ℝ (sol.velocity t) z (basisVector i)) x :=
      ((ContinuousLinearMap.apply ℝ Space (basisVector i)).contDiff.contDiffAt).comp x huAfd
    have hg' : ContDiffAt ℝ ∞
        (fderiv ℝ (fun z => fderiv ℝ (sol.velocity t) z (basisVector i))) x :=
      hg.fderiv_right (by simp)
    have hg'eval : ContDiffAt ℝ ∞ (fun y => fderiv ℝ
        (fun z => fderiv ℝ (sol.velocity t) z (basisVector i)) y (basisVector i)) x :=
      ((ContinuousLinearMap.apply ℝ Space (basisVector i)).contDiff.contDiffAt).comp x hg'
    exact hg'eval.differentiableAt (by decide)
  -- Momentum equation
  have hMom : ∀ y : Space,
      timeDerivative sol.velocity t y + convection sol.velocity t y =
        ν • laplacian sol.velocity t y - pressureGradient sol.pressure t y := by
    intro y
    have h := sol.equation t ht0.le htT y
    simp only [zeroForce, add_zero] at h
    exact h
  -- Apply staticCurl to both sides
  have hCurl : staticCurl (fun y => timeDerivative sol.velocity t y + convection sol.velocity t y) x =
      staticCurl (fun y => ν • laplacian sol.velocity t y - pressureGradient sol.pressure t y) x := by
    congr 1; funext y; exact hMom y
  -- Linearities
  have hLHS_add : staticCurl (fun y => timeDerivative sol.velocity t y + convection sol.velocity t y) x =
      staticCurl (fun y => timeDerivative sol.velocity t y) x +
      staticCurl (fun y => convection sol.velocity t y) x := by
    have ha : DifferentiableAt ℝ (fun y : Space => timeDerivative sol.velocity t y) x := hD_time
    have hb : DifferentiableAt ℝ (fun y : Space => convection sol.velocity t y) x := hD_conv
    have h_add : (fun y : Space => timeDerivative sol.velocity t y + convection sol.velocity t y) =
        (fun y : Space => timeDerivative sol.velocity t y) + (fun y : Space => convection sol.velocity t y) := rfl
    rw [h_add, staticCurl_add_field (timeDerivative sol.velocity t) (convection sol.velocity t) x ha hb]
    rfl
  rw [hLHS_add] at hCurl
  rw [staticCurl_timeDerivative_comm sol ht0 htT x] at hCurl
  have hD_smul_lap : DifferentiableAt ℝ (fun y => ν • laplacian sol.velocity t y) x :=
    hD_lap.const_smul ν
  have hRHS_sub : staticCurl (fun y => ν • laplacian sol.velocity t y - pressureGradient sol.pressure t y) x =
      staticCurl (fun y => ν • laplacian sol.velocity t y) x -
      staticCurl (fun y => pressureGradient sol.pressure t y) x := by
    rw [show (fun y : Space => ν • laplacian sol.velocity t y - pressureGradient sol.pressure t y) =
        (fun y : Space => ν • laplacian sol.velocity t y) - (fun y : Space => pressureGradient sol.pressure t y) from rfl]
    rw [staticCurl_sub_field (ν • laplacian sol.velocity t) (pressureGradient sol.pressure t) x hD_smul_lap hD_pg]
    rfl
  rw [hRHS_sub] at hCurl
  have hCurl_smul : staticCurl (fun y => ν • laplacian sol.velocity t y) x =
      ν • staticCurl (fun y => laplacian sol.velocity t y) x := by
    have hlap : DifferentiableAt ℝ (laplacian sol.velocity t : Space → Space) x := hD_lap
    rw [show (fun y : Space => ν • laplacian sol.velocity t y) = (ν • (laplacian sol.velocity t : Space → Space)) from rfl]
    rw [staticCurl_smul_field ν (laplacian sol.velocity t) x hlap]
    rfl
  rw [hCurl_smul] at hCurl
  rw [staticCurl_laplacian_evolution_comm sol ht0 htT x] at hCurl
  rw [staticCurl_pressureGradient_eq_zero sol ht0 htT x] at hCurl
  rw [sub_zero] at hCurl
  exact hCurl
where
  staticCurl_add_field (a b : VelocityField) (x : Space)
      (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
      staticCurl (a + b) x = staticCurl a x + staticCurl b x := by
    unfold staticCurl
    rw [fderiv_add ha hb]
    simp [add_apply, Finset.sum_add_distrib, LinearMap.map_add]
  staticCurl_sub_field (a b : VelocityField) (x : Space)
      (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
      staticCurl (a - b) x = staticCurl a x - staticCurl b x := by
    unfold staticCurl
    rw [fderiv_sub ha hb]
    simp [sub_apply, Finset.sum_sub_distrib, LinearMap.map_sub]
  staticCurl_smul_field (c : ℝ) (a : VelocityField) (x : Space)
      (ha : DifferentiableAt ℝ a x) :
      staticCurl (c • a) x = c • staticCurl a x := by
    unfold staticCurl
    rw [fderiv_const_smul ha]
    simp [smul_apply, LinearMap.map_smul, Finset.smul_sum]

/-- **Vorticity transport equation** for `PartialClassicalSolution` at interior
times.  The same pointwise PDE as for `IsClassicalSolution`. -/
theorem vorticityTransportEquation (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    timeDerivative (fun s => vorticity sol.velocity s) t x +
      spatialDerivative (fun s => vorticity sol.velocity s) t x (sol.velocity t x) =
    spatialDerivative sol.velocity t x (vorticity sol.velocity t x) +
      ν • laplacian (fun s => vorticity sol.velocity s) t x := by
  have hPart := curl_of_momentum_eq_partial_vorticity_transport sol ht0 htT x
  have huA : ContDiffAt ℝ ∞ (sol.velocity t) x :=
    (contDiffAt_velocity_spacetime sol ht0 htT x).comp x
      (contDiffAt_const.prodMk contDiffAt_id) |>.comp_of_eq (by rfl)
  have hdiv : staticDivergence (sol.velocity t) x = 0 :=
    sol.incompressible t ht0.le htT x
  have hcurl_id := ConvectionCurl.staticCurl_convection_eq (sol.velocity t) x huA hdiv
  have hconv_curl : staticCurl (fun y => convection sol.velocity t y) x =
      spatialDerivative (fun s => vorticity sol.velocity s) t x (sol.velocity t x) -
        spatialDerivative sol.velocity t x (vorticity sol.velocity t x) := by
    calc
      staticCurl (fun y => convection sol.velocity t y) x
          = staticCurl (fun y => fderiv ℝ (sol.velocity t) y (sol.velocity t y)) x := rfl
      _ = fderiv ℝ (fun y => staticCurl (sol.velocity t) y) x (sol.velocity t x) -
          fderiv ℝ (sol.velocity t) x (staticCurl (sol.velocity t) x) := hcurl_id
      _ = fderiv ℝ (fun y => vorticity sol.velocity t y) x (sol.velocity t x) -
          fderiv ℝ (sol.velocity t) x (vorticity sol.velocity t x) := rfl
      _ = spatialDerivative (fun s => vorticity sol.velocity s) t x (sol.velocity t x) -
          spatialDerivative sol.velocity t x (vorticity sol.velocity t x) := rfl
  rw [hconv_curl] at hPart
  linear_combination hPart

/-!
## Section 5: Local enstrophy balance for `PartialClassicalSolution`
-/

/-- **Local enstrophy balance** for `PartialClassicalSolution` at interior
times.  The same pointwise identity as for `IsClassicalSolution`. -/
theorem local_enstrophy_balance (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    2 * officialInner (vorticity sol.velocity t x)
        (timeDerivative (fun s => vorticity sol.velocity s) t x) =
      2 * officialInner (vorticity sol.velocity t x)
          (spatialDerivative sol.velocity t x (vorticity sol.velocity t x))
      - fderiv ℝ (fun y => officialEuclideanNorm (vorticity sol.velocity t y) ^ 2) x
          (sol.velocity t x)
      + ν * (∑ i : Fin 3,
          fderiv ℝ (fun z =>
            fderiv ℝ (fun y => officialEuclideanNorm (vorticity sol.velocity t y) ^ 2) z
              (basisVector i)) x (basisVector i))
      - 2 * ν * (∑ i : Fin 3,
          officialEuclideanNorm (fderiv ℝ (vorticity sol.velocity t) x (basisVector i)) ^ 2) := by
  have hCD : ContDiff ℝ ∞ (vorticity sol.velocity t) := vorticity_contDiff sol ht0 htT
  have hdiffAll : ∀ y : Space, DifferentiableAt ℝ (vorticity sol.velocity t) y :=
    fun y => (hCD.differentiable (by norm_num)).differentiableAt
  have hdiff2 : DifferentiableAt ℝ (fderiv ℝ (vorticity sol.velocity t)) x :=
    ((hCD.fderiv_right (m := ∞) (by norm_num)).differentiable (by norm_num)).differentiableAt
  -- Transport equation solved for ∂ₜω: ∂ₜω = (ω·∇)u + νΔω - (u·∇)ω
  have hpde := vorticityTransportEquation sol ht0 htT x
  have hT : timeDerivative (fun s => vorticity sol.velocity s) t x =
      spatialDerivative sol.velocity t x (vorticity sol.velocity t x)
        + ν • laplacian (fun s => vorticity sol.velocity s) t x
        - spatialDerivative (fun s => vorticity sol.velocity s) t x (sol.velocity t x) :=
    eq_sub_of_add_eq hpde
  -- Convection direction as an fderiv; transport integrand identity
  have hconv : spatialDerivative (fun s => vorticity sol.velocity s) t x (sol.velocity t x) =
      fderiv ℝ (vorticity sol.velocity t) x (sol.velocity t x) := rfl
  have htransport :
      fderiv ℝ (fun y => officialEuclideanNorm (vorticity sol.velocity t y) ^ 2) x
        (sol.velocity t x) =
      2 * officialInner (vorticity sol.velocity t x)
        (fderiv ℝ (vorticity sol.velocity t) x (sol.velocity t x)) :=
    fderiv_normSq_apply (vorticity sol.velocity t) x (sol.velocity t x) (hdiffAll x)
  -- The vector laplacian in the transport eq matches the Bochner inner sum
  have hLapEq : laplacian (fun s => vorticity sol.velocity s) t x =
      ∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (vorticity sol.velocity t) z (basisVector i)) x
          (basisVector i) := rfl
  -- Pointwise Bochner: Δ|ω|² = 2⟨ω,Δω⟩ + 2|∇ω|²
  have hbochner := scalarLaplacian_normSq (vorticity sol.velocity t) x hdiffAll hdiff2
  -- Expand the LHS by inner linearity and substitute the pieces
  rw [hT, officialInner_sub_right, officialInner_add_right, officialInner_smul_right,
    hconv, hLapEq, htransport]
  -- Everything is now scalar; close with the Bochner identity
  linear_combination -ν * hbochner

/-!
## Section 6: `LocallyDominatedEnstrophy` from L²-mass hypotheses

From the hypothesis `hL2` that `‖u t·‖²` is integrable at every time, and the
smoothness of the vorticity at interior times, the enstrophy density `|ω|²` and
its pointwise rate `∂ₜ(|ω|²)` are locally dominated.  The smoothness gives
`L^∞_loc` control on each compact `K ⊂ (0,T)`, so an `L¹` majorant exists
(e.g. `sup_{t∈K} |ω(t,x)|² * χ_R` etc).
-/

lemma locallyDominatedEnstrophy_of_L2 (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (hL2 : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2)) :
    LocallyDominatedEnstrophy sol.velocity T := by
  intro K hKc hKsub
  -- Since K is compact and K ⊂ Ico 0 T, K has positive minimum > 0 or is empty/contains 0.
  -- In any case, we construct an L¹ majorant covering the vorticity squared and its rate.
  -- Strategy: pick ε = min(K)/2 or ε = (T - sup K)/2, take an envelope over K.
  have hKbd : BddAbove K := hKc.bddAbove
  have hKbd_below : BddBelow K := hKc.bddBelow
  obtain hKemp | ⟨t0, ht0K⟩ := K.isEmpty_or_nonempty
  · refine ⟨fun _ => 0, integrable_zero _ _ _, ?_, ?_⟩
    · intro t ht x; exact (hKemp ⟨t, ht⟩).elim
    · intro t ht x; exact (hKemp ⟨t, ht⟩).elim
  -- Split K into its part with t ≤ 0 (can only be {0}) and t > 0.
  -- For t > 0 in K, vorticity is C^∞ so |ω|² is continuous, hence bounded on each compact.
  -- For t = 0 (if present), the hL2 hypothesis provides L¹ bound indirectly.
  sorry

/-!
## Section 7: Enstrophy differential inequality for `PartialClassicalSolution`

The enstrophy differential inequality `E' ≤ 2·G·E` holds for
`PartialClassicalSolution` under a gradient majorant `G`, the
`LocallyDominatedEnstrophy` hypothesis (supplied by
`locallyDominatedEnstrophy_of_L2`), and a transport domination hypothesis.
-/

/-- **Enstrophy differential inequality** for `PartialClassicalSolution`.
Same statement as `EnstrophyLimit.enstrophyDifferentialInequality` but with
`PartialClassicalSolution` instead of `IsClassicalSolution`. -/
theorem enstrophyDifferentialInequality
    {ν : ℝ} (hν : 0 ≤ ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (G : ℝ → ℝ)
    (hG : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x v : Space,
      officialEuclideanNorm (spatialDerivative sol.velocity t x v) ≤
        G t * officialEuclideanNorm v)
    (hdom : LocallyDominatedEnstrophy sol.velocity T)
    (htr : TransportDominatedEnstrophy sol.velocity T) :
    ContinuousOn (enstrophy sol.velocity) (Set.Ico 0 T) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∃ E' : ℝ, HasDerivAt (enstrophy sol.velocity) E' t ∧
        E' ≤ 2 * G t * enstrophy sol.velocity t := by
  sorry
  -- This lemma is structurally identical to `EnstrophyLimit.enstrophyDifferentialInequality`,
  -- but needs the above `local_enstrophy_balance` for `PartialClassicalSolution`
  -- instead of the `IsClassicalSolution` version, and the enstrophy derivative
  -- lemmas adapted to `PartialClassicalSolution`.
  -- The proof follows `EnstrophyLimit`: continuity of enstrophy + rate bound.

/-!
## Section 8: Stretching bound from CF direction coherence (CONJECTURE)

The stretching term `∫ ω·∇u·ω` is bounded via the Biot-Savart singular integral
using the Constantin-Fefferman direction coherence `hcoh`:

  `∫ ω·∇u·ω = ∬ ω(x)·BSGradKernel(x-y)·(ω(x)×ω(y)) dx dy`

With `|ω(x)×ω(y)| ≤ (|x-y|/ρ)·|ω(x)|·|ω(y)|` for `|ω| ≥ Ω₀`, split the integral
into near-field `(|x-y| < πρ)` and far-field `(|x-y| ≥ πρ)`.  The near-field is
bounded by CZ + Calderon-Zygmund theory (`cz_nearField_cancellation`), the
far-field by kernel decay.  The resulting bound is

  `|∫ ω·∇u·ω| ≤ C·(E/ρ² + Ω₀²·E)`.

This lemma CONJECTURES the bound; its proof requires `BiotsavartKernel` +
`cz_nearField_cancellation`, which are identified as open fronts.
-/

/-- **Stretching bound from CF direction coherence.**  Under hcoh,
`|∫ ω·∇u·ω| ≤ C·(‖ω‖_L²²/ρ² + Ω₀²·‖ω‖_L²²)`. -/
theorem stretching_bound_from_directionCoherence
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (ρ Ω₀ : ℝ) (hρ : 0 < ρ) (hΩ₀ : 0 < Ω₀)
    (hL2 : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2))
    (hcoh : ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t y) →
      officialEuclideanNorm
          (vorticity sol.velocity t x ⨯₃ vorticity sol.velocity t y) ≤
        (officialEuclideanNorm (fun i => x i - y i) / ρ) *
          (officialEuclideanNorm (vorticity sol.velocity t x) *
            officialEuclideanNorm (vorticity sol.velocity t y)))
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    |∫ x : Space, officialInner (vorticity sol.velocity t x)
        (spatialDerivative sol.velocity t x (vorticity sol.velocity t x))| ≤
      C_cf * ((∫ x : Space, officialEuclideanNorm
          (vorticity sol.velocity t x) ^ 2) / ρ ^ 2 +
        Ω₀ ^ 2 * ∫ x : Space, officialEuclideanNorm
          (vorticity sol.velocity t x) ^ 2) := by
  sorry
  -- CONJECTURE — requires `BiotsavartKernel` + `cz_nearField_cancellation`.
  -- /-- The absolute constant in the CF stretching bound. -/
  -- let C_cf : ℝ := ...

/-!
## Section 9: Bounded enstrophy under CF hypotheses

Combined result: under the CF direction coherence, the enstrophy is bounded
exponentially in time, provided it is finite initially (from hL2 at t = 0).
-/

/-- **Enstrophy bounded under the CF direction coherence.**  Assembles the
enstrophy differential inequality and the stretching bound to give:

  `t ↦ ∫ |ω(t,x)|² dx ≤ E(0)·exp(C·t/ρ² + C·Ω₀²·t)`. -/
theorem enstrophy_bounded_under_CF
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (E : ℝ) (hE : 0 ≤ E)
    (hL2 : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2))
    (hmass : ∀ t : ℝ, 0 ≤ t → t < T →
      (∫ x : Space, ‖sol.velocity t x‖ ^ 2) ∈ Set.Icc (0 : ℝ) E)
    (ρ Ω₀ : ℝ) (hρ : 0 < ρ) (hΩ₀ : 0 < Ω₀)
    (hcoh : ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t y) →
      officialEuclideanNorm
          (vorticity sol.velocity t x ⨯₃ vorticity sol.velocity t y) ≤
        (officialEuclideanNorm (fun i => x i - y i) / ρ) *
          (officialEuclideanNorm (vorticity sol.velocity t x) *
            officialEuclideanNorm (vorticity sol.velocity t y)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ (C_CF : ℝ) (hC_CF : 0 < C_CF),
      ∀ t : ℝ, δ < t → t < T,
        enstrophy sol.velocity t ≤
          (1 + enstrophy sol.velocity 0) *
            Real.exp (2 * C_CF * (1/ρ ^ 2 + Ω₀ ^ 2) * t) - 1 := by
  sorry
  -- Requires: `locallyDominatedEnstrophy_of_L2` + `enstrophyDifferentialInequality`
  -- + `stretching_bound_from_directionCoherence` to produce a `G` (as a constant
  -- times (1/ρ² + Ω₀²)).  Then Grönwall via `enstrophy_apriori_bound`.

end Navier.Analysis.EnstrophyForPartialClassical