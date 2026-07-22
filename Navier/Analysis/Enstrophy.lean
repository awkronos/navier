import Navier.Analysis.BKMLogBootstrap
import Navier.Analysis.ConvectionCurl

/-!
# Enstrophy: the vortex-stretching energy layer

The enstrophy `E(t) = ∫ |ω(t,x)|² dx` obeys the vortex-stretching estimate

  `dE/dt = 2∫ ⟨ω, (ω·∇)u⟩ − 2ν∫ |∇ω|²  ≤  2‖∇u(t)‖_∞ · E(t)`

(Majda–Bertozzi §3.3): the transport term integrates to zero by
incompressibility, the viscous term is dissipative, and the stretching term is
bounded pointwise by Cauchy–Schwarz.  Combined with the linear Grönwall engine
`gronwall_log_apriori` this bounds the enstrophy by the time-integral of the
gradient sup — the exact `M₂` (vorticity-`L²`) majorant that
`logBKMControl_of_schwartzSliced` consumes.  The assembly line is:

  `∫‖ω‖_∞ < ∞` → (Biot–Savart log) gradient majorant → (this file) enstrophy
  bounded → `M₂` majorant → `LogBKMControl` → `velocity_bounded`.

## Certified here (no sorry)

* `officialInner` + Cauchy–Schwarz + `stretching_pointwise_bound` — the
  pointwise vortex-stretching estimate `⟨ω, Aω⟩ ≤ M·|ω|²`.
* `enstrophy` (with its nonnegativity), `enstrophy_zero_velocity`.
* `enstrophy_apriori_bound` — the Grönwall wiring: GIVEN the differential
  inequality (skeleton below), `E(t) ≤ (1+E(0))·exp(2∫₀ᵗ G) − 1` on `[0,T)`.
  (Inherits the skeleton's `sorryAx`; the Grönwall application, derivative
  extraction, and bound algebra are fully derived.)
* `vorticityTransportEquation` — `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω`
  [curl of Navier–Stokes; Majda–Bertozzi (1.33) / §1.6]: the curl of the
  momentum equation (`VorticityTransport`) composed with the convection–curl
  identity (`ConvectionCurl`).

## Skeletons (honest `sorry`, truth-checked signatures)

* `enstrophyDifferentialInequality` — continuity + derivative existence +
  `E' ≤ 2·G·E` under a gradient majorant and **explicit integrability
  hypotheses** (without which the Bochner integral degenerates to `0` and the
  statement would be vacuously about the junk value — Step-0e disclosed)
  [Majda–Bertozzi §3.3; est ~350 LOC].
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral

namespace Navier.Analysis.Enstrophy

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BealeKatoMajda

/-!
## Pointwise layer: official inner product and the stretching bound
-/

/-- Fefferman's Euclidean inner product on the `Space` coordinates. -/
def officialInner (x y : Space) : ℝ :=
  inner ℝ (officialEuclideanPoint x) (officialEuclideanPoint y)

@[simp] theorem officialInner_self (x : Space) :
    officialInner x x = officialEuclideanNorm x ^ 2 := by
  simp [officialInner, officialEuclideanNorm]

/-- Cauchy–Schwarz in the official Euclidean coordinates. -/
theorem abs_officialInner_le (x y : Space) :
    |officialInner x y| ≤ officialEuclideanNorm x * officialEuclideanNorm y :=
  abs_real_inner_le_norm _ _

/-- **Pointwise vortex-stretching bound.**  If the deformation applied to the
vorticity is dominated by `M` times the vorticity (an operator-norm bound in
the official coordinates), then the stretching production `⟨ω, Aω⟩` is at most
`M·|ω|²`.  This is the pointwise Cauchy–Schwarz step of the enstrophy
estimate. -/
theorem stretching_pointwise_bound {M : ℝ} (ω Aω : Space)
    (hA : officialEuclideanNorm Aω ≤ M * officialEuclideanNorm ω) :
    officialInner ω Aω ≤ M * officialEuclideanNorm ω ^ 2 := by
  calc officialInner ω Aω ≤ |officialInner ω Aω| := le_abs_self _
    _ ≤ officialEuclideanNorm ω * officialEuclideanNorm Aω :=
        abs_officialInner_le _ _
    _ ≤ officialEuclideanNorm ω * (M * officialEuclideanNorm ω) :=
        mul_le_mul_of_nonneg_left hA (officialEuclideanNorm_nonneg _)
    _ = M * officialEuclideanNorm ω ^ 2 := by ring

/-!
## The enstrophy integral
-/

/-- The enstrophy: the squared vorticity `L²` integral at time `t`.  (For a
non-`L²` vorticity field the Bochner integral degenerates to `0`; consumers
must carry integrability, as `enstrophyDifferentialInequality` does.) -/
def enstrophy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, officialEuclideanNorm (vorticity u t x) ^ 2

theorem enstrophy_nonneg (u : VelocityEvolution) (t : ℝ) :
    0 ≤ enstrophy u t :=
  integral_nonneg fun x => by positivity

/-- The zero velocity has zero enstrophy at every time (non-vacuity anchor for
the layer). -/
theorem enstrophy_zero_velocity (t : ℝ) :
    enstrophy (fun _ _ => 0) t = 0 := by
  have h : ∀ x : Space,
      officialEuclideanNorm (vorticity (fun _ _ => 0) t x) ^ 2 = 0 := by
    intro x
    have hv : vorticity (fun _ _ => 0) t x = 0 := by
      simp [vorticity, staticCurl]
    rw [hv, (officialEuclideanNorm_eq_zero_iff 0).mpr rfl]
    norm_num
  simp only [enstrophy]
  rw [show (fun x : Space =>
      officialEuclideanNorm (vorticity (fun _ _ => 0) t x) ^ 2) =
      fun _ => (0:ℝ) from funext h]
  simp

/-!
## Skeletons
-/

/-- **Vorticity transport equation** (Majda–Bertozzi (1.33)/§1.6).  Along a
classical solution the vorticity satisfies `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω`
pointwise on nonnegative time.  The curl of the momentum equation kills the
pressure gradient and commutes with `∂ₜ` and `Δ`
(`curl_of_momentum_eq_partial_vorticity_transport`), reducing the PDE to the
convection–curl identity `curl((u·∇)u) = (u·∇)ω − (ω·∇)u`
(`vorticityTransport_eq_partial_and_convection_curl`), which
`staticCurl_convection_evolution` derives from the bilinear product rule,
Clairaut symmetry, and the gradient-square cross identity under `div u = 0`. -/
theorem vorticityTransportEquation
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      timeDerivative (fun s => vorticity u s) t x +
        spatialDerivative (fun s => vorticity u s) t x (u t x) =
      spatialDerivative u t x (vorticity u t x) +
        ν • laplacian (fun s => vorticity u s) t x := by
  intro t ht x
  exact (VorticityTransport.vorticityTransport_eq_partial_and_convection_curl
      hsol ht x).mpr
    (ConvectionCurl.staticCurl_convection_evolution hsol ht x)

/-- **[SKELETON — enstrophy differential inequality; Majda–Bertozzi §3.3;
est ~350 LOC.]**  Along a classical solution with a gradient majorant `G`
(an official-coordinates operator bound) and explicitly integrable vorticity
data on `[0,T)`, the enstrophy is continuous on `[0,T)`, differentiable on
`(0,T)`, and satisfies `E' ≤ 2·G·E`: the transport term integrates to zero by
incompressibility, the viscous term is dissipative (`0 ≤ ν`), and the
stretching term is bounded by `stretching_pointwise_bound` under the integral.

The integrability hypotheses are load-bearing: without them the Bochner
integral in `enstrophy` degenerates to the junk value `0` and the statement
would be vacuous (Step-0e).  Closure route: differentiation under the integral
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), integration by parts for
the transport/viscous terms with Schwartz-class decay, then the pointwise
bound. -/
theorem enstrophyDifferentialInequality
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p) (hν : 0 ≤ ν)
    {T : ℝ} (G : ℝ → ℝ)
    (hG : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x v : Space,
      officialEuclideanNorm (spatialDerivative u t x v) ≤
        G t * officialEuclideanNorm v)
    (hint : ∀ t ∈ Set.Ico (0:ℝ) T,
      Integrable (fun x : Space =>
        officialEuclideanNorm (vorticity u t x) ^ 2)) :
    ContinuousOn (enstrophy u) (Set.Ico 0 T) ∧
    ∀ t ∈ Set.Ioo (0:ℝ) T,
      ∃ E' : ℝ, HasDerivAt (enstrophy u) E' t ∧
        E' ≤ 2 * G t * enstrophy u t := by
  sorry

/-!
## Engine wiring: enstrophy a-priori bound (feeds the BKM `M₂` slot)
-/

/-- **Enstrophy a-priori bound.**  Along a classical solution with a
continuous nonnegative gradient majorant `G`, the enstrophy obeys

  `E(t) ≤ (1 + E(0))·exp(2∫₀ᵗ G) − 1`  on `[0,T)`.

Derived by feeding the differential inequality (skeleton) into the linear
Grönwall engine `gronwall_log_apriori` applied to `Y = 1 + E` (which keeps the
control positive even when the enstrophy vanishes).  This is exactly the
vorticity-`L²` majorant `M₂` that `logBKMControl_of_schwartzSliced` consumes:
`∫ |curl u(t)|² = E(t) ≤` this bound. -/
theorem enstrophy_apriori_bound
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p) (hν : 0 ≤ ν)
    {T : ℝ} (G : ℝ → ℝ)
    (hGc : ContinuousOn G (Set.Ico 0 T))
    (hGnn : ∀ t ∈ Set.Ico (0:ℝ) T, 0 ≤ G t)
    (hG : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x v : Space,
      officialEuclideanNorm (spatialDerivative u t x v) ≤
        G t * officialEuclideanNorm v)
    (hint : ∀ t ∈ Set.Ico (0:ℝ) T,
      Integrable (fun x : Space =>
        officialEuclideanNorm (vorticity u t x) ^ 2)) :
    ∀ t ∈ Set.Ico (0:ℝ) T,
      enstrophy u t ≤
        (1 + enstrophy u 0) *
          Real.exp (∫ s in (0:ℝ)..t, 2 * G s) - 1 := by
  obtain ⟨hEc, hEderiv⟩ := enstrophyDifferentialInequality hsol hν G hG hint
  intro t ht
  -- restrict to the closed interval [0, t] ⊂ [0, T)
  have hIcc_sub : Set.Icc 0 t ⊆ Set.Ico 0 T := by
    intro s hs; exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hIoo_sub : Set.Ioo 0 t ⊆ Set.Ioo 0 T := by
    intro s hs; exact ⟨hs.1, lt_trans hs.2 ht.2⟩
  -- the positive control Y = 1 + E with derivative deriv Y
  set Y : ℝ → ℝ := fun s => 1 + enstrophy u s with hYdef
  have hYc : ContinuousOn Y (Set.Icc 0 t) :=
    continuousOn_const.add (hEc.mono hIcc_sub)
  have hYpos : ∀ s ∈ Set.Icc 0 t, 0 < Y s := by
    intro s _
    have := enstrophy_nonneg u s
    simp only [hYdef]; linarith
  have hYfacts : ∀ s ∈ Set.Ioo 0 t,
      HasDerivAt Y (deriv Y s) s ∧
      deriv Y s ≤ (2 * G s) * Y s := by
    intro s hs
    obtain ⟨E', hE', hE'le⟩ := hEderiv s (hIoo_sub hs)
    have hYd : HasDerivAt Y E' s := hE'.const_add 1
    have hderiv : deriv Y s = E' := hYd.deriv
    rw [hderiv]
    refine ⟨hYd, ?_⟩
    have hsIco : s ∈ Set.Ico (0:ℝ) T :=
      ⟨le_of_lt hs.1, lt_trans hs.2 ht.2⟩
    have hGs : 0 ≤ G s := hGnn s hsIco
    have hEs : 0 ≤ enstrophy u s := enstrophy_nonneg u s
    calc E' ≤ 2 * G s * enstrophy u s := hE'le
      _ ≤ (2 * G s) * Y s := by
          simp only [hYdef]; nlinarith
  have hgc : ContinuousOn (fun s => 2 * G s) (Set.Icc 0 t) :=
    continuousOn_const.mul (hGc.mono hIcc_sub)
  have hcore := gronwall_log_apriori (Y := Y) (Y' := deriv Y)
    (g := fun s => 2 * G s) (T := t) ht.1 hgc hYc
    (fun s hs => (hYfacts s hs).1) hYpos
    (fun s hs => (hYfacts s hs).2)
    t ⟨ht.1, le_rfl⟩
  have hY0 : Y 0 = 1 + enstrophy u 0 := rfl
  have hYt : Y t = 1 + enstrophy u t := rfl
  rw [hY0, hYt] at hcore
  linarith [hcore]

end Navier.Analysis.Enstrophy
