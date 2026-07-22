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
* `vorticityTransportEquation` — `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω`
  [curl of Navier–Stokes; Majda–Bertozzi (1.33) / §1.6]: the curl of the
  momentum equation (`VorticityTransport`) composed with the convection–curl
  identity (`ConvectionCurl`).

## The integral layer (downstream)

The pointwise integrand layer is `EnstrophyPointwise` +
`LocalEnstrophyBalance`; the integral layer — the cutoff enstrophy rate
(`CutoffEnstrophy`), the integration-by-parts remainders
(`CutoffIntegrationByParts`), the scaled cutoff family (`ScaledCutoff`), and
the `R → ∞` assembly (`EnstrophyLimit`) — derives
`EnstrophyLimit.enstrophyDifferentialInequality` (`E' ≤ 2·G·E`, with the
continuity clause) and the now-unconditional
`EnstrophyLimit.enstrophy_apriori_bound`
(`E(t) ≤ (1+E(0))·exp(2∫₀ᵗ G) − 1`) under the two named Pattern-A
domination hypotheses (`LocallyDominatedEnstrophy`,
`TransportDominatedEnstrophy`) — both automatic for `H^m`/Schwartz-class
solutions and both anchored non-vacuous by the zero solution.  The former
in-file skeleton carried a bare per-time integrability hypothesis that
cannot support the derivative interchange (Step-0e); the strengthened
hypotheses are the honest operative regime.
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
## The vorticity transport equation
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

end Navier.Analysis.Enstrophy
