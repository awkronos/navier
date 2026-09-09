import Navier.Analysis.Enstrophy
import Navier.Analysis.EuclideanPDETransport
import Navier.Analysis.HalfSpaceConsumerBridge
import Navier.Construction.PeriodicUniqueness

/-!
# Periodic enstrophy evolution on the native solution carrier

For an actual smooth unforced periodic solution, this file derives on the
physical Euclidean unit cell

`Z'(t) = S(t) - ν Dω(t)`,

where `Z = 1/2 ∫|ω|²`, `S = ∫⟨ω,(ω·∇)u⟩`, and
`Dω = ∫∑ᵢ|∂ᵢω|²`.  The vortex-stretching term is retained with its exact
sign.  A trajectory-dependent gradient bound gives
`Z' + ν Dω ≤ 2 G Z`.

This estimate is scale-consistent but supercritical: under the integer
periodic rescaling `u(t,x) ↦ λ u(λ²t,λx)`, `Z` scales like `λ⁴` on the fixed
unit cell while `Z'`, `S`, and `Dω` scale like `λ⁶`, and `G` like `λ²`.
Consequently this identity does not turn the kinetic-energy budget alone into
a horizon-uniform critical estimate; control of the stretching trajectory is
still required.

Reference: Majda--Bertozzi, *Vorticity and Incompressible Flow*, §3.3.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace Matrix

namespace Navier.Analysis.PeriodicEnstrophyControl

open Navier
open Navier.Analysis.Vorticity

private theorem euclideanVelocity_unitPeriods
    {u : VelocityEvolution} (hu : SpatiallyPeriodicVelocity u)
    {t : ℝ} (ht : 0 ≤ t) :
    Navier.Construction.PeriodicIntegration.UnitPeriods
      (fun x => EuclideanPDETransport.euclideanVelocity u (t, x)) := by
  intro x i
  apply EuclideanPDETransport.toNative.injective
  simp only [EuclideanPDETransport.euclideanVelocity,
    EuclideanPDETransport.toNative_toEuclidean]
  rw [map_add]
  have hb : EuclideanPDETransport.toNative
      (Navier.Construction.ProblemStatement.coordinateVector i) = basisVector i :=
    EuclideanPDETransport.toNative_eBasisVector i
  rw [hb]
  exact hu t ht (EuclideanPDETransport.toNative x) i

private theorem euclidean_spatialDivergence_zero
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 ≤ t) (x : EuclideanPDETransport.ESpace) :
    Navier.Construction.ProblemStatement.spatialDivergence
      (EuclideanPDETransport.euclideanVelocity u) t x = 0 := by
  have heu := EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime
    h.velocity_smooth
  have hs := EuclideanPDETransport.eFutureSpatialSlice_contDiff heu ht
  have hd := EuclideanPDETransport.divergence_nativeVelocity
    (EuclideanPDETransport.euclideanVelocity u)
    (x := x) (hs.differentiable (by simp) x)
  rw [EuclideanPDETransport.nativeVelocity_euclideanVelocity] at hd
  exact hd.symm.trans (h.incompressible t ht (EuclideanPDETransport.toNative x))

private theorem staticCurl_add_field (a b : VelocityField) (x : Space)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    staticCurl (fun y => a y + b y) x = staticCurl a x + staticCurl b x := by
  unfold staticCurl
  rw [show (fun y => a y + b y) = (a + b) from rfl, fderiv_add ha hb]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [add_apply, map_add]

private theorem staticCurl_sub_field (a b : VelocityField) (x : Space)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    staticCurl (fun y => a y - b y) x = staticCurl a x - staticCurl b x := by
  unfold staticCurl
  rw [show (fun y => a y - b y) = (a - b) from rfl, fderiv_sub ha hb]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sub_apply, map_sub]

private theorem staticCurl_smul_field (c : ℝ) (a : VelocityField) (x : Space)
    (ha : DifferentiableAt ℝ a x) :
    staticCurl (fun y => c • a y) x = c • staticCurl a x := by
  unfold staticCurl
  rw [show (fun y => c • a y) = (c • a) from rfl, fderiv_const_smul ha]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (crossProduct (basisVector i))
      (c • fderiv ℝ a x (basisVector i)) =
    c • (crossProduct (basisVector i)) (fderiv ℝ a x (basisVector i))
  exact (crossProduct (basisVector i)).map_smul c _

/-- Curling the native periodic momentum equation gives the partial
vorticity equation.  This is the periodic analogue of the whole-space lemma;
it consumes only the smoothness and PDE fields present in
`IsPeriodicClassicalSolution`. -/
theorem periodic_curl_momentum
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    timeDerivative (fun s => vorticity u s) t x +
      staticCurl (fun y => convection u t y) x =
      ν • laplacian (fun s => vorticity u s) t x := by
  have huA : ContDiffAt ℝ ∞ (u t) x :=
    VorticityTransport.contDiffAt_spatial_slice hsol.velocity_smooth ht x
  have hpA : ContDiffAt ℝ ∞ (p t) x :=
    VorticityTransport.contDiffAt_spatial_slice hsol.pressure_smooth ht x
  have huAfd : ContDiffAt ℝ ∞ (fderiv ℝ (u t)) x := huA.fderiv_right (by simp)
  have hD_conv : DifferentiableAt ℝ (fun y => convection u t y) x :=
    (huAfd.clm_apply huA).differentiableAt (by decide)
  have hD_pg : DifferentiableAt ℝ (fun y => pressureGradient p t y) x := by
    have hpfd : ContDiffAt ℝ ∞ (fderiv ℝ (p t)) x := hpA.fderiv_right (by simp)
    rw [show (fun y => pressureGradient p t y) =
        (fun y i => fderiv ℝ (p t) y (basisVector i)) from rfl]
    apply differentiableAt_pi.mpr
    intro i
    exact ((ContinuousLinearMap.apply ℝ ℝ (basisVector i)).contDiff.contDiffAt).comp
      x hpfd |>.differentiableAt (by decide)
  have hD_lap : DifferentiableAt ℝ (laplacian u t) x := by
    rw [show (laplacian u t : VelocityField) =
        (∑ i : Fin 3, fun y =>
          fderiv ℝ (fun z => fderiv ℝ (u t) z (basisVector i)) y (basisVector i))
      from by ext y; simp only [laplacian, Finset.sum_apply]]
    apply DifferentiableAt.sum
    intro i hi
    have hg : ContDiffAt ℝ ∞
        (fun z => fderiv ℝ (u t) z (basisVector i)) x :=
      ((ContinuousLinearMap.apply ℝ Space (basisVector i)).contDiff.contDiffAt).comp
        x huAfd
    have hg' : ContDiffAt ℝ ∞
        (fderiv ℝ (fun z => fderiv ℝ (u t) z (basisVector i))) x :=
      hg.fderiv_right (by simp)
    exact (((ContinuousLinearMap.apply ℝ Space
      (basisVector i)).contDiff.contDiffAt).comp x hg').differentiableAt (by decide)
  have hMom : ∀ y : Space,
      timeDerivative u t y + convection u t y =
        ν • laplacian u t y - pressureGradient p t y := by
    intro y
    simpa [zeroForce] using hsol.equation t ht y
  have hD_smul_lap : DifferentiableAt ℝ (fun y => ν • laplacian u t y) x := by
    rw [show (fun y => ν • laplacian u t y) = (ν • laplacian u t) from rfl]
    exact hD_lap.const_smul ν
  have hD_time : DifferentiableAt ℝ (fun y => timeDerivative u t y) x := by
    have heq : (fun y => timeDerivative u t y) =
        (fun y => ν • laplacian u t y - pressureGradient p t y - convection u t y) := by
      funext y
      have hm := hMom y
      rw [← hm]
      abel
    rw [heq]
    exact (hD_smul_lap.sub hD_pg).sub hD_conv
  have hCurl : staticCurl (fun y => timeDerivative u t y + convection u t y) x =
      staticCurl (fun y => ν • laplacian u t y - pressureGradient p t y) x := by
    congr 1
    funext y
    exact hMom y
  rw [staticCurl_add_field _ _ _ hD_time hD_conv] at hCurl
  rw [VorticityTransport.staticCurl_timeDerivative_comm
    u hsol.velocity_smooth ht x] at hCurl
  rw [staticCurl_sub_field (fun y => ν • laplacian u t y)
      (fun y => pressureGradient p t y) x hD_smul_lap hD_pg] at hCurl
  rw [staticCurl_smul_field ν (laplacian u t) x hD_lap] at hCurl
  rw [VorticityTransport.staticCurl_laplacian_evolution_comm
    u hsol.velocity_smooth ht x] at hCurl
  rw [VorticityTransport.staticCurl_pressureGradient_eq_zero
    p hsol.pressure_smooth ht x, sub_zero] at hCurl
  exact hCurl

/-- The exact native vorticity transport equation for periodic solutions. -/
theorem periodic_vorticityTransportEquation
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    timeDerivative (fun s => vorticity u s) t x +
        spatialDerivative (fun s => vorticity u s) t x (u t x) =
      spatialDerivative u t x (vorticity u t x) +
        ν • laplacian (fun s => vorticity u s) t x := by
  have hpart := periodic_curl_momentum hsol ht x
  have hcurl := ConvectionCurl.staticCurl_convection_eq (u t) x
    (VorticityTransport.contDiffAt_spatial_slice hsol.velocity_smooth ht x)
    (hsol.incompressible t ht x)
  simp only [convection, spatialDerivative] at hpart
  rw [hcurl] at hpart
  simp only [spatialDerivative, vorticity]
  rw [← hpart]
  abel

/-- Vorticity inherits smoothness on the entire closed nonnegative-time
half-space.  The boundary regularity is obtained from the proved Seeley
extension and an actual differentiated extension, rather than assumed. -/
theorem vorticity_smoothOnNonnegativeTime
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsPeriodicClassicalSolution ν zeroForce u₀ u p) :
    SmoothVelocityOnNonnegativeTime (fun t => vorticity u t) := by
  obtain ⟨w⟩ :=
    (HalfSpaceConsumerBridge.smoothVelocity_iff_globalExtension u).mp
      hsol.velocity_smooth
  let U : ℝ × Space → Space := w.extension
  let Ω : ℝ × Space → Space := fun z =>
    ∑ i : Fin 3, basisVector i ⨯₃
      (fderiv ℝ (fun y => U (z.1, y)) z.2 (basisVector i))
  have huncurry : ContDiff ℝ ∞
      (Function.uncurry (fun z : ℝ × Space => fun y : Space => U (z.1, y))) := by
    exact w.smooth.comp
      ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hD : ContDiff ℝ ∞ (fun z : ℝ × Space =>
      fderiv ℝ (fun y => U (z.1, y)) z.2) :=
    ContDiff.fderiv huncurry contDiff_snd (by simp)
  have hΩ : ContDiff ℝ ∞ Ω := by
    apply ContDiff.sum
    intro i hi
    exact (crossProduct (basisVector i)).toContinuousLinearMap.contDiff.comp
      (hD.clm_apply contDiff_const)
  refine hΩ.contDiffOn.congr ?_
  intro z hz
  have hslices : (fun y => U (z.1, y)) = u z.1 := by
    funext y
    exact w.agrees z.1 hz.1 y
  simp only [Ω, vorticity, staticCurl]
  rw [hslices]

/-- Native vorticity inherits every spatial unit period. -/
theorem vorticity_periodic
    {u : VelocityEvolution} (hu : SpatiallyPeriodicVelocity u) :
    SpatiallyPeriodicVelocity (fun t => vorticity u t) := by
  intro t ht x i
  have hfun : (fun y => u t (y + basisVector i)) = u t := by
    funext y
    exact hu t ht y i
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := u t)
    (x := x) (basisVector i)
  rw [hfun] at hd
  unfold vorticity staticCurl
  simp only
  apply Finset.sum_congr rfl
  intro j hj
  rw [← hd]

def euclideanVorticity (u : VelocityEvolution) :
    Navier.Analysis.EuclideanPDETransport.EVelocityField :=
  Navier.Analysis.EuclideanPDETransport.euclideanVelocity
    (fun t => vorticity u t)

/-- Physical enstrophy `1/2 ∫_[0,1]^3 |ω|²`. -/
def unitCellEnstrophy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Navier.Construction.PeriodicUniqueness.energy
    (euclideanVorticity u) 0 t

/-- Vorticity-gradient dissipation `∫_[0,1]^3 ∑ᵢ|∂ᵢω|²`. -/
def unitCellVorticityDissipation (u : VelocityEvolution) (t : ℝ) : ℝ :=
  Navier.Construction.PeriodicUniqueness.dissipation (euclideanVorticity u) t

/-- Exact vortex-stretching production in the unit cell. -/
def unitCellVortexStretching (u : VelocityEvolution) (t : ℝ) : ℝ :=
  Navier.Construction.PeriodicIntegration.cubeIntegral (fun x =>
    ⟪euclideanVorticity u (t, x),
      Navier.Construction.ProblemStatement.spatialDerivative
        (Navier.Analysis.EuclideanPDETransport.euclideanVelocity u) t x
        (euclideanVorticity u (t, x))⟫_ℝ)

theorem unitCellEnstrophy_nonneg (u : VelocityEvolution) (t : ℝ) :
    0 ≤ unitCellEnstrophy u t := by
  unfold unitCellEnstrophy
  exact mul_nonneg (by norm_num)
    (Navier.Construction.PeriodicUniqueness.energy_nonneg
      (euclideanVorticity u) 0 t)

theorem unitCellVorticityDissipation_nonneg (u : VelocityEvolution) (t : ℝ) :
    0 ≤ unitCellVorticityDissipation u t :=
  Navier.Construction.PeriodicUniqueness.dissipation_nonneg
    (euclideanVorticity u) t

private theorem directionalDerivative_nativeVelocity
    (a b : Navier.Analysis.EuclideanPDETransport.EVelocityField)
    {t : ℝ} {x : Navier.Analysis.EuclideanPDETransport.ESpace}
    (ha : DifferentiableAt ℝ (fun y => a (t, y)) x) :
    spatialDerivative
        (Navier.Analysis.EuclideanPDETransport.nativeVelocity a) t
        (Navier.Analysis.EuclideanPDETransport.toNative x)
        (Navier.Analysis.EuclideanPDETransport.nativeVelocity b t
          (Navier.Analysis.EuclideanPDETransport.toNative x)) =
      Navier.Analysis.EuclideanPDETransport.toNative
        (Navier.Analysis.EuclideanPDETransport.eSpatialDerivative a t x (b (t, x))) := by
  rw [Navier.Analysis.EuclideanPDETransport.spatialDerivative_nativeVelocity a ha]
  simp [Navier.Analysis.EuclideanPDETransport.nativeVelocity_value,
    ContinuousLinearMap.comp_apply]

/-- Euclidean-coordinate vorticity transport used by unit-cell integration. -/
theorem euclidean_vorticity_transport
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 < t)
    (x : Navier.Analysis.EuclideanPDETransport.ESpace) :
    Navier.Construction.ProblemStatement.temporalDerivative
        (euclideanVorticity u) t x +
      Navier.Construction.ProblemStatement.spatialDerivative
        (euclideanVorticity u) t x
        (Navier.Analysis.EuclideanPDETransport.euclideanVelocity u (t, x)) =
      Navier.Construction.ProblemStatement.spatialDerivative
          (Navier.Analysis.EuclideanPDETransport.euclideanVelocity u) t x
          (euclideanVorticity u (t, x)) +
        ν • Navier.Construction.ProblemStatement.spatialLaplacian
          (euclideanVorticity u) t x := by
  let ew := euclideanVorticity u
  let eu := Navier.Analysis.EuclideanPDETransport.euclideanVelocity u
  have hewSmooth := Navier.Analysis.EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime
    (vorticity_smoothOnNonnegativeTime hsol)
  have heuSmooth := Navier.Analysis.EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime
    hsol.velocity_smooth
  have hsw := Navier.Analysis.EuclideanPDETransport.eFutureSpatialSlice_contDiff
    hewSmooth ht.le
  have hsu := Navier.Analysis.EuclideanPDETransport.eFutureSpatialSlice_contDiff
    heuSmooth ht.le
  have htw := Navier.Analysis.EuclideanPDETransport.eFutureTimeSlice_differentiableAt
    hewSmooth ht x
  have hdt := Navier.Analysis.EuclideanPDETransport.timeDerivative_nativeVelocity_of_pos
    ew ht x htw
  have htrans := directionalDerivative_nativeVelocity ew eu
    (hsw.differentiable (by simp) x)
  have hstretch := directionalDerivative_nativeVelocity eu ew
    (hsu.differentiable (by simp) x)
  have hlap := Navier.Analysis.EuclideanPDETransport.laplacian_nativeVelocity
    ew (x := x) hsw
  have hpde := periodic_vorticityTransportEquation hsol ht.le
    (Navier.Analysis.EuclideanPDETransport.toNative x)
  change Navier.Analysis.EuclideanPDETransport.eTimeDerivative ew t x +
      Navier.Analysis.EuclideanPDETransport.eSpatialDerivative ew t x (eu (t, x)) =
    Navier.Analysis.EuclideanPDETransport.eSpatialDerivative eu t x (ew (t, x)) +
      ν • Navier.Analysis.EuclideanPDETransport.eLaplacian ew t x
  apply Navier.Analysis.EuclideanPDETransport.toNative.injective
  simp only [map_add, map_smul]
  rw [← hdt, ← htrans, ← hstretch, ← hlap]
  simpa [ew, eu, euclideanVorticity] using hpde

/-- Exact squared-enstrophy rate before the physical factor `1/2`. -/
theorem euclidean_vorticity_energyRate
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 < t) :
    Navier.Construction.PeriodicUniqueness.energyRate
        (euclideanVorticity u) 0 t =
      2 * unitCellVortexStretching u t -
        2 * ν * unitCellVorticityDissipation u t := by
  let ew : Navier.Construction.ProblemStatement.VelocityField := euclideanVorticity u
  let eu : Navier.Construction.ProblemStatement.VelocityField :=
    Navier.Analysis.EuclideanPDETransport.euclideanVelocity u
  have hewSmooth := Navier.Analysis.EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime
    (vorticity_smoothOnNonnegativeTime hsol)
  have heuSmooth := Navier.Analysis.EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime
    hsol.velocity_smooth
  have hsw := Navier.Analysis.EuclideanPDETransport.eFutureSpatialSlice_contDiff
    hewSmooth ht.le
  have hsu := Navier.Analysis.EuclideanPDETransport.eFutureSpatialSlice_contDiff
    heuSmooth ht.le
  have hpw := euclideanVelocity_unitPeriods
    (vorticity_periodic hsol.velocity_periodic) ht.le
  have hpu := euclideanVelocity_unitPeriods
    hsol.velocity_periodic ht.le
  have hdiv := fun x =>
    euclidean_spatialDivergence_zero hsol ht.le x
  have hL := (hsw.inner ℝ
    (Navier.Construction.PeriodicUniqueness.spatialLaplacian_contDiff hsw)).continuous
  have hT := (hsw.inner ℝ ((hsw.fderiv_right (by simp)).clm_apply hsu)).continuous
  have hS := (hsw.inner ℝ ((hsu.fderiv_right (by simp)).clm_apply hsw)).continuous
  have heq : (fun x => ⟪ew (t, x),
      Navier.Construction.ProblemStatement.temporalDerivative ew t x⟫_ℝ) =
    (fun x => ⟪ew (t, x),
        Navier.Construction.ProblemStatement.spatialDerivative eu t x (ew (t, x))⟫_ℝ +
      ν * ⟪ew (t, x),
        Navier.Construction.ProblemStatement.spatialLaplacian ew t x⟫_ℝ -
      ⟪ew (t, x),
        Navier.Construction.ProblemStatement.spatialDerivative ew t x (eu (t, x))⟫_ℝ) := by
    funext x
    have hpde := euclidean_vorticity_transport hsol ht x
    change Navier.Construction.ProblemStatement.temporalDerivative ew t x +
        Navier.Construction.ProblemStatement.spatialDerivative ew t x (eu (t, x)) =
      Navier.Construction.ProblemStatement.spatialDerivative eu t x (ew (t, x)) +
        ν • Navier.Construction.ProblemStatement.spatialLaplacian ew t x at hpde
    have hpde' := congrArg (fun z => z -
      Navier.Construction.ProblemStatement.spatialDerivative ew t x (eu (t, x))) hpde
    simp only [add_sub_cancel_right] at hpde'
    rw [hpde']
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
  have hrate : Navier.Construction.PeriodicUniqueness.energyRate ew 0 t =
      2 * Navier.Construction.PeriodicIntegration.cubeIntegral (fun x =>
        ⟪ew (t, x), Navier.Construction.ProblemStatement.temporalDerivative ew t x⟫_ℝ) := by
    simp [Navier.Construction.PeriodicUniqueness.energyRate,
      Navier.Construction.ProblemStatement.temporalDerivative,
      Navier.Construction.PeriodicIntegration.cubeIntegral_const_mul]
  change Navier.Construction.PeriodicUniqueness.energyRate ew 0 t =
    2 * Navier.Construction.PeriodicIntegration.cubeIntegral (fun x =>
      ⟪ew (t, x), Navier.Construction.ProblemStatement.spatialDerivative eu t x (ew (t, x))⟫_ℝ) -
      2 * ν * Navier.Construction.PeriodicUniqueness.dissipation ew t
  rw [hrate, heq]
  rw [Navier.Construction.PeriodicIntegration.cubeIntegral_sub
      (f := fun x =>
        ⟪ew (t, x), Navier.Construction.ProblemStatement.spatialDerivative eu t x
          (ew (t, x))⟫_ℝ +
        ν * ⟪ew (t, x), Navier.Construction.ProblemStatement.spatialLaplacian ew t x⟫_ℝ)
      (g := fun x =>
        ⟪ew (t, x), Navier.Construction.ProblemStatement.spatialDerivative ew t x
          (eu (t, x))⟫_ℝ)
      (hS.add (continuous_const.mul hL)) hT]
  simp only [Navier.Construction.ProblemStatement.spatialDerivative]
  rw [Navier.Construction.PeriodicIntegration.cubeIntegral_add
      (f := fun x => ⟪ew (t, x),
        (fderiv ℝ (fun y => eu (t, y)) x) (ew (t, x))⟫_ℝ)
      (g := fun x => ν * ⟪ew (t, x),
        Navier.Construction.ProblemStatement.spatialLaplacian ew t x⟫_ℝ)
      hS (continuous_const.mul hL),
    Navier.Construction.PeriodicIntegration.cubeIntegral_const_mul ν,
    Navier.Construction.PeriodicUniqueness.cubeIntegral_laplacian_energy
      (w := ew) (t := t) hsw hpw,
    Navier.Construction.PeriodicUniqueness.cubeIntegral_transport_energy_zero
      (w := fun x => ew (t, x)) (v := fun x => eu (t, x))
      hsw hsu hpw hpu hdiv]
  unfold Navier.Construction.PeriodicUniqueness.dissipation
  simp only [ew, eu, sub_zero]
  ring

/-- Exact physical enstrophy evolution with the signed stretching term. -/
theorem unitCellEnstrophy_hasDerivAt
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (unitCellEnstrophy u)
      (unitCellVortexStretching u t - ν * unitCellVorticityDissipation u t) t := by
  have hew := Navier.Analysis.EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime
    (vorticity_smoothOnNonnegativeTime hsol)
  have hewSlab : ContDiffOn ℝ ∞ (euclideanVorticity u)
      (Navier.Construction.PeriodicUniqueness.slab 0 (t + 1)) :=
    hew.mono (by intro z hz; exact ⟨hz.1.1, Set.mem_univ _⟩)
  have hz : ContDiffOn ℝ ∞ (0 : Navier.Construction.ProblemStatement.VelocityField)
      (Navier.Construction.PeriodicUniqueness.slab 0 (t + 1)) := contDiffOn_const
  have hd := Navier.Construction.PeriodicUniqueness.energy_hasDerivAt hewSlab hz
    (show t ∈ Ioo (0 : ℝ) (t + 1) by constructor <;> linarith)
  rw [euclidean_vorticity_energyRate hsol ht] at hd
  have hh := hd.const_mul (1 / 2 : ℝ)
  change HasDerivAt (fun s => (1 / 2 : ℝ) *
      Navier.Construction.PeriodicUniqueness.energy (euclideanVorticity u) 0 s)
    (unitCellVortexStretching u t - ν * unitCellVorticityDissipation u t) t
  have halg : (1 / 2 : ℝ) *
      (2 * unitCellVortexStretching u t -
        2 * ν * unitCellVorticityDissipation u t) =
      unitCellVortexStretching u t - ν * unitCellVorticityDissipation u t := by ring
  rw [← halg]
  exact hh

/-- A trajectory-wise gradient bound controls the exact stretching
production. -/
theorem unitCellVortexStretching_le
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t G : ℝ} (ht : 0 ≤ t)
    (hgrad : ∀ y ∈ Navier.Construction.PeriodicIntegration.cube,
      ‖Navier.Construction.ProblemStatement.spatialDerivative
        (Navier.Analysis.EuclideanPDETransport.euclideanVelocity u) t
        (Navier.Construction.PeriodicIntegration.toSpace y)‖ ≤ G) :
    unitCellVortexStretching u t ≤ 2 * G * unitCellEnstrophy u t := by
  let ew : Navier.Construction.ProblemStatement.VelocityField := euclideanVorticity u
  let eu : Navier.Construction.ProblemStatement.VelocityField :=
    Navier.Analysis.EuclideanPDETransport.euclideanVelocity u
  have hewSmooth := Navier.Analysis.EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime
    (vorticity_smoothOnNonnegativeTime hsol)
  have heuSmooth := Navier.Analysis.EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime
    hsol.velocity_smooth
  have hsw := Navier.Analysis.EuclideanPDETransport.eFutureSpatialSlice_contDiff
    hewSmooth ht
  have hsu := Navier.Analysis.EuclideanPDETransport.eFutureSpatialSlice_contDiff
    heuSmooth ht
  have hleft := (hsw.inner ℝ ((hsu.fderiv_right (by simp)).clm_apply hsw)).continuous
  have hright : Continuous (fun x => G * ‖ew (t, x)‖ ^ 2) :=
    continuous_const.mul (hsw.norm_sq ℝ).continuous
  have hint : Navier.Construction.PeriodicIntegration.cubeIntegral (fun x =>
      ⟪ew (t, x), Navier.Construction.ProblemStatement.spatialDerivative eu t x
        (ew (t, x))⟫_ℝ) ≤
      Navier.Construction.PeriodicIntegration.cubeIntegral (fun x =>
        G * ‖ew (t, x)‖ ^ 2) := by
    apply Navier.Construction.PeriodicIntegration.cubeIntegral_mono_on_cube
      hleft hright
    intro y hy
    calc
      ⟪ew (t, Navier.Construction.PeriodicIntegration.toSpace y),
          Navier.Construction.ProblemStatement.spatialDerivative eu t
            (Navier.Construction.PeriodicIntegration.toSpace y)
            (ew (t, Navier.Construction.PeriodicIntegration.toSpace y))⟫_ℝ
          ≤ |⟪ew (t, Navier.Construction.PeriodicIntegration.toSpace y),
            Navier.Construction.ProblemStatement.spatialDerivative eu t
              (Navier.Construction.PeriodicIntegration.toSpace y)
              (ew (t, Navier.Construction.PeriodicIntegration.toSpace y))⟫_ℝ| :=
            le_abs_self _
      _ ≤ ‖ew (t, Navier.Construction.PeriodicIntegration.toSpace y)‖ *
          ‖Navier.Construction.ProblemStatement.spatialDerivative eu t
            (Navier.Construction.PeriodicIntegration.toSpace y)
            (ew (t, Navier.Construction.PeriodicIntegration.toSpace y))‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖ew (t, Navier.Construction.PeriodicIntegration.toSpace y)‖ *
          (G * ‖ew (t, Navier.Construction.PeriodicIntegration.toSpace y)‖) := by
          exact mul_le_mul_of_nonneg_left
            ((Navier.Construction.ProblemStatement.spatialDerivative eu t
              (Navier.Construction.PeriodicIntegration.toSpace y)).le_opNorm _ |>.trans
              (mul_le_mul_of_nonneg_right (hgrad y hy)
                (norm_nonneg _))) (norm_nonneg _)
      _ = G * ‖ew (t, Navier.Construction.PeriodicIntegration.toSpace y)‖ ^ 2 := by ring
  rw [Navier.Construction.PeriodicIntegration.cubeIntegral_const_mul] at hint
  change unitCellVortexStretching u t ≤ 2 * G * unitCellEnstrophy u t
  unfold unitCellVortexStretching unitCellEnstrophy
  change Navier.Construction.PeriodicIntegration.cubeIntegral (fun x =>
      ⟪ew (t, x), Navier.Construction.ProblemStatement.spatialDerivative eu t x
        (ew (t, x))⟫_ℝ) ≤
    2 * G * ((1 / 2 : ℝ) *
      Navier.Construction.PeriodicUniqueness.energy ew 0 t)
  have henergy : Navier.Construction.PeriodicUniqueness.energy ew 0 t =
      Navier.Construction.PeriodicIntegration.cubeIntegral (fun x => ‖ew (t, x)‖ ^ 2) := by
    simp [Navier.Construction.PeriodicUniqueness.energy]
  rw [henergy]
  nlinarith

/-- Scale-consistent differential inequality along the actual trajectory. -/
theorem unitCellEnstrophy_deriv_add_dissipation_le
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t G : ℝ} (ht : 0 < t)
    (hgrad : ∀ y ∈ Navier.Construction.PeriodicIntegration.cube,
      ‖Navier.Construction.ProblemStatement.spatialDerivative
        (Navier.Analysis.EuclideanPDETransport.euclideanVelocity u) t
        (Navier.Construction.PeriodicIntegration.toSpace y)‖ ≤ G) :
    deriv (unitCellEnstrophy u) t + ν * unitCellVorticityDissipation u t ≤
      2 * G * unitCellEnstrophy u t := by
  rw [(unitCellEnstrophy_hasDerivAt hsol ht).deriv]
  have hs := unitCellVortexStretching_le hsol ht.le hgrad
  linarith

/-- Every witness supplied by periodic global regularity carries the exact
unit-cell enstrophy evolution.  This is a conditional enrichment of the
official B witness and does not establish periodic global regularity. -/
theorem ProblemStatements.PeriodicGlobalRegularity.with_unitCellEnstrophyEvolution
    (hreg : ProblemStatements.PeriodicGlobalRegularity)
    (ν : ℝ) (hν : 0 < ν) (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsPeriodicClassicalSolution ν zeroForce u₀ u p ∧
      ∀ t : ℝ, 0 < t →
        HasDerivAt (unitCellEnstrophy u)
          (unitCellVortexStretching u t -
            ν * unitCellVorticityDissipation u t) t := by
  obtain ⟨u, p, hsol⟩ := hreg ν hν u₀ hu₀
  exact ⟨u, p, hsol, fun t ht => unitCellEnstrophy_hasDerivAt hsol ht⟩

end Navier.Analysis.PeriodicEnstrophyControl
