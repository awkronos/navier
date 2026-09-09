import Navier.Analysis.EuclideanPDETransport
import Navier.Analysis.HalfSpaceConsumerBridge
import Navier.Construction.PeriodicUniqueness
import Navier.Construction.ResidualRegularity

/-!
# Physical energy balance for native periodic solutions

This file derives the unit-cell kinetic-energy equality for the repository's
actual `IsPeriodicClassicalSolution` carrier.  No whole-space integrability or
energy bound is assumed: periodicity cancels the transport and pressure fluxes
on the unit cube, while integration by parts turns the viscosity term into the
sum of squared spatial derivatives.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped BigOperators ContDiff Topology InnerProductSpace

namespace Navier.Analysis.PeriodicNativeEnergyBalance

open Navier

/-- Physical kinetic energy in one period cell.  The Euclidean-coordinate
transport makes this `1/2 ∫_[0,1]^3 |u|²`, independently of the native
carrier's product norm. -/
def unitCellKineticEnergy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Navier.Construction.PeriodicUniqueness.energy (EuclideanPDETransport.euclideanVelocity u) 0 t

/-- Viscous dissipation density in one period cell:
`∫_[0,1]^3 ∑ᵢ |∂ᵢu|²`. -/
def unitCellDissipation (u : VelocityEvolution) (t : ℝ) : ℝ :=
  Navier.Construction.PeriodicUniqueness.dissipation (EuclideanPDETransport.euclideanVelocity u) t

theorem unitCellKineticEnergy_nonneg (u : VelocityEvolution) (t : ℝ) :
    0 ≤ unitCellKineticEnergy u t := by
  unfold unitCellKineticEnergy
  exact mul_nonneg (by norm_num)
    (Navier.Construction.PeriodicUniqueness.energy_nonneg
      (EuclideanPDETransport.euclideanVelocity u) 0 t)

theorem unitCellDissipation_nonneg (u : VelocityEvolution) (t : ℝ) :
    0 ≤ unitCellDissipation u t :=
  Navier.Construction.PeriodicUniqueness.dissipation_nonneg (EuclideanPDETransport.euclideanVelocity u) t

/-- Native unit periods become the unit periods used by the Euclidean cube
integration library. -/
theorem euclideanVelocity_unitPeriods
    {u : VelocityEvolution} (hu : SpatiallyPeriodicVelocity u)
    {t : ℝ} (ht : 0 ≤ t) :
    Navier.Construction.PeriodicIntegration.UnitPeriods (fun x => EuclideanPDETransport.euclideanVelocity u (t, x)) := by
  intro x i
  apply EuclideanPDETransport.toNative.injective
  simp only [EuclideanPDETransport.euclideanVelocity, EuclideanPDETransport.toNative_toEuclidean]
  rw [map_add]
  have hb : EuclideanPDETransport.toNative (Navier.Construction.ProblemStatement.coordinateVector i) = basisVector i := by
    exact EuclideanPDETransport.toNative_eBasisVector i
  rw [hb]
  exact hu t ht (EuclideanPDETransport.toNative x) i

theorem euclideanPressure_unitPeriods
    {p : PressureEvolution} (hp : SpatiallyPeriodicPressure p)
    {t : ℝ} (ht : 0 ≤ t) :
    Navier.Construction.PeriodicIntegration.UnitPeriods (fun x => EuclideanPDETransport.euclideanPressure p (t, x)) := by
  intro x i
  change p t (EuclideanPDETransport.toNative (x + Navier.Construction.ProblemStatement.coordinateVector i)) = p t (EuclideanPDETransport.toNative x)
  rw [map_add]
  have hb : EuclideanPDETransport.toNative (Navier.Construction.ProblemStatement.coordinateVector i) = basisVector i := by
    exact EuclideanPDETransport.toNative_eBasisVector i
  rw [hb]
  exact hp t ht (EuclideanPDETransport.toNative x) i

/-- The native incompressibility equation transported to the Euclidean
operators used by periodic integration. -/
theorem euclidean_spatialDivergence_zero
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 ≤ t) (x : EuclideanPDETransport.ESpace) :
    Navier.Construction.ProblemStatement.spatialDivergence (EuclideanPDETransport.euclideanVelocity u) t x = 0 := by
  have heu := EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime h.velocity_smooth
  have hs := EuclideanPDETransport.eFutureSpatialSlice_contDiff heu ht
  have hd := EuclideanPDETransport.divergence_nativeVelocity (EuclideanPDETransport.euclideanVelocity u)
    (x := x) (hs.differentiable (by simp) x)
  rw [EuclideanPDETransport.nativeVelocity_euclideanVelocity] at hd
  change Navier.Construction.ProblemStatement.spatialDivergence (EuclideanPDETransport.euclideanVelocity u) t x = 0
  exact hd.symm.trans (h.incompressible t ht (EuclideanPDETransport.toNative x))

/-- The actual viscosity-`ν` native momentum equation transported to the
Euclidean periodic operators. -/
theorem euclidean_momentum_equation
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 < t) (x : EuclideanPDETransport.ESpace) :
    Navier.Construction.ProblemStatement.temporalDerivative (EuclideanPDETransport.euclideanVelocity u) t x +
        Navier.Construction.ProblemStatement.advection (EuclideanPDETransport.euclideanVelocity u) t x =
      ν • Navier.Construction.ProblemStatement.spatialLaplacian (EuclideanPDETransport.euclideanVelocity u) t x -
        Navier.Construction.ProblemStatement.pressureGradient (EuclideanPDETransport.euclideanPressure p) t x := by
  let eu := EuclideanPDETransport.euclideanVelocity u
  let ep := EuclideanPDETransport.euclideanPressure p
  have heu := EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime h.velocity_smooth
  have hep := EuclideanPDETransport.euclideanPressure_smoothOnNonnegativeTime h.pressure_smooth
  have hs := EuclideanPDETransport.eFutureSpatialSlice_contDiff heu ht.le
  have hps := EuclideanPDETransport.eFuturePressureSlice_contDiff hep ht.le
  have htime := EuclideanPDETransport.eFutureTimeSlice_differentiableAt heu ht x
  have ht' := EuclideanPDETransport.timeDerivative_nativeVelocity_of_pos eu ht x htime
  have hc := EuclideanPDETransport.convection_nativeVelocity eu
    (x := x) (hs.differentiable (by simp) x)
  have hl := EuclideanPDETransport.laplacian_nativeVelocity eu (x := x) hs
  have hp' := EuclideanPDETransport.pressureGradient_nativePressure ep
    (x := x) (hps.differentiable (by simp) x)
  change EuclideanPDETransport.eTimeDerivative eu t x +
      EuclideanPDETransport.eConvection eu t x =
    ν • EuclideanPDETransport.eLaplacian eu t x -
      EuclideanPDETransport.ePressureGradient ep t x
  apply EuclideanPDETransport.toNative.injective
  simp only [map_add, map_sub, map_smul]
  rw [← ht', ← hc, ← hl, ← hp']
  simpa [eu, ep, zeroForce] using h.equation t ht.le (EuclideanPDETransport.toNative x)

/-- The viscosity-general instantaneous squared-energy rate.  This is derived
from the native PDE and the three periodic integration identities; it is not
an energy identity supplied as a premise. -/
theorem euclidean_energyRate_eq_neg_two_mul_dissipation
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 < t) :
    Navier.Construction.PeriodicUniqueness.energyRate (EuclideanPDETransport.euclideanVelocity u) 0 t =
      -2 * ν * Navier.Construction.PeriodicUniqueness.dissipation (EuclideanPDETransport.euclideanVelocity u) t := by
  let eu : Navier.Construction.ProblemStatement.VelocityField := EuclideanPDETransport.euclideanVelocity u
  let ep : Navier.Construction.ProblemStatement.PressureField := EuclideanPDETransport.euclideanPressure p
  have heu := EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime h.velocity_smooth
  have hep := EuclideanPDETransport.euclideanPressure_smoothOnNonnegativeTime h.pressure_smooth
  have hs : ContDiff ℝ ∞ (fun x => eu (t, x)) :=
    EuclideanPDETransport.eFutureSpatialSlice_contDiff heu ht.le
  have hps : ContDiff ℝ ∞ (fun x => ep (t, x)) :=
    EuclideanPDETransport.eFuturePressureSlice_contDiff hep ht.le
  have hperu : Navier.Construction.PeriodicIntegration.UnitPeriods (fun x => eu (t, x)) :=
    euclideanVelocity_unitPeriods h.velocity_periodic ht.le
  have hperp : Navier.Construction.PeriodicIntegration.UnitPeriods (fun x => ep (t, x)) :=
    euclideanPressure_unitPeriods h.pressure_periodic ht.le
  have hdiv : ∀ x, Navier.Construction.ProblemStatement.spatialDivergence eu t x = 0 :=
    fun x => euclidean_spatialDivergence_zero h ht.le x
  have hL := (hs.inner ℝ (Navier.Construction.PeriodicUniqueness.spatialLaplacian_contDiff hs)).continuous
  have hN := (hs.inner ℝ ((hs.fderiv_right (by simp)).clm_apply hs)).continuous
  have hP := (hs.inner ℝ (Navier.Construction.PeriodicUniqueness.pressureGradient_contDiff hps)).continuous
  have hLN : Continuous (fun x =>
      ν * ⟪eu (t, x), Navier.Construction.ProblemStatement.spatialLaplacian eu t x⟫_ℝ -
        ⟪eu (t, x), Navier.Construction.ProblemStatement.spatialDerivative eu t x (eu (t, x))⟫_ℝ) :=
    (continuous_const.mul hL).sub hN
  have hEq :
      (fun x => ⟪eu (t, x), Navier.Construction.ProblemStatement.temporalDerivative eu t x⟫_ℝ) =
        (fun x => ν * ⟪eu (t, x), Navier.Construction.ProblemStatement.spatialLaplacian eu t x⟫_ℝ -
          ⟪eu (t, x), Navier.Construction.ProblemStatement.spatialDerivative eu t x (eu (t, x))⟫_ℝ -
          ⟪eu (t, x), Navier.Construction.ProblemStatement.pressureGradient ep t x⟫_ℝ) := by
    funext x
    have heq := euclidean_momentum_equation h ht x
    change Navier.Construction.ProblemStatement.temporalDerivative eu t x + Navier.Construction.ProblemStatement.advection eu t x =
      ν • Navier.Construction.ProblemStatement.spatialLaplacian eu t x - Navier.Construction.ProblemStatement.pressureGradient ep t x at heq
    have heq' := congrArg
      (fun z => z - Navier.Construction.ProblemStatement.advection eu t x) heq
    simp only [add_sub_cancel_right] at heq'
    rw [heq']
    simp only [inner_sub_right, real_inner_smul_right,
      Navier.Construction.ProblemStatement.advection]
    ring
  have hrate : Navier.Construction.PeriodicUniqueness.energyRate eu 0 t =
      2 * Navier.Construction.PeriodicIntegration.cubeIntegral (fun x =>
        ⟪eu (t, x), Navier.Construction.ProblemStatement.temporalDerivative eu t x⟫_ℝ) := by
    simp [Navier.Construction.PeriodicUniqueness.energyRate,
      Navier.Construction.ProblemStatement.temporalDerivative,
      Navier.Construction.PeriodicIntegration.cubeIntegral_const_mul]
  change Navier.Construction.PeriodicUniqueness.energyRate eu 0 t =
    -2 * ν * Navier.Construction.PeriodicUniqueness.dissipation eu t
  rw [hrate, hEq]
  rw [Navier.Construction.PeriodicIntegration.cubeIntegral_sub hLN hP]
  simp only [Navier.Construction.ProblemStatement.spatialDerivative]
  rw [Navier.Construction.PeriodicIntegration.cubeIntegral_sub
      (f := fun x => ν * ⟪eu (t, x),
        Navier.Construction.ProblemStatement.spatialLaplacian eu t x⟫_ℝ)
      (g := fun x => ⟪eu (t, x),
        (fderiv ℝ (fun y => eu (t, y)) x) (eu (t, x))⟫_ℝ)
      (continuous_const.mul hL) hN,
    Navier.Construction.PeriodicIntegration.cubeIntegral_const_mul ν,
    Navier.Construction.PeriodicUniqueness.cubeIntegral_laplacian_energy hs hperu,
    Navier.Construction.PeriodicUniqueness.cubeIntegral_transport_energy_zero hs hs hperu hperu hdiv,
    Navier.Construction.PeriodicUniqueness.cubeIntegral_pressure_energy_zero hs hps hperu hperp hdiv]
  simp only [sub_zero]
  unfold Navier.Construction.PeriodicUniqueness.dissipation
  ring

/-- Exact instantaneous physical energy law at every positive time. -/
theorem unitCellKineticEnergy_hasDerivAt
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (unitCellKineticEnergy u) (-ν * unitCellDissipation u t) t := by
  have heu := EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime h.velocity_smooth
  have heuSlab : ContDiffOn ℝ ∞ (EuclideanPDETransport.euclideanVelocity u) (Navier.Construction.PeriodicUniqueness.slab 0 (t + 1)) :=
    heu.mono (by
      intro z hz
      exact ⟨hz.1.1, Set.mem_univ _⟩)
  have hz : ContDiffOn ℝ ∞ (0 : Navier.Construction.ProblemStatement.VelocityField) (Navier.Construction.PeriodicUniqueness.slab 0 (t + 1)) :=
    contDiffOn_const
  have hd := Navier.Construction.PeriodicUniqueness.energy_hasDerivAt heuSlab hz
    (show t ∈ Ioo (0 : ℝ) (t + 1) by constructor <;> linarith)
  rw [euclidean_energyRate_eq_neg_two_mul_dissipation h ht] at hd
  have hh := hd.const_mul (1 / 2 : ℝ)
  change HasDerivAt
    (fun s => (1 / 2 : ℝ) * Navier.Construction.PeriodicUniqueness.energy
      (EuclideanPDETransport.euclideanVelocity u) 0 s)
    (-ν * Navier.Construction.PeriodicUniqueness.dissipation
      (EuclideanPDETransport.euclideanVelocity u) t) t
  have halg : (1 / 2 : ℝ) *
      (-2 * ν * Navier.Construction.PeriodicUniqueness.dissipation
        (EuclideanPDETransport.euclideanVelocity u) t) =
      -ν * Navier.Construction.PeriodicUniqueness.dissipation
        (EuclideanPDETransport.euclideanVelocity u) t := by ring
  rw [← halg]
  exact hh

/-- The physical dissipation density is continuous on every finite forward
time slab.  The proof consumes the repository's proved Seeley extension
theorem, differentiates that genuine smooth extension, and then uses its exact
agreement with the native solution on nonnegative time. -/
theorem unitCellDissipation_continuousOn
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν zeroForce u₀ u p) (T : ℝ) :
    ContinuousOn (unitCellDissipation u) (Icc 0 T) := by
  obtain ⟨w⟩ := (HalfSpaceConsumerBridge.smoothVelocity_iff_globalExtension u).mp h.velocity_smooth
  let U : Navier.Construction.ProblemStatement.VelocityField := fun z : ℝ × EuclideanPDETransport.ESpace =>
    EuclideanPDETransport.toEuclidean (w.extension (z.1, EuclideanPDETransport.toNative z.2))
  have hU : ContDiff ℝ ∞ U := by
    exact EuclideanPDETransport.toEuclidean.contDiff.comp
      (w.smooth.comp (contDiff_fst.prodMk (EuclideanPDETransport.toNative.contDiff.comp contDiff_snd)))
  have hUagree : ∀ t : ℝ, 0 ≤ t → ∀ x, U (t, x) = EuclideanPDETransport.euclideanVelocity u (t, x) := by
    intro t ht x
    simp only [U, EuclideanPDETransport.euclideanVelocity]
    rw [w.agrees t ht (EuclideanPDETransport.toNative x)]
  have hDU : ContDiff ℝ ∞ (fun z : ℝ × EuclideanPDETransport.ESpace =>
      Navier.Construction.ProblemStatement.spatialDerivative U z.1 z.2) := by
    rw [← contDiffOn_univ]
    exact Navier.Construction.ResidualRegularity.contDiffOn_spatialDerivative isOpen_univ hU.contDiffOn
  have hcU : ContinuousOn (Navier.Construction.PeriodicUniqueness.dissipation U) (Icc 0 T) := by
    unfold Navier.Construction.PeriodicUniqueness.dissipation
    apply continuousOn_finsetSum
    intro i hi
    have hFi : ContDiff ℝ ∞ (fun z : ℝ × EuclideanPDETransport.ESpace =>
        ‖(Navier.Construction.ProblemStatement.spatialDerivative U z.1 z.2)
          (Navier.Construction.ProblemStatement.coordinateVector i)‖ ^ 2) :=
      (hDU.clm_apply contDiff_const).norm_sq ℝ
    have hci := Navier.Construction.PeriodicIntegration.cubeIntegral_continuousOn_Icc
      (a := 0) (b := T) hFi.continuous.continuousOn
    simpa [Navier.Construction.PeriodicIntegration.spatialPartial,
      Navier.Construction.ProblemStatement.spatialDerivative] using hci
  refine hcU.congr ?_
  intro t ht
  unfold unitCellDissipation Navier.Construction.PeriodicUniqueness.dissipation
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext x
  have hslices : (fun y => U (t, y)) =
      (fun y => EuclideanPDETransport.euclideanVelocity u (t, y)) := by
    funext y
    exact hUagree t ht.1 y
  rw [← hslices]

/-- Exact finite-time physical energy-dissipation identity on the unit cell. -/
theorem unitCell_energy_dissipation_identity
    {ν : ℝ} {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {T : ℝ} (hT : 0 ≤ T) :
    unitCellKineticEnergy u T +
        ν * (∫ t in (0 : ℝ)..T, unitCellDissipation u t) =
      unitCellKineticEnergy u 0 := by
  have hcontE : ContinuousOn (unitCellKineticEnergy u) (Icc 0 T) := by
    have heu := EuclideanPDETransport.euclideanVelocity_smoothOnNonnegativeTime h.velocity_smooth
    have heuSlab : ContDiffOn ℝ ∞ (EuclideanPDETransport.euclideanVelocity u) (Navier.Construction.PeriodicUniqueness.slab 0 T) :=
      heu.mono (by
        intro z hz
        exact ⟨hz.1.1, Set.mem_univ _⟩)
    have hz : ContDiffOn ℝ ∞ (0 : Navier.Construction.ProblemStatement.VelocityField) (Navier.Construction.PeriodicUniqueness.slab 0 T) := contDiffOn_const
    exact (Navier.Construction.PeriodicUniqueness.energy_continuousOn heuSlab hz).const_mul (1 / 2 : ℝ)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivWithinAt (unitCellKineticEnergy u) (-ν * unitCellDissipation u t)
        (Ioi t) t := by
    intro t ht
    exact (unitCellKineticEnergy_hasDerivAt h ht.1).hasDerivWithinAt
  have hint : IntervalIntegrable (fun t => -ν * unitCellDissipation u t) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact continuousOn_const.mul (unitCellDissipation_continuousOn h T)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hT hcontE hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  linarith

/-- Positive viscosity bounds total unit-cell dissipation by the initial
physical kinetic energy divided by viscosity. -/
theorem unitCell_dissipation_integral_le
    {ν : ℝ} (hν : 0 < ν)
    {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, unitCellDissipation u t) ≤
      unitCellKineticEnergy u 0 / ν := by
  have hid := unitCell_energy_dissipation_identity h hT
  rw [le_div_iff₀ hν]
  nlinarith [unitCellKineticEnergy_nonneg u T]

/-- The unit-cell kinetic energy cannot exceed its initial value. -/
theorem unitCellKineticEnergy_le_initial
    {ν : ℝ} (hν : 0 ≤ ν)
    {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    {T : ℝ} (hT : 0 ≤ T) :
    unitCellKineticEnergy u T ≤ unitCellKineticEnergy u 0 := by
  have hid := unitCell_energy_dissipation_identity h hT
  have hD : 0 ≤ ∫ t in (0 : ℝ)..T, unitCellDissipation u t :=
    intervalIntegral.integral_nonneg hT
      (fun t _ => unitCellDissipation_nonneg u t)
  nlinarith

/-- A periodic global-regularity witness automatically carries the exact
physical unit-cell equality and its viscosity-uniform-in-time dissipation
budget.  This strengthens the witness package conditionally; it does not prove
`PeriodicGlobalRegularity`. -/
theorem PeriodicGlobalRegularity.with_unitCell_energy_dissipation
    (hreg : ProblemStatements.PeriodicGlobalRegularity)
    (ν : ℝ) (hν : 0 < ν) (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsPeriodicClassicalSolution ν zeroForce u₀ u p ∧
      ∀ T : ℝ, 0 ≤ T →
        unitCellKineticEnergy u T +
            ν * (∫ t in (0 : ℝ)..T, unitCellDissipation u t) =
          unitCellKineticEnergy u 0 ∧
        (∫ t in (0 : ℝ)..T, unitCellDissipation u t) ≤
          unitCellKineticEnergy u 0 / ν := by
  obtain ⟨u, p, h⟩ := hreg ν hν u₀ hu₀
  exact ⟨u, p, h, fun T hT =>
    ⟨unitCell_energy_dissipation_identity h hT,
      unitCell_dissipation_integral_le hν h hT⟩⟩

end Navier.Analysis.PeriodicNativeEnergyBalance
