/-
Lane L6b4 (2026-09-14): exact axis vorticity of the Borel base field.

The actual spatial curl of `SlowBorelBase.baseVelocity` evaluated on the
symmetry axis is computed exactly. The swirl profile's `partialS` is the
repo's own `partialS_swirlPotential` identity, the chart lands on
`(1 - t, (0, 0))` exactly (`BaseResidual.physicalChart_origin`), and the
slow sum cuts to its leading term when the positive-order axis constants of
`phi` vanish. The two transverse vorticity components vanish at the axis
unconditionally; the axial component is
`2 * C⁻¹ * phi 0 (0,0) * (1 - t) ^ (-A h - 1/2)`.

Consequences: the base vorticity norm on the axis, its blow-up along
`𝓝[<] 1`, and the `FinalSlowBase` instance on the actual modulated
coefficients, where `C⁻¹ * phi 0 (0, 0)` cancels to the nominal profile
value `v.profiles.f (0, 0)`, whose strict positivity is proved through
`fields_outside` -> `extendedf` -> `f_before_Xi` -> `seedF_positive` at
`X = 0`.
-/
import Navier.Construction.FinalSlowBase
import Navier.Construction.BaseResidual

noncomputable section

open Set Filter
open scoped BigOperators ContDiff Topology EuclideanSpace

namespace Navier.Construction.BaseVorticityAxis

open SlowBorelBase AxisymmetricFields SpatialCurl ProblemStatement

/-- The exact axis vorticity of the Borel base field: the actual Euclidean
curl of `baseVelocity` at `(t, 0)` is axial, and its value is the leading
swirl coefficient transported through the exact axis chart. No germ or
limit argument is used; every identity is a pointwise evaluation. -/
theorem baseVorticity_axis {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ} (hh : 0 < h)
    (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ)
    (hz : ∀ j, 0 < j → d.phi j (0, 0) = 0) {t : ℝ} (ht : t < 1) :
    SpatialCurl.spatialCurl (baseVelocity a h C d) (t, 0) =
      (2 * C⁻¹ * d.phi 0 (0, 0) * (1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2)) •
        coordinateVector 2 := by
  set U : Set Chart := Iio (1 : ℝ) ×ˢ (univ : Set Inner)
  have hU : IsOpen U := isOpen_Iio.prod isOpen_univ
  let sf := streamFactor a h C d
  let sw := swirlPotential a h C d
  let pp : Space → ProfilePoint := profilePoint t
  have pp0 : pp 0 = (t, (0, 0)) := by
    show (t, (radialEnergy (0 : Space), (0 : Space) 2)) = _
    simp [radialEnergy]
  have hpp_mem (y : Space) : pp y ∈ U := ⟨ht, mem_univ _⟩
  have hc_sf : ContDiffOn ℝ ∞ sf U :=
    physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 0)
      (-CoordinateAlgebra.A h)
  have hc_sw : ContDiffOn ℝ ∞ sw U :=
    physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 1)
      (1 / 2 - CoordinateAlgebra.A h)
  have hd_sf (y : Space) : DifferentiableAt ℝ sf (pp y) :=
    (hc_sf.contDiffAt (hU.mem_nhds (hpp_mem y))).differentiableAt (by simp)
  have hd_sw (y : Space) : DifferentiableAt ℝ sw (pp y) :=
    (hc_sw.contDiffAt (hU.mem_nhds (hpp_mem y))).differentiableAt (by simp)
  -- slices of the first partials of the two profiles
  let psi : Space → ℝ := fun y => partialZ sf (pp y)
  let phis : Space → ℝ := fun y => partialS sw (pp y)
  let sH : Space → ℝ := fun y => partialS sf (pp y)
  have hcD_sf : ContDiffOn ℝ ∞ (fun p : Chart => fderiv ℝ sf p) U :=
    hc_sf.fderiv_of_isOpen hU (by simp)
  have hcD_sw : ContDiffOn ℝ ∞ (fun p : Chart => fderiv ℝ sw p) U :=
    hc_sw.fderiv_of_isOpen hU (by simp)
  have hpsi_diff : DifferentiableAt ℝ (partialZ sf) (pp 0) := by
    change DifferentiableAt ℝ (fun p : Chart => fderiv ℝ sf p (0, (0, 1))) (pp 0)
    have hc1 : ContDiffAt ℝ ∞ (fun p : Chart => fderiv ℝ sf p) (pp 0) :=
      hcD_sf.contDiffAt (hU.mem_nhds (hpp_mem 0))
    have hc2 : ContDiffAt ℝ ∞ (fun p : Chart => fderiv ℝ sf p (0, (0, 1))) (pp 0) :=
      hc1.clm_apply contDiffAt_const
    exact hc2.differentiableAt (by simp)
  have hphis_diff : DifferentiableAt ℝ (partialS sw) (pp 0) := by
    change DifferentiableAt ℝ (fun p : Chart => fderiv ℝ sw p (0, (1, 0))) (pp 0)
    have hc1 : ContDiffAt ℝ ∞ (fun p : Chart => fderiv ℝ sw p) (pp 0) :=
      hcD_sw.contDiffAt (hU.mem_nhds (hpp_mem 0))
    have hc2 : ContDiffAt ℝ ∞ (fun p : Chart => fderiv ℝ sw p (0, (1, 0))) (pp 0) :=
      hc1.clm_apply contDiffAt_const
    exact hc2.differentiableAt (by simp)
  have hs_diff : DifferentiableAt ℝ (partialS sf) (pp 0) := by
    change DifferentiableAt ℝ (fun p : Chart => fderiv ℝ sf p (0, (1, 0))) (pp 0)
    have hc1 : ContDiffAt ℝ ∞ (fun p : Chart => fderiv ℝ sf p) (pp 0) :=
      hcD_sf.contDiffAt (hU.mem_nhds (hpp_mem 0))
    have hc2 : ContDiffAt ℝ ∞ (fun p : Chart => fderiv ℝ sf p (0, (1, 0))) (pp 0) :=
      hc1.clm_apply contDiffAt_const
    exact hc2.differentiableAt (by simp)
  have hpsi : HasFDerivAt psi (profileDerivative (partialZ sf) t 0) 0 :=
    hasFDerivAt_profile_composition (partialZ sf) t 0 hpsi_diff
  have hphis : HasFDerivAt phis (profileDerivative (partialS sw) t 0) 0 :=
    hasFDerivAt_profile_composition (partialS sw) t 0 hphis_diff
  have hs : HasFDerivAt sH (profileDerivative (partialS sf) t 0) 0 :=
    hasFDerivAt_profile_composition (partialS sf) t 0 hs_diff
  have hsf : HasFDerivAt (fun y => sf (pp y)) (profileDerivative sf t 0) 0 :=
    hasFDerivAt_profile_composition sf t 0 (hd_sf 0)
  -- the three component derivatives at the axis
  have h1 : HasFDerivAt (fun y : Space => -(y 0) * psi y / 2 + y 1 * phis y)
      (-(psi 0 / 2) • projection 0 + phis 0 • projection 1) 0 := by
    have e1 : HasFDerivAt (fun y : Space => -(y 0) * psi y / 2)
        (-(psi 0 / 2) • projection 0) 0 := by
      have e0 : HasFDerivAt (fun y : Space => y 0 * psi y) (psi 0 • projection 0) 0 :=
        ((projection 0).hasFDerivAt.mul hpsi).congr_fderiv (by ext v; simp)
      convert! e0.const_mul (-1 / 2 : ℝ) using 1
      · funext y
        simp only [div_eq_mul_inv, neg_mul]
        ring
      · ext v
        simp only [smul_apply, smul_smul]
        ring
    have e2 : HasFDerivAt (fun y : Space => y 1 * phis y) (phis 0 • projection 1) 0 :=
      ((projection 1).hasFDerivAt.mul hphis).congr_fderiv (by ext v; simp)
    exact e1.add e2
  have h2 : HasFDerivAt (fun y : Space => -(y 1) * psi y / 2 - y 0 * phis y)
      (-(psi 0 / 2) • projection 1 - phis 0 • projection 0) 0 := by
    have e1 : HasFDerivAt (fun y : Space => -(y 1) * psi y / 2)
        (-(psi 0 / 2) • projection 1) 0 := by
      have e0 : HasFDerivAt (fun y : Space => y 1 * psi y) (psi 0 • projection 1) 0 :=
        ((projection 1).hasFDerivAt.mul hpsi).congr_fderiv (by ext v; simp)
      convert! e0.const_mul (-1 / 2 : ℝ) using 1
      · funext y
        simp only [div_eq_mul_inv, neg_mul]
        ring
      · ext v
        simp only [smul_apply, smul_smul]
        ring
    have e : HasFDerivAt (fun y : Space => y 0 * phis y) (phis 0 • projection 0) 0 :=
      ((projection 0).hasFDerivAt.mul hphis).congr_fderiv (by ext v; simp)
    have e2 : HasFDerivAt (fun y : Space => -(y 0 * phis y))
        (-(phis 0 • projection 0)) 0 := e.neg
    exact e1.add e2
  have h3 : HasFDerivAt (fun y : Space => sf (pp y) + radialEnergy y * sH y)
      (profileDerivative sf t 0) 0 := by
    have e1 : HasFDerivAt (fun y : Space => radialEnergy y * sH y) 0 0 :=
      ((hasFDerivAt_radialEnergy (0 : Space)).mul hs).congr_fderiv
        (by ext v; simp [radialEnergy, radialLinear])
    have e2 : HasFDerivAt (fun y : Space => sf (pp y) + radialEnergy y * sH y)
        (profileDerivative sf t 0 + 0) 0 := hsf.add e1
    exact e2.congr_fderiv (add_zero _)
  -- pointwise component formulas on the time slice
  have hA_eq : ∀ y : Space,
      baseVelocity a h C d (t, y) 0 = -(y 0) * psi y / 2 + y 1 * phis y := fun y =>
    velocity_zero sf sw t y (hd_sf y) (hd_sw y)
  have hB_eq : ∀ y : Space,
      baseVelocity a h C d (t, y) 1 = -(y 1) * psi y / 2 - y 0 * phis y := fun y =>
    velocity_one sf sw t y (hd_sf y) (hd_sw y)
  have hC_eq : ∀ y : Space,
      baseVelocity a h C d (t, y) 2 = sf (pp y) + radialEnergy y * sH y := fun y =>
    velocity_two sf sw t y (hd_sf y) (hd_sw y)
  let M0 : Space →L[ℝ] ℝ := -((psi 0 : ℝ) / 2) • projection 0 + phis 0 • projection 1
  let M1 : Space →L[ℝ] ℝ := -((psi 0 : ℝ) / 2) • projection 1 - phis 0 • projection 0
  let M2 : Space →L[ℝ] ℝ := profileDerivative sf t 0
  let Lfull : Space →L[ℝ] Space :=
    M0.smulRight (coordinateVector 0) +
      (M1.smulRight (coordinateVector 1) + M2.smulRight (coordinateVector 2))
  have hchain : HasFDerivAt (fun y : Space =>
      (-(y 0) * psi y / 2 + y 1 * phis y) • coordinateVector 0 +
        ((-(y 1) * psi y / 2 - y 0 * phis y) • coordinateVector 1 +
          (sf (pp y) + radialEnergy y * sH y) • coordinateVector 2)) Lfull 0 :=
    (h1.smul_const (coordinateVector 0)).add
      ((h2.smul_const (coordinateVector 1)).add (h3.smul_const (coordinateVector 2)))
  have hexp : (fun y : Space => baseVelocity a h C d (t, y)) =ᶠ[𝓝 0] fun y =>
      (-(y 0) * psi y / 2 + y 1 * phis y) • coordinateVector 0 +
        ((-(y 1) * psi y / 2 - y 0 * phis y) • coordinateVector 1 +
          (sf (pp y) + radialEnergy y * sH y) • coordinateVector 2) := by
    apply eventually_of_mem univ_mem
    intro y _
    ext i
    fin_cases i <;> simp [hA_eq, hB_eq, hC_eq, coordinateVector, EuclideanSpace.single]
  have hfull : HasFDerivAt (fun y : Space => baseVelocity a h C d (t, y)) Lfull 0 :=
    hchain.congr_of_eventuallyEq hexp
  have hLapp (j : Fin 3) : Lfull (coordinateVector j) =
      M0 (coordinateVector j) • coordinateVector 0 +
        (M1 (coordinateVector j) • coordinateVector 1 +
          M2 (coordinateVector j) • coordinateVector 2) := by
    simp [Lfull, ContinuousLinearMap.smulRight_apply]
  have hphis_axis : phis 0 =
      -C⁻¹ * ((1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2) * d.phi 0 (0, 0)) := by
    have hp := partialS_swirlPotential ha hh hh1 hd C
      (p := (t, (0, 0))) ht
    have hpf : physicalProfile a h (-CoordinateAlgebra.A h - 1 / 2) d.phi (t, (0, 0)) =
        (1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2) * d.phi 0 (0, 0) := by
      show ((physicalChart h (t, (0, 0))).1 ^ (-CoordinateAlgebra.A h - 1 / 2)) •
          slowSum a h d.phi (physicalChart h (t, (0, 0))) = _
      rw [BaseResidual.physicalChart_origin hh hh1 ht]
      rw [BaseResidual.slowSum_eq_leading_of_positive_zero a h (1 - t) hz]
      simp [smul_eq_mul]
    have hs0 : phis 0 = partialS sw (t, (0, 0)) := by
      show partialS sw (pp 0) = _
      rw [pp0]
    rw [hs0, hp, hpf]
  change curl (fun y : Space => baseVelocity a h C d (t, y)) 0 = _
  show curlLinear (fderiv ℝ (fun y : Space => baseVelocity a h C d (t, y)) 0) = _
  rw [hfull.fderiv]
  ext i
  fin_cases i
  · change (curlLinear Lfull) 0 =
      ((2 * C⁻¹ * d.phi 0 (0, 0) * (1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2)) •
        coordinateVector 2) 0
    rw [curlLinear_apply_zero, hLapp, hLapp]
    unfold M0 M1 M2
    simp [coordinateVector, EuclideanSpace.single, profileDerivative_apply, projection_apply,
      psi]
  · change (curlLinear Lfull) 1 =
      ((2 * C⁻¹ * d.phi 0 (0, 0) * (1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2)) •
        coordinateVector 2) 1
    rw [curlLinear_apply_one, hLapp, hLapp]
    unfold M0 M1 M2
    simp [coordinateVector, EuclideanSpace.single, profileDerivative_apply, projection_apply,
      psi]
  · change (curlLinear Lfull) 2 =
      ((2 * C⁻¹ * d.phi 0 (0, 0) * (1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2)) •
        coordinateVector 2) 2
    rw [curlLinear_apply_two, hLapp, hLapp]
    unfold M0 M1 M2
    simp only [hphis_axis]
    simp [coordinateVector, EuclideanSpace.single, profileDerivative_apply, projection_apply,
      psi]
    ring

/-- The axis vorticity norm of the Borel base field: the exact value of
`‖curl u‖` on the axis when the leading swirl constant is positive. -/
theorem baseVorticity_norm_at_origin {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ} (hh : 0 < h)
    (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ)
    (hz : ∀ j, 0 < j → d.phi j (0, 0) = 0)
    (h0 : 0 < 2 * C⁻¹ * d.phi 0 (0, 0)) {t : ℝ} (ht : t < 1) :
    ‖SpatialCurl.spatialCurl (baseVelocity a h C d) (t, 0)‖ =
      2 * C⁻¹ * d.phi 0 (0, 0) * (1 - t) ^ (-CoordinateAlgebra.A h - 1 / 2) := by
  rw [baseVorticity_axis ha hh hh1 hd C hz ht, norm_smul]
  simp only [ProblemStatement.coordinateVector, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs]
  exact abs_of_pos (mul_pos h0 (Real.rpow_pos_of_pos (sub_pos.mpr ht) _))

/-- The Borel base vorticity blows up on the axis as `t → 1⁻`, at the rate
`(1 - t) ^ (-A h - 1/2)`, whenever the leading swirl constant is positive. -/
theorem baseVorticity_axis_tendsto_atTop {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ} (hh : 0 < h)
    (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ)
    (hz : ∀ j, 0 < j → d.phi j (0, 0) = 0) (h0 : 0 < 2 * C⁻¹ * d.phi 0 (0, 0)) :
    Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl (baseVelocity a h C d) (t, 0)‖)
      (𝓝[<] 1) atTop := by
  have hA : 0 < CoordinateAlgebra.A h + 1 / 2 := by dsimp [CoordinateAlgebra.A]; linarith
  have ht := (BlowupImplication.negative_power_tendsto_atTop hA
    (BlowupImplication.remaining_time_tendsto 1)).atTop_mul_pos h0 tendsto_const_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [baseVorticity_norm_at_origin ha hh hh1 hd C hz h0 ht, neg_add]
  exact mul_comm _ _

end Navier.Construction.BaseVorticityAxis

/-! ## The instance for the actual modulated slow base -/

namespace Navier.Construction.FinalSlowBase

open SlowBorelBase SpatialCurl ProblemStatement

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

/-- The leading swirl coefficient on the axis is the actual profile value:
`C⁻¹ * phi 0 (0, 0) = v.profiles.f (0, 0)`, with the normalization canceling
exactly. -/
theorem inv_phi_axis :
    W.axis.normalization⁻¹ * (coefficients H v).phi 0 (0, 0) = v.profiles.f (0, 0) := by
  have hphi : (coefficients H v).phi 0 (0, 0) = W.axis.normalization * v.profiles.f (0, 0) := by
    show (EntranceAlignedBase.modulatedCoefficients H v).phi 0 (0, 0) =
        W.axis.normalization * v.profiles.f (0, 0)
    exact (EntranceAlignedBase.modulated_zero_fields H v (p := (0, 0)) le_rfl
      (by norm_num : |(0 : ℝ)| ≤ 1)).1
  rw [hphi, ← mul_assoc, inv_mul_cancel₀ W.axis.normalization_pos.ne', one_mul]

/-- The nominal profile value at the axis origin is strictly positive. This is
the `X = 0` case of the seed positivity, taken through `fields_outside`
(the point lies below `ld.modulation.left`), `extendedf`, `f_before_Xi`, and
`Controls.seedF_positive`, which holds for `0 ≤ X`. -/
theorem f_axis_positive : 0 < v.profiles.f (0, 0) := by
  have h4 : (0 : ℝ) < 4 / W.axis.scale := div_pos (by norm_num) W.axis.scale_pos
  have hleft : 0 < ld.modulation.left := h4.trans ld.after_initial
  have hfo := v.fields_outside (p := (0, 0))
    (fun h => lt_irrefl 0 (hleft.trans h.1))
  have hW : W.profiles.f (0, 0) = W.controls.f (0, 0) := by
    show W.controls.extendedf W.heat.coefficients (0, 0) = W.controls.f (0, 0)
    rw [NominalProfile.Controls.extendedf]
    exact ite_eq_left (le_of_lt NominalProfile.Xi_pos)
  have hcf : W.controls.f (0, 0) = W.controls.seedF (0, 0) :=
    W.controls.f_before_Xi (by linarith [NominalProfile.Xi_pos] : (0 : ℝ) ≤ NominalProfile.Xi)
  have hseed : 0 < W.controls.seedF (0, 0) :=
    W.controls.seedF_positive (p := (0, 0))
      (NominalProfile.physical_band_in_parameterInterval
        (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1))
      le_rfl
  rw [hfo.1, hW, hcf]
  exact hseed

/-- The actual vorticity of the modulated slow base at the axis origin:
exactly axial, with the sharp rate `(1 - t) ^ (-A h - 1/2)` and the exact
lower constant `2 * v.profiles.f (0, 0)`. -/
theorem axis_vorticity_origin (upper : ℝ) (B : ℕ) {t : ℝ} (ht : t < 1) :
    SpatialCurl.spatialCurl (velocity H v upper B) (t, 0) =
      (2 * v.profiles.f (0, 0) * (1 - t) ^ (-CoordinateAlgebra.A F.data.h - 1 / 2)) •
        coordinateVector 2 := by
  have hgen := BaseVorticityAxis.baseVorticity_axis (scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (coefficients_smooth H v) W.axis.normalization
    (fun j hj => (EntranceAlignedBase.modulated_positive_axis H v hj
      (by norm_num : |(0 : ℝ)| ≤ 1)).1) ht
  have hstep : (2 : ℝ) * W.axis.normalization⁻¹ * (coefficients H v).phi 0 (0, 0) =
      2 * v.profiles.f (0, 0) := by
    rw [mul_assoc, inv_phi_axis]
  show SpatialCurl.spatialCurl (baseVelocity (scales H v upper B) F.data.h
      W.axis.normalization (coefficients H v)) (t, 0) = _
  rw [hgen, hstep]

/-- The modulated slow base vorticity blows up on the axis as `t → 1⁻` at
the sharp rate `(1 - t) ^ (-A h - 1/2)`, with the exact constant. -/
theorem axis_vorticity_tendsto (upper : ℝ) (B : ℕ) :
    Tendsto (fun t : ℝ =>
      ‖SpatialCurl.spatialCurl (velocity H v upper B) (t, 0)‖) (𝓝[<] 1) atTop := by
  refine BaseVorticityAxis.baseVorticity_axis_tendsto_atTop (scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (coefficients_smooth H v) W.axis.normalization
    (fun j hj => (EntranceAlignedBase.modulated_positive_axis H v hj
      (by norm_num : |(0 : ℝ)| ≤ 1)).1) ?_
  rw [mul_assoc, inv_phi_axis]
  exact mul_pos (by norm_num) (f_axis_positive v)

end Navier.Construction.FinalSlowBase
