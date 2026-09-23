import Navier.Analysis.WienerPhysicalAssembly

/-!
# Local classical existence at physical viscosity one: the assembled clauses

For every divergence-free Schwartz datum `u₀`, the rescaled large-data Wiener
solution with datum `-2π u₀` at repository viscosity `4π²` gives, on a positive
horizon `T`, a velocity/pressure pair with

* the initial condition `u 0 = u₀`;
* joint `C^∞` velocity on `[0,T) × ℝ³`;
* pointwise incompressibility on `[0,T)`;
* the official equation `SatisfiesNavierStokesBefore 1 zeroForce T u p`.

The remaining clauses of `SolvesBefore 1 T u p` are the pressure smoothness
`SmoothPressureBefore T p`, finite energy slices and the energy inequality.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set SchwartzMap LineDeriv
open scoped FourierTransform SchwartzMap ContDiff ComplexConjugate

namespace Navier.Analysis.WienerLocalExistence

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace Navier.Analysis.ContinuousLeiLinReality
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.ContinuousLeiLinSelfMap Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.FourierMajorant
open Navier.Analysis.WienerSchwartzLocal
open Navier.Analysis.WienerPhysicalAssembly

/-- **Transversality of the Fourier datum of a divergence-free Schwartz velocity.** -/
theorem profileDivergenceFree_fourierDatum (u₀ : SchwartzVelocity)
    (hdiv : DivergenceFreeInitial u₀) : ProfileDivergenceFree (fourierDatum u₀) := by
  intro ξ
  let e : Fin 3 → 𝓢(ES, ℂ) := fun i => euclidComponent u₀ i
  let m : Fin 3 → ES := fun i => EuclideanSpace.single i (1 : ℝ)
  have hg : ∀ i, (fun x : ES => inner ℝ x (m i)).HasTemperateGrowth := fun i =>
    ((innerSL ℝ).flip (m i)).hasTemperateGrowth
  have hF : ∀ i, (𝓕 (∂_{m i} (e i) : 𝓢(ES, ℂ))) ξ =
      (2 * Real.pi * Complex.I) * ((ξ i : ℝ) : ℂ) * (𝓕 (e i)) ξ := by
    intro i
    rw [SchwartzMap.fourier_lineDerivOp_eq, smul_apply, smulLeftCLM_apply_apply (hg i)]
    simp [m, EuclideanSpace.inner_single_right]
    ring
  have hd : ∀ (i : Fin 3) (y : ES), (∂_{m i} (e i) : 𝓢(ES, ℂ)) y =
      ((fderiv ℝ (⇑u₀) (spaceProj y) (basisVector i) i : ℝ) : ℂ) := by
    intro i y
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have he : ⇑(e i) = fun y => componentCLM i (u₀ (spaceProj y)) := rfl
    have hh : HasFDerivAt (fun y => componentCLM i (u₀ (spaceProj y)))
        ((componentCLM i).comp ((fderiv ℝ (⇑u₀) (spaceProj y)).comp
          (spaceProj : ES →L[ℝ] Space))) y :=
      (componentCLM i).hasFDerivAt.comp y
        ((u₀.differentiableAt).hasFDerivAt.comp y spaceProj.hasFDerivAt)
    rw [he, hh.fderiv]
    rfl
  have hS : (∑ i, (∂_{m i} (e i) : 𝓢(ES, ℂ))) = 0 := by
    ext y
    simp only [sum_apply, hd, zero_apply]
    rw [← Complex.ofReal_sum]
    have h := hdiv (spaceProj y)
    unfold staticDivergence at h
    rw [h, Complex.ofReal_zero]
  have h2 : ∑ i, (2 * Real.pi * Complex.I) * ((ξ i : ℝ) : ℂ) * (𝓕 (e i)) ξ = 0 := by
    rw [← Finset.sum_congr rfl fun i _ => hF i, ← sum_apply, ← FourierTransform.fourier_sum,
      hS, FourierTransform.fourier_zero, zero_apply]
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h3 : (2 * Real.pi * Complex.I : ℂ) *
      ∑ i, ((ξ i : ℝ) : ℂ) * (𝓕 (e i)) ξ = 0 := by
    rw [Finset.mul_sum]; rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h4 := (mul_eq_zero.mp h3).resolve_left hne
  exact h4

theorem divergenceFreeInitial_smul (c : ℝ) {u₀ : SchwartzVelocity}
    (hdiv : DivergenceFreeInitial u₀) : DivergenceFreeInitial (c • u₀) := by
  intro x
  have h := hdiv x
  unfold staticDivergence at h ⊢
  have hf : (fun y => (c • u₀) y) = fun y => c • u₀ y := rfl
  rw [hf, fderiv_fun_const_smul (u₀.differentiableAt) c]
  simp only [ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, h, mul_zero]

/-- The mild solution starts at its datum. -/
theorem mild_zero {ν : ℝ} (hν : 0 < ν) (a : ES → ComplexSpace) (w : ℝ → ES → ComplexSpace)
    (ξ : ES) : continuousMildImage ν hν a w 0 ξ = a ξ := by
  funext i
  show heatVec ν 0 a ξ i + continuousDuhamel ν w w 0 ξ i = a ξ i
  have h1 : heatVec ν 0 a ξ i = a ξ i := by
    show heatMode ν 0 (fun ζ => a ζ i) ξ = a ξ i
    simp [heatMode]
  have h2 : continuousDuhamel ν w w 0 ξ i = 0 := by
    show ∫ s in Icc (0 : ℝ) 0, _ = 0
    rw [Icc_self, Measure.restrict_eq_zero.mpr (Real.volume_singleton), integral_zero_measure]
  rw [h1, h2, add_zero]

/-- **The assembled local classical clauses at viscosity one.** -/
theorem exists_local_classical_clauses (u₀ : SchwartzVelocity)
    (hdiv : DivergenceFreeInitial u₀) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : VelocityEvolution, ∃ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) ∧ SmoothVelocityBefore T u ∧ IncompressibleBefore T u ∧
        SatisfiesNavierStokesBefore 1 zeroForce T u p := by
  set v₀ : SchwartzVelocity := (-(2 * Real.pi)) • u₀ with hv₀
  set ν : ℝ := 4 * Real.pi ^ 2 with hνdef
  have hν : 0 < ν := by positivity
  set n : ℝ := ‖wienerDatum v₀‖ ^ 2 with hn
  have hn0 : 0 ≤ n := by positivity
  set T : ℝ := ν / (10 ^ 4 * (n + 1)) with hTdef
  have hT : 0 < T := by positivity
  have hsmall : 10 ^ 4 * T * ‖wienerDatum v₀‖ ^ 2 ≤ ν := by
    rw [← hn, hTdef]
    have hpos : (0 : ℝ) < 10 ^ 4 * (n + 1) := by positivity
    rw [show 10 ^ 4 * (ν / (10 ^ 4 * (n + 1))) * n = ν * (n / (n + 1)) by field_simp]
    have : n / (n + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  obtain ⟨-, -, w, -, hfix, hG, hsm, hreal⟩ :=
    Navier.Analysis.WienerReality.exists_real_smooth_wienerSolution hν hT v₀ hsmall
  have ha : ProfileDivergenceFree (fourierDatum v₀) :=
    profileDivergenceFree_fourierDatum v₀ (divergenceFreeInitial_smul _ hdiv)
  refine ⟨T, hT, physU w, physP w, fun x => ?_, smoothVelocityBefore_physU hsm,
    incompressibleBefore_physU hT hν (fourierDatum v₀) hfix hG ha,
    satisfiesNavierStokesBefore_physU hT hν (fourierDatum v₀) hfix hG rfl ha hreal⟩
  funext i
  have hw0 : (fun ξ => w 0 ξ i) = fun ξ => fourierDatum v₀ ξ i := by
    funext ξ
    rw [hfix 0 ⟨le_rfl, hT.le⟩ ξ, mild_zero]
  have h := physicalCoord_fourierDatum v₀ i (euclidPoint x)
  unfold physicalCoord at h
  show -(1 / (2 * Real.pi)) * (𝓕⁻ (fun ξ => w 0 ξ i) (euclidPoint x)).re = u₀ x i
  rw [hw0, h, Complex.ofReal_re]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  show -(1 / (2 * Real.pi)) * ((-(2 * Real.pi)) • u₀) x i = u₀ x i
  simp only [smul_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

end Navier.Analysis.WienerLocalExistence

set_option pp.fullNames true in
#check @Navier.Analysis.WienerLocalExistence.exists_local_classical_clauses
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerLocalExistence.exists_local_classical_clauses
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerLocalExistence.profileDivergenceFree_fourierDatum
