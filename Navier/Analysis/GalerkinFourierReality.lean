import Navier.Analysis.GalerkinSmoothBandCutoff
import Navier.Analysis.GalerkinBandDenseFamily

/-! Even real Fourier cutoffs preserve the reality symmetry and the
divergence-free symbol equation. The approximants below are actual Schwartz
maps with weighted L² convergence. Inverse Fourier transformation gives
actual real divergence-free velocities with exactly these Fourier fields. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform

namespace Navier.Analysis.GalerkinFourierReality

open DivFreeGradientEnstrophy GalerkinSmoothBandCutoff

/-- The Fourier symmetry of a real vector field, in actual coordinates. -/
def HermitianReal (g : EuclSpace → CxSpace) : Prop :=
  ∀ ξ i, g (-ξ) i = star (g ξ i)

/-- The Fourier symbol of zero divergence. -/
def Transverse (g : EuclSpace → CxSpace) : Prop :=
  ∀ ξ, ∑ i : Fin 3, (ξ i : ℂ) * g ξ i = 0

theorem cutoff_hermitianReal (χ : EuclSpace → ℝ)
    (hχ : ∀ ξ, χ (-ξ) = χ ξ) {g : EuclSpace → CxSpace}
    (hg : HermitianReal g) : HermitianReal (fun ξ => χ ξ • g ξ) := by
  intro ξ i
  simp only [PiLp.smul_apply, hχ ξ, hg ξ i]
  simp

theorem cutoff_transverse (χ : EuclSpace → ℝ) {g : EuclSpace → CxSpace}
    (hg : Transverse g) : Transverse (fun ξ => χ ξ • g ξ) := by
  intro ξ
  simp only [PiLp.smul_apply, Complex.real_smul]
  calc
    (∑ i : Fin 3, (ξ i : ℂ) * ((χ ξ : ℂ) * g ξ i)) =
        (χ ξ : ℂ) * ∑ i : Fin 3, (ξ i : ℂ) * g ξ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hg ξ, mul_zero]

/-- Band approximation retains both constraints, as well as convergence
against every nonnegative integrable weighted energy of the original field. -/
theorem exists_hermitian_transverse_band_approximation
    (B : Set EuclSpace) (hB : IsOpen B) (hc : IsCompact (closure B))
    (hneg : ∀ ξ, -ξ ∈ B ↔ ξ ∈ B) (g : 𝓢(EuclSpace, CxSpace))
    (hr : HermitianReal g) (ht : Transverse g) :
    ∃ v : ℕ → 𝓢(EuclSpace, CxSpace),
      (∀ n ξ, ξ ∉ B → v n ξ = 0) ∧
      (∀ n, HermitianReal (v n) ∧ Transverse (v n)) ∧
      ∀ w : EuclSpace → ℝ, (∀ ξ, 0 ≤ w ξ) →
        Integrable (fun ξ => w ξ * ‖g ξ‖ ^ 2) →
        Tendsto (fun n => ∫ ξ, w ξ * ‖v n ξ - B.indicator g ξ‖ ^ 2)
          atTop (𝓝 0) := by
  obtain ⟨χ, hχd, hχc, hχrange, hχzero, hχeven, hχlim⟩ :=
    exists_smooth_band_cutoffs B hB hc hneg
  let v : ℕ → 𝓢(EuclSpace, CxSpace) :=
    fun n => cutoffSchwartz (χ n) (hχc n) (hχd n) g
  refine ⟨v, ?_, ?_, ?_⟩
  · intro n ξ hξ
    simp [v, hχzero n ξ hξ]
  · intro n
    exact ⟨cutoff_hermitianReal (χ n) (hχeven n) hr,
      cutoff_transverse (χ n) ht⟩
  · intro w hw hwi
    have hlim := tendsto_integral_cutoff_error B hB.measurableSet χ
      (fun n => (hχd n).continuous) hχrange hχlim hwi
      (fun ξ => mul_nonneg (hw ξ) (sq_nonneg _))
    have heq (n : ℕ) (ξ : EuclSpace) :
        w ξ * ‖v n ξ - B.indicator g ξ‖ ^ 2 =
          (χ n ξ - B.indicator (fun _ => 1) ξ) ^ 2 * (w ξ * ‖g ξ‖ ^ 2) := by
      have hid : B.indicator g ξ = B.indicator (fun _ => (1 : ℝ)) ξ • g ξ := by
        by_cases hξ : ξ ∈ B <;> simp [hξ]
      rw [hid]
      change w ξ * ‖χ n ξ • g ξ - B.indicator (fun _ => (1 : ℝ)) ξ • g ξ‖ ^ 2 = _
      rw [← sub_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    simpa only [heq] using hlim

/-- A Hermitian-symmetric integrable scalar Fourier field has a convergent
inverse Fourier integral whose value is real. -/
theorem scalar_inverse_fourier_real (g : EuclSpace → ℂ) (hg : Integrable g)
    (hr : ∀ ξ, g (-ξ) = star (g ξ)) (x : EuclSpace) :
    Integrable (fun ξ => 𝐞 (inner ℝ ξ x) • g ξ) ∧
      star (𝓕⁻ g x) = 𝓕⁻ g x := by
  refine ⟨?_, ?_⟩
  · simpa using (Real.fourierIntegral_convergent_iff (-x)).2 hg
  · rw [Real.fourierInv_eq]
    change (starRingEnd ℂ) (∫ ξ, 𝐞 (inner ℝ ξ x) • g ξ) = _
    rw [← integral_conj]
    calc
      (∫ ξ, (starRingEnd ℂ) (𝐞 (inner ℝ ξ x) • g ξ)) =
          ∫ ξ, 𝐞 (inner ℝ (-ξ) x) • g (-ξ) := by
        apply integral_congr_ae
        filter_upwards [] with ξ
        simp [Circle.smul_def, hr ξ]
      _ = ∫ ξ, 𝐞 (inner ℝ ξ x) • g ξ :=
        integral_neg_eq_self (fun ξ : EuclSpace => 𝐞 (inner ℝ ξ x) • g ξ) volume

/-- Inverse Fourier transformation commutes with each complex coordinate. -/
theorem inverse_fourier_coordinate (g : 𝓢(EuclSpace, CxSpace))
    (x : EuclSpace) (i : Fin 3) :
    (𝓕⁻ g) x i = 𝓕⁻ (fun ξ => g ξ i) x := by
  have hint : Integrable (fun ξ => 𝐞 (inner ℝ ξ x) • g ξ) := by
    simpa using (Real.fourierIntegral_convergent_iff (-x)).2 g.integrable
  change ((𝓕⁻ g : 𝓢(EuclSpace, CxSpace)) : EuclSpace → CxSpace) x i = _
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, Real.fourierInv_eq]
  have hcomm := (EuclideanSpace.proj (𝕜 := ℂ) i).integral_comp_comm hint
  simpa [Circle.smul_def] using hcomm.symm

/-- Every coordinate of the inverse transform of a Hermitian Schwartz field
is real; the scalar proof above also supplies convergence of its integral. -/
theorem inverse_fourier_coordinate_real (g : 𝓢(EuclSpace, CxSpace))
    (hr : HermitianReal g) (x : EuclSpace) (i : Fin 3) :
    star ((𝓕⁻ g) x i) = (𝓕⁻ g) x i := by
  rw [inverse_fourier_coordinate]
  have hi : Integrable (fun ξ => g ξ i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).integrable_comp g.integrable
  exact (scalar_inverse_fourier_real (fun ξ => g ξ i) hi (fun ξ => hr ξ i) x).2

/-- Coordinatewise real part, with the physical velocity-space norm. -/
def cxRealPart : CxSpace →L[ℝ] Navier.Space :=
  ContinuousLinearMap.pi fun i =>
    Complex.reCLM.comp ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ)

@[simp] theorem cxRealPart_apply (z : CxSpace) (i : Fin 3) :
    cxRealPart z i = (z i).re := rfl

/-- An actual real Schwartz velocity obtained by inverse Fourier transform
and the fixed coordinate equivalence. -/
def inverseRealVelocity (g : 𝓢(EuclSpace, CxSpace)) : Navier.SchwartzVelocity :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ euclCoords.symm
    (SchwartzMap.postcompCLM cxRealPart (𝓕⁻ g))

/-- Hermitian symmetry ensures real-part extraction loses no information:
the existing physical complexification is exactly the inverse transform. -/
theorem euclModel_inverseRealVelocity (g : 𝓢(EuclSpace, CxSpace))
    (hr : HermitianReal g) : euclModel (inverseRealVelocity g) = 𝓕⁻ g := by
  ext x i
  have hreal := inverse_fourier_coordinate_real g hr x i
  have him : ((𝓕⁻ g) x i).im = 0 := by
    have h := congrArg Complex.im hreal
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  change (((𝓕⁻ g) (euclCoords.symm (euclCoords x)) i).re : ℂ) = (𝓕⁻ g) x i
  rw [euclCoords.symm_apply_apply]
  apply Complex.ext <;> simp [him]

/-- The reconstructed physical field has exactly the prescribed Fourier
transform, with no loss from taking real parts. -/
theorem fourier_euclModel_inverseRealVelocity (g : 𝓢(EuclSpace, CxSpace))
    (hr : HermitianReal g) : 𝓕 (euclModel (inverseRealVelocity g)) = g := by
  rw [euclModel_inverseRealVelocity g hr, FourierTransform.fourier_fourierInv_eq]

/-- Fourier transversality becomes actual zero physical divergence. -/
theorem inverseRealVelocity_divergenceFree (g : 𝓢(EuclSpace, CxSpace))
    (hr : HermitianReal g) (ht : Transverse g) :
    Navier.DivergenceFreeInitial (inverseRealVelocity g) := by
  have hzF : 𝓕 (divModel (inverseRealVelocity g)) = 0 := by
    ext ξ
    rw [fourier_divModel, fourier_euclModel_inverseRealVelocity g hr, ht ξ]
    simp
  have hz : divModel (inverseRealVelocity g) = 0 := by
    have h := congrArg (fun f : 𝓢(EuclSpace, ℂ) => 𝓕⁻ f) hzF
    simpa only [FourierTransform.fourierInv_fourier_eq,
      FourierTransform.fourierInv_zero] using h
  intro x
  have hx := congrArg (fun f : 𝓢(EuclSpace, ℂ) => f (euclCoords.symm x)) hz
  rw [divModel_apply, euclCoords.apply_symm_apply] at hx
  change (Navier.staticDivergence (inverseRealVelocity g) x : ℂ) = 0 at hx
  exact_mod_cast hx

/-- Pointwise real Schwartz functions have Hermitian Fourier transforms. -/
theorem scalar_fourier_conjugate (g : 𝓢(EuclSpace, ℂ))
    (hr : ∀ x, star (g x) = g x) (ξ : EuclSpace) :
    star ((𝓕 g) ξ) = (𝓕 g) (-ξ) := by
  change star (((𝓕 g : 𝓢(EuclSpace, ℂ)) : EuclSpace → ℂ) ξ) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq]
  change (starRingEnd ℂ) (∫ x, 𝐞 (-inner ℝ x ξ) • g x) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Circle.smul_def, smul_eq_mul, map_mul, Circle.starRingEnd_addChar,
    neg_neg, inner_neg_right]
  congr 1
  exact hr x

/-- The original physical complexification satisfies the required reality
symmetry after Fourier transformation. -/
theorem fourier_euclModel_hermitianReal (u : Navier.SchwartzVelocity) :
    HermitianReal (𝓕 (euclModel u) : 𝓢(EuclSpace, CxSpace)) := by
  intro ξ i
  let g := SchwartzMap.postcompCLM (𝕜 := ℂ)
    (EuclideanSpace.proj (𝕜 := ℂ) i) (euclModel u)
  have hr : ∀ x, star (g x) = g x := by
    intro x
    change star ((u (euclCoords x) i : ℂ)) = (u (euclCoords x) i : ℂ)
    simp
  have h := (scalar_fourier_conjugate g hr ξ).symm
  simpa [g, fourier_postcompCLM_apply, EuclideanSpace.proj] using h

/-- The actual physical zero-divergence equation supplies transversality of
the Fourier transform. -/
theorem fourier_euclModel_transverse (u : Navier.SchwartzVelocity)
    (hu : Navier.DivergenceFreeInitial u) :
    Transverse (𝓕 (euclModel u) : 𝓢(EuclSpace, CxSpace)) := by
  have hz : divModel u = 0 := by
    ext x
    rw [divModel_apply, hu (euclCoords x)]
    simp
  intro ξ
  have h := fourier_divModel u ξ
  rw [hz, FourierTransform.fourier_zero] at h
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  exact (mul_eq_zero.mp h.symm).resolve_left hc

/-- Smooth band approximation now produces actual divergence-free real
Schwartz velocities, whose Fourier transforms converge to the intended
sharp restriction with every integrable nonnegative weighted energy. -/
theorem exists_real_velocity_band_approximation
    (B : Set EuclSpace) (hB : IsOpen B) (hc : IsCompact (closure B))
    (hneg : ∀ ξ, -ξ ∈ B ↔ ξ ∈ B) (g : 𝓢(EuclSpace, CxSpace))
    (hr : HermitianReal g) (ht : Transverse g) :
    ∃ v : ℕ → Navier.SchwartzVelocity,
      (∀ n, Navier.DivergenceFreeInitial (v n)) ∧
      (∀ n ξ, ξ ∉ B → (𝓕 (euclModel (v n))) ξ = 0) ∧
      ∀ w : EuclSpace → ℝ, (∀ ξ, 0 ≤ w ξ) →
        Integrable (fun ξ => w ξ * ‖g ξ‖ ^ 2) →
        Tendsto (fun n => ∫ ξ, w ξ *
          ‖(𝓕 (euclModel (v n))) ξ - B.indicator g ξ‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨f, hfB, hft, hflim⟩ :=
    exists_hermitian_transverse_band_approximation B hB hc hneg g hr ht
  refine ⟨fun n => inverseRealVelocity (f n), ?_, ?_, ?_⟩
  · intro n
    exact inverseRealVelocity_divergenceFree (f n) (hft n).1 (hft n).2
  · intro n ξ hξ
    rw [fourier_euclModel_inverseRealVelocity (f n) (hft n).1]
    exact hfB n ξ hξ
  · intro w hw hwi
    simpa only [fourier_euclModel_inverseRealVelocity _ (hft _).1] using
      hflim w hw hwi

/-- Every real divergence-free Schwartz velocity admits approximants in the
actual dyadic band space. Schwartz decay discharges the weighted-integrability
input; the physical field supplies both Fourier constraints. -/
theorem exists_dyadic_divFree_schwartz_band_approximation
    (k : ℤ) (u : Navier.SchwartzVelocity) (hu : Navier.DivergenceFreeInitial u) :
    ∃ v : ℕ → Navier.SchwartzVelocity,
      (∀ n, v n ∈ GalerkinBandDenseFamily.bandFields
        (GalerkinAnnularApproximation.dyadicAnnulus k)) ∧
      Tendsto (fun n => ∫ ξ, (1 + ‖ξ‖ ^ 2) *
        ‖(𝓕 (euclModel (v n))) ξ -
          (GalerkinAnnularApproximation.dyadicAnnulus k).indicator
            (𝓕 (euclModel u) : 𝓢(EuclSpace, CxSpace)) ξ‖ ^ 2) atTop (𝓝 0) := by
  let B := GalerkinAnnularApproximation.dyadicAnnulus k
  let g : 𝓢(EuclSpace, CxSpace) := 𝓕 (euclModel u)
  have hc : IsCompact (closure B) := by
    apply (isCompact_closedBall (0 : EuclSpace) ((2 : ℝ) ^ (k + 1))).of_isClosed_subset
      isClosed_closure
    apply closure_minimal _ Metric.isClosed_closedBall
    intro ξ hξ
    simpa only [Metric.mem_closedBall, dist_zero_right] using hξ.2.le
  have hneg : ∀ ξ, -ξ ∈ B ↔ ξ ∈ B := by
    intro ξ
    simp [B, GalerkinAnnularApproximation.dyadicAnnulus]
  obtain ⟨v, hvdiv, hvB, happ⟩ := exists_real_velocity_band_approximation B
    (GalerkinAnnularApproximation.dyadicAnnulus_isOpen k) hc hneg g
      (fourier_euclModel_hermitianReal u) (fourier_euclModel_transverse u hu)
  refine ⟨v, fun n => ⟨hvdiv n, hvB n⟩,
    happ (fun ξ => 1 + ‖ξ‖ ^ 2) (fun ξ => by positivity) ?_⟩
  have h0 : Integrable (fun ξ => ‖g ξ‖ ^ 2) := by
    simpa using GalerkinDisjointBands.integrable_weighted_normSq g 0
  have h2 := GalerkinDisjointBands.integrable_weighted_normSq g 2
  have heq : (fun ξ => (1 + ‖ξ‖ ^ 2) * ‖g ξ‖ ^ 2) =
      (fun ξ => ‖g ξ‖ ^ 2 + ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2) := by
    funext ξ
    ring
  rw [heq]
  exact h0.add h2

end Navier.Analysis.GalerkinFourierReality
