import Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace Navier.Analysis.ContinuousLeiLinRecentTailMoment

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinTimeDuhamel

/-- Polynomial output frequency is allocated to either convolution input. -/
theorem frequency_pow_product_split (n : ℕ) (ξ η : ES) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖ξ‖ ^ n * (a * b) ≤
      (2 : ℝ) ^ (n - 1) *
        (((‖η‖ ^ n * a) * b) + a * (‖ξ - η‖ ^ n * b)) := by
  have hp : ‖ξ‖ ^ n ≤ (‖η‖ + ‖ξ - η‖) ^ n :=
    pow_le_pow_left₀ (norm_nonneg ξ) (frequency_triangle ξ η) n
  have hs : (‖η‖ + ‖ξ - η‖) ^ n ≤
      (2 : ℝ) ^ (n - 1) * (‖η‖ ^ n + ‖ξ - η‖ ^ n) :=
    add_pow_le (norm_nonneg η) (norm_nonneg (ξ - η)) n
  calc
    ‖ξ‖ ^ n * (a * b) ≤ (‖η‖ + ‖ξ - η‖) ^ n * (a * b) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg ha hb)
    _ ≤ ((2 : ℝ) ^ (n - 1) * (‖η‖ ^ n + ‖ξ - η‖ ^ n)) * (a * b) :=
      mul_le_mul_of_nonneg_right hs (mul_nonneg ha hb)
    _ = (2 : ℝ) ^ (n - 1) *
        (((‖η‖ ^ n * a) * b) + a * (‖ξ - η‖ ^ n * b)) := by ring

/-- Pointwise polynomially weighted convolution estimate on every fiber where
the three Bochner integrals exist. -/
theorem frequency_pow_convolution_pointwise (n : ℕ) (f g : ES → ℝ)
    (hf : ∀ η, 0 ≤ f η) (hg : ∀ η, 0 ≤ g η) (ξ : ES)
    (hfg : Integrable (fun η : ES => f η * g (ξ - η)))
    (hl : Integrable (fun η : ES => (‖η‖ ^ n * f η) * g (ξ - η)))
    (hr : Integrable (fun η : ES => f η * (‖ξ - η‖ ^ n * g (ξ - η)))) :
    ‖ξ‖ ^ n * convolution f g ξ ≤
      (2 : ℝ) ^ (n - 1) *
        (convolution (fun η => ‖η‖ ^ n * f η) g ξ +
          convolution f (fun η => ‖η‖ ^ n * g η) ξ) := by
  change ‖ξ‖ ^ n * (∫ η : ES, f η * g (ξ - η)) ≤ _
  rw [← integral_const_mul]
  change (∫ η : ES, ‖ξ‖ ^ n * (f η * g (ξ - η))) ≤
    (2 : ℝ) ^ (n - 1) *
      ((∫ η : ES, (‖η‖ ^ n * f η) * g (ξ - η)) +
        ∫ η : ES, f η * (‖ξ - η‖ ^ n * g (ξ - η)))
  rw [← integral_add hl hr, ← integral_const_mul]
  apply integral_mono (hfg.const_mul _) ((hl.add hr).const_mul _)
  intro η
  exact frequency_pow_product_split n ξ η (hf η) (hg (ξ - η))

/-- Finite input mass and degree-`n` moments propagate to the same moment of
their convolution. -/
theorem integrable_polynomial_weighted_convolution (n : ℕ) (f g : ES → ℝ)
    (hf0 : Integrable f) (hg0 : Integrable g)
    (hfn : Integrable (fun η => ‖η‖ ^ n * f η))
    (hgn : Integrable (fun η => ‖η‖ ^ n * g η))
    (hf : ∀ η, 0 ≤ f η) (hg : ∀ η, 0 ≤ g η) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ n * convolution f g ξ) := by
  have h0 := hf0.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg0
  have hl := hfn.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg0
  have hr : Integrable (fun p : ES × ES =>
      f p.2 * (‖p.1 - p.2‖ ^ n * g (p.1 - p.2))) (volume.prod volume) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hf0.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hgn
  have h0ae := (integrable_prod_iff h0.aestronglyMeasurable).mp h0 |>.1
  have hlae := (integrable_prod_iff hl.aestronglyMeasurable).mp hl |>.1
  have hrae := (integrable_prod_iff hr.aestronglyMeasurable).mp hr |>.1
  have hae : ∀ᵐ ξ : ES, ‖ξ‖ ^ n * convolution f g ξ ≤
      (2 : ℝ) ^ (n - 1) *
        (convolution (fun η => ‖η‖ ^ n * f η) g ξ +
          convolution f (fun η => ‖η‖ ^ n * g η) ξ) := by
    filter_upwards [h0ae, hlae, hrae] with ξ h0ξ hlξ hrξ
    exact frequency_pow_convolution_pointwise n f g hf hg ξ h0ξ hlξ hrξ
  have hc0 := integrable_scalar_convolution f g hf0 hg0
  have hcl := integrable_scalar_convolution (fun η => ‖η‖ ^ n * f η) g hfn hg0
  have hcr := integrable_scalar_convolution f (fun η => ‖η‖ ^ n * g η) hf0 hgn
  refine ((hcl.add hcr).const_mul ((2 : ℝ) ^ (n - 1))).mono' ?_ ?_
  · exact (continuous_norm.pow n).aestronglyMeasurable.mul hc0.aestronglyMeasurable
  · filter_upwards [hae] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg ξ) n) (by
      apply integral_nonneg_of_ae
      filter_upwards with η
      exact mul_nonneg (hf η) (hg (ξ - η))))]
    exact hξ

/-- Global polynomial moment bound for a nonnegative scalar convolution. -/
theorem polynomial_weighted_convolution_mass_le (n : ℕ) (f g : ES → ℝ)
    (hf0 : Integrable f) (hg0 : Integrable g)
    (hfn : Integrable (fun η => ‖η‖ ^ n * f η))
    (hgn : Integrable (fun η => ‖η‖ ^ n * g η))
    (hf : ∀ η, 0 ≤ f η) (hg : ∀ η, 0 ≤ g η) :
    (∫ ξ : ES, ‖ξ‖ ^ n * convolution f g ξ) ≤
      (2 : ℝ) ^ (n - 1) *
        ((∫ η : ES, ‖η‖ ^ n * f η) * (∫ η : ES, g η) +
          (∫ η : ES, f η) * (∫ η : ES, ‖η‖ ^ n * g η)) := by
  have h0 := hf0.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg0
  have hl := hfn.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg0
  have hr : Integrable (fun p : ES × ES =>
      f p.2 * (‖p.1 - p.2‖ ^ n * g (p.1 - p.2))) (volume.prod volume) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hf0.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hgn
  have h0ae := (integrable_prod_iff h0.aestronglyMeasurable).mp h0 |>.1
  have hlae := (integrable_prod_iff hl.aestronglyMeasurable).mp hl |>.1
  have hrae := (integrable_prod_iff hr.aestronglyMeasurable).mp hr |>.1
  have hae : ∀ᵐ ξ : ES, ‖ξ‖ ^ n * convolution f g ξ ≤
      (2 : ℝ) ^ (n - 1) *
        (convolution (fun η => ‖η‖ ^ n * f η) g ξ +
          convolution f (fun η => ‖η‖ ^ n * g η) ξ) := by
    filter_upwards [h0ae, hlae, hrae] with ξ h0ξ hlξ hrξ
    exact frequency_pow_convolution_pointwise n f g hf hg ξ h0ξ hlξ hrξ
  have hc0 := integrable_scalar_convolution f g hf0 hg0
  have hcl := integrable_scalar_convolution (fun η => ‖η‖ ^ n * f η) g hfn hg0
  have hcr := integrable_scalar_convolution f (fun η => ‖η‖ ^ n * g η) hf0 hgn
  have hrhs : Integrable (fun ξ : ES => (2 : ℝ) ^ (n - 1) *
      (convolution (fun η => ‖η‖ ^ n * f η) g ξ +
        convolution f (fun η => ‖η‖ ^ n * g η) ξ)) :=
    (hcl.add hcr).const_mul _
  have hconv_nonneg : ∀ ξ : ES, 0 ≤ convolution f g ξ := by
    intro ξ
    apply integral_nonneg_of_ae
    filter_upwards with η
    exact mul_nonneg (hf η) (hg (ξ - η))
  have hlhs : Integrable (fun ξ : ES => ‖ξ‖ ^ n * convolution f g ξ) := by
    refine hrhs.mono' ?_ ?_
    · exact (continuous_norm.pow n).aestronglyMeasurable.mul hc0.aestronglyMeasurable
    · filter_upwards [hae] with ξ hξ
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (pow_nonneg (norm_nonneg ξ) n) (hconv_nonneg ξ))]
      exact hξ
  calc
    (∫ ξ : ES, ‖ξ‖ ^ n * convolution f g ξ) ≤ _ :=
      integral_mono_ae hlhs hrhs hae
    _ = (2 : ℝ) ^ (n - 1) *
        ((∫ η : ES, ‖η‖ ^ n * f η) * (∫ η : ES, g η) +
          (∫ η : ES, f η) * (∫ η : ES, ‖η‖ ^ n * g η)) := by
      rw [integral_const_mul, integral_add hcl hcr]
      change (2 : ℝ) ^ (n - 1) *
        (normX0 (convolution (fun η => ‖η‖ ^ n * f η) g) +
          normX0 (convolution f (fun η => ‖η‖ ^ n * g η))) = _
      rw [normX0_convolution_eq _ _ hfn hg0, normX0_convolution_eq _ _ hf0 hgn]
      rfl

/-- A degree-`n+1` moment on both velocity profiles supplies the degree-`n`
moment of the genuine continuous Navier source.  The loss of one degree is
the output derivative in the bilinear symbol. -/
theorem integrable_pow_norm_continuousNavierSource
    (n : ℕ) (u v : ℝ → ES → ComplexSpace) (t : ℝ)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u t η j))
    (hv : ∀ i : Fin 3, AEStronglyMeasurable (fun η : ES => v t η i))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u t η j‖))
    (hv0 : ∀ i : Fin 3, Integrable (fun η : ES => ‖v t η i‖))
    (huN : ∀ j : Fin 3, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖u t η j‖))
    (hvN : ∀ i : Fin 3, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖v t η i‖)) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ n *
      complexEuclideanNorm (continuousNavierSource u v t ξ)) := by
  have hmeas := continuousNavierBilinear_aestronglyMeasurable
    (u t) (v t) hu hv hu0 hv0
  have hsum : Integrable (fun ξ : ES => ∑ i : Fin 3, ∑ j : Fin 3,
      ‖ξ‖ ^ (n + 1) *
        convolution (fun η => ‖u t η j‖) (fun η => ‖v t η i‖) ξ) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact integrable_polynomial_weighted_convolution (n + 1)
      (fun η => ‖u t η j‖) (fun η => ‖v t η i‖)
      (hu0 j) (hv0 i) (huN j) (hvN i) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine hsum.mono' ?_ ?_
  · exact (continuous_norm.pow n).aestronglyMeasurable.mul hmeas.norm
  · filter_upwards with ξ
    have hout : 0 ≤ complexEuclideanNorm (continuousNavierSource u v t ξ) := by
      unfold complexEuclideanNorm
      exact norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg ξ) n)
      hout)]
    calc
      ‖ξ‖ ^ n * complexEuclideanNorm (continuousNavierSource u v t ξ) ≤
          ‖ξ‖ ^ n * (∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ *
            convolution (fun η => ‖u t η j‖) (fun η => ‖v t η i‖) ξ) :=
        mul_le_mul_of_nonneg_left (continuousNavierBilinear_majorant (u t) (v t) ξ)
          (pow_nonneg (norm_nonneg ξ) n)
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ ^ (n + 1) *
            convolution (fun η => ‖u t η j‖) (fun η => ‖v t η i‖) ξ := by
        simp only [Finset.mul_sum, pow_succ, mul_assoc]

/-- The literal recent-time Duhamel slice. -/
def continuousDuhamelRecent (ν τ : ℝ) (u v : ℝ → ES → ComplexSpace)
    (t : ℝ) (ξ : ES) : ComplexSpace := fun i =>
  ∫ s in Icc τ t,
    heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u v s ζ i) ξ

/-- On `[τ,t]` the heat factor is a contraction.  Thus a joint degree-`n`
source moment, rather than an artificial positive heat lag, controls the
recent integrand. -/
theorem integrable_weighted_heat_on_recent_tail
    (b : ℝ → ES → ℂ) (ν τ t : ℝ) (hν : 0 ≤ ν) (n : ℕ)
    (hmeas : AEStronglyMeasurable (fun p : ES × ℝ => b p.2 p.1)
      (volume.prod (volume.restrict (Icc τ t))))
    (hsrc : Integrable (fun p : ES × ℝ => ‖p.1‖ ^ n * ‖b p.2 p.1‖)
      (volume.prod (volume.restrict (Icc τ t)))) :
    Integrable (fun p : ES × ℝ => (‖p.1‖ ^ n : ℝ) •
      heatMode ν (t - p.2) (b p.2) p.1)
      (volume.prod (volume.restrict (Icc τ t))) := by
  let μ := volume.restrict (Icc τ t)
  have hmem : ∀ᵐ p : ES × ℝ ∂volume.prod μ, p.2 ∈ Icc τ t := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · exact Filter.Eventually.of_forall fun _ => ae_restrict_mem isClosed_Icc.measurableSet
    · exact isClosed_Icc.measurableSet.preimage measurable_snd
  have hmajor : ∀ᵐ p : ES × ℝ ∂volume.prod μ,
      ‖(‖p.1‖ ^ n : ℝ) • heatMode ν (t - p.2) (b p.2) p.1‖ ≤
        ‖p.1‖ ^ n * ‖b p.2 p.1‖ := by
    filter_upwards [hmem] with p hp
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    simp only [heatMode, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    gcongr
    have he : Real.exp (-(ν * ‖p.1‖ ^ 2 * (t - p.2))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        (mul_nonneg (mul_nonneg hν (sq_nonneg ‖p.1‖)) (sub_nonneg.mpr hp.2)))
    simpa using mul_le_mul_of_nonneg_right he (norm_nonneg (b p.2 p.1))
  refine hsrc.mono' ?_ hmajor
  have hmult : AEStronglyMeasurable (fun p : ES × ℝ =>
      ‖p.1‖ ^ n * Real.exp (-(ν * ‖p.1‖ ^ 2 * (t - p.2)))) (volume.prod μ) := by
    fun_prop
  exact (hmult.smul hmeas).congr (Filter.Eventually.of_forall fun p => by
    simp [heatMode, mul_assoc])

/-- Fubini sends the recent joint moment through the literal time integral. -/
theorem integrable_pow_norm_continuousDuhamelRecent
    (u v : ℝ → ES → ComplexSpace) (ν τ t : ℝ) (i : Fin 3) (n : ℕ)
    (hjoint : Integrable (fun p : ES × ℝ =>
      (‖p.1‖ ^ n : ℝ) • heatMode ν (t - p.2)
        (fun ζ : ES => continuousNavierSource u v p.2 ζ i) p.1)
      (volume.prod (volume.restrict (Icc τ t)))) :
    Integrable (fun ξ : ES =>
      ‖ξ‖ ^ n * ‖continuousDuhamelRecent ν τ u v t ξ i‖) := by
  set μ := volume.restrict (Icc τ t)
  have hi : Integrable (fun ξ : ES => ∫ s,
      (‖ξ‖ ^ n : ℝ) • heatMode ν (t - s)
        (fun ζ : ES => continuousNavierSource u v s ζ i) ξ ∂μ) :=
    hjoint.integral_prod_left
  refine hi.norm.congr (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖∫ s, (‖ξ‖ ^ n : ℝ) • heatMode ν (t - s)
      (fun ζ : ES => continuousNavierSource u v s ζ i) ξ ∂μ‖ =
    ‖ξ‖ ^ n * ‖continuousDuhamelRecent ν τ u v t ξ i‖
  rw [integral_smul, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  rfl

/-- The source-moment premise in its direct form feeds the actual recent
Duhamel slice. -/
theorem integrable_pow_norm_continuousDuhamelRecent_of_source
    (u v : ℝ → ES → ComplexSpace) (ν τ t : ℝ) (i : Fin 3) (n : ℕ)
    (hν : 0 ≤ ν)
    (hmeas : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc τ t))))
    (hsrc : Integrable (fun p : ES × ℝ => ‖p.1‖ ^ n *
      ‖continuousNavierSource u v p.2 p.1 i‖)
      (volume.prod (volume.restrict (Icc τ t)))) :
    Integrable (fun ξ : ES =>
      ‖ξ‖ ^ n * ‖continuousDuhamelRecent ν τ u v t ξ i‖) := by
  apply integrable_pow_norm_continuousDuhamelRecent u v ν τ t i n
  exact integrable_weighted_heat_on_recent_tail
    (fun s ξ => continuousNavierSource u v s ξ i) ν τ t hν n hmeas hsrc

end Navier.Analysis.ContinuousLeiLinRecentTailMoment

#print axioms Navier.Analysis.ContinuousLeiLinRecentTailMoment.frequency_pow_product_split
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailMoment.frequency_pow_convolution_pointwise
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailMoment.integrable_polynomial_weighted_convolution
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailMoment.polynomial_weighted_convolution_mass_le
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailMoment.integrable_pow_norm_continuousNavierSource
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailMoment.integrable_weighted_heat_on_recent_tail
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailMoment.integrable_pow_norm_continuousDuhamelRecent
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailMoment.integrable_pow_norm_continuousDuhamelRecent_of_source
