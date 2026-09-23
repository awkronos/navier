import Navier.Analysis.WienerPhysicalPDE

/-!
# The Fourier-side cancellation of the Navier nonlinearity

For a bounded, integrable profile `u` with integrable first moment which is
transversal (`∑ⱼ ξⱼ uⱼ(ξ) = 0` a.e.), the trilinear form

`∫ ∑ᵢⱼ uᵢ(-ξ) ξⱼ (uⱼ ⋆ uᵢ)(ξ) dξ`

vanishes.  In the coordinates `ξ = η + ζ` the integrand becomes
`a(η,ζ) b(η,ζ)` with `a` even and `b` odd under `ζ ↦ -η - ζ` (by transversality
at `η`), so every `ζ`-integral is zero.  With the reflection symmetry
`uᵢ(-ξ) = conj uᵢ(ξ)` this is the Fourier form of `∫ u·(u·∇)u = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Convolution ComplexConjugate

namespace Navier.Analysis.WienerEnergyCancel

open Navier.Analysis.ContinuousLeiLinSpace

variable {u : ES → ComplexSpace} {R : ℝ}

/-- The integrand in shear coordinates `ξ = η + ζ`. -/
def Gs (u : ES → ComplexSpace) (η ζ : ES) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, u (-(η + ζ)) i * (((η + ζ) j : ℝ) : ℂ) * u η j * u ζ i

theorem norm_coord_ES_le (ξ : ES) (j : Fin 3) : ‖(((ξ j : ℝ)) : ℂ)‖ ≤ ‖ξ‖ := by
  rw [Complex.norm_real]; exact PiLp.norm_apply_le ξ j

theorem stronglyMeasurable_Gs (hum : StronglyMeasurable u) :
    StronglyMeasurable (fun p : ES × ES => Gs u p.1 p.2) := by
  have hm : Measurable (fun p : ES × ES => Gs u p.1 p.2) := by
    unfold Gs
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    have h1 : Measurable (fun p : ES × ES => u (-(p.1 + p.2)) i) :=
      ((continuous_apply i).comp_stronglyMeasurable hum).measurable.comp
        (measurable_fst.add measurable_snd).neg
    have h2 : Measurable (fun p : ES × ES => (((p.1 + p.2) j : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ j).comp
        (continuous_fst.add continuous_snd))).measurable
    have h3 : Measurable (fun p : ES × ES => u p.1 j) :=
      ((continuous_apply j).comp_stronglyMeasurable hum).measurable.comp measurable_fst
    have h4 : Measurable (fun p : ES × ES => u p.2 i) :=
      ((continuous_apply i).comp_stronglyMeasurable hum).measurable.comp measurable_snd
    exact ((h1.mul h2).mul h3).mul h4
  exact hm.stronglyMeasurable

theorem norm_Gs_le (hb : ∀ ξ, ‖u ξ‖ ≤ R) (η ζ : ES) :
    ‖Gs u η ζ‖ ≤ 9 * R * ((‖η‖ * ‖u η‖) * ‖u ζ‖ + ‖u η‖ * (‖ζ‖ * ‖u ζ‖)) := by
  unfold Gs
  have hR : 0 ≤ R := (norm_nonneg _).trans (hb 0)
  have hterm : ∀ i j : Fin 3, ‖u (-(η + ζ)) i * (((η + ζ) j : ℝ) : ℂ) * u η j * u ζ i‖ ≤
      R * ((‖η‖ * ‖u η‖) * ‖u ζ‖ + ‖u η‖ * (‖ζ‖ * ‖u ζ‖)) := by
    intro i j
    rw [norm_mul, norm_mul, norm_mul]
    have a1 : ‖u (-(η + ζ)) i‖ ≤ R := (norm_le_pi_norm _ i).trans (hb _)
    have a2 : ‖(((η + ζ) j : ℝ) : ℂ)‖ ≤ ‖η‖ + ‖ζ‖ :=
      (norm_coord_ES_le _ j).trans (norm_add_le _ _)
    have a3 : ‖u η j‖ ≤ ‖u η‖ := norm_le_pi_norm _ j
    have a4 : ‖u ζ i‖ ≤ ‖u ζ‖ := norm_le_pi_norm _ i
    calc ‖u (-(η + ζ)) i‖ * ‖(((η + ζ) j : ℝ) : ℂ)‖ * ‖u η j‖ * ‖u ζ i‖
        ≤ R * (‖η‖ + ‖ζ‖) * ‖u η‖ * ‖u ζ‖ := by gcongr
      _ = R * ((‖η‖ * ‖u η‖) * ‖u ζ‖ + ‖u η‖ * (‖ζ‖ * ‖u ζ‖)) := by ring
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin 3, ‖∑ j : Fin 3, u (-(η + ζ)) i * (((η + ζ) j : ℝ) : ℂ) * u η j * u ζ i‖
      ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, R * ((‖η‖ * ‖u η‖) * ‖u ζ‖ + ‖u η‖ * (‖ζ‖ * ‖u ζ‖)) :=
        Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => hterm i j)
    _ = 9 * R * ((‖η‖ * ‖u η‖) * ‖u ζ‖ + ‖u η‖ * (‖ζ‖ * ‖u ζ‖)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring

theorem integrable_Gs (hum : StronglyMeasurable u) (hb : ∀ ξ, ‖u ξ‖ ≤ R)
    (hi0 : Integrable (fun ξ => ‖u ξ‖)) (hi1 : Integrable (fun ξ => ‖ξ‖ * ‖u ξ‖)) :
    Integrable (fun p : ES × ES => Gs u p.1 p.2) (volume.prod volume) := by
  refine Integrable.mono' (((hi1.mul_prod hi0).add (hi0.mul_prod hi1)).const_mul (9 * R))
    (stronglyMeasurable_Gs hum).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  exact norm_Gs_le hb p.1 p.2

/-- **Each shear slice integrates to zero** at a transversal `η`. -/
theorem integral_Gs_slice (η : ES) (hη : ∑ j : Fin 3, ((η j : ℝ) : ℂ) * u η j = 0) :
    ∫ ζ, Gs u η ζ = 0 := by
  set a : ES → ℂ := fun ζ => ∑ i : Fin 3, u (-(η + ζ)) i * u ζ i with ha
  set b : ES → ℂ := fun ζ => ∑ j : Fin 3, ((ζ j : ℝ) : ℂ) * u η j with hb
  have hG : ∀ ζ, Gs u η ζ = a ζ * b ζ := by
    intro ζ
    have hsplit : ∑ j : Fin 3, (((η + ζ) j : ℝ) : ℂ) * u η j = b ζ := by
      simp only [hb, PiLp.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, hη,
        zero_add]
    rw [ha, ← hsplit, Finset.sum_mul]
    unfold Gs
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hrefl : ∀ ζ, a (-η - ζ) * b (-η - ζ) = -(a ζ * b ζ) := by
    intro ζ
    have ha' : a (-η - ζ) = a ζ := by
      simp only [ha, show -η - ζ = -(η + ζ) by abel, show -(η + -(η + ζ)) = ζ by abel]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hb' : b (-η - ζ) = -b ζ := by
      simp only [hb, PiLp.sub_apply, PiLp.neg_apply, Complex.ofReal_sub, Complex.ofReal_neg,
        sub_mul, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib, hη, neg_zero,
        zero_sub]
    rw [ha', hb', mul_neg]
  have h := integral_sub_left_eq_self (fun ζ => a ζ * b ζ) (μ := (volume : Measure ES)) (-η)
  simp only [hrefl, integral_neg] at h
  simp_rw [hG]
  linear_combination (-1 / 2 : ℂ) * h

/-- The integrand in the original coordinates `(ξ, η)`. -/
def G0 (u : ES → ComplexSpace) (ξ η : ES) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, u (-ξ) i * ((ξ j : ℝ) : ℂ) * u η j * u (ξ - η) i

theorem G0_shear (u : ES → ComplexSpace) (η ζ : ES) : G0 u (η + ζ) η = Gs u η ζ := by
  unfold G0 Gs
  simp only [add_sub_cancel_left]

/-- **The trilinear cancellation.** -/
theorem trilinear_zero (hum : StronglyMeasurable u) (hb : ∀ ξ, ‖u ξ‖ ≤ R)
    (hi0 : Integrable (fun ξ => ‖u ξ‖)) (hi1 : Integrable (fun ξ => ‖ξ‖ * ‖u ξ‖))
    (htr : ∀ᵐ η ∂(volume : Measure ES), ∑ j : Fin 3, ((η j : ℝ) : ℂ) * u η j = 0) :
    ∫ ξ, ∑ i : Fin 3, u (-ξ) i * ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) *
      ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => u η i)) ξ = 0 := by
  have hR : 0 ≤ R := (norm_nonneg _).trans (hb 0)
  -- pointwise: the integrand is the `η`-integral of `G0`
  have hpt : ∀ ξ, (∑ i : Fin 3, u (-ξ) i * ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) *
      ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => u η i)) ξ) =
      ∫ η, G0 u ξ η := by
    intro ξ
    have hint : ∀ i j : Fin 3, Integrable (fun η => u η j * u (ξ - η) i) := by
      intro i j
      refine (hi0.mul_const R).mono' ?_ (Eventually.of_forall fun η => ?_)
      · exact (((continuous_apply j).comp_stronglyMeasurable hum).mul
          (((continuous_apply i).comp_stronglyMeasurable hum).comp_measurable
            (measurable_const.sub measurable_id))).aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_mul (norm_le_pi_norm _ j) ((norm_le_pi_norm _ i).trans (hb _))
          (norm_nonneg _) (norm_nonneg _)
    unfold G0
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      ((hint i j).const_mul (u (-ξ) i * ((ξ j : ℝ) : ℂ))).congr
        (Eventually.of_forall fun η => by simp only; ring)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ =>
      ((hint i j).const_mul (u (-ξ) i * ((ξ j : ℝ) : ℂ))).congr
        (Eventually.of_forall fun η => by simp only; ring), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    simp only; ring
  simp_rw [hpt]
  -- shear coordinates
  have hGs := integrable_Gs hum hb hi0 hi1
  set e := MeasurableEquiv.shearAddRight ES
  have hmp : MeasurePreserving e ((volume : Measure ES).prod volume)
      ((volume : Measure ES).prod volume) := measurePreserving_prod_add volume volume
  set G' : ES × ES → ℂ := fun p => G0 u p.2 p.1 with hG'
  have hcomp : G' ∘ e = fun p => Gs u p.1 p.2 := by
    funext p
    show G0 u (p.1 + p.2) p.1 = Gs u p.1 p.2
    exact G0_shear u p.1 p.2
  have hG'int : Integrable G' ((volume : Measure ES).prod volume) := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding, hcomp]; exact hGs
  have hswap : Integrable (Function.uncurry (G0 u)) ((volume : Measure ES).prod volume) :=
    hG'int.swap
  rw [integral_integral_swap hswap]
  have h1 : ∫ η, ∫ ξ, G0 u ξ η = ∫ p, G' p ∂((volume : Measure ES).prod volume) :=
    (integral_prod G' hG'int).symm
  rw [h1, ← hmp.integral_comp' G']
  have hce : (fun x => G' (e x)) = fun p => Gs u p.1 p.2 := hcomp
  rw [hce, integral_prod _ hGs]
  have h0 : (fun η => ∫ ζ, Gs u η ζ) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [htr] with η hη using integral_Gs_slice η hη
  rw [integral_congr_ae h0, integral_zero]

end Navier.Analysis.WienerEnergyCancel

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerEnergyCancel.trilinear_zero
