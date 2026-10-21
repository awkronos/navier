import Navier.Transfer.LatticeExtensionTransport
import Navier.Analysis.ContinuousLeiLinRecentTailMoment

/-!
# The convolution-vs-extension defect, quantified as a BUDGET

`Navier/Transfer/LatticeExtensionTransport` lands the `X⁻¹`-weighted bilinear
amplitude budget of the cell extension and proves it factorizes EXACTLY into the
product of the two coordinate `X⁰` masses
(`sum_convolution_eq_coordinateX0Mass_mul`).  At that weight the
convolution-vs-extension overlap defect contributes nothing: the kernel witness
that falsifies symbol transport (`ext(δ_{m+n}) ≠ ext δ_m ⋆ ext δ_n`, overlap
volume `1/4` at `ξ = m+n+(3/4,0,0)`) lives in the symbol, while the `X⁻¹` budget
integrates precisely the quantity the symbol defect moves.  This is the measured
answer to the wave's step (c) for the weight the peer mixed-estimate family
actually consumes: the correction term is `0`, not a hidden premise — so the
falsification branch is not triggered at budget level.

This file supplies the next weight up, which is the one the Duhamel-side feed
asks for: the `X¹`-weighted symbol mass `∫ ξ, ‖ξ‖ · ‖B(a,b) ξ‖`.  There the
defect is not zero.  The peer majorant `continuousNavierBilinear_majorant`
carries one explicit power of the output frequency, so allocating that power
across the convolution costs exactly one degree of input moment:

```text
∫ ‖ξ‖ · ‖B(a,b) ξ‖  ≤  2 · Σᵢⱼ ( M₂(aⱼ)·M₀(bᵢ) + M₀(aⱼ)·M₂(bᵢ) )
```

with `M₂(f) = ∫ ‖η‖² · ‖f η‖` and `2 = (2:ℝ)^(2-1)` the triangle allocation
(`frequency_pow_product_split`).  That is defective-symbol transport stated as a
defect BUDGET: the correction is an explicit, finite, named feed rather than
something assumed away.

Carrier boundary, named rather than hidden: `WeightedLatticeBanach` is plain
`ℓ¹` after the weight division, so it bounds `M₀`
(`integral_latticeExtensionCoord_le`, `≤ ‖u‖`) and `M₁`
(`normX1_latticeExtensionCoord_le`, `≤ C₁‖u‖`) and NOTHING at `M₂`; no
element-independent `M₂` budget exists on this carrier, and the repository's own
language for the extra feed is the hypothesis `LatticePolynomialMoment s u`
(`Navier/Analysis/CriticalMildPolynomialMomentConvolution`), whose
`outputDerivativeWeight_le_inputPolynomialWeights` states the same one-degree
cost on the discrete side.  The instantiated theorem below therefore carries
`M₂` of the two extensions as the explicit named budgets `Au`, `Av`: the
correction does not diverge at any scale (it is a finite number fed in), so
budget transport survives — its cost is the degree, and that cost is the honest
boundary of this lane's deliverable.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Navier.Transfer.MildSelfMapDefectBudget

open MeasureTheory Set BigOperators Filter Topology
open scoped ENNReal
open Navier
open Navier.Analysis
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinRecentTailMoment
open Navier.Transfer.LatticeExtensionTransport

/-! ## The degree-allocation defect budget, general form -/

/-- Defect budget, general form: the `X¹`-weighted mass of the continuous Navier
bilinear symbol of two profiles is at most the one-degree allocation sum
`2 · Σᵢⱼ (M₂(aⱼ)M₀(bᵢ) + M₀(aⱼ)M₂(bᵢ))`.  The lost degree is the output
frequency of `continuousNavierBilinear_majorant`; nothing else enters. -/
theorem integral_normX1_bilinear_le_moment_allocation (a b : ES → ComplexSpace)
    (ha : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => a η j))
    (hb : ∀ i : Fin 3, AEStronglyMeasurable (fun η : ES => b η i))
    (ha0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖a η j‖))
    (hb0 : ∀ i : Fin 3, Integrable (fun η : ES => ‖b η i‖))
    (ha2 : ∀ j : Fin 3, Integrable (fun η : ES => ‖η‖ ^ 2 * ‖a η j‖))
    (hb2 : ∀ i : Fin 3, Integrable (fun η : ES => ‖η‖ ^ 2 * ‖b η i‖)) :
    ∫ ξ : ES, ‖ξ‖ * complexEuclideanNorm (continuousNavierBilinear a b ξ) ≤
      (2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
        ((∫ η : ES, ‖η‖ ^ 2 * ‖a η j‖) * (∫ η : ES, ‖b η i‖) +
          (∫ η : ES, ‖a η j‖) * (∫ η : ES, ‖η‖ ^ 2 * ‖b η i‖)) := by
  -- one power of the output frequency, allocated across the two convolution inputs
  have hpt (ξ : ES) : ‖ξ‖ * complexEuclideanNorm (continuousNavierBilinear a b ξ) ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ ^ 2 *
        convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ := by
    calc ‖ξ‖ * complexEuclideanNorm (continuousNavierBilinear a b ξ)
        ≤ ‖ξ‖ * ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ *
              convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ :=
          mul_le_mul_of_nonneg_left (continuousNavierBilinear_majorant a b ξ)
            (norm_nonneg ξ)
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ ^ 2 *
              convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ := by
          simp only [Finset.mul_sum, pow_two, mul_assoc]
  have hconvInt (i j : Fin 3) : Integrable (fun ξ : ES => ‖ξ‖ ^ 2 *
      convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ) :=
    integrable_polynomial_weighted_convolution 2 (fun η : ES => ‖a η j‖)
      (fun η : ES => ‖b η i‖) (ha0 j) (hb0 i) (ha2 j) (hb2 i)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hR : Integrable (fun ξ : ES => ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ ^ 2 *
      convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hconvInt i j
  have hnout (ξ : ES) : 0 ≤ complexEuclideanNorm (continuousNavierBilinear a b ξ) := by
    unfold complexEuclideanNorm
    exact norm_nonneg _
  have ham : AEStronglyMeasurable (fun ξ : ES => ‖ξ‖ *
      complexEuclideanNorm (continuousNavierBilinear a b ξ)) :=
    continuous_norm.aestronglyMeasurable.mul
      (continuousNavierBilinear_aestronglyMeasurable a b ha hb ha0 hb0).norm
  -- `Integrable.mono'` in this Mathlib bounds `‖g‖` by the (already nonnegative)
  -- dominating integrand, so only the LEFT outer norm has to be stripped.  The
  -- equality is proved on a closed term: a `rw` with the lemma itself
  -- over-cleared occurrences, and a trailing `=` calc step re-anchored the chain.
  have hL : Integrable (fun ξ : ES => ‖ξ‖ *
      complexEuclideanNorm (continuousNavierBilinear a b ξ)) := by
    refine hR.mono' ham ?_
    refine ae_of_all volume fun ξ => ?_
    have hl : ‖‖ξ‖ * complexEuclideanNorm (continuousNavierBilinear a b ξ)‖ =
        ‖ξ‖ * complexEuclideanNorm (continuousNavierBilinear a b ξ) :=
      Real.norm_of_nonneg (mul_nonneg (norm_nonneg ξ) (hnout ξ))
    exact le_trans (le_of_eq hl) (hpt ξ)
  have hinner (i : Fin 3) : Integrable (fun ξ : ES => ∑ j : Fin 3, ‖ξ‖ ^ 2 *
      convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ) :=
    integrable_finsetSum Finset.univ fun j _ => hconvInt i j
  have hsum : (∫ ξ : ES, ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ ^ 2 *
        convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ)
      = ∑ i : Fin 3, ∑ j : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ 2 *
          convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ := by
    refine Eq.trans (integral_finsetSum Finset.univ fun i _ => hinner i) ?_
    refine Finset.sum_congr rfl fun i _ =>
      integral_finsetSum Finset.univ (fun j _ => hconvInt i j)
  calc (∫ ξ : ES, ‖ξ‖ * complexEuclideanNorm (continuousNavierBilinear a b ξ))
      ≤ ∫ ξ : ES, ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ ^ 2 *
            convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ :=
          integral_mono_ae hL hR (ae_of_all volume fun ξ => hpt ξ)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ 2 *
            convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ := hsum
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, (2 : ℝ) *
            ((∫ η : ES, ‖η‖ ^ 2 * ‖a η j‖) * (∫ η : ES, ‖b η i‖) +
              (∫ η : ES, ‖a η j‖) * (∫ η : ES, ‖η‖ ^ 2 * ‖b η i‖)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            (polynomial_weighted_convolution_mass_le 2 (fun η : ES => ‖a η j‖)
              (fun η : ES => ‖b η i‖) (ha0 j) (hb0 i) (ha2 j) (hb2 i)
              (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).trans
              (by rw [show (2 : ℝ) ^ (2 - 1) = (2 : ℝ) from by norm_num])
    _ = (2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
            ((∫ η : ES, ‖η‖ ^ 2 * ‖a η j‖) * (∫ η : ES, ‖b η i‖) +
              (∫ η : ES, ‖a η j‖) * (∫ η : ES, ‖η‖ ^ 2 * ‖b η i‖)) := by
          simp only [Finset.mul_sum]

/-! ## Instantiation at the cell extension -/

/-- Defect budget at the cell extension: supplying the quadratic frequency feed
of the two extensions as the named budgets `Au`, `Av`, the `X¹`-weighted
bilinear symbol mass is at most `18 · (Au · ‖v‖ + ‖u‖ · Av)`.  The `X⁰` factors
are the landed lattice budgets (`∫ ξ, ‖latticeExtension u ξ j‖ ≤ ‖u‖`,
`integral_latticeExtensionCoord_le`); the `M₂` factors are exactly the feed the
carrier does not supply, and `LatticePolynomialMoment 2 u` is the repository's
named supplier of it.  Nine coordinate pairs, allocation factor `2` each. -/
theorem integral_normX1_bilinear_latticeExtension_le
    (u v : WeightedLatticeBanach) (Au Av : ℝ)
    (hu2 : ∀ j : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖latticeExtension u ξ j‖))
    (hv2 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖latticeExtension v ξ i‖))
    (huA : ∀ j : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖latticeExtension u ξ j‖ ≤ Au)
    (hvA : ∀ i : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖latticeExtension v ξ i‖ ≤ Av) :
    ∫ ξ : ES, ‖ξ‖ * complexEuclideanNorm
        (continuousNavierBilinear (latticeExtension u) (latticeExtension v) ξ) ≤
      (18 : ℝ) * (Au * ‖v‖ + ‖u‖ * Av) := by
  have h0u (j : Fin 3) : 0 ≤ ∫ η : ES, ‖latticeExtension u η j‖ :=
    integral_nonneg fun η : ES => norm_nonneg _
  have h0v (i : Fin 3) : 0 ≤ ∫ η : ES, ‖latticeExtension v η i‖ :=
    integral_nonneg fun η : ES => norm_nonneg _
  have h2u (j : Fin 3) : 0 ≤ ∫ η : ES, ‖η‖ ^ 2 * ‖latticeExtension u η j‖ :=
    integral_nonneg fun η : ES =>
      mul_nonneg (pow_nonneg (norm_nonneg η) 2) (norm_nonneg _)
  have h2v (i : Fin 3) : 0 ≤ ∫ η : ES, ‖η‖ ^ 2 * ‖latticeExtension v η i‖ :=
    integral_nonneg fun η : ES =>
      mul_nonneg (pow_nonneg (norm_nonneg η) 2) (norm_nonneg _)
  have hAu : 0 ≤ Au := le_trans (h2u ⟨0, by norm_num⟩) (huA ⟨0, by norm_num⟩)
  have hAv : 0 ≤ Av := le_trans (h2v ⟨0, by norm_num⟩) (hvA ⟨0, by norm_num⟩)
  have hterm (i j : Fin 3) :
      (∫ η : ES, ‖η‖ ^ 2 * ‖latticeExtension u η j‖) * (∫ η : ES, ‖latticeExtension v η i‖) +
          (∫ η : ES, ‖latticeExtension u η j‖) *
            (∫ η : ES, ‖η‖ ^ 2 * ‖latticeExtension v η i‖)
        ≤ Au * ‖v‖ + ‖u‖ * Av := by
    refine add_le_add ?_ ?_
    · refine le_trans (mul_le_mul_of_nonneg_right (huA j) (h0v i)) ?_
      exact mul_le_mul_of_nonneg_left (integral_latticeExtensionCoord_le v i) hAu
    · refine le_trans (mul_le_mul_of_nonneg_left (hvA i) (h0u j)) ?_
      exact mul_le_mul_of_nonneg_right (integral_latticeExtensionCoord_le u j) hAv
  have hsum9 : ∑ i : Fin 3, ∑ j : Fin 3, (Au * ‖v‖ + ‖u‖ * Av) =
      (9 : ℝ) * (Au * ‖v‖ + ‖u‖ * Av) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  refine le_trans (integral_normX1_bilinear_le_moment_allocation (latticeExtension u)
    (latticeExtension v) (aestm_latticeExtensionCoord u) (aestm_latticeExtensionCoord v)
    (integrable_norm_latticeExtensionCoord u) (integrable_norm_latticeExtensionCoord v)
    hu2 hv2) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j)
    (by norm_num : (0 : ℝ) ≤ 2)) ?_
  rw [hsum9]
  exact le_of_eq (by ring)

/-- The constant `18` of the instantiated budget, as visible arithmetic: the
allocation factor `2` (one lost degree) times the nine coordinate pairs. -/
theorem nsb_defect_constant : (2 : ℝ) * (9 : ℝ) = (18 : ℝ) := by norm_num

end Navier.Transfer.MildSelfMapDefectBudget

#print axioms Navier.Transfer.MildSelfMapDefectBudget.integral_normX1_bilinear_le_moment_allocation
#print axioms Navier.Transfer.MildSelfMapDefectBudget.integral_normX1_bilinear_latticeExtension_le
