import Navier.Analysis.LeiLinPositiveRestartFractional
import Navier.Analysis.GalerkinBasis

/-!
# What the finite-mode energy identity supplies at a positive restart

The checked Galerkin construction controls the physical modal enstrophy in
unweighted `L¹_t` (equivalently, its square root in unweighted `L²_t`).  This
file records the resulting backward-*vanishing* weighted estimate and the
sharp obstruction to replacing that weight by the backward-singular Hardy
weight required at a prescribed terminal time.

There is deliberately no bridge from this physical Galerkin trajectory to the
separately constructed Lei--Lin critical mild path: no such identification is
present in the current API.
-/

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Topology

namespace Navier.Analysis.LeiLinPositiveRestartEnergy

open Navier.Analysis.GalerkinBasis
open Navier.Analysis.LeiLinPositiveRestartBootstrap
open Navier.Analysis.LeiLinPositiveRestartFractional

/-- Modal enstrophy is literally the square of its nonnegative dissipation
moment. -/
theorem sqrt_coefficientEnstrophy_sq (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) :
    Real.sqrt (W.coefficientEnstrophy a) ^ 2 = W.coefficientEnstrophy a := by
  apply Real.sq_sqrt
  unfold GalerkinBasisFamily.coefficientEnstrophy
  exact integral_nonneg fun _ => sq_nonneg _

/-- The exact Galerkin energy identity gives the honest unweighted square
budget: `sqrt Ω` lies in `L²_t`, with mass bounded by the initial kinetic
energy.  The statement is kept in the equivalent `Ω` form so that it composes
directly with the certified identity. -/
theorem coefficientFlow_unweighted_enstrophy_energy_le
    (W : GalerkinBasisFamily) {ν : ℝ}
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Ici (0 : ℝ)) t)
    (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    2 * ν * (∫ s in Ioc (0 : ℝ) T, W.coefficientEnstrophy (c m s)) ≤
      ‖c m 0‖ ^ 2 := by
  have hid := coefficientFlow_energy_identity W c hc m hT
  nlinarith [sq_nonneg ‖c m T‖]

/-- The strongest backward weight obtained for free from the Galerkin energy
identity is a *vanishing* weight.  It is coefficientwise and loses only the
interval length (the usual initial projection bound makes it uniform in the
mode cutoff).  Here `Ω = (sqrt Ω)²`, so this is the actual finite-mode
dissipation-square estimate supplied by coercivity; it is not a Lei--Lin `X2`
graph moment, and its weight has the opposite sign from the terminal Hardy
weight. -/
theorem coefficientFlow_backwardVanishing_enstrophy_energy_le
    (W : GalerkinBasisFamily) {ν : ℝ} (hν : 0 < ν)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Ici (0 : ℝ)) t)
    (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ s in Ioc (0 : ℝ) T,
      backwardTime T s * W.coefficientEnstrophy (c m s)) ≤
        T * (‖c m 0‖ ^ 2 / (2 * ν)) := by
  have hΩcontIcc : ContinuousOn
      (fun s => W.coefficientEnstrophy (c m s)) (Icc (0 : ℝ) T) :=
    (coefficientFlow_enstrophy_continuousOn W c hc m).mono Icc_subset_Ici_self
  have hback : Continuous (fun s : ℝ => backwardTime T s) := by
    exact (continuous_const.sub continuous_id).max continuous_const
  have hweighted : IntegrableOn
      (fun s => backwardTime T s * W.coefficientEnstrophy (c m s))
      (Ioc (0 : ℝ) T) :=
    ((hback.continuousOn.mul hΩcontIcc).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hmajor : IntegrableOn
      (fun s => T * W.coefficientEnstrophy (c m s)) (Ioc (0 : ℝ) T) :=
    ((continuous_const.continuousOn.mul hΩcontIcc).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hpoint : ∀ s ∈ Ioc (0 : ℝ) T,
      backwardTime T s * W.coefficientEnstrophy (c m s) ≤
        T * W.coefficientEnstrophy (c m s) := by
    intro s hs
    have hΩ : 0 ≤ W.coefficientEnstrophy (c m s) := by
      unfold GalerkinBasisFamily.coefficientEnstrophy
      exact integral_nonneg fun _ => sq_nonneg _
    have hback_le : backwardTime T s ≤ T := by
      rw [backwardTime, max_eq_left (sub_nonneg.mpr hs.2)]
      linarith [hs.1]
    exact mul_le_mul_of_nonneg_right hback_le hΩ
  have hmono :
      (∫ s in Ioc (0 : ℝ) T,
        backwardTime T s * W.coefficientEnstrophy (c m s)) ≤
          ∫ s in Ioc (0 : ℝ) T, T * W.coefficientEnstrophy (c m s) :=
    setIntegral_mono_on hweighted hmajor measurableSet_Ioc hpoint
  have hunweighted :
      (∫ s in Ioc (0 : ℝ) T, W.coefficientEnstrophy (c m s)) ≤
        ‖c m 0‖ ^ 2 / (2 * ν) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * ν)).2
    nlinarith [coefficientFlow_unweighted_enstrophy_energy_le W c hc m hT]
  calc
    (∫ s in Ioc (0 : ℝ) T,
        backwardTime T s * W.coefficientEnstrophy (c m s))
        ≤ ∫ s in Ioc (0 : ℝ) T, T * W.coefficientEnstrophy (c m s) := hmono
    _ = T * (∫ s in Ioc (0 : ℝ) T,
        W.coefficientEnstrophy (c m s)) := by rw [integral_const_mul]
    _ ≤ T * (‖c m 0‖ ^ 2 / (2 * ν)) :=
      mul_le_mul_of_nonneg_left hunweighted hT

/-- A simple kernel witness: unweighted square energy does not imply any
positive backward-singular square energy at a prescribed endpoint. -/
theorem not_intervalIntegrable_backwardSingular_sq_of_unweighted_sq :
    IntervalIntegrable (fun _s : ℝ => (1 : ℝ)) volume 0 1 ∧
      ¬ IntervalIntegrable
        (fun s : ℝ => backwardTime 1 s ^ (-(1 : ℝ)) * (1 : ℝ) ^ 2)
        volume 0 1 := by
  constructor
  · exact intervalIntegrable_const
  · intro h
    have h' : IntervalIntegrable (fun s : ℝ => (1 - s)⁻¹) volume 0 1 := by
      apply h.congr
      intro s hs
      have hs' : s ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hs
      have hnonneg : 0 ≤ 1 - s := sub_nonneg.mpr hs'.2
      simp [backwardTime, max_eq_left hnonneg, Real.rpow_neg_one]
    have hsub : IntervalIntegrable (fun s : ℝ => (s - 1)⁻¹) volume 0 1 := by
      convert h'.neg using 1
      funext s
      rw [show s - 1 = -(1 - s) by ring]
      exact inv_neg
    simp at hsub

/-- **Sharp endpoint falsification for every positive Hardy exponent.**

For `E(τ) = τ^(-1 + β/2)`, the unweighted energy density is integrable, while
`τ^-β E(τ) = τ^(-1-β/2)` is not.  Thus no positive backward-singular weight is
a formal consequence of the unweighted Galerkin energy budget, even before
the separate Galerkin-to-mild-path identification problem is considered. -/
theorem exists_unweightedEnergy_not_backwardSingular
    (β : ℝ) (hβ : 0 < β) :
    ∃ E : ℝ → ℝ,
      IntervalIntegrable E volume 0 1 ∧
      ¬ IntervalIntegrable (fun τ => τ ^ (-β) * E τ) volume 0 1 := by
  refine ⟨fun τ => τ ^ (-(1 : ℝ) + β / 2), ?_, ?_⟩
  · exact intervalIntegrable_rpow_zero (by norm_num) (by linarith)
  · intro hsingular
    have hpower : IntervalIntegrable
        (fun τ : ℝ => τ ^ (-(1 : ℝ) - β / 2)) volume 0 1 := by
      apply hsingular.congr
      intro τ hτ
      have hτ' : τ ∈ Ioc (0 : ℝ) 1 := by
        simpa [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hτ
      change τ ^ (-β) * τ ^ (-(1 : ℝ) + β / 2) =
        τ ^ (-(1 : ℝ) - β / 2)
      calc
        τ ^ (-β) * τ ^ (-(1 : ℝ) + β / 2) =
            τ ^ (-β + (-(1 : ℝ) + β / 2)) :=
          (Real.rpow_add hτ'.1 _ _).symm
        _ = τ ^ (-(1 : ℝ) - β / 2) := by congr 1; ring
    have hIoo : IntegrableOn
        (fun τ : ℝ => τ ^ (-(1 : ℝ) - β / 2)) (Ioo 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (show (0 : ℝ) ≤ 1 by norm_num)).mp hpower
    have hexp :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hIoo
    linarith

end Navier.Analysis.LeiLinPositiveRestartEnergy

#print axioms Navier.Analysis.LeiLinPositiveRestartEnergy.coefficientFlow_unweighted_enstrophy_energy_le
#print axioms Navier.Analysis.LeiLinPositiveRestartEnergy.sqrt_coefficientEnstrophy_sq
#print axioms Navier.Analysis.LeiLinPositiveRestartEnergy.coefficientFlow_backwardVanishing_enstrophy_energy_le
#print axioms Navier.Analysis.LeiLinPositiveRestartEnergy.not_intervalIntegrable_backwardSingular_sq_of_unweighted_sq
#print axioms Navier.Analysis.LeiLinPositiveRestartEnergy.exists_unweightedEnergy_not_backwardSingular
