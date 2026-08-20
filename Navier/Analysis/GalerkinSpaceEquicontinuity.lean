import Navier.Analysis.LerayWeak
import Navier.Analysis.DivFreeGradientEnstrophy
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Spatial equicontinuity of the Galerkin modal family (Riesz–Fréchet–Kolmogorov input)

This file discharges the `hspace` residual of
`GalerkinBasis.exists_galerkinModeData`: the finite-mode Galerkin
approximants are uniformly spatially-translation equicontinuous.

## Route

The banked `LerayWeak.spaceEquicontinuous_of_dissipation_bound` reduces
`SpaceEquicontinuous` to four analytic inputs, all certified here for a modal
family `u_m(t) = Σᵢ cᵢ(t) • wᵢ` with Schwartz modes `wᵢ` and continuous
coefficients:

1. **Brezis Prop. 9.3 per slice** — `∫ ‖f(x+y) − f(x)‖² ≤ ‖y‖² ∫ ‖Df‖²` for
   a single Schwartz field (`brezis_schwartz`), from the repo's
   `RieszKolmogorov.integral_norm_sub_sq_le_mul_integral_fderiv_sq` with all
   six integrability side conditions discharged by rapid decay.
2. **The dissipation bound** — `∫₀^T ∫ ‖D u_m(t)‖² ≤ 3C` from the enstrophy
   budget via
   `DivFreeGradientEnstrophy.integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree`.
   This is exactly where the divergence-free basis earns its keep.
3. **Time integrability** of the translation and derivative energies —
   joint continuity in `(t, x)` plus Schwartz decay envelopes, via strong
   measurability of partial integrals.

## Axiom policy

Everything is proved from the banked layers and mathlib; the audit target is
`{propext, Classical.choice, Quot.sound}` only.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped LineDeriv Matrix

namespace Navier.Analysis.GalerkinSpaceEquicontinuity

open Navier
open Navier.Analysis.LerayWeak
open Navier.Analysis.DivFreeGradientEnstrophy
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.EnergyNormBridge

section LocalCopies

/-- Divergence of a finite `ℝ`-combination of Schwartz fields is the
combination of the divergences (linearity of the Fréchet derivative).
Self-contained copy of the `GalerkinBasis` lemma pattern: this file sits
*upstream* of `GalerkinBasis` and must not import it. -/
private theorem schwartz_differentiableAt' (f : SchwartzVelocity) (x : Space) :
    DifferentiableAt ℝ (fun y => f y) x :=
  ((f.smooth 1).differentiable (by norm_num)).differentiableAt

/-- The static divergence is additive on differentiable summands
(self-contained copy of the `GalerkinBasis` lemma; this file is upstream of
`GalerkinBasis` and must not import it). -/
private theorem staticDivergence_add' (f g : VelocityField) (x : Space)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    staticDivergence (fun y => f y + g y) x = staticDivergence f x + staticDivergence g x := by
  unfold staticDivergence
  rw [← Finset.sum_add_distrib]
  congr 1; funext i
  rw [show (fun y => f y + g y) = f + g from rfl, fderiv_add hf hg]
  simp

/-- Finite `ℝ`-combinations of divergence-free Schwartz fields are
divergence-free (self-contained copy of
`GalerkinBasis.divergenceFreeInitial_sum_smul`, via
`Navier.staticDivergence_const_smul` from `VectorCalculus`). -/
private theorem divFree_sum_smul {m : ℕ} (s : Finset (Fin m)) (c : Fin m → ℝ)
    (v : Fin m → SchwartzVelocity) (hv : ∀ j, DivergenceFreeInitial (v j)) :
    DivergenceFreeInitial (∑ j ∈ s, c j • v j) := by
  intro x
  induction s using Finset.induction_on with
  | empty => simp [staticDivergence]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hcoe : (fun y => (c a • v a + ∑ j ∈ s, c j • v j : SchwartzVelocity) y) =
        fun y => (c a • v a : SchwartzVelocity) y +
          (∑ j ∈ s, c j • v j : SchwartzVelocity) y := by
      funext y; simp
    rw [hcoe, staticDivergence_add' _ _ x
      (schwartz_differentiableAt' _ x) (schwartz_differentiableAt' _ x)]
    have h1 : staticDivergence (fun y => (c a • v a : SchwartzVelocity) y) x = 0 := by
      have hcoe2 : (fun y => (c a • v a : SchwartzVelocity) y) =
          fun y => c a • (v a) y := by funext y; simp
      rw [hcoe2, Navier.staticDivergence_const_smul _ _ _ (schwartz_differentiableAt' _ x),
        hv a x, mul_zero]
    rw [h1, ih, add_zero]

/-- The curl as a continuous linear operator on Schwartz velocity fields
(self-contained copy of `GalerkinBasis.curlSchwartzCLM`; this file is
upstream of `GalerkinBasis`). -/
private noncomputable def curlCLM : SchwartzVelocity →L[ℝ] SchwartzVelocity :=
  ∑ i : Fin 3,
    (SchwartzMap.postcompCLM (𝕜 := ℝ)
      (crossProduct (basisVector i)).toContinuousLinearMap).comp
      (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i))

private theorem curlCLM_apply (u : SchwartzVelocity) (x : Space) :
    curlCLM u x = staticCurl u x := by
  simp [curlCLM, staticCurl, SchwartzMap.lineDerivOp_apply_eq_fderiv]

end LocalCopies

section Decay

/-- Rapid decay, squared form: a Schwartz map's squared norm is dominated by
`D / (1 + ‖x‖⁴)`. -/
theorem schwartz_norm_sq_decay {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap Space F) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : Space, ‖f x‖ ^ 2 ≤ D / (1 + ‖x‖ ^ 4) := by
  obtain ⟨C0, hC0pos, hC0⟩ := f.decay 0 0
  obtain ⟨C4, hC4pos, hC4⟩ := f.decay 4 0
  have h0 : ∀ x, ‖f x‖ ≤ C0 := by
    intro x
    have h := hC0 x
    simpa using h
  have h4 : ∀ x, ‖x‖ ^ 4 * ‖f x‖ ≤ C4 := by
    intro x
    have h := hC4 x
    simpa using h
  refine ⟨C0 ^ 2 + C4 * C0, by positivity, fun x => ?_⟩
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 4)]
  calc ‖f x‖ ^ 2 * (1 + ‖x‖ ^ 4) = ‖f x‖ ^ 2 + (‖x‖ ^ 4 * ‖f x‖) * ‖f x‖ := by ring
    _ ≤ C0 ^ 2 + C4 * C0 :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) (h0 x) 2)
          (mul_le_mul (h4 x) (h0 x) (norm_nonneg _) hC4pos.le)

/-- The quadratic Bessel weight is integrable on `Space = ℝ³` (dimension 3 <
4).  Self-contained copy of the short `BKMLogBootstrap` proof, inlined to
decouple this file's build from that module. -/
theorem integrable_inv_one_add_normSq_sq :
    Integrable (fun ξ : Space => (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) := by
  have hr : (Module.finrank ℝ Space : ℝ) < 4 := by
    have h3 : Module.finrank ℝ Space = 3 := by simp
    rw [h3]; norm_num
  refine (integrable_rpow_neg_one_add_norm_sq (E := Space) (μ := volume)
    (r := 4) hr).congr ?_
  filter_upwards with ξ
  rw [show (-4 : ℝ) / 2 = -(2 : ℕ) by norm_num, Real.rpow_neg (by positivity),
    Real.rpow_natCast]

/-- The quartic Bessel weight is integrable on `Space = ℝ³`:
`(1 + ‖x‖⁴)⁻¹ ≤ 2·(1 + ‖x‖²)⁻²` since `(1 + t²)² ≤ 2(1 + t⁴)`. -/
theorem integrable_inv_one_add_norm_four :
    Integrable (fun x : Space => ((1 : ℝ) + ‖x‖ ^ 4)⁻¹) := by
  refine (integrable_inv_one_add_normSq_sq.const_mul 2).mono'
    (((Continuous.const_add (continuous_norm.pow 4) (1 : ℝ)).inv₀
      (fun x => ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 4))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have hsq : (1 + ‖x‖ ^ 2) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 4) := by
    nlinarith [sq_nonneg (‖x‖ ^ 2 - 1)]
  have h1 : (0 : ℝ) < 1 + ‖x‖ ^ 4 := by positivity
  have h2 : (0 : ℝ) < (1 + ‖x‖ ^ 2) ^ 2 := by positivity
  rw [inv_le_iff_one_le_mul₀ h1]
  rw [show (2 : ℝ) * ((1 + ‖x‖ ^ 2) ^ 2)⁻¹ * (1 + ‖x‖ ^ 4)
      = 2 * (1 + ‖x‖ ^ 4) / (1 + ‖x‖ ^ 2) ^ 2 by
    rw [div_eq_mul_inv]; ring]
  rw [le_div_iff₀ h2, one_mul]
  exact hsq

/-- The Peetre inequality for the quartic weight, valid for every
displacement. -/
theorem one_add_norm_four_le_peetre (x z : Space) :
    (1 : ℝ) + ‖x‖ ^ 4 ≤ 8 * (1 + ‖x + z‖ ^ 4) * (1 + ‖z‖ ^ 4) := by
  have htr : ‖x‖ ≤ ‖x + z‖ + ‖z‖ := by
    have h : x = (x + z) - z := by rw [add_sub_cancel_right]
    conv_lhs => rw [h]
    exact norm_sub_le _ _
  have hstep : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
    intro a b ha hb
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a * b),
      mul_nonneg ha hb]
  have h4 : ‖x‖ ^ 4 ≤ 8 * (‖x + z‖ ^ 4 + ‖z‖ ^ 4) :=
    (pow_le_pow_left₀ (norm_nonneg _) htr 4).trans
      (hstep _ _ (norm_nonneg _) (norm_nonneg _))
  nlinarith [h4, norm_nonneg (x + z), norm_nonneg z,
    mul_nonneg (by positivity : (0 : ℝ) ≤ ‖x + z‖ ^ 4)
      (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 4)]

/-- **Translate envelope (all shifts).**  A Schwartz map's squared norm along
any translate is dominated by an `x`-integrable envelope times a scalar
weight in the shift. -/
theorem schwartz_translate_envelope {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap Space F) (y : Space) :
    ∃ D : ℝ, 0 < D ∧ ∀ (s : ℝ) (x : Space),
      ‖f (x + s • y)‖ ^ 2 ≤ D * (1 + ‖s • y‖ ^ 4) / (1 + ‖x‖ ^ 4) := by
  obtain ⟨D0, hD0pos, hD0⟩ := schwartz_norm_sq_decay f
  refine ⟨8 * D0, by positivity, fun s x => ?_⟩
  calc ‖f (x + s • y)‖ ^ 2 ≤ D0 / (1 + ‖x + s • y‖ ^ 4) := hD0 _
    _ ≤ 8 * D0 * (1 + ‖s • y‖ ^ 4) / (1 + ‖x‖ ^ 4) := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + ‖x + s • y‖ ^ 4)
          (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 4)]
        calc D0 * (1 + ‖x‖ ^ 4)
            ≤ D0 * (8 * (1 + ‖x + s • y‖ ^ 4) * (1 + ‖s • y‖ ^ 4)) :=
              mul_le_mul_of_nonneg_left (one_add_norm_four_le_peetre x (s • y)) hD0pos.le
          _ = 8 * D0 * (1 + ‖s • y‖ ^ 4) * (1 + ‖x + s • y‖ ^ 4) := by ring

/-- The squared norm of a Schwartz map is integrable. -/
theorem schwartz_integrable_norm_sq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap Space F) : Integrable (fun x : Space => ‖f x‖ ^ 2) := by
  obtain ⟨D, hDpos, hD⟩ := schwartz_norm_sq_decay f
  refine (integrable_inv_one_add_norm_four.const_mul D).mono'
    (f.continuous.norm.pow 2 |>.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact hD x

/-- The squared norm of a translate of a Schwartz map is integrable. -/
theorem schwartz_translate_integrable_norm_sq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : SchwartzMap Space F) (y : Space) :
    Integrable (fun x : Space => ‖f (x + y)‖ ^ 2) := by
  obtain ⟨D, hDpos, hD⟩ := schwartz_translate_envelope f y
  have hbound : ∀ x : Space, ‖f (x + y)‖ ^ 2 ≤ D * (1 + ‖y‖ ^ 4) / (1 + ‖x‖ ^ 4) := by
    intro x
    have h := hD 1 x
    rwa [one_smul] at h
  refine ((integrable_inv_one_add_norm_four.const_mul (D * (1 + ‖y‖ ^ 4)))).mono'
    (((f.continuous.comp (continuous_id.add continuous_const))).norm.pow 2
      |>.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact hbound x

end Decay

section SquareSumIntegrability

/-- The product of two square-integrable nonnegative-style norm functions is
integrable, via `ab ≤ (a² + b²)/2`. -/
theorem integrable_norm_mul_of_sq {g h : Space → ℝ}
    (hg : Integrable (fun x => (g x) ^ 2)) (hh : Integrable (fun x => (h x) ^ 2))
    (hgmeas : AEStronglyMeasurable g volume) (hhmeas : AEStronglyMeasurable h volume)
    (hg_nn : ∀ x, 0 ≤ g x) (hh_nn : ∀ x, 0 ≤ h x) :
    Integrable (fun x : Space => g x * h x) := by
  refine (((hg.add hh).const_mul (1 / 2))).mono' (hgmeas.mul hhmeas)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (hg_nn x) (hh_nn x))]
  show g x * h x ≤ (1 / 2 : ℝ) * (g x ^ 2 + h x ^ 2)
  have h := two_mul_le_add_sq (g x) (h x)
  linarith [h]

/-- A weighted sum of squared-integrable functions is square-integrable. -/
theorem integrable_sq_sum {ι : Type*} [Fintype ι] {g : ι → Space → ℝ}
    (hg : ∀ i, Integrable (fun x => (g i x) ^ 2))
    (hgmeas : ∀ i, AEStronglyMeasurable (g i) volume) (hg_nn : ∀ i x, 0 ≤ g i x)
    (K : ι → ℝ) :
    Integrable (fun x : Space => (∑ i, K i * g i x) ^ 2) := by
  have h1 : ∀ (i j : ι), i ∈ Finset.univ → j ∈ Finset.univ →
      Integrable (fun x : Space => (K i * g i x) * (K j * g j x)) := by
    intro i j _ _
    have h := integrable_norm_mul_of_sq (hg i) (hg j) (hgmeas i) (hgmeas j) (hg_nn i) (hg_nn j)
    refine ((h.const_mul (K i * K j))).congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have h2 : Integrable (fun x : Space => ∑ i : ι, ∑ j : ι, (K i * g i x) * (K j * g j x)) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => h1 i j (Finset.mem_univ i) (Finset.mem_univ j)
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  show (∑ i : ι, ∑ j : ι, (K i * g i x) * (K j * g j x)) = (∑ i, K i * g i x) ^ 2
  rw [sq, Finset.sum_mul_sum]

end SquareSumIntegrability

section ModalField

/-- The modal field: the finite Schwartz sum realizing a Galerkin
approximant. -/
def modalField (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (t : ℝ) : SchwartzVelocity :=
  ∑ i : Fin m, coef m t i • modes m i

theorem modalField_apply (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (t : ℝ) (x : Space) :
    modalField modes coef m t x = ∑ i : Fin m, coef m t i • (modes m i) x := by
  simp only [modalField, sum_apply, smul_apply]

theorem modalField_divFree (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (hdiv : ∀ m i, DivergenceFreeInitial (modes m i))
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (t : ℝ) :
    DivergenceFreeInitial (modalField modes coef m t) :=
  divFree_sum_smul Finset.univ _ _ (hdiv m)

/-- Line derivatives distribute over the modal sum. -/
theorem lineDeriv_modalField (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (t : ℝ) (j : Fin 3) :
    ∂_{basisVector j} (modalField modes coef m t)
      = ∑ i : Fin m, coef m t i • ∂_{basisVector j} (modes m i) := by
  show (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector j)) _ = _
  simp only [modalField, map_sum, map_smul]
  rfl

/-- The Fréchet derivative of the modal field distributes over the sum. -/
theorem fderiv_modalField (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (t : ℝ) (x : Space) :
    fderiv ℝ (⇑(modalField modes coef m t)) x
      = ∑ i : Fin m, coef m t i • fderiv ℝ (⇑(modes m i)) x := by
  have hdiff0 : ∀ i : Fin m, DifferentiableAt ℝ (⇑(modes m i)) x :=
    fun i => ((modes m i).smooth 1).differentiable (by norm_num) x
  have hdiff : ∀ i : Fin m,
      DifferentiableAt ℝ (coef m t i • ⇑(modes m i)) x :=
    fun i => (hdiff0 i).const_smul (coef m t i)
  have hfun : (⇑(modalField modes coef m t) : Space → Space)
      = ∑ i : Fin m, coef m t i • ⇑(modes m i) := by
    funext x
    rw [modalField_apply]
    simp [Finset.sum_apply, Pi.smul_apply]
  rw [hfun, fderiv_sum fun i _ => hdiff i]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact fderiv_const_smul (hdiff0 i) (coef m t i)

/-- The static curl of the modal field distributes over the sum. -/
theorem staticCurl_modalField (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (t : ℝ) (x : Space) :
    staticCurl (⇑(modalField modes coef m t)) x
      = ∑ i : Fin m, coef m t i • staticCurl (⇑(modes m i)) x := by
  have step1 : ∀ i : Fin 3,
      (basisVector i) ⨯₃
          ((∑ l : Fin m, coef m t l • fderiv ℝ (⇑(modes m l)) x) (basisVector i))
      = ∑ l : Fin m, coef m t l •
          ((basisVector i) ⨯₃ (fderiv ℝ (⇑(modes m l)) x (basisVector i))) := by
    intro i
    simp only [sum_apply, smul_apply]
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => map_smul _ _ _
  calc staticCurl (⇑(modalField modes coef m t)) x
      = ∑ i : Fin 3, (basisVector i) ⨯₃
          ((∑ l : Fin m, coef m t l • fderiv ℝ (⇑(modes m l)) x) (basisVector i)) := by
        simp only [staticCurl, fderiv_modalField]
    _ = ∑ i : Fin 3, ∑ l : Fin m, coef m t l •
          ((basisVector i) ⨯₃ (fderiv ℝ (⇑(modes m l)) x (basisVector i))) :=
        Finset.sum_congr rfl fun i _ => step1 i
    _ = ∑ l : Fin m, ∑ i : Fin 3, coef m t l •
          ((basisVector i) ⨯₃ (fderiv ℝ (⇑(modes m l)) x (basisVector i))) :=
        Finset.sum_comm
    _ = ∑ l : Fin m, coef m t l • staticCurl (⇑(modes m l)) x := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [staticCurl, Finset.smul_sum]

end ModalField

section SchwartzBrezis

/-- The derivative of a Schwartz velocity along a translated segment is
jointly continuous in base point and segment parameter. -/
theorem continuous_fderiv_translate (f : SchwartzVelocity) (y : Space) :
    Continuous (Function.uncurry fun (x : Space) (s : ℝ) => fderiv ℝ f (x + s • y)) := by
  have hf : Continuous fun z : Space => fderiv ℝ (⇑f) z :=
    (f.smooth 1).continuous_fderiv (by norm_num)
  exact hf.comp (continuous_fst.add (continuous_snd.smul continuous_const))

/-- The squared Fréchet operator norm is bounded by `3` times the sum of the
squared coordinate line-derivative norms. -/
theorem fderiv_norm_sq_le_three_sum_lineDeriv (f : SchwartzVelocity) (z : Space) :
    ‖fderiv ℝ f z‖ ^ 2 ≤ 3 * ∑ j : Fin 3, ‖(∂_{basisVector j} f) z‖ ^ 2 := by
  have h1 : ‖fderiv ℝ (⇑f) z‖ ≤ ∑ j : Fin 3, ‖fderiv ℝ (⇑f) z (basisVector j)‖ :=
    opNorm_le_sum _
  have hcs : (∑ j : Fin 3, ‖fderiv ℝ (⇑f) z (basisVector j)‖) ^ 2
      ≤ (∑ j : Fin 3, ‖fderiv ℝ (⇑f) z (basisVector j)‖ ^ 2) * 3 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
      (fun j => ‖fderiv ℝ (⇑f) z (basisVector j)‖) (fun _ => 1)
    simpa using h
  have h2 : ∀ j : Fin 3,
      fderiv ℝ (⇑f) z (basisVector j) = (∂_{basisVector j} f) z :=
    fun j => (SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _).symm
  have hsum : (∑ j : Fin 3, ‖fderiv ℝ (⇑f) z (basisVector j)‖ ^ 2)
      = ∑ j : Fin 3, ‖(∂_{basisVector j} f) z‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ => by
      show ‖(fderiv ℝ (⇑f) z) (basisVector j)‖ ^ 2 = ‖(∂_{basisVector j} f) z‖ ^ 2
      rw [h2 j]
  have hlast : (∑ j : Fin 3, ‖fderiv ℝ (⇑f) z (basisVector j)‖ ^ 2) * 3
      = 3 * ∑ j : Fin 3, ‖(∂_{basisVector j} f) z‖ ^ 2 := by
    rw [hsum]; ring
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (hcs.trans (le_of_eq hlast))

set_option maxHeartbeats 1600000 in
/-- The segment derivative bound in product form: the squared Fréchet norm at
`x + s • y` is dominated by a product envelope built from the per-direction
translate envelopes. -/
theorem fderiv_translate_sq_le_prod (f : SchwartzVelocity) (y : Space) (D : Fin 3 → ℝ)
    (hD : ∀ j : Fin 3, ∀ (s : ℝ) (x : Space),
      ‖(∂_{basisVector j} f) (x + s • y)‖ ^ 2 ≤ D j * (1 + ‖s • y‖ ^ 4) / (1 + ‖x‖ ^ 4))
    (s : ℝ) (x : Space) :
    ‖fderiv ℝ f (x + s • y)‖ ^ 2 ≤
      3 * (∑ j : Fin 3, D j) * ((1 + ‖s • y‖ ^ 4) * (1 + ‖x‖ ^ 4)⁻¹) := by
  have hbase := fderiv_norm_sq_le_three_sum_lineDeriv f (x + s • y)
  calc ‖fderiv ℝ f (x + s • y)‖ ^ 2
      ≤ 3 * ∑ j : Fin 3, ‖(∂_{basisVector j} f) (x + s • y)‖ ^ 2 :=
        hbase
    _ ≤ 3 * ∑ j : Fin 3, D j * (1 + ‖s • y‖ ^ 4) / (1 + ‖x‖ ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun j _ => hD j s x
    _ = 3 * (∑ j : Fin 3, D j) * ((1 + ‖s • y‖ ^ 4) * (1 + ‖x‖ ^ 4)⁻¹) := by
        have hstep : ∀ j : Fin 3, D j * (1 + ‖s • y‖ ^ 4) / (1 + ‖x‖ ^ 4)
            = D j * ((1 + ‖s • y‖ ^ 4) * (1 + ‖x‖ ^ 4)⁻¹) := fun j => by
          rw [div_eq_mul_inv, mul_assoc]
        rw [Finset.sum_congr rfl fun j _ => hstep j, ← Finset.sum_mul]
        ring

/-- **Brezis Prop. 9.3 for a single Schwartz field** — all six integrability
side conditions of the repo's segment-estimate theorem discharged by rapid
decay. -/
theorem brezis_schwartz (f : SchwartzVelocity) (y : Space) :
    ∫ x : Space, ‖f (x + y) - f x‖ ^ 2
      ≤ ‖y‖ ^ 2 * ∫ x : Space, ‖fderiv ℝ f x‖ ^ 2 := by
  have hf : Differentiable ℝ (⇑f) := (f.smooth 1).differentiable (by norm_num)
  have hcont := continuous_fderiv_translate f y
  have hseg : ∀ x : Space, Continuous fun s : ℝ => fderiv ℝ (⇑f) (x + s • y) := by
    intro x
    have hfcont : Continuous fun z : Space => fderiv ℝ (⇑f) z :=
      (f.smooth 1).continuous_fderiv (by norm_num)
    exact hfcont.comp (continuous_const.add (continuous_id.smul continuous_const))
  -- the segment integrability hypotheses
  have hi : ∀ x : Space,
      IntervalIntegrable (fun s : ℝ => fderiv ℝ f (x + s • y) y) volume 0 1 :=
    fun x => (((hseg x)).clm_apply continuous_const).intervalIntegrable 0 1
  have hsq : ∀ x : Space,
      IntervalIntegrable (fun s : ℝ => ‖fderiv ℝ f (x + s • y) y‖ ^ 2) volume 0 1 :=
    fun x => ((((hseg x)).clm_apply continuous_const).norm.pow 2).intervalIntegrable 0 1
  have hop : ∀ x : Space,
      IntervalIntegrable (fun s : ℝ => ‖fderiv ℝ f (x + s • y)‖ ^ 2) volume 0 1 :=
    fun x => (((hseg x)).norm.pow 2).intervalIntegrable 0 1
  -- hlhs: squared translate difference
  have hlhs : Integrable (fun x : Space => ‖f (x + y) - f x‖ ^ 2) := by
    have htr := schwartz_translate_integrable_norm_sq f y
    have hbase := schwartz_integrable_norm_sq f
    refine (((htr.const_mul 2).add (hbase.const_mul 2))).mono'
      (((f.continuous.comp (continuous_id.add continuous_const)).sub f.continuous).norm.pow 2
        |>.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have hle : ‖f (x + y) - f x‖ ≤ ‖f (x + y)‖ + ‖f x‖ := norm_sub_le _ _
    show ‖f (x + y) - f x‖ ^ 2 ≤ 2 * ‖f (x + y)‖ ^ 2 + 2 * ‖f x‖ ^ 2
    calc ‖f (x + y) - f x‖ ^ 2 ≤ (‖f (x + y)‖ + ‖f x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ ≤ 2 * ‖f (x + y)‖ ^ 2 + 2 * ‖f x‖ ^ 2 := by
          nlinarith [two_mul_le_add_sq ‖f (x + y)‖ ‖f x‖]
  -- the per-direction translate envelopes
  choose D hDpos hD using
    fun j : Fin 3 => schwartz_translate_envelope (∂_{basisVector j} f) y
  -- hmid: the segment-integrated derivative energy
  have hmid : Integrable
      (fun x : Space => ∫ s in Set.Ioc (0:ℝ) 1, ‖fderiv ℝ f (x + s • y)‖ ^ 2) := by
    have hFcont : Continuous (fun p : Space × ℝ => ‖fderiv ℝ f (p.1 + p.2 • y)‖ ^ 2) :=
      (((f.smooth 1).continuous_fderiv (by norm_num)).comp
        (continuous_fst.add (continuous_snd.smul continuous_const))).norm.pow 2
    -- the segment-integral is continuous in `x` by domination: for `s ∈ [0,1]`
    -- the integrand is uniformly bounded by the constant `3(ΣDⱼ)(1+‖y‖⁴)`.
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    have hGcont : Continuous
        (fun x : Space => ∫ s, ‖fderiv ℝ f (x + s • y)‖ ^ 2
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) := by
      refine continuous_of_dominated
        (bound := fun _ : ℝ => 3 * (∑ j : Fin 3, D j) * (1 + ‖y‖ ^ 4)) ?_ ?_ ?_ ?_
      · intro x
        exact ((hseg x).norm.pow 2).aestronglyMeasurable
      · intro x
        refine Filter.Eventually.mono (ae_restrict_mem measurableSet_Ioc) fun s hs => ?_
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have hs01 : s ∈ Set.Icc 0 1 := Set.Ioc_subset_Icc_self hs
        have hsy : (1 : ℝ) + ‖s • y‖ ^ 4 ≤ 1 + ‖y‖ ^ 4 := by
          have hle : ‖s • y‖ ≤ ‖y‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs01.1]
            exact mul_le_of_le_one_left (norm_nonneg y) hs01.2
          have h4 : ‖s • y‖ ^ 4 ≤ ‖y‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hle 4
          linarith [h4]
        calc ‖fderiv ℝ f (x + s • y)‖ ^ 2
            ≤ 3 * (∑ j : Fin 3, D j) * ((1 + ‖s • y‖ ^ 4) * (1 + ‖x‖ ^ 4)⁻¹) :=
              fderiv_translate_sq_le_prod f y D hD s x
          _ ≤ 3 * (∑ j : Fin 3, D j) * ((1 + ‖y‖ ^ 4) * 1) := by
              apply mul_le_mul_of_nonneg_left _
                (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => (hDpos j).le))
              exact mul_le_mul hsy
                (inv_le_one_of_one_le₀ (a := 1 + ‖x‖ ^ 4)
                  (le_add_of_nonneg_right (b := ‖x‖ ^ 4) (by positivity)))
                (inv_nonneg.mpr (show (0 : ℝ) ≤ 1 + ‖x‖ ^ 4 by positivity))
                (show (0 : ℝ) ≤ 1 + ‖y‖ ^ 4 by positivity)
          _ = 3 * (∑ j : Fin 3, D j) * (1 + ‖y‖ ^ 4) := by ring
      · exact integrable_const _
      · exact Filter.Eventually.of_forall fun s => by
          have hfs : Continuous fun z : Space => fderiv ℝ (⇑f) z :=
            (f.smooth 1).continuous_fderiv (by norm_num)
          exact (hfs.comp (continuous_id.add continuous_const)).norm.pow 2
    have hGsm : StronglyMeasurable
        (fun x : Space => ∫ s in Set.Ioc (0:ℝ) 1, ‖fderiv ℝ f (x + s • y)‖ ^ 2) :=
      hGcont.stronglyMeasurable
    -- the x-integrable envelope, constant along the segment
    have hE : Integrable
        (fun x : Space => 3 * (∑ j : Fin 3, D j) * ((1 + ‖y‖ ^ 4) * (1 + ‖x‖ ^ 4)⁻¹)) := by
      have h := integrable_inv_one_add_norm_four.const_mul (3 * (∑ j : Fin 3, D j) * (1 + ‖y‖ ^ 4))
      refine h.congr (Filter.Eventually.of_forall fun x => ?_)
      ring
    refine hE.mono' (hGsm.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun s _ => by positivity)]
    have hmono : (∫ s in Set.Ioc (0:ℝ) 1, ‖fderiv ℝ f (x + s • y)‖ ^ 2)
        ≤ ∫ _ in Set.Ioc (0:ℝ) 1,
            (3 * (∑ j : Fin 3, D j) * ((1 + ‖y‖ ^ 4) * (1 + ‖x‖ ^ 4)⁻¹)) := by
      refine setIntegral_mono_on (hop x).1
        (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc fun s hs => ?_
      have hs01 : s ∈ Set.Icc 0 1 := Set.Ioc_subset_Icc_self hs
      have hsy : (1 : ℝ) + ‖s • y‖ ^ 4 ≤ 1 + ‖y‖ ^ 4 := by
        have hle : ‖s • y‖ ≤ ‖y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs01.1]
          exact mul_le_of_le_one_left (norm_nonneg y) hs01.2
        have h4 : ‖s • y‖ ^ 4 ≤ ‖y‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hle 4
        linarith [h4]
      exact (fderiv_translate_sq_le_prod f y D hD s x).trans (by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => (hDpos j).le))
        apply mul_le_mul_of_nonneg_right _
          (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 1 + ‖x‖ ^ 4))
        exact hsy)
    have hconst : (∫ _ in Set.Ioc (0:ℝ) 1,
        (3 * (∑ j : Fin 3, D j) * ((1 + ‖y‖ ^ 4) * (1 + ‖x‖ ^ 4)⁻¹)))
        = 3 * (∑ j : Fin 3, D j) * ((1 + ‖y‖ ^ 4) * (1 + ‖x‖ ^ 4)⁻¹) := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1 - 0)]
      simp
    exact hmono.trans_eq hconst
  -- hprod: joint integrability on the product strip
  have hprod : Integrable
      (Function.uncurry fun (x : Space) (s : ℝ) => ‖fderiv ℝ f (x + s • y)‖ ^ 2)
      (volume.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    have hFcont : Continuous
        (Function.uncurry fun (x : Space) (s : ℝ) => ‖fderiv ℝ f (x + s • y)‖ ^ 2) :=
      hcont.norm.pow 2
    have hgS : Integrable (fun s : ℝ => (1 : ℝ) + ‖s • y‖ ^ 4)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      have hcont2 : Continuous fun s : ℝ => (1 : ℝ) + ‖s • y‖ ^ 4 := by fun_prop
      exact (hcont2.intervalIntegrable 0 1).1
    have hB : Integrable
        (fun p : Space × ℝ =>
          (3 * (∑ j : Fin 3, D j)) * ((1 + ‖p.1‖ ^ 4)⁻¹ * (1 + ‖p.2 • y‖ ^ 4)))
        (volume.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
      (integrable_inv_one_add_norm_four.mul_prod hgS).const_mul _
    refine hB.mono' (hFcont.aestronglyMeasurable) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ (Function.uncurry
        (fun (x : Space) (s : ℝ) => ‖fderiv ℝ f (x + s • y)‖ ^ 2)) p from sq_nonneg _)]
    show ‖fderiv ℝ f (p.1 + p.2 • y)‖ ^ 2 ≤
      (3 * (∑ j : Fin 3, D j)) * ((1 + ‖p.1‖ ^ 4)⁻¹ * (1 + ‖p.2 • y‖ ^ 4))
    rw [show (1 + ‖p.1‖ ^ 4)⁻¹ * (1 + ‖p.2 • y‖ ^ 4)
        = (1 + ‖p.2 • y‖ ^ 4) * (1 + ‖p.1‖ ^ 4)⁻¹ from mul_comm _ _]
    exact fderiv_translate_sq_le_prod f y D hD p.2 p.1
  exact Navier.Analysis.RieszKolmogorov.integral_norm_sub_sq_le_mul_integral_fderiv_sq
    (⇑f) hf y hi hsq hop hlhs hmid hprod

end SchwartzBrezis

section ModalFamilyTimeIntegrability

/-- Coefficients of a continuous curve are uniformly absolutely bounded on
compact time intervals. -/
theorem abs_coef_le_on_Icc (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hcoef : ∀ m, Continuous (coef m)) (m : ℕ) (i : Fin m) {a b : ℝ} :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc a b, |coef m t i| ≤ K := by
  have h1 : Continuous fun t => EuclideanSpace.proj i (coef m t) :=
    (EuclideanSpace.proj i).continuous.comp (hcoef m)
  have hcont : Continuous fun t => |coef m t i| := h1.abs
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont.continuousOn
  exact ⟨max C 0, le_max_right _ _,
    fun t ht => (hC (mem_image_of_mem _ ht)).trans (le_max_left _ _)⟩

/-- The translate-difference of a modal field expands over the modes. -/
theorem modalField_sub_apply (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (t : ℝ) (y x : Space) :
    (modalField modes coef m t) (x + y) - (modalField modes coef m t) x
      = ∑ i : Fin m, coef m t i • ((modes m i) (x + y) - (modes m i) x) := by
  rw [modalField_apply, modalField_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_sub]

/-- Generic time-integrability of a modal integrand: if the joint integrand
is continuous in `(t, x)` and pointwise dominated, uniformly for `t` in the
compact window, by the square of a weighted sum of square-integrable norm
functions, then its `x`-integral is integrable in `t` on `(0, T]`. -/
theorem integrableOn_tIntegral_modal
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hcoef : ∀ m, Continuous (coef m)) (m : ℕ) {T : ℝ} (_hT : 0 ≤ T)
    (V : Fin m → Space → ℝ)
    (hV : ∀ i, Integrable (fun x : Space => (V i x) ^ 2))
    (hVmeas : ∀ i, AEStronglyMeasurable (V i) volume)
    (hVnn : ∀ i x, 0 ≤ V i x)
    (F : ℝ → Space → ℝ)
    (hFcont : Continuous (Function.uncurry F))
    (hFbound : ∀ (K : Fin m → ℝ), (∀ i, 0 ≤ K i) →
      (∀ t ∈ Set.Icc 0 T, ∀ i, |coef m t i| ≤ K i) →
      ∀ t ∈ Set.Icc 0 T, ∀ x : Space, |F t x| ≤ (∑ i, K i * V i x) ^ 2) :
    IntegrableOn (fun t => ∫ x : Space, F t x) (Set.Ioc 0 T) volume := by
  -- uniform coefficient bound on the window
  have hK : ∀ i, ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc 0 T, |coef m t i| ≤ K :=
    fun i => abs_coef_le_on_Icc coef hcoef m i
  choose K hKnn hK using hK
  have hK' : ∀ t ∈ Set.Icc 0 T, ∀ i, |coef m t i| ≤ K i := fun t ht i => hK i t ht
  -- the dominating envelope
  have hbound_int : Integrable (fun x : Space => (∑ i, K i * V i x) ^ 2) :=
    integrable_sq_sum hV hVmeas hVnn K
  have hFb := hFbound K hKnn hK'
  -- per-slice integrability of `F (t, ·)` on the window
  have hF_int : ∀ t ∈ Set.Icc 0 T, Integrable (F t) := by
    intro t ht
    have hmeas : AEStronglyMeasurable (F t) volume :=
      (hFcont.comp (Continuous.prodMk_right t)).aestronglyMeasurable
    refine hbound_int.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hFb t ht x
  -- continuity of the `t`-integral on the window by domination
  have hGcont : ContinuousOn (fun t => ∫ x : Space, F t x) (Set.Icc 0 T) := by
    refine continuousOn_of_dominated (s := Set.Icc 0 T)
      (bound := fun x : Space => (∑ i, K i * V i x) ^ 2) ?_ ?_ hbound_int ?_
    · intro t ht
      exact (hFcont.comp (Continuous.prodMk_right t)).aestronglyMeasurable
    · intro t ht
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hFb t ht x
    · exact Filter.Eventually.of_forall fun x =>
        (hFcont.comp (Continuous.prodMk_left x)).continuousOn
  -- a continuous function on `Icc 0 T` is integrable there, hence on `Ioc 0 T`
  exact (hGcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

end ModalFamilyTimeIntegrability

section ModalEnergies

/-- The official Euclidean norm satisfies the triangle inequality. -/
theorem officialEuclideanNorm_add_le' (a b : Space) :
    officialEuclideanNorm (a + b) ≤ officialEuclideanNorm a + officialEuclideanNorm b := by
  have h : officialEuclideanPoint (a + b) = officialEuclideanPoint a + officialEuclideanPoint b :=
    rfl
  rw [officialEuclideanNorm, officialEuclideanNorm, officialEuclideanNorm, h]
  exact norm_add_le _ _

/-- The official Euclidean norm of a finite sum is bounded by the sum of the
norms. -/
theorem officialEuclideanNorm_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → Space) :
    officialEuclideanNorm (∑ i ∈ s, v i) ≤ ∑ i ∈ s, officialEuclideanNorm (v i) := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h : officialEuclideanPoint (0 : Space) = 0 := rfl
      rw [officialEuclideanNorm, h, norm_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (officialEuclideanNorm_add_le' _ _).trans (add_le_add_right ih _)

/-- The official Euclidean norm pulls scalars out as absolute values. -/
theorem officialEuclideanNorm_smul' (c : ℝ) (a : Space) :
    officialEuclideanNorm (c • a) = |c| * officialEuclideanNorm a := by
  have h : officialEuclideanPoint (c • a) = c • officialEuclideanPoint a := rfl
  simp only [officialEuclideanNorm, h, norm_smul, Real.norm_eq_abs]

/-- The translation energy `t ↦ ∫ ‖u_m(t)(·+y) − u_m(t)‖²` is integrable on
`(0, T]`: joint continuity plus the coefficient-bounded Schwartz envelope. -/
theorem integrableOn_translation_energy
    (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hcoef : ∀ m, Continuous (coef m)) (m : ℕ) {T : ℝ} (hT : 0 ≤ T) (y : Space) :
    IntegrableOn (fun t => ∫ x : Space,
      ‖(modalField modes coef m t) (x + y) - (modalField modes coef m t) x‖ ^ 2)
      (Set.Ioc 0 T) volume := by
  have hV : ∀ i : Fin m, Integrable (fun x : Space =>
      (‖(modes m i) (x + y)‖ + ‖(modes m i) x‖) ^ 2) := by
    intro i
    have h1 := schwartz_translate_integrable_norm_sq (modes m i) y
    have h2 := schwartz_integrable_norm_sq (modes m i)
    refine (((h1.const_mul 2).add (h2.const_mul 2))).mono'
      (((((modes m i).continuous.comp (continuous_id.add continuous_const)).norm.add
        (modes m i).continuous.norm).pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    show (‖(modes m i) (x + y)‖ + ‖(modes m i) x‖) ^ 2 ≤
      2 * ‖(modes m i) (x + y)‖ ^ 2 + 2 * ‖(modes m i) x‖ ^ 2
    nlinarith [two_mul_le_add_sq ‖(modes m i) (x + y)‖ ‖(modes m i) x‖]
  refine integrableOn_tIntegral_modal coef hcoef m hT
    (V := fun i : Fin m => fun x : Space => ‖(modes m i) (x + y)‖ + ‖(modes m i) x‖)
    hV ?_ ?_
    (F := fun t x => ‖(modalField modes coef m t) (x + y) - (modalField modes coef m t) x‖ ^ 2)
    ?_ ?_
  · intro i
    exact ((((modes m i).continuous.comp (continuous_id.add continuous_const)).norm.add
      (modes m i).continuous.norm)).aestronglyMeasurable
  · intro i x
    positivity
  · -- joint continuity of the translate-difference integrand
    have hsum : (Function.uncurry fun (t : ℝ) (x : Space) =>
        ‖(modalField modes coef m t) (x + y) - (modalField modes coef m t) x‖ ^ 2)
        = fun p : ℝ × Space =>
          ‖∑ i : Fin m, coef m p.1 i • ((modes m i) (p.2 + y) - (modes m i) p.2)‖ ^ 2 := by
      funext p
      obtain ⟨t, x⟩ := p
      simp only [Function.uncurry_apply_pair]
      rw [modalField_sub_apply]
    rw [hsum]
    refine (continuous_finsetSum _ fun i _ => ?_).norm.pow 2
    have hci : Continuous fun p : ℝ × Space => coef m p.1 i :=
      (EuclideanSpace.proj i).continuous.comp ((hcoef m).comp continuous_fst)
    exact Continuous.smul hci
      (((modes m i).continuous.comp (continuous_snd.add continuous_const)).sub
        ((modes m i).continuous.comp continuous_snd))
  · -- the pointwise coefficient bound
    intro K hKnn hKbound t ht x
    rw [abs_of_nonneg (by positivity)]
    rw [modalField_sub_apply]
    have h1 : ‖∑ i : Fin m, coef m t i • ((modes m i) (x + y) - (modes m i) x)‖
        ≤ ∑ i : Fin m, K i * (‖(modes m i) (x + y)‖ + ‖(modes m i) x‖) := by
      calc ‖∑ i : Fin m, coef m t i • ((modes m i) (x + y) - (modes m i) x)‖
          ≤ ∑ i : Fin m, ‖coef m t i • ((modes m i) (x + y) - (modes m i) x)‖ :=
            norm_sum_le _ _
        _ = ∑ i : Fin m, |coef m t i| * ‖(modes m i) (x + y) - (modes m i) x‖ :=
            Finset.sum_congr rfl fun i _ => by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ∑ i : Fin m, K i * (‖(modes m i) (x + y)‖ + ‖(modes m i) x‖) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul (hKbound t ht i) (norm_sub_le _ _) (norm_nonneg _) (hKnn i)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

set_option maxHeartbeats 0 in
/-- The derivative energy `t ↦ ∫ ‖D u_m(t)‖²` is integrable on `(0, T]`. -/
theorem integrableOn_fderiv_energy
    (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hcoef : ∀ m, Continuous (coef m)) (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun t => ∫ x : Space,
      ‖fderiv ℝ (⇑(modalField modes coef m t)) x‖ ^ 2)
      (Set.Ioc 0 T) volume := by
  have hV : ∀ i : Fin m, Integrable (fun x : Space =>
      (∑ j : Fin 3, ‖(∂_{basisVector j} (modes m i)) x‖) ^ 2) := by
    intro i
    have h := integrable_sq_sum
      (g := fun j : Fin 3 => fun x : Space => ‖(∂_{basisVector j} (modes m i)) x‖)
      (fun j => schwartz_integrable_norm_sq _)
      (fun j => ((∂_{basisVector j} (modes m i)).continuous.norm).aestronglyMeasurable)
      (fun j x => norm_nonneg _) (fun _ => (1 : ℝ))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [one_mul]
  refine integrableOn_tIntegral_modal coef hcoef m hT
    (V := fun i : Fin m => fun x : Space => ∑ j : Fin 3, ‖(∂_{basisVector j} (modes m i)) x‖)
    hV ?_ ?_
    (F := fun t x => ‖fderiv ℝ (⇑(modalField modes coef m t)) x‖ ^ 2) ?_ ?_
  · intro i
    exact (continuous_finsetSum _ fun j _ =>
      (∂_{basisVector j} (modes m i)).continuous.norm).aestronglyMeasurable
  · intro i x
    positivity
  · -- joint continuity of the derivative integrand
    have hsum : (Function.uncurry fun (t : ℝ) (x : Space) =>
        ‖fderiv ℝ (⇑(modalField modes coef m t)) x‖ ^ 2)
        = fun p : ℝ × Space =>
          ‖∑ i : Fin m, coef m p.1 i • fderiv ℝ (⇑(modes m i)) p.2‖ ^ 2 := by
      funext p
      obtain ⟨t, x⟩ := p
      simp only [Function.uncurry_apply_pair]
      rw [fderiv_modalField]
    rw [hsum]
    refine (continuous_finsetSum _ fun i _ => ?_).norm.pow 2
    have hci : Continuous fun p : ℝ × Space => coef m p.1 i :=
      (EuclideanSpace.proj i).continuous.comp ((hcoef m).comp continuous_fst)
    exact Continuous.smul hci
      ((((modes m i).smooth 1).continuous_fderiv (by norm_num)).comp continuous_snd)
  · -- the pointwise coefficient bound
    intro K hKnn hKbound t ht x
    rw [abs_of_nonneg (by positivity)]
    rw [fderiv_modalField]
    have hmode : ∀ i : Fin m, ∀ x : Space, ‖fderiv ℝ (⇑(modes m i)) x‖
        ≤ ∑ j : Fin 3, ‖(∂_{basisVector j} (modes m i)) x‖ := by
      intro i x
      have h := opNorm_le_sum (fderiv ℝ (⇑(modes m i)) x)
      have h_eq : (∑ j : Fin 3, ‖fderiv ℝ (⇑(modes m i)) x (basisVector j)‖)
          = (∑ j : Fin 3, ‖(∂_{basisVector j} (modes m i)) x‖) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact h.trans (le_of_eq h_eq)
    have h1 : ‖∑ i : Fin m, coef m t i • fderiv ℝ (⇑(modes m i)) x‖
        ≤ ∑ i : Fin m, K i * (∑ j : Fin 3, ‖(∂_{basisVector j} (modes m i)) x‖) := by
      have h_sum_norm : ‖∑ i : Fin m, coef m t i • fderiv ℝ (⇑(modes m i)) x‖
          ≤ ∑ i : Fin m, ‖coef m t i • fderiv ℝ (⇑(modes m i)) x‖ := norm_sum_le _ _
      have h_norm_abs : (∑ i : Fin m, ‖coef m t i • fderiv ℝ (⇑(modes m i)) x‖)
          = (∑ i : Fin m, |coef m t i| * ‖fderiv ℝ (⇑(modes m i)) x‖) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
      have h_abs_k : (∑ i : Fin m, |coef m t i| * ‖fderiv ℝ (⇑(modes m i)) x‖)
          ≤ ∑ i : Fin m, K i * (∑ j : Fin 3, ‖(∂_{basisVector j} (modes m i)) x‖) :=
        Finset.sum_le_sum fun i _ => mul_le_mul (hKbound t ht i) (hmode i x) (norm_nonneg _) (hKnn i)
      exact (h_sum_norm.trans (le_of_eq h_norm_abs)).trans h_abs_k
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- The curl (enstrophy) energy `t ↦ ∫ ‖curl u_m(t)‖²` is integrable on
`(0, T]`. -/
theorem integrableOn_curl_energy
    (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hcoef : ∀ m, Continuous (coef m)) (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun t => ∫ x : Space,
      officialEuclideanNorm (staticCurl (⇑(modalField modes coef m t)) x) ^ 2)
      (Set.Ioc 0 T) volume := by
  have hcurlcont_field : ∀ i : Fin m, Continuous fun x : Space => staticCurl (⇑(modes m i)) x := by
    intro i
    have h : Continuous fun x : Space => curlCLM (modes m i) x :=
      (curlCLM (modes m i)).continuous
    exact h.congr fun x => by rw [curlCLM_apply]
  have hcurlcont : ∀ i : Fin m, Continuous fun x : Space =>
      officialEuclideanNorm (staticCurl (⇑(modes m i)) x) :=
    fun i => continuous_officialEuclideanNorm.comp (hcurlcont_field i)
  have hV : ∀ i : Fin m, Integrable (fun x : Space =>
      (officialEuclideanNorm (staticCurl (⇑(modes m i)) x)) ^ 2) := by
    intro i
    have hbase := schwartz_integrable_norm_sq (curlCLM (modes m i))
    refine (hbase.const_mul 3).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hcurlcont i).pow 2 |>.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      show officialEuclideanNorm (staticCurl (⇑(modes m i)) x) ^ 2 ≤
        3 * ‖curlCLM (modes m i) x‖ ^ 2
      rw [← curlCLM_apply]
      exact officialEuclideanNorm_sq_le_three_mul_norm_sq _
  refine integrableOn_tIntegral_modal coef hcoef m hT
    (V := fun i : Fin m => fun x : Space => officialEuclideanNorm (staticCurl (⇑(modes m i)) x))
    hV ?_ ?_
    (F := fun t x => officialEuclideanNorm (staticCurl (⇑(modalField modes coef m t)) x) ^ 2)
    ?_ ?_
  · intro i
    exact (hcurlcont i).aestronglyMeasurable
  · intro i x
    exact officialEuclideanNorm_nonneg _
  · -- joint continuity of the curl integrand
    have hsum : (Function.uncurry fun (t : ℝ) (x : Space) =>
        officialEuclideanNorm (staticCurl (⇑(modalField modes coef m t)) x) ^ 2)
        = fun p : ℝ × Space =>
          officialEuclideanNorm (∑ i : Fin m, coef m p.1 i • staticCurl (⇑(modes m i)) p.2) ^ 2 := by
      funext p
      obtain ⟨t, x⟩ := p
      simp only [Function.uncurry_apply_pair]
      rw [staticCurl_modalField]
    rw [hsum]
    refine (continuous_officialEuclideanNorm.comp (continuous_finsetSum _ fun i _ => ?_)).pow 2
    exact Continuous.smul
      ((EuclideanSpace.proj i).continuous.comp ((hcoef m).comp continuous_fst))
      ((hcurlcont_field i).comp continuous_snd)
  · -- the pointwise coefficient bound
    intro K hKnn hKbound t ht x
    rw [abs_of_nonneg (by positivity)]
    rw [staticCurl_modalField]
    have h1 : officialEuclideanNorm (∑ i : Fin m, coef m t i • staticCurl (⇑(modes m i)) x)
        ≤ ∑ i : Fin m, K i * officialEuclideanNorm (staticCurl (⇑(modes m i)) x) := by
      calc officialEuclideanNorm (∑ i : Fin m, coef m t i • staticCurl (⇑(modes m i)) x)
          ≤ ∑ i : Fin m, officialEuclideanNorm (coef m t i • staticCurl (⇑(modes m i)) x) :=
            officialEuclideanNorm_sum_le _ _
        _ = ∑ i : Fin m, |coef m t i| * officialEuclideanNorm (staticCurl (⇑(modes m i)) x) :=
            Finset.sum_congr rfl fun i _ => officialEuclideanNorm_smul' _ _
        _ ≤ ∑ i : Fin m, K i * officialEuclideanNorm (staticCurl (⇑(modes m i)) x) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul (hKbound t ht i) le_rfl (officialEuclideanNorm_nonneg _) (hKnn i)
    exact pow_le_pow_left₀ (officialEuclideanNorm_nonneg _) h1 2

end ModalEnergies

section Main

/-- **Spatial equicontinuity of a modal family.**  A Galerkin family
`u_m(t) = Σᵢ cᵢ(t) • wᵢ` with divergence-free Schwartz modes and continuous
coefficient curves, whose curl energy is uniformly budgeted by `C` on every
window `(0, T]`, is uniformly spatially-translation equicontinuous — the
Riesz–Fréchet–Kolmogorov hypothesis of the Aubin–Lions compactness input.

The proof is the banked `spaceEquicontinuous_of_dissipation_bound` fed by
`brezis_schwartz` (per-slice Brezis 9.3), the two time-integrability
certificates, and the dissipation bound `∫₀^T ∫ ‖Du_m‖² ≤ 3C` that the
divergence-free Dirichlet=enstrophy identity extracts from the curl budget. -/
theorem spaceEquicontinuous_of_modalFamily
    (modes : ∀ m : ℕ, Fin m → SchwartzVelocity)
    (hdiv : ∀ m i, DivergenceFreeInitial (modes m i))
    (coef : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hcoef : ∀ m, Continuous (coef m))
    (C : ℝ) (hC : 0 ≤ C)
    (henst : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      ∫ t in Set.Ioc 0 T, ∫ x : Space,
        officialEuclideanNorm (staticCurl (⇑(modalField modes coef m t)) x) ^ 2 ≤ C) :
    SpaceEquicontinuous (fun m t x => modalField modes coef m t x) := by
  refine spaceEquicontinuous_of_dissipation_bound _ (3 * C) (by positivity) ?_ ?_ ?_ ?_
  · -- Brezis Prop. 9.3, per time slice
    intro m t ht y
    exact brezis_schwartz (modalField modes coef m t) y
  · -- time-integrability of the translation energy
    intro m T y
    rcases lt_or_ge T 0 with hT | hT
    · rw [Set.Ioc_eq_empty (by linarith)]
      exact integrableOn_empty
    · exact integrableOn_translation_energy modes coef hcoef m hT y
  · -- time-integrability of the derivative energy
    intro m T
    rcases lt_or_ge T 0 with hT | hT
    · rw [Set.Ioc_eq_empty (by linarith)]
      exact integrableOn_empty
    · exact integrableOn_fderiv_energy modes coef hcoef m hT
  · -- the dissipation bound: Dirichlet ≤ 3 × curl budget, integrated
    intro m T hT
    have hpt : ∀ t : ℝ,
        (∫ x : Space, ‖fderiv ℝ (fun x => modalField modes coef m t x) x‖ ^ 2)
        ≤ 3 * ∫ x : Space,
            officialEuclideanNorm (staticCurl (fun x => modalField modes coef m t x) x) ^ 2 := by
      intro t
      exact integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree _
        (modalField_divFree modes hdiv coef m t)
    calc ∫ t in Set.Ioc 0 T, ∫ x : Space,
          ‖fderiv ℝ (fun x => modalField modes coef m t x) x‖ ^ 2
        ≤ ∫ t in Set.Ioc 0 T, 3 * ∫ x : Space,
            officialEuclideanNorm (staticCurl (fun x => modalField modes coef m t x) x) ^ 2 :=
          setIntegral_mono_on (integrableOn_fderiv_energy modes coef hcoef m hT)
            ((integrableOn_curl_energy modes coef hcoef m hT).const_mul _)
            measurableSet_Ioc fun t _ => hpt t
      _ = 3 * ∫ t in Set.Ioc 0 T, ∫ x : Space,
            officialEuclideanNorm (staticCurl (fun x => modalField modes coef m t x) x) ^ 2 :=
          integral_const_mul _ _
      _ ≤ 3 * C := mul_le_mul_of_nonneg_left (henst m T hT) (by norm_num)

end Main

end Navier.Analysis.GalerkinSpaceEquicontinuity

end
