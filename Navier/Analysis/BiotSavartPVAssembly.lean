import Navier.Analysis.BiotSavartGradientRecovery
import Navier.Analysis.BiotSavartPVNearEstimate
import Navier.Analysis.BiotSavartPVShellEstimate
import Navier.Analysis.BiotSavartPVFarEstimate

/-!
# Quantitative assembly of the Biot--Savart gradient split

The actual principal-value limit is bounded by its near, shell, and far
pieces, then the gradient recovery tensor is contracted in the sup norm on
`Space = Fin 3 → ℝ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Matrix LineDeriv

namespace Navier.Analysis.BiotSavartPVAssembly

open Navier
open Navier.Analysis.BiotSavartConvolution
open Navier.Analysis.BiotSavartGradientRecovery
open Navier.Analysis.BiotSavartPVSplitEstimate
open Navier.Analysis.BiotSavartPVNearEstimate
open Navier.Analysis.BiotSavartPVShellEstimate
open Navier.Analysis.BiotSavartPVFarEstimate
open Navier.Analysis.CZNearField
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.Vorticity

private theorem abs_cross_basis_le_one (k j l : Fin 3) :
    |(basisVector k ⨯₃ basisVector j) l| ≤ (1 : ℝ) := by
  fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [basisVector, cross_apply]

private theorem abs_basisVector_le_one (i j : Fin 3) :
    |basisVector i j| ≤ (1 : ℝ) := by
  by_cases h : j = i
  · subst j
    simp [basisVector]
  · simp [basisVector, h]

private theorem opNorm_le_sum_basisVector (T : Space →L[ℝ] Space) :
    ‖T‖ ≤ ∑ i : Fin 3, ‖T (basisVector i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => norm_nonneg _) (fun v => ?_)
  have hbasis : v = ∑ i : Fin 3, v i • basisVector i := by
    simpa only [basisVector] using (pi_eq_sum_univ' v)
  calc
    ‖T v‖ = ‖T (∑ i : Fin 3, v i • basisVector i)‖ :=
      congrArg (fun X => ‖T X‖) hbasis
    _ = ‖∑ i : Fin 3, v i • T (basisVector i)‖ := by
      rw [map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • T (basisVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖T (basisVector i)‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖T (basisVector i)‖) * ‖v‖ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem principalValue_curlComponent_bound
    (Cn Cs Cf : ℝ)
    (hnear : ∀ (u : SchwartzVelocity) (H₂ : ℝ),
      sobolevH2NormSq (staticCurlSchwartz u) ≤ H₂ →
      ∀ (x : Space) (i j k : Fin 3) (ε ρ : ℝ),
        0 < ε → ε < ρ →
        |∫ z in pvNearSet ε ρ,
          (1 / (4 * Real.pi)) * bsGradKernel i j z *
            (curlComponentSchwartz u k (x - z) -
              curlComponentSchwartz u k x)| ≤
          Cn * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂)
    (hshell : ∀ (u : SchwartzVelocity) (Mω : ℝ),
      (∀ y : Space, officialEuclideanNorm (staticCurl (⇑u) y) ≤ Mω) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ (x : Space) (i j k : Fin 3),
        |∫ z in pvShellSet ρ,
          (1 / (4 * Real.pi)) * bsGradKernel i j z *
            curlComponentSchwartz u k (x - z)| ≤
          Cs * Mω * (1 + Real.log (1 / ρ)))
    (hfar : ∀ (u : SchwartzVelocity) (M₂ : ℝ),
      (∫ y : Space,
        officialEuclideanNorm (staticCurl (⇑u) y) ^ 2) ≤ M₂ →
      ∀ (x : Space) (i j k : Fin 3),
        |∫ z in pvFarSet,
          (1 / (4 * Real.pi)) * bsGradKernel i j z *
            curlComponentSchwartz u k (x - z)| ≤ Cf * Real.sqrt M₂)
    (u : SchwartzVelocity) (H₂ Mω M₂ : ℝ)
    (hH₂ : sobolevH2NormSq (staticCurlSchwartz u) ≤ H₂)
    (hMω : ∀ y : Space,
      officialEuclideanNorm (staticCurl (⇑u) y) ≤ Mω)
    (hM₂ : (∫ y : Space,
      officialEuclideanNorm (staticCurl (⇑u) y) ^ 2) ≤ M₂)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (x : Space) (i j k : Fin 3) :
    |principalValueConvolution i j (curlComponentSchwartz u k) x| ≤
      Cn * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂ +
        Cs * Mω * (1 + Real.log (1 / ρ)) + Cf * Real.sqrt M₂ := by
  have hlim := tendsto_principalValueConvolution_split hρ hρ1 i j
    (curlComponentSchwartz u k) x
  apply le_of_tendsto hlim.abs
  have hsmall : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), ε < ρ :=
    (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
      (Iio_mem_nhds hρ)
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hερ
  have hn := hnear u H₂ hH₂ x i j k ε ρ hε hερ
  have hs := hshell u Mω hMω ρ hρ hρ1 x i j k
  have hf := hfar u M₂ hM₂ x i j k
  calc
    |((∫ z in pvNearSet ε ρ,
          (1 / (4 * Real.pi)) * bsGradKernel i j z *
            (curlComponentSchwartz u k (x - z) -
              curlComponentSchwartz u k x)) +
        (∫ z in pvShellSet ρ,
          (1 / (4 * Real.pi)) * bsGradKernel i j z *
            curlComponentSchwartz u k (x - z)) +
        ∫ z in pvFarSet,
          (1 / (4 * Real.pi)) * bsGradKernel i j z *
            curlComponentSchwartz u k (x - z))|
        ≤ |∫ z in pvNearSet ε ρ,
            (1 / (4 * Real.pi)) * bsGradKernel i j z *
              (curlComponentSchwartz u k (x - z) -
                curlComponentSchwartz u k x)| +
          |∫ z in pvShellSet ρ,
            (1 / (4 * Real.pi)) * bsGradKernel i j z *
              curlComponentSchwartz u k (x - z)| +
          |∫ z in pvFarSet,
            (1 / (4 * Real.pi)) * bsGradKernel i j z *
              curlComponentSchwartz u k (x - z)| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Cn * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂ +
          Cs * Mω * (1 + Real.log (1 / ρ)) + Cf * Real.sqrt M₂ :=
      add_le_add (add_le_add hn hs) hf

/-- The complete quantitative Biot--Savart split with a supplied vorticity
`H²` majorant. -/
theorem exists_gradient_bound_of_curlH2 :
    ∃ A B F : ℝ, 0 < A ∧ 0 < B ∧ 0 < F ∧
      ∀ (u : SchwartzVelocity), DivergenceFreeInitial u →
        ∀ H₂ Mω M₂ : ℝ,
          sobolevH2NormSq (staticCurlSchwartz u) ≤ H₂ →
          (∀ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ≤ Mω) →
          (∫ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ^ 2) ≤ M₂ →
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
          ∀ x : Space,
            ‖fderiv ℝ (⇑u) x‖ ≤
              A * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂ +
                B * Mω * (1 + Real.log (1 / ρ)) +
                F * Real.sqrt M₂ := by
  obtain ⟨Cn, hCn, hnear⟩ := exists_pvNearCurlComponent_bound
  obtain ⟨Cs, hCs, hshell⟩ := exists_pvShellCurlComponent_bound
  obtain ⟨Cf, hCf, hfar⟩ := exists_pvFarCurlComponent_bound
  refine ⟨27 * Cn, 27 * (Cs + 1), 27 * Cf,
    by positivity, by positivity, by positivity, ?_⟩
  intro u hdiv H₂ Mω M₂ hH₂ hMω hM₂ ρ hρ hρ1 x
  have hH₂0 : 0 ≤ H₂ :=
    (sobolevH2NormSq_nonneg (staticCurlSchwartz u)).trans hH₂
  have hMω0 : 0 ≤ Mω :=
    (officialEuclideanNorm_nonneg (staticCurl (⇑u) 0)).trans (hMω 0)
  have hM₂0 : 0 ≤ M₂ :=
    (integral_nonneg fun y => sq_nonneg
      (officialEuclideanNorm (staticCurl (⇑u) y))).trans hM₂
  have hlog : 0 ≤ Real.log (1 / ρ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
  let R : ℝ :=
    Cn * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂ +
      Cs * Mω * (1 + Real.log (1 / ρ)) + Cf * Real.sqrt M₂
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hpv : ∀ i j k : Fin 3,
      |principalValueConvolution i j (curlComponentSchwartz u k) x| ≤ R := by
    intro i j k
    exact principalValue_curlComponent_bound Cn Cs Cf hnear hshell hfar
      u H₂ Mω M₂ hH₂ hMω hM₂ ρ hρ hρ1 x i j k
  have hentry : ∀ i l : Fin 3,
      |fderiv ℝ (⇑u) x (basisVector i) l| ≤ 9 * (R + Mω) := by
    intro i l
    rw [fderiv_eq_principalValueConvolution_curl u hdiv x i l]
    calc
      |∑ k : Fin 3, ∑ j : Fin 3,
          (basisVector k ⨯₃ basisVector j) l *
            (principalValueConvolution i j (curlComponentSchwartz u k) x +
              (1 / 3 : ℝ) * basisVector i j * staticCurl (⇑u) x k)|
          ≤ ∑ k : Fin 3, |∑ j : Fin 3,
            (basisVector k ⨯₃ basisVector j) l *
              (principalValueConvolution i j (curlComponentSchwartz u k) x +
                (1 / 3 : ℝ) * basisVector i j * staticCurl (⇑u) x k)| := by
        simpa [Real.norm_eq_abs] using
          (norm_sum_le Finset.univ (fun k : Fin 3 => ∑ j : Fin 3,
            (basisVector k ⨯₃ basisVector j) l *
              (principalValueConvolution i j (curlComponentSchwartz u k) x +
                (1 / 3 : ℝ) * basisVector i j * staticCurl (⇑u) x k)))
      _ ≤ ∑ k : Fin 3, ∑ j : Fin 3,
          |(basisVector k ⨯₃ basisVector j) l *
            (principalValueConvolution i j (curlComponentSchwartz u k) x +
              (1 / 3 : ℝ) * basisVector i j * staticCurl (⇑u) x k)| := by
        refine Finset.sum_le_sum fun k _ => ?_
        simpa [Real.norm_eq_abs] using
          (norm_sum_le Finset.univ (fun j : Fin 3 =>
            (basisVector k ⨯₃ basisVector j) l *
              (principalValueConvolution i j (curlComponentSchwartz u k) x +
                (1 / 3 : ℝ) * basisVector i j * staticCurl (⇑u) x k)))
      _ ≤ ∑ _k : Fin 3, ∑ _j : Fin 3, (R + Mω) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        have hcurl : |staticCurl (⇑u) x k| ≤ Mω :=
          (coord_abs_le_officialEuclideanNorm _ k).trans (hMω x)
        have hlocal : |(1 / 3 : ℝ) * basisVector i j *
            staticCurl (⇑u) x k| ≤ Mω := by
          rw [abs_mul, abs_mul]
          have hthird : |(1 / 3 : ℝ)| ≤ 1 := by norm_num
          calc
            |(1 / 3 : ℝ)| * |basisVector i j| * |staticCurl (⇑u) x k|
                ≤ 1 * 1 * Mω :=
              mul_le_mul (mul_le_mul hthird (abs_basisVector_le_one i j)
                (abs_nonneg _) (by norm_num)) hcurl
                (abs_nonneg _) (by positivity)
            _ = Mω := by ring
        have hbracket : |principalValueConvolution i j
            (curlComponentSchwartz u k) x +
              (1 / 3 : ℝ) * basisVector i j * staticCurl (⇑u) x k| ≤
            R + Mω :=
          (abs_add_le _ _).trans (add_le_add (hpv i j k) hlocal)
        exact (mul_le_mul (abs_cross_basis_le_one k j l) hbracket
          (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = 9 * (R + Mω) := by simp; ring
  have hcolumn : ∀ i : Fin 3,
      ‖fderiv ℝ (⇑u) x (basisVector i)‖ ≤ 9 * (R + Mω) := by
    intro i
    refine (pi_norm_le_iff_of_nonneg ?_).2 fun l => ?_
    · positivity
    · rw [Real.norm_eq_abs]
      exact hentry i l
  calc
    ‖fderiv ℝ (⇑u) x‖ ≤
        ∑ i : Fin 3, ‖fderiv ℝ (⇑u) x (basisVector i)‖ :=
      opNorm_le_sum_basisVector _
    _ ≤ ∑ _i : Fin 3, 9 * (R + Mω) :=
      Finset.sum_le_sum fun i _ => hcolumn i
    _ = 27 * (R + Mω) := by simp; ring
    _ ≤ (27 * Cn) * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂ +
        (27 * (Cs + 1)) * Mω * (1 + Real.log (1 / ρ)) +
        (27 * Cf) * Real.sqrt M₂ := by
      dsimp only [R]
      nlinarith [mul_nonneg hMω0 hlog]

end Navier.Analysis.BiotSavartPVAssembly
