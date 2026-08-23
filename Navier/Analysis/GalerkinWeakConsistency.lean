import Navier.Analysis.GalerkinBasis
import Navier.Analysis.Ladyzhenskaya

/-!
# Galerkin weak-consistency commutator identities

This file isolates the exact representation transport used by the remaining
Galerkin weak-consistency limit.  It does not assume convergence of the
projection in a stronger norm.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.GalerkinBasis

open Navier
open MeasureTheory

/-- Against a retained Galerkin field, the Laplacian/projection commutator is
exactly the negative curl pairing with the test projection error.

This is the whole-space Schwartz integration-by-parts form of
`coefficientField_pairing_proj`; it exposes the genuinely remaining task as
control of `curl (P_m phi - phi)` rather than a raw commutator limit.

Citation: Temam, *Navier--Stokes Equations*, Chapter III, Section 3. -/
theorem coefficientField_laplacianProjectionCommutator_pairing_eq_neg_curl_error
    (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (φ : SchwartzVelocity)
    (hφ : DivergenceFreeInitial φ) :
    schwartzL2Inner (W.coefficientField a)
        (W.laplacianProjectionCommutator m φ) =
      -schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
        (curlSchwartzCLM (W.proj m φ - φ)) := by
  have hpairSub :
      schwartzL2Inner (W.coefficientField a)
          (laplacianSchwartz (W.proj m φ) - W.proj m (laplacianSchwartz φ)) =
        schwartzL2Inner (W.coefficientField a) (laplacianSchwartz (W.proj m φ)) -
          schwartzL2Inner (W.coefficientField a) (W.proj m (laplacianSchwartz φ)) := by
    calc
      schwartzL2Inner (W.coefficientField a)
          (laplacianSchwartz (W.proj m φ) - W.proj m (laplacianSchwartz φ)) =
          schwartzL2Inner
            (laplacianSchwartz (W.proj m φ) - W.proj m (laplacianSchwartz φ))
            (W.coefficientField a) := schwartzL2Inner_comm _ _
      _ = schwartzL2Inner (laplacianSchwartz (W.proj m φ)) (W.coefficientField a) -
          schwartzL2Inner (W.proj m (laplacianSchwartz φ))
            (W.coefficientField a) := schwartzL2Inner_sub_left _ _ _
      _ = schwartzL2Inner (W.coefficientField a) (laplacianSchwartz (W.proj m φ)) -
          schwartzL2Inner (W.coefficientField a)
            (W.proj m (laplacianSchwartz φ)) := by
              rw [schwartzL2Inner_comm (laplacianSchwartz (W.proj m φ)),
                schwartzL2Inner_comm (W.proj m (laplacianSchwartz φ))]
  have hcurlSub :
      schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
          (curlSchwartzCLM (W.proj m φ - φ)) =
        schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
            (curlSchwartzCLM (W.proj m φ)) -
          schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
            (curlSchwartzCLM φ) := by
    calc
      schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
          (curlSchwartzCLM (W.proj m φ - φ)) =
          schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
            (curlSchwartzCLM (W.proj m φ) - curlSchwartzCLM φ) := by rw [map_sub]
      _ = schwartzL2Inner
          (curlSchwartzCLM (W.proj m φ) - curlSchwartzCLM φ)
          (curlSchwartzCLM (W.coefficientField a)) := schwartzL2Inner_comm _ _
      _ = schwartzL2Inner (curlSchwartzCLM (W.proj m φ))
            (curlSchwartzCLM (W.coefficientField a)) -
          schwartzL2Inner (curlSchwartzCLM φ)
            (curlSchwartzCLM (W.coefficientField a)) :=
        schwartzL2Inner_sub_left _ _ _
      _ = schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
            (curlSchwartzCLM (W.proj m φ)) -
          schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
            (curlSchwartzCLM φ) := by
              rw [schwartzL2Inner_comm (curlSchwartzCLM (W.proj m φ)),
                schwartzL2Inner_comm (curlSchwartzCLM φ)]
  have hproj := coefficientField_pairing_proj W a (laplacianSchwartz φ)
  have hprojCurl := schwartzL2Inner_curl_eq_neg_laplacian
    (W.coefficientField a) (W.proj m φ) (proj_divergence_free W m φ)
  have hφCurl := schwartzL2Inner_curl_eq_neg_laplacian
    (W.coefficientField a) φ hφ
  unfold GalerkinBasisFamily.laplacianProjectionCommutator
  rw [hpairSub, hproj, hcurlSub]
  linarith

/-- Sharp Cauchy--Schwarz control of the Laplacian/projection commutator by
modal enstrophy and the fixed test's curl projection error.

The constant is exactly one.  In particular, this theorem does not assume that
the displayed error norm tends to zero; that stronger approximation property
remains a separate basis-realization obligation.

Citation: Temam, *Navier--Stokes Equations*, Chapter III, Section 3. -/
theorem abs_coefficientField_laplacianProjectionCommutator_pairing_le
    (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (φ : SchwartzVelocity)
    (hφ : DivergenceFreeInitial φ) :
    |schwartzL2Inner (W.coefficientField a)
        (W.laplacianProjectionCommutator m φ)| ≤
      Real.sqrt (W.coefficientEnstrophy a) *
        ‖toL2 (curlSchwartzCLM (W.proj m φ - φ))‖ := by
  rw [coefficientField_laplacianProjectionCommutator_pairing_eq_neg_curl_error
    W a φ hφ, abs_neg]
  have hcs := abs_schwartzL2Inner_le
    (curlSchwartzCLM (W.coefficientField a))
    (curlSchwartzCLM (W.proj m φ - φ))
  have henstrophyNorm :
      ‖toL2 (curlSchwartzCLM (W.coefficientField a))‖ =
        Real.sqrt (W.coefficientEnstrophy a) := by
    rw [coefficientEnstrophy_eq_curlSchwartz, ← norm_toL2_sq]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [henstrophyNorm] at hcs
  exact hcs

/-- Spacetime Cauchy--Schwarz control of the Laplacian/projection commutator.

The modal enstrophy budget is the only PDE estimate used.  Integrability of
the fixed test's squared curl-projection error is explicit, and no convergence
of that error (in particular no `H¹` projection convergence) is assumed.

Citation: Temam, *Navier--Stokes Equations*, Chapter III, Section 3. -/
theorem abs_intervalIntegral_laplacianProjectionCommutator_le
    (W : GalerkinBasisFamily) {m : ℕ}
    (c : ℝ → EuclideanSpace ℝ (Fin m)) (φ : ℝ → SchwartzVelocity)
    (hφ : ∀ t, DivergenceFreeInitial (φ t))
    (ν T enstrophyBound : ℝ) (hT : 0 ≤ T)
    (henstrophy :
      (∫ t in Set.Ioc (0 : ℝ) T, W.coefficientEnstrophy (c t)) ≤ enstrophyBound)
    (henstrophyIntegrable : IntegrableOn
      (fun t => W.coefficientEnstrophy (c t)) (Set.Ioc (0 : ℝ) T))
    (errorSqIntegrable : IntegrableOn (fun t =>
      ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
      (Set.Ioc (0 : ℝ) T))
    (pairingIntervalIntegrable : IntervalIntegrable (fun t =>
      ν * schwartzL2Inner (W.coefficientField (c t))
        (W.laplacianProjectionCommutator m (φ t))) volume 0 T) :
    |∫ t in (0 : ℝ)..T, ν * schwartzL2Inner (W.coefficientField (c t))
        (W.laplacianProjectionCommutator m (φ t))| ≤
      |ν| * Real.sqrt enstrophyBound * Real.sqrt
        (∫ t in Set.Ioc (0 : ℝ) T,
          ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2) := by
  let Ω : ℝ → ℝ := fun t => W.coefficientEnstrophy (c t)
  let err : ℝ → ℝ := fun t =>
    ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖
  let pair : ℝ → ℝ := fun t => schwartzL2Inner (W.coefficientField (c t))
    (W.laplacianProjectionCommutator m (φ t))
  have hΩ0 : ∀ t, 0 ≤ Ω t := by
    intro t
    dsimp only [Ω]
    unfold GalerkinBasisFamily.coefficientEnstrophy
    exact integral_nonneg fun _ => by positivity
  have herr0 : ∀ t, 0 ≤ err t := fun _ => norm_nonneg _
  have hpoint : ∀ t, |pair t| ≤ Real.sqrt (Ω t) * err t := by
    intro t
    simpa only [pair, Ω, err] using
      abs_coefficientField_laplacianProjectionCommutator_pairing_le
        W (c t) (φ t) (hφ t)
  have hsqrtΩMeas : AEStronglyMeasurable (fun t => Real.sqrt (Ω t))
      (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      henstrophyIntegrable.aestronglyMeasurable
  have herrMeas : AEStronglyMeasurable err
      (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
    have h := Real.continuous_sqrt.comp_aestronglyMeasurable
      errorSqIntegrable.aestronglyMeasurable
    simpa only [err, Real.sqrt_sq (norm_nonneg _)] using h
  have hsqrtΩSqIntegrable : IntegrableOn (fun t => (Real.sqrt (Ω t)) ^ 2)
      (Set.Ioc (0 : ℝ) T) := by
    refine henstrophyIntegrable.congr ?_
    filter_upwards with t
    exact (Real.sq_sqrt (hΩ0 t)).symm
  have herrorSqIntegrable : IntegrableOn (fun t => err t ^ 2)
      (Set.Ioc (0 : ℝ) T) := by
    simpa only [err] using errorSqIntegrable
  have hsqrtProductIntegrable : IntegrableOn
      (fun t => Real.sqrt (Ω t) * err t) (Set.Ioc (0 : ℝ) T) := by
    have hf : MemLp (fun t => Real.sqrt (Ω t)) 2
        (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
      (memLp_two_iff_integrable_sq hsqrtΩMeas).mpr hsqrtΩSqIntegrable
    have hg : MemLp err 2 (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
      (memLp_two_iff_integrable_sq herrMeas).mpr herrorSqIntegrable
    exact hf.integrable_mul hg
  have hcs :
      (∫ t in Set.Ioc (0 : ℝ) T, Real.sqrt (Ω t) * err t) ≤
        Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Ω t) *
          Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2) :=
    calc
      (∫ t in Set.Ioc (0 : ℝ) T, Real.sqrt (Ω t) * err t) ≤
          Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, (Real.sqrt (Ω t)) ^ 2) *
            Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2) :=
        Navier.Analysis.Ladyzhenskaya.integral_mul_le_sqrt_mul_sqrt
          (μ := volume.restrict (Set.Ioc (0 : ℝ) T))
          (fun t => Real.sqrt_nonneg _) herr0 hsqrtΩMeas herrMeas
          hsqrtΩSqIntegrable herrorSqIntegrable
      _ = Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Ω t) *
            Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2) := by
        congr 2
        apply integral_congr_ae
        filter_upwards with t
        exact Real.sq_sqrt (hΩ0 t)
  have hpairAbsIntegrable : IntegrableOn (fun t => |ν * pair t|)
      (Set.Ioc (0 : ℝ) T) := by
    change Integrable (fun t => |ν * pair t|)
      (volume.restrict (Set.Ioc (0 : ℝ) T))
    simpa only [pair] using pairingIntervalIntegrable.1.abs
  have hmajorantIntegrable : IntegrableOn
      (fun t => |ν| * (Real.sqrt (Ω t) * err t)) (Set.Ioc (0 : ℝ) T) :=
    hsqrtProductIntegrable.const_mul _
  rw [intervalIntegral.integral_of_le hT]
  calc
    |∫ t in Set.Ioc (0 : ℝ) T, ν * pair t| ≤
        ∫ t in Set.Ioc (0 : ℝ) T, |ν * pair t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) T,
        |ν| * (Real.sqrt (Ω t) * err t) :=
      integral_mono hpairAbsIntegrable hmajorantIntegrable fun t => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpoint t) (abs_nonneg ν)
    _ = |ν| * (∫ t in Set.Ioc (0 : ℝ) T, Real.sqrt (Ω t) * err t) :=
      integral_const_mul _ _
    _ ≤ |ν| * (Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Ω t) *
        Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2)) :=
      mul_le_mul_of_nonneg_left hcs (abs_nonneg ν)
    _ ≤ |ν| * (Real.sqrt enstrophyBound *
        Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ν)
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt henstrophy)
        (Real.sqrt_nonneg _)
    _ = |ν| * Real.sqrt enstrophyBound * Real.sqrt
        (∫ t in Set.Ioc (0 : ℝ) T,
          ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2) := by
      simp only [err]
      ring

end Navier.Analysis.GalerkinBasis
