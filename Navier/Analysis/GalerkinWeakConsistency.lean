import Navier.Analysis.GalerkinBasis
import Navier.Analysis.Ladyzhenskaya
import Navier.Analysis.ConvectionTrilinear

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
open Navier.Analysis.LerayWeak
open Navier.Analysis.OfficialABEncoding

/-- Quantitative continuity of the fixed-time Galerkin weak pairing in the
natural test topology.

The time leg is continuous in `L²`, the viscous leg in the divergence-free
`H¹` curl norm, and the convection leg in the `L²` norm of the spatial
derivative.  Every coefficient depending on the velocity is displayed.  Thus
this is the honest continuity contract needed to extend weak consistency from
eventually retained tests by density; it does not assert that the present
`L²`-dense Galerkin basis is dense in these stronger spacetime test norms.

Citation: Temam, *Navier--Stokes Equations*, Chapter III, Section 3. -/
theorem abs_modalWeakPairing_le_testH1Gauge
    (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (φ φ' : SchwartzVelocity)
    (hφ : DivergenceFreeInitial φ) (ν : ℝ) :
    |schwartzL2Inner (W.coefficientField a) φ' +
      schwartzL2Inner (W.coefficientField a)
        (ν • laplacianSchwartz φ +
          convectionSchwartzBilin (W.coefficientField a) φ)| ≤
      ‖toL2 (W.coefficientField a)‖ * ‖toL2 φ'‖ +
      |ν| * Real.sqrt (W.coefficientEnstrophy a) *
        ‖toL2 (curlSchwartzCLM φ)‖ +
      Real.sqrt 3 *
        ((∫ x : Space,
          officialEuclideanNorm ((W.coefficientField a) x) ^ 4) ^ (1 / 4 : ℝ) *
        (∫ x : Space, ‖fderiv ℝ (⇑φ) x‖ ^ 2) ^ (1 / 2 : ℝ) *
        (∫ x : Space,
          officialEuclideanNorm ((W.coefficientField a) x) ^ 4) ^ (1 / 4 : ℝ)) := by
  have ht := abs_schwartzL2Inner_le (W.coefficientField a) φ'
  have hc := Navier.Analysis.ConvectionTrilinear.abs_schwartzL2Inner_convection_le
    (W.coefficientField a) (W.coefficientField a) φ
  have hv0 := schwartzL2Inner_curl_eq_neg_laplacian
    (W.coefficientField a) φ hφ
  have hvcs := abs_schwartzL2Inner_le
    (curlSchwartzCLM (W.coefficientField a)) (curlSchwartzCLM φ)
  have hven : ‖toL2 (curlSchwartzCLM (W.coefficientField a))‖ =
      Real.sqrt (W.coefficientEnstrophy a) := by
    rw [coefficientEnstrophy_eq_curlSchwartz, ← norm_toL2_sq]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [hven] at hvcs
  rw [schwartzL2Inner_add_right, schwartzL2Inner_smul_right]
  have hv : |ν * schwartzL2Inner (W.coefficientField a) (laplacianSchwartz φ)| ≤
      |ν| * Real.sqrt (W.coefficientEnstrophy a) *
        ‖toL2 (curlSchwartzCLM φ)‖ := by
    rw [abs_mul, ← neg_eq_iff_eq_neg.mpr hv0, abs_neg]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hvcs (abs_nonneg ν)
  calc
    |schwartzL2Inner (W.coefficientField a) φ' +
        (ν * schwartzL2Inner (W.coefficientField a) (laplacianSchwartz φ) +
          schwartzL2Inner (W.coefficientField a)
            (convectionSchwartzBilin (W.coefficientField a) φ))| ≤
        |schwartzL2Inner (W.coefficientField a) φ'| +
          |ν * schwartzL2Inner (W.coefficientField a) (laplacianSchwartz φ)| +
          |schwartzL2Inner (W.coefficientField a)
            (convectionSchwartzBilin (W.coefficientField a) φ)| := by
      rw [← add_assoc]
      exact abs_add_three _ _ _
    _ ≤ _ := add_le_add (add_le_add ht hv) hc

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

/-- Dominated convergence for the spacetime squared curl-projection error.

The input is genuinely pointwise: the unsquared curl-error norms converge to
zero almost everywhere, while one integrable function dominates every squared
error.  Thus this theorem does not assume the desired convergence of the
integrals, nor does it claim that the current `L²`-only basis supplies these
hypotheses.

Citation: Folland, *Real Analysis*, Theorem 2.24. -/
theorem integral_curlProjectionError_sq_tendsto_zero_of_dominated
    (W : GalerkinBasisFamily) (φ : ℝ → SchwartzVelocity) (T : ℝ)
    (bound : ℝ → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable (fun t =>
      ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) T)))
    (hBoundIntegrable : IntegrableOn bound (Set.Ioc (0 : ℝ) T))
    (hBound : ∀ m, ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2 ≤ bound t)
    (hPoint : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      Filter.Tendsto (fun m =>
        ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m =>
      ∫ t in Set.Ioc (0 : ℝ) T,
        ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
      Filter.atTop (nhds 0) := by
  have hBoundNorm : ∀ m, ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      ‖‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2‖ ≤ bound t := by
    intro m
    filter_upwards [hBound m] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact ht
  have hSqPoint : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      Filter.Tendsto (fun m =>
        ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
        Filter.atTop (nhds 0) := by
    filter_upwards [hPoint] with t ht
    simpa using ht.pow 2
  simpa using MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc (0 : ℝ) T))
    (F := fun m t => ‖toL2
      (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
    (f := fun _ => 0) bound hMeas hBoundIntegrable hBoundNorm hSqPoint

/-- The dominated curl-error bridge closes the viscous commutator limit under
a uniform modal enstrophy budget.

This is the direct `hlap`-shaped consumer of
`integral_curlProjectionError_sq_tendsto_zero_of_dominated`: dominated
convergence first makes the test error vanish in spacetime, and the preceding
Cauchy--Schwarz estimate then squeezes the commutator integral to zero.

Citation: Temam, *Navier--Stokes Equations*, Chapter III, Section 3. -/
theorem intervalIntegral_laplacianProjectionCommutator_tendsto_zero_of_dominated
    (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (φ : ℝ → SchwartzVelocity) (hφ : ∀ t, DivergenceFreeInitial (φ t))
    (ν T enstrophyBound : ℝ) (hT : 0 ≤ T)
    (henstrophy : ∀ m,
      (∫ t in Set.Ioc (0 : ℝ) T, W.coefficientEnstrophy (c m t)) ≤
        enstrophyBound)
    (henstrophyIntegrable : ∀ m, IntegrableOn
      (fun t => W.coefficientEnstrophy (c m t)) (Set.Ioc (0 : ℝ) T))
    (pairingIntervalIntegrable : ∀ m, IntervalIntegrable (fun t =>
      ν * schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (φ t))) volume 0 T)
    (bound : ℝ → ℝ)
    (hErrorMeas : ∀ m, AEStronglyMeasurable (fun t =>
      ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) T)))
    (hBoundIntegrable : IntegrableOn bound (Set.Ioc (0 : ℝ) T))
    (hBound : ∀ m, ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2 ≤ bound t)
    (hPoint : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      Filter.Tendsto (fun m =>
        ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m =>
      ∫ t in (0 : ℝ)..T, ν * schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (φ t)))
      Filter.atTop (nhds 0) := by
  have herror := integral_curlProjectionError_sq_tendsto_zero_of_dominated
    W φ T bound hErrorMeas hBoundIntegrable hBound hPoint
  apply squeeze_zero_norm (a := fun m =>
    |ν| * Real.sqrt enstrophyBound * Real.sqrt
      (∫ t in Set.Ioc (0 : ℝ) T,
        ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2))
  · intro m
    rw [Real.norm_eq_abs]
    have hErrorInt : IntegrableOn (fun t =>
        ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
        (Set.Ioc (0 : ℝ) T) := by
      refine Integrable.mono' hBoundIntegrable (hErrorMeas m) ?_
      filter_upwards [hBound m] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact ht
    exact abs_intervalIntegral_laplacianProjectionCommutator_le
      W (c m) φ hφ ν T enstrophyBound hT (henstrophy m)
        (henstrophyIntegrable m) hErrorInt (pairingIntervalIntegrable m)
  · have hsqrt := herror.sqrt
    have hconst : Filter.Tendsto (fun _ : ℕ => |ν| * Real.sqrt enstrophyBound)
        Filter.atTop (nhds (|ν| * Real.sqrt enstrophyBound)) := tendsto_const_nhds
    simpa using hconst.mul hsqrt

/-- The concrete Schwartz-to-`L²` map preserves zero. -/
theorem toL2_zero : toL2 (0 : SchwartzVelocity) = 0 := by
  simpa using toL2_smul 0 (0 : SchwartzVelocity)

/-- Nested Galerkin projections stabilize: projecting an `M`-mode field onto
any larger retained span changes nothing.

This is finite orthonormality algebra, independent of density or any Sobolev
stability claim.

Citation: Temam, *Navier--Stokes Equations*, Chapter III, Section 3. -/
theorem proj_proj_of_le (W : GalerkinBasisFamily) {M m : ℕ}
    (hMm : M ≤ m) (u : SchwartzVelocity) :
    W.proj m (W.proj M u) = W.proj M u := by
  change W.proj m (∑ j ∈ Finset.range M, W.coeff u j • W.w j) =
    ∑ j ∈ Finset.range M, W.coeff u j • W.w j
  have hcoeff (i : ℕ) :
      W.coeff (∑ j ∈ Finset.range M, W.coeff u j • W.w j) i =
        if i < M then W.coeff u i else 0 := by
    unfold GalerkinBasisFamily.coeff
    rw [schwartzL2Inner_sum_left]
    by_cases hi : i < M
    · rw [if_pos hi, Finset.sum_eq_single i]
      · rw [schwartzL2Inner_smul_left, W.orthonormal i i, if_pos rfl, mul_one]
      · intro j _ hji
        rw [schwartzL2Inner_smul_left, W.orthonormal j i,
          if_neg hji, mul_zero]
      · exact fun hi' => (hi' (Finset.mem_range.mpr hi)).elim
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j ≠ i := by
        intro hji
        subst i
        exact hi (Finset.mem_range.mp hj)
      rw [schwartzL2Inner_smul_left, W.orthonormal j i,
        if_neg hji, mul_zero]
  unfold GalerkinBasisFamily.proj
  conv_lhs =>
    enter [2, i]
    rw [hcoeff i]
  rw [← Finset.sum_subset (Finset.range_mono hMm) (fun i _ hiM => by
    have hnot : ¬i < M := by simpa only [Finset.mem_range] using hiM
    simp only [hnot, if_false, zero_smul])]
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos (Finset.mem_range.mp hi)]

/-- A time-dependent Schwartz test fixed by one finite Galerkin projection has
identically zero curl-projection error at every later projection level. -/
theorem curlProjectionError_sq_eventually_zero_of_fixed_proj
    (W : GalerkinBasisFamily) (φ : ℝ → SchwartzVelocity) (M : ℕ)
    (hretained : ∀ t, W.proj M (φ t) = φ t) :
    ∀ᶠ m in Filter.atTop, ∀ t,
      ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2 = 0 := by
  filter_upwards [Filter.eventually_ge_atTop M] with m hm
  intro t
  have hproj : W.proj m (φ t) = φ t := by
    calc
      W.proj m (φ t) = W.proj m (W.proj M (φ t)) := by rw [hretained t]
      _ = W.proj M (φ t) := proj_proj_of_le W hm (φ t)
      _ = φ t := hretained t
  simp only [hproj, sub_self, map_zero, toL2_zero, norm_zero]
  norm_num

/-- On the eventually retained test class, the spacetime curl-projection error
integral is eventually exactly zero, hence converges to zero without a
dominated-convergence hypothesis. -/
theorem integral_curlProjectionError_sq_tendsto_zero_of_fixed_proj
    (W : GalerkinBasisFamily) (φ : ℝ → SchwartzVelocity) (M : ℕ)
    (hretained : ∀ t, W.proj M (φ t) = φ t) (T : ℝ) :
    Filter.Tendsto (fun m =>
      ∫ t in Set.Ioc (0 : ℝ) T,
        ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
      Filter.atTop (nhds 0) := by
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [curlProjectionError_sq_eventually_zero_of_fixed_proj
    W φ M hretained] with m hm
  symm
  simp_rw [hm]
  simp

/-- The viscous projection commutator vanishes against every modal field for
an eventually retained time-dependent divergence-free test.  Consequently its
interval integral is eventually exactly zero for arbitrary coefficient curves,
viscosity, and time horizon.

This is a non-asymptotic concrete consumer: it needs neither an enstrophy bound
nor measurability/integrability premises because stabilization makes the scalar
integrand identically zero.

Citation: Temam, *Navier--Stokes Equations*, Chapter III, Section 3. -/
theorem intervalIntegral_laplacianProjectionCommutator_tendsto_zero_of_fixed_proj
    (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (φ : ℝ → SchwartzVelocity) (hφ : ∀ t, DivergenceFreeInitial (φ t))
    (M : ℕ) (hretained : ∀ t, W.proj M (φ t) = φ t)
    (ν T : ℝ) :
    Filter.Tendsto (fun m =>
      ∫ t in (0 : ℝ)..T, ν * schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (φ t)))
      Filter.atTop (nhds 0) := by
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop M] with m hm
  have hproj (t : ℝ) : W.proj m (φ t) = φ t := by
    calc
      W.proj m (φ t) = W.proj m (W.proj M (φ t)) := by rw [hretained t]
      _ = W.proj M (φ t) := proj_proj_of_le W hm (φ t)
      _ = φ t := hretained t
  have hpair (t : ℝ) :
      schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (φ t)) = 0 := by
    rw [coefficientField_laplacianProjectionCommutator_pairing_eq_neg_curl_error
      W (c m t) (φ t) (hφ t), hproj t]
    rw [sub_self, map_zero, schwartzL2Inner_comm,
      schwartzL2Inner_zero_left, neg_zero]
  simp_rw [hpair, mul_zero]
  symm
  simp

/-- Fully concrete specialization: projecting any time-dependent Schwartz
family once produces an eventually retained divergence-free test family whose
viscous commutator integral vanishes.  No convergence, domination, energy, or
integrability hypothesis is needed. -/
theorem intervalIntegral_laplacianProjectionCommutator_tendsto_zero_projectedTest
    (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (ψ : ℝ → SchwartzVelocity) (M : ℕ) (ν T : ℝ) :
    Filter.Tendsto (fun m =>
      ∫ t in (0 : ℝ)..T, ν * schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (W.proj M (ψ t))))
      Filter.atTop (nhds 0) := by
  apply intervalIntegral_laplacianProjectionCommutator_tendsto_zero_of_fixed_proj
    W c (fun t => W.proj M (ψ t))
    (fun t => proj_divergence_free W M (ψ t)) M
    (fun t => proj_proj_of_le W le_rfl (ψ t)) ν T

/-- The nonlinear test-projection commutator is eventually zero for a
time-dependent test fixed by one finite Galerkin projection.  Unlike the
general nonlinear limit, this needs no velocity bound: the test error itself
is identically zero at every level `m ≥ M`. -/
theorem intervalIntegral_convectionTestProjectionCommutator_tendsto_zero_of_fixed_proj
    (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (φ : ℝ → SchwartzVelocity) (M : ℕ)
    (hretained : ∀ t, W.proj M (φ t) = φ t) (T : ℝ) :
    Filter.Tendsto (fun m =>
      ∫ t in (0 : ℝ)..T, schwartzL2Inner (W.coefficientField (c m t))
        (W.convectionTestProjectionCommutator m
          (W.coefficientField (c m t)) (φ t)))
      Filter.atTop (nhds 0) := by
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop M] with m hm
  have hproj (t : ℝ) : W.proj m (φ t) = φ t := by
    calc
      W.proj m (φ t) = W.proj m (W.proj M (φ t)) := by rw [hretained t]
      _ = W.proj M (φ t) := proj_proj_of_le W hm (φ t)
      _ = φ t := hretained t
  have hcomm (t : ℝ) :
      W.convectionTestProjectionCommutator m
        (W.coefficientField (c m t)) (φ t) = 0 := by
    unfold GalerkinBasisFamily.convectionTestProjectionCommutator
    rw [hproj t, sub_self]
    unfold convectionSchwartzBilin
    have hderiv : ∀ i : Fin 3,
        LineDeriv.lineDerivOp (basisVector i) (0 : SchwartzVelocity) = 0 := by
      intro i
      exact map_zero (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i))
    simp [hderiv]
  have hpair (t : ℝ) :
      schwartzL2Inner (W.coefficientField (c m t))
        (W.convectionTestProjectionCommutator m
          (W.coefficientField (c m t)) (φ t)) = 0 := by
    rw [hcomm t, schwartzL2Inner_comm, schwartzL2Inner_zero_left]
  simp_rw [hpair]
  symm
  simp

/-- Weak consistency for the exact eventually retained test class.

For a divergence-free test whose spatial slices are fixed by `P_M`, both
projection commutators are identically zero for `m ≥ M`.  Their interval
integrability and integrals are therefore automatic on that tail; the retained
ODE identity makes the projected weak residual eventually zero, and
`modalApprox_fixedTest_weakConsistent_of_projectedDatum` removes the initial
projection correction.

The ODE, common window, time differentiation, and main-term integrability
premises are deliberately retained.  No commutator limit or commutator
integrability premise remains, and no density extension to arbitrary tests is
claimed.

Citation: Temam, *Navier--Stokes Equations*, Chapter III, Section 3. -/
theorem modalApprox_fixedTest_weakConsistent_of_fixed_proj
    (W : GalerkinBasisFamily) (ν : ℝ)
    (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (hc0 : ∀ m, c m 0 = W.initialCoefficients u₀ m)
    (φ : DivergenceFreeTestFunction)
    (M : ℕ) (hretained : ∀ t, W.proj M (φ.field t) = φ.field t)
    (T : ℝ) (hT : 0 ≤ T) (hφzero : ∀ t, T ≤ t → φ.field t = 0)
    (hφ'zero : ∀ t, T ≤ t → φ.timeDerivSchwartz t = 0)
    (hmodal_deriv : ∀ (m : ℕ) (t : ℝ),
      HasDerivAt (W.modalTestCoefficients φ.field m)
        (W.modalTestCoefficients φ.timeDerivSchwartz m t) t)
    (hmodal_deriv_cont : ∀ m,
      Continuous (W.modalTestCoefficients φ.timeDerivSchwartz m))
    (hmainInt : ∀ m, IntervalIntegrable (fun t =>
      schwartzL2Inner (W.coefficientField (c m t)) (φ.timeDerivSchwartz t) +
      schwartzL2Inner (W.coefficientField (c m t))
        (ν • laplacianSchwartz (φ.field t) +
          convectionSchwartzBilin (W.coefficientField (c m t)) (φ.field t)))
      volume 0 T) :
    Filter.Tendsto
      (fun m => weakFormResidual ν u₀ (W.modalApprox c m) φ)
      Filter.atTop (nhds 0) := by
  have hprojected : Filter.Tendsto
      (fun m => weakFormResidual ν (W.proj m u₀) (W.modalApprox c m) φ)
      Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop M] with m hm
    have hproj (t : ℝ) : W.proj m (φ.field t) = φ.field t := by
      calc
        W.proj m (φ.field t) = W.proj m (W.proj M (φ.field t)) := by
          rw [hretained t]
        _ = W.proj M (φ.field t) := proj_proj_of_le W hm (φ.field t)
        _ = φ.field t := hretained t
    have hlapPair (t : ℝ) :
        schwartzL2Inner (W.coefficientField (c m t))
          (W.laplacianProjectionCommutator m (φ.field t)) = 0 := by
      rw [coefficientField_laplacianProjectionCommutator_pairing_eq_neg_curl_error
        W (c m t) (φ.field t) (φ.divergence_free t), hproj t]
      rw [sub_self, map_zero, schwartzL2Inner_comm,
        schwartzL2Inner_zero_left, neg_zero]
    have hconvField (t : ℝ) :
        W.convectionTestProjectionCommutator m
          (W.coefficientField (c m t)) (φ.field t) = 0 := by
      unfold GalerkinBasisFamily.convectionTestProjectionCommutator
      rw [hproj t, sub_self]
      unfold convectionSchwartzBilin
      have hderiv : ∀ i : Fin 3,
          LineDeriv.lineDerivOp (basisVector i) (0 : SchwartzVelocity) = 0 := by
        intro i
        exact map_zero (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i))
      simp [hderiv]
    have hconvPair (t : ℝ) :
        schwartzL2Inner (W.coefficientField (c m t))
          (W.convectionTestProjectionCommutator m
            (W.coefficientField (c m t)) (φ.field t)) = 0 := by
      rw [hconvField t, schwartzL2Inner_comm, schwartzL2Inner_zero_left]
    have hlapInt : IntervalIntegrable (fun t =>
        ν * schwartzL2Inner (W.coefficientField (c m t))
          (W.laplacianProjectionCommutator m (φ.field t))) volume 0 T := by
      simpa only [hlapPair, mul_zero] using
        (intervalIntegrable_const (c := (0 : ℝ)) (μ := volume) (a := 0) (b := T))
    have hconvInt : IntervalIntegrable (fun t =>
        schwartzL2Inner (W.coefficientField (c m t))
          (W.convectionTestProjectionCommutator m
            (W.coefficientField (c m t)) (φ.field t))) volume 0 T := by
      simpa only [hconvPair] using
        (intervalIntegrable_const (c := (0 : ℝ)) (μ := volume) (a := 0) (b := T))
    have heq := modalFlow_projectedTest_splitResidualWeakEquation_at
      W ν c hc φ φ.timeDerivSchwartz T hT hφzero m
        (hmodal_deriv m) (hmodal_deriv_cont m)
    have hidentify := weakFormResidual_modalApprox_eq_interval
      W ν (W.proj m u₀) c φ m T hT hφzero hφ'zero
    rw [intervalIntegral.integral_add ((hmainInt m).add hlapInt) hconvInt,
      intervalIntegral.integral_add (hmainInt m) hlapInt] at heq
    rw [hidentify, ← coefficientField_initialCoefficients_eq_proj W u₀ m,
      ← hc0 m]
    simp_rw [hlapPair, mul_zero, hconvPair] at heq
    simp only [intervalIntegral.integral_zero, add_zero] at heq
    linarith [heq]
  exact modalApprox_fixedTest_weakConsistent_of_projectedDatum
    W ν u₀ hu₀ c φ hprojected

end Navier.Analysis.GalerkinBasis
