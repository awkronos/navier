import Navier.Analysis.GalerkinBasis
import Navier.Analysis.Ladyzhenskaya
import Navier.Analysis.ConvectionTrilinear
import Navier.Analysis.SobolevGNS
import Navier.Analysis.DivFreeGradientEnstrophy
import Navier.Analysis.GramSchmidt

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
    have hmodal_cont : Continuous (W.modalTestCoefficients φ.field m) :=
      continuous_iff_continuousAt.mpr fun t => (hmodal_deriv m t).continuousAt
    have heq := modalFlow_projectedTest_splitResidualWeakEquation_at
      W ν c hc φ φ.timeDerivSchwartz T hT hφzero m
        hmodal_cont.continuousOn (fun t _ => hmodal_deriv m t)
        (hmodal_deriv_cont m).continuousOn
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

/-- **The viscous commutator vanishes under L²-convergence of the curl-projection error.**

The `abs_intervalIntegral_laplacianProjectionCommutator_le` bound gives a spacetime
Cauchy--Schwarz estimate: for each mode `m`, the commutator interval integral is
bounded by `|ν|·√enstrophyBound·√(∫‖curl(P_m φ - φ)‖² dt)`.  If the right-hand
factor tends to zero, the commutator integral tends to zero.

This theorem isolates the exact mathematical condition needed to close the
`hlap` subgap of `hweak`: the vanishing of the spacetime curl-projection error.
No dominated convergence, no pointwise convergence, and no H¹-boundedness of the
projection is assumed — the `abs` bound supplies the squeeze directly.

The four integrability hypotheses (`henstrophyIntegrable`, `errorSqIntegrable`,
`pairingIntervalIntegrable`) are per-`m` and are satisfied for any Schwartz test
family and any coefficient curve with bounded enstrophy.  The `hcurlError`
hypothesis is the genuinely open condition.

Citation: Temam, *Navier--Stokes Equations*, Chapter III, Section 3. -/
theorem hlap_tendsto_zero_of_curlSqError_tendsto_zero
    (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (φ : ℝ → SchwartzVelocity) (hφ : ∀ t, DivergenceFreeInitial (φ t))
    (ν T enstrophyBound : ℝ) (hT : 0 ≤ T)
    (henstrophy : ∀ m,
      (∫ t in Set.Ioc (0 : ℝ) T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound)
    (henstrophyIntegrable : ∀ m, IntegrableOn
      (fun t => W.coefficientEnstrophy (c m t)) (Set.Ioc (0 : ℝ) T))
    (errorSqIntegrable : ∀ m, IntegrableOn (fun t =>
      ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
      (Set.Ioc (0 : ℝ) T))
    (pairingIntervalIntegrable : ∀ m, IntervalIntegrable (fun t =>
      ν * schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (φ t))) volume 0 T)
    (hcurlError : Filter.Tendsto (fun m =>
      ∫ t in Set.Ioc (0 : ℝ) T,
        ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m =>
      ∫ t in (0 : ℝ)..T, ν * schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (φ t)))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun m =>
    |ν| * Real.sqrt enstrophyBound * Real.sqrt
      (∫ t in Set.Ioc (0 : ℝ) T,
        ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2))
  · intro m
    rw [Real.norm_eq_abs]
    exact abs_intervalIntegral_laplacianProjectionCommutator_le
      W (c m) φ hφ ν T enstrophyBound hT (henstrophy m) (henstrophyIntegrable m)
      (errorSqIntegrable m) (pairingIntervalIntegrable m)
  · have hsqrt := hcurlError.sqrt
    have hconst : Filter.Tendsto (fun _ : ℕ => |ν| * Real.sqrt enstrophyBound)
        Filter.atTop (nhds (|ν| * Real.sqrt enstrophyBound)) := tendsto_const_nhds
    simpa using hconst.mul hsqrt

set_option maxHeartbeats 4000000 in
/--
Pointwise GNS–Ladyzhenskaya chain (Temam Ch. III §3): for each mode and
time,
`|⟨u_m, (u_m·∇)(P_m φ − φ)⟩| ≤ (3⁷·C₀·energyBound)^(1/4) · Ω_m(t)^(3/4) · ‖curl(P_m φ − φ)‖₂`,
where `Ω_m(t)` is the coefficient enstrophy and `C₀` any admissible
Ladyzhenskaya constant.  Providers:
`ConvectionTrilinear.abs_schwartzL2Inner_convection_le`,
`SobolevGNS.exists_ladyzhenskaya_official`,
`DivFreeGradientEnstrophy.integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree`,
`GramSchmidt.divFree_sub`.  ≈150 LOC.
-/
theorem convectionTestProjectionCommutator_abs_le_pointwise_sub
    (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (φ : ℝ → SchwartzVelocity) (hφ : ∀ t, DivergenceFreeInitial (φ t))
    (energyBound M C₀ : ℝ) (hC₀0 : 0 ≤ C₀)
    (hC₀ : ∀ u : SchwartzVelocity,
      (∫ x : Space, officialEuclideanNorm ((⇑u) x) ^ 4) ^ 2 ≤
        (C₀ * ∫ x : Space, officialEuclideanNorm ((⇑u) x) ^ 2) *
          (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3)
    (hE : ∀ (m : ℕ) (t : ℝ),
      ∫ x : Space, officialEuclideanNorm ((⇑(W.coefficientField (c m t))) x) ^ 2 ≤
        energyBound)
    (hfM : ∀ (m : ℕ) (t : ℝ),
      ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ≤ M) :
    ∀ (m : ℕ) (t : ℝ),
      |schwartzL2Inner (W.coefficientField (c m t))
          (W.convectionTestProjectionCommutator m (W.coefficientField (c m t)) (φ t))| ≤
        Real.sqrt (Real.sqrt (2187 * C₀ * energyBound)) *
          (W.coefficientEnstrophy (c m t)) ^ (3 / 4 : ℝ) *
            ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ := by
  have hE0 : 0 ≤ energyBound :=
    le_trans (integral_nonneg fun x => by positivity) (hE 0 0)
  have hΩ0 : ∀ (m : ℕ) (t : ℝ), 0 ≤ W.coefficientEnstrophy (c m t) := by
    intro m t
    unfold GalerkinBasisFamily.coefficientEnstrophy
    exact integral_nonneg fun _ => by positivity
  set K := Real.sqrt (Real.sqrt (2187 * C₀ * energyBound)) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hrpow4 : ∀ y : ℝ, 0 ≤ y → (y ^ 4) ^ (1 / 4 : ℝ) = y := by
    intro y hy
    rw [← Real.rpow_natCast y 4, ← Real.rpow_mul hy,
      show ((4 : ℕ) : ℝ) * (1 / 4 : ℝ) = (1 : ℝ) by norm_num, Real.rpow_one]
  have hrpow34 : ∀ y : ℝ, 0 ≤ y → (y ^ 3) ^ (1 / 4 : ℝ) = y ^ (3 / 4 : ℝ) := by
    intro y hy
    rw [← Real.rpow_natCast y 3, ← Real.rpow_mul hy,
      show ((3 : ℕ) : ℝ) * (1 / 4 : ℝ) = (3 / 4 : ℝ) by norm_num]
  have hK4 : (2187 * C₀ * energyBound) ^ (1 / 4 : ℝ) = K := by
    have hA : 0 ≤ 2187 * C₀ * energyBound := by positivity
    have hstep : Real.sqrt (Real.sqrt (2187 * C₀ * energyBound)) =
        (2187 * C₀ * energyBound) ^ (1 / 4 : ℝ) := by
      rw [show Real.sqrt (2187 * C₀ * energyBound) =
            (2187 * C₀ * energyBound) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow _,
        Real.sqrt_eq_rpow, ← Real.rpow_mul hA,
        show ((1 / 2 : ℝ) * (1 / 2 : ℝ)) = (1 / 4 : ℝ) by norm_num]
    rw [hKdef]
    exact hstep.symm
  have hbound : ∀ (m : ℕ) (t : ℝ),
      |schwartzL2Inner (W.coefficientField (c m t))
          (W.convectionTestProjectionCommutator m (W.coefficientField (c m t)) (φ t))| ≤
        K * (W.coefficientEnstrophy (c m t)) ^ (3 / 4 : ℝ) *
          ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ := by
    intro m t
    set u : SchwartzVelocity := W.coefficientField (c m t) with hu
    set e : SchwartzVelocity := W.proj m (φ t) - φ t with he
    have he_div : DivergenceFreeInitial e :=
      Navier.Analysis.GramSchmidt.divFree_sub _ _
        (proj_divergence_free W m (φ t)) (hφ t)
    have hu_div : DivergenceFreeInitial u := coefficientField_divergenceFree W (c m t)
    have hs : schwartzL2Inner (W.coefficientField (c m t))
        (W.convectionTestProjectionCommutator m (W.coefficientField (c m t)) (φ t)) =
        schwartzL2Inner u (convectionSchwartzBilin u e) := by
      unfold GalerkinBasisFamily.convectionTestProjectionCommutator
      rw [← hu, ← he]
    rw [hs]
    set X : ℝ := ∫ x : Space, officialEuclideanNorm ((⇑u) x) ^ 4 with hXset
    set Y : ℝ := ∫ x : Space, ‖fderiv ℝ (⇑e) x‖ ^ 2 with hYset
    have hX0 : 0 ≤ X := integral_nonneg fun x => by positivity
    have hY0 : 0 ≤ Y := integral_nonneg fun x => by positivity
    have hbase : |schwartzL2Inner u (convectionSchwartzBilin u e)| ≤
        Real.sqrt 3 * (X ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ)) := by
      refine (Navier.Analysis.ConvectionTrilinear.abs_schwartzL2Inner_convection_le
        u u e).trans ?_
      have h : X ^ (1 / 4 : ℝ) * X ^ (1 / 4 : ℝ) = X ^ (1 / 2 : ℝ) := by
        by_cases hXp : (0 : ℝ) < X
        · rw [← Real.rpow_add hXp,
            show ((1 / 4 : ℝ) + (1 / 4 : ℝ)) = (1 / 2 : ℝ) by norm_num]
        · have hXz : X = 0 := le_antisymm (le_of_not_gt hXp) hX0
          rw [hXz, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0),
            Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
          simp
      calc Real.sqrt 3 * (X ^ (1 / 4 : ℝ) * Y ^ (1 / 2 : ℝ) * X ^ (1 / 4 : ℝ))
          = Real.sqrt 3 * ((X ^ (1 / 4 : ℝ) * X ^ (1 / 4 : ℝ)) * Y ^ (1 / 2 : ℝ)) := by ring
        _ ≤ Real.sqrt 3 * (X ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ)) := by rw [h]
    have hfour : |schwartzL2Inner u (convectionSchwartzBilin u e)| ^ 4 ≤
        9 * (X ^ 2 * Y ^ 2) := by
      refine (pow_le_pow_left₀ (abs_nonneg _) hbase 4).trans ?_
      have hsx : (X ^ (1 / 2 : ℝ)) ^ 4 = X ^ 2 := by
        rw [← Real.rpow_natCast (X ^ (1 / 2 : ℝ)) 4, ← Real.rpow_mul hX0]
        norm_num
      have hsy : (Y ^ (1 / 2 : ℝ)) ^ 4 = Y ^ 2 := by
        rw [← Real.rpow_natCast (Y ^ (1 / 2 : ℝ)) 4, ← Real.rpow_mul hY0]
        norm_num
      have hs3 : (Real.sqrt 3) ^ 4 = 9 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]
        norm_num
      rw [mul_pow, mul_pow, hsx, hsy, hs3]
    have hG2u : 0 ≤ ∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2 :=
      integral_nonneg fun x => by positivity
    have hΩ : 0 ≤ W.coefficientEnstrophy (c m t) := hΩ0 m t
    have hX2 : X ^ 2 ≤ 27 * C₀ * energyBound * (W.coefficientEnstrophy (c m t)) ^ 3 := by
      have hG : (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ≤
          3 * W.coefficientEnstrophy (c m t) := by
        refine (Navier.Analysis.DivFreeGradientEnstrophy.integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree u hu_div).trans ?_
        exact le_of_eq rfl
      have hG3 : (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3 ≤
          (3 * W.coefficientEnstrophy (c m t)) ^ 3 :=
        pow_le_pow_left₀ hG2u hG 3
      refine (((hC₀ u).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE m t) hC₀0)
          (pow_nonneg hG2u 3))).trans
        (mul_le_mul_of_nonneg_left hG3 (mul_nonneg hC₀0 hE0))).trans (le_of_eq ?_)
      ring
    have hb : (∫ x : Space, officialEuclideanNorm (Navier.Analysis.Vorticity.staticCurl e x) ^ 2) =
        ‖toL2 (curlSchwartzCLM e)‖ ^ 2 := by
      rw [norm_toL2_sq]
      unfold schwartzL2Inner
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [curlSchwartzCLM_apply, Navier.Analysis.Enstrophy.officialInner_self]
    have hY3 : Y ≤ 3 * ‖toL2 (curlSchwartzCLM e)‖ ^ 2 := by
      refine (Navier.Analysis.DivFreeGradientEnstrophy.integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree e he_div).trans ?_
      rw [hb]
    have hY2 : Y ^ 2 ≤ 9 * ‖toL2 (curlSchwartzCLM e)‖ ^ 4 := by
      refine (pow_le_pow_left₀ hY0 hY3 2).trans (le_of_eq ?_)
      ring
    have hF4 : |schwartzL2Inner u (convectionSchwartzBilin u e)| ^ 4 ≤
        2187 * C₀ * energyBound * (W.coefficientEnstrophy (c m t)) ^ 3 *
          ‖toL2 (curlSchwartzCLM e)‖ ^ 4 := by
      refine (hfour.trans
        (mul_le_mul_of_nonneg_left
          (mul_le_mul hX2 hY2 (by positivity) (by positivity))
          (by norm_num : (0 : ℝ) ≤ 9))).trans (le_of_eq ?_)
      ring
    have hN : 0 ≤ ‖toL2 (curlSchwartzCLM e)‖ := norm_nonneg _
    calc |schwartzL2Inner u (convectionSchwartzBilin u e)|
        = (|schwartzL2Inner u (convectionSchwartzBilin u e)| ^ 4) ^ (1 / 4 : ℝ) :=
          (hrpow4 _ (abs_nonneg _)).symm
      _ ≤ (2187 * C₀ * energyBound * (W.coefficientEnstrophy (c m t)) ^ 3 *
            ‖toL2 (curlSchwartzCLM e)‖ ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (pow_nonneg (abs_nonneg _) 4) hF4 (by norm_num)
      _ = (2187 * C₀ * energyBound) ^ (1 / 4 : ℝ) *
            ((W.coefficientEnstrophy (c m t)) ^ 3) ^ (1 / 4 : ℝ) *
            (‖toL2 (curlSchwartzCLM e)‖ ^ 4) ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
      _ = K * (W.coefficientEnstrophy (c m t)) ^ (3 / 4 : ℝ) *
            ‖toL2 (curlSchwartzCLM e)‖ := by
          rw [hK4, hrpow34 _ hΩ, hrpow4 _ hN]
  rw [hKdef] at hbound
  exact hbound

set_option maxHeartbeats 4000000 in
/--
Abstract time envelope for the commutator pairing: given pointwise control
`|pair| ≤ K·Ω^(3/4)·err`, an enstrophy budget, a uniform error bound and the
integrability data, the `intervalIntegral` of `pair` is bounded by
`K·√B·√(√B·M)·√√(∫err²)`.  Proof data: two uses of
`Ladyzhenskaya.integral_mul_le_sqrt_mul_sqrt`, Young's inequality for the
integrability of `√Ω·err²`, and `integral_mono`.  ≈200 LOC.
-/
theorem convectionTestProjectionCommutator_intervalIntegral_abs_le_sub
    (T enstrophyBound M K : ℝ) (hT : 0 ≤ T) (hK0 : 0 ≤ K)
    (Ω err pair : ℝ → ℝ) (hΩ0 : ∀ t, 0 ≤ Ω t) (h_err0 : ∀ t, 0 ≤ err t)
    (hpoint : ∀ t, |pair t| ≤ K * (Ω t) ^ (3 / 4 : ℝ) * err t)
    (henstrophy : ∫ t in Set.Ioc (0 : ℝ) T, Ω t ≤ enstrophyBound)
    (henstrophyIntegrable : IntegrableOn Ω (Set.Ioc (0 : ℝ) T))
    (hfM : ∀ t, err t ≤ M)
    (errorSqIntegrable : IntegrableOn (fun t => err t ^ 2) (Set.Ioc (0 : ℝ) T))
    (pairingIntervalIntegrable : IntervalIntegrable pair volume (0 : ℝ) T) :
    |∫ t in (0 : ℝ)..T, pair t| ≤
      K * Real.sqrt enstrophyBound * Real.sqrt (Real.sqrt enstrophyBound * M) *
        Real.sqrt (Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2)) := by
    have hΩ0' : ∀ t, 0 ≤ Ω t := hΩ0
    have hM0 : 0 ≤ M := le_trans (h_err0 0) (hfM 0)
    have herr0 : ∀ t, 0 ≤ err t := h_err0
    have hpoint' : ∀ t, |pair t| ≤ K * (Ω t) ^ (3 / 4 : ℝ) * err t := hpoint
    have henstI : IntegrableOn Ω (Set.Ioc (0 : ℝ) T) := henstrophyIntegrable
    have herr2I : IntegrableOn (fun t => err t ^ 2) (Set.Ioc (0 : ℝ) T) :=
      errorSqIntegrable
    have hΩMeas : AEStronglyMeasurable Ω (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
      henstI.aestronglyMeasurable
    have hsqrtΩMeas : AEStronglyMeasurable (fun t => Real.sqrt (Ω t))
        (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hΩMeas
    have hquarterΩMeas : AEStronglyMeasurable (fun t => Real.sqrt (Real.sqrt (Ω t)))
        (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hsqrtΩMeas
    have herrMeas : AEStronglyMeasurable err
        (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
      exact (Real.continuous_sqrt.comp_aestronglyMeasurable
          herr2I.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall fun t => Real.sqrt_sq (h_err0 t))
    have hF4I : IntegrableOn (fun t => err t ^ 4) (Set.Ioc (0 : ℝ) T) := by
      refine Integrable.mono' (herr2I.const_mul (M ^ 2)) (herrMeas.pow 4) ?_
      filter_upwards with t
      have hsq : err t ^ 2 ≤ M ^ 2 :=
        pow_le_pow_left₀ (herr0 t) (hfM t) 2
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (herr0 t) 4)]
      calc err t ^ 4 = err t ^ 2 * err t ^ 2 := by ring
        _ ≤ M ^ 2 * err t ^ 2 := mul_le_mul_of_nonneg_right hsq (pow_nonneg (herr0 t) 2)
    have hprodI : IntegrableOn (fun t => Real.sqrt (Ω t) * err t ^ 2)
        (Set.Ioc (0 : ℝ) T) := by
      refine Integrable.mono' (henstI.add hF4I)
        (hsqrtΩMeas.mul herr2I.aestronglyMeasurable) ?_
      filter_upwards with t
      have h2 := two_mul_le_add_sq (Real.sqrt (Ω t)) (err t ^ 2)
      rw [Real.sq_sqrt (hΩ0' t),
        show (err t ^ 2) ^ 2 = err t ^ 4 from by ring] at h2
      have hpos : 0 ≤ Real.sqrt (Ω t) * err t ^ 2 :=
        mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (herr0 t) 2)
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg hpos]
      linarith
    have hsqrtΩSqI : IntegrableOn (fun t => (Real.sqrt (Ω t)) ^ 2)
        (Set.Ioc (0 : ℝ) T) := by
      refine henstI.congr ?_
      filter_upwards with t
      exact (Real.sq_sqrt (hΩ0' t)).symm
    have hg2I : IntegrableOn (fun t => (Real.sqrt (Real.sqrt (Ω t)) * err t) ^ 2)
        (Set.Ioc (0 : ℝ) T) := by
      refine hprodI.congr ?_
      filter_upwards with t
      rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
    have hsplit : ∀ t,
        Real.sqrt (Ω t) * (Real.sqrt (Real.sqrt (Ω t)) * err t) =
          (Ω t) ^ (3 / 4 : ℝ) * err t := by
      intro t
      by_cases hp : 0 < Ω t
      · have h1 : Real.sqrt (Ω t) = (Ω t) ^ (1 / 2 : ℝ) :=
          Real.sqrt_eq_rpow (Ω t)
        have h2 : Real.sqrt (Real.sqrt (Ω t)) = (Ω t) ^ (1 / 4 : ℝ) := by
          rw [h1, Real.sqrt_eq_rpow,
            ← Real.rpow_mul (hΩ0' t) (1 / 2 : ℝ) (1 / 2 : ℝ),
            show ((1 / 2 : ℝ) * (1 / 2 : ℝ)) = (1 / 4 : ℝ) by norm_num]
        rw [h2, h1, ← mul_assoc,
          ← Real.rpow_add hp (1 / 2 : ℝ) (1 / 4 : ℝ),
          show ((1 / 2 : ℝ) + (1 / 4 : ℝ)) = (3 / 4 : ℝ) by norm_num]
      · have hz : Ω t = 0 := le_antisymm (le_of_not_gt hp) (hΩ0' t)
        rw [hz, show (0 : ℝ) ^ (3 / 4 : ℝ) = 0 from
          Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0),
          Real.sqrt_zero, Real.sqrt_zero]
        simp
    have hJ1 : (∫ t in Set.Ioc (0 : ℝ) T, Real.sqrt (Ω t) * err t ^ 2) ≤
        Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Ω t) *
          Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 4) := by
      calc (∫ t in Set.Ioc (0 : ℝ) T, Real.sqrt (Ω t) * err t ^ 2)
          ≤ Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, (Real.sqrt (Ω t)) ^ 2) *
              Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, (err t ^ 2) ^ 2) :=
              Navier.Analysis.Ladyzhenskaya.integral_mul_le_sqrt_mul_sqrt
                (μ := volume.restrict (Set.Ioc (0 : ℝ) T))
                (f := fun t => Real.sqrt (Ω t)) (g := fun t => err t ^ 2)
                (fun t => Real.sqrt_nonneg _) (fun t => pow_nonneg (herr0 t) 2)
                hsqrtΩMeas herr2I.aestronglyMeasurable hsqrtΩSqI
                (hF4I.congr (by filter_upwards with t; ring))
        _ = Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Ω t) *
              Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 4) := by
              congr 2
              · refine integral_congr_ae (Filter.Eventually.of_forall fun t =>
                  Real.sq_sqrt (hΩ0' t))
              · refine integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
    have hJ2 : (∫ t in Set.Ioc (0 : ℝ) T, (Ω t) ^ (3 / 4 : ℝ) * err t) ≤
        Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Ω t) *
          Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Real.sqrt (Ω t) * err t ^ 2) := by
      calc (∫ t in Set.Ioc (0 : ℝ) T, (Ω t) ^ (3 / 4 : ℝ) * err t)
          = ∫ t in Set.Ioc (0 : ℝ) T,
              Real.sqrt (Ω t) * (Real.sqrt (Real.sqrt (Ω t)) * err t) := by
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro t
              symm
              exact hsplit t
        _ ≤ Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, (Real.sqrt (Ω t)) ^ 2) *
              Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T,
                (Real.sqrt (Real.sqrt (Ω t)) * err t) ^ 2) :=
              Navier.Analysis.Ladyzhenskaya.integral_mul_le_sqrt_mul_sqrt
                (μ := volume.restrict (Set.Ioc (0 : ℝ) T))
                (f := fun t => Real.sqrt (Ω t))
                (g := fun t => Real.sqrt (Real.sqrt (Ω t)) * err t)
                (fun t => Real.sqrt_nonneg _)
                (fun t => mul_nonneg (Real.sqrt_nonneg _) (herr0 t))
                hsqrtΩMeas (hquarterΩMeas.mul herrMeas) hsqrtΩSqI hg2I
        _ = Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Ω t) *
              Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Real.sqrt (Ω t) * err t ^ 2) := by
              congr 2
              · refine integral_congr_ae (Filter.Eventually.of_forall fun t =>
                  Real.sq_sqrt (hΩ0' t))
              · refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
                show (Real.sqrt (Real.sqrt (Ω t)) * err t) ^ 2 =
                  Real.sqrt (Ω t) * err t ^ 2
                rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
    have hF4le : (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 4) ≤
        M ^ 2 * ∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2 := by
      refine (integral_mono hF4I (herr2I.const_mul (M ^ 2)) fun t => ?_).trans
        (le_of_eq (integral_const_mul (M ^ 2) _))
      have hsq : err t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (herr0 t) (hfM t) 2
      calc err t ^ 4 = err t ^ 2 * err t ^ 2 := by ring
        _ ≤ M ^ 2 * err t ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (pow_nonneg (herr0 t) 2)
    rw [intervalIntegral.integral_of_le hT]
    have hpairAbsI : IntegrableOn (fun t => |pair t|) (Set.Ioc (0 : ℝ) T) :=
      pairingIntervalIntegrable.1.abs
    have henvI : IntegrableOn (fun t => K * (Ω t) ^ (3 / 4 : ℝ) * err t)
        (Set.Ioc (0 : ℝ) T) := by
      have hf : MemLp (fun t => Real.sqrt (Ω t)) 2
          (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
        (memLp_two_iff_integrable_sq hsqrtΩMeas).mpr hsqrtΩSqI
      have hg : MemLp (fun t => Real.sqrt (Real.sqrt (Ω t)) * err t) 2
          (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
        (memLp_two_iff_integrable_sq (hquarterΩMeas.mul herrMeas)).mpr hg2I
      have hmul : Integrable (fun t =>
          Real.sqrt (Ω t) * (Real.sqrt (Real.sqrt (Ω t)) * err t))
          (volume.restrict (Set.Ioc (0 : ℝ) T)) := hf.integrable_mul hg
      have hmul' : Integrable (fun t => (Ω t) ^ (3 / 4 : ℝ) * err t)
          (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
        convert hmul using 1
        funext t
        exact (hsplit t).symm
      have heq : (fun t => K * (Ω t) ^ (3 / 4 : ℝ) * err t) =
          (fun t => K * ((Ω t) ^ (3 / 4 : ℝ) * err t)) :=
        funext fun t => mul_assoc K _ _
      rw [heq]
      exact (hmul').const_mul K
    calc |∫ t in Set.Ioc (0 : ℝ) T, pair t|
        ≤ ∫ t in Set.Ioc (0 : ℝ) T, |pair t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Set.Ioc (0 : ℝ) T, K * (Ω t) ^ (3 / 4 : ℝ) * err t :=
          integral_mono hpairAbsI henvI fun t => hpoint' t
      _ = K * ∫ t in Set.Ioc (0 : ℝ) T, (Ω t) ^ (3 / 4 : ℝ) * err t := by
          rw [show (fun t => K * (Ω t) ^ (3 / 4 : ℝ) * err t) =
              (fun t => K * ((Ω t) ^ (3 / 4 : ℝ) * err t)) from
            funext fun t => mul_assoc K _ _,
            integral_const_mul]
      _ ≤ K * (Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Ω t) *
          Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Real.sqrt (Ω t) * err t ^ 2)) :=
          mul_le_mul_of_nonneg_left hJ2 hK0
      _ ≤ K * (Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Ω t) *
          Real.sqrt (Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, Ω t) *
            Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 4))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (le_refl _) (Real.sqrt_le_sqrt hJ1)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hK0
      _ ≤ K * (Real.sqrt enstrophyBound *
          Real.sqrt (Real.sqrt enstrophyBound *
            Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 4))) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          exact mul_le_mul (Real.sqrt_le_sqrt (henstrophy))
            (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
              (Real.sqrt_le_sqrt (henstrophy)) (Real.sqrt_nonneg _)))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ K * (Real.sqrt enstrophyBound *
          Real.sqrt (Real.sqrt enstrophyBound *
            (M * Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2)))) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul (le_refl _)
              (Real.sqrt_le_sqrt
                (mul_le_mul_of_nonneg_left
                  ((Real.sqrt_le_sqrt hF4le).trans
                    (by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM0]))
                  (Real.sqrt_nonneg _)))
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hK0
      _ = K * Real.sqrt enstrophyBound *
          Real.sqrt (Real.sqrt enstrophyBound * M) *
          Real.sqrt (Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2)) := by
          have hY : Real.sqrt (Real.sqrt enstrophyBound *
              (M * Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2))) =
              Real.sqrt (Real.sqrt enstrophyBound * M) *
                Real.sqrt (Real.sqrt (∫ t in Set.Ioc (0 : ℝ) T, err t ^ 2)) := by
            rw [← mul_assoc,
              Real.sqrt_mul (mul_nonneg (Real.sqrt_nonneg _) hM0)]
          rw [hY]
          ring


set_option maxHeartbeats 4000000 in
/-- **Spacetime control of the nonlinear test-projection commutator by the
squared curl-projection error (certified, no `sorry`).**

For coefficient curves whose realized velocity carries an `L²` budget
(`hE`) and an enstrophy budget (`henstrophy`) over the window, and for a
divergence-free test family whose curl-projection error is uniformly bounded
(`hfM`) and has vanishing `L²ₜ` norm (`hcurlError`), the nonlinear commutator
integral
`∫₀^T ⟨u_m, (u_m·∇)(P_m φ − φ)⟩ dt` tends to zero.

Pointwise, the Ladyzhenskaya–GNS chain
(`ConvectionTrilinear.abs_schwartzL2Inner_convection_le`,
`SobolevGNS.exists_ladyzhenskaya_official`,
`DivFreeGradientEnstrophy.integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree`)
gives the fourth-power form
`|s_m(t)| ≤ K · Ω_m(t)^{3/4} · f_m(t)`,
`K = (3⁷ · C_Ladyzhenskaya · energyBound)^{1/4}`, uniform in `m` and `t`.
The time integration is two Cauchy–Schwarz steps,
`∫Ω^{3/4}f ≤ (∫Ω)^{3/4} (∫f⁴)^{1/4} ≤ enstrophyBound^{3/4} · M^{1/2} · (∫f²)^{1/4}`,
whose last factor is exactly `hcurlError`.

Endpoint checks.  `T = 0`: the window is empty and the interval integral is
`0`; `m = 0`: `EuclideanSpace ℝ (Fin 0)` is trivial, `u₀`-side and both sides
vanish; `energyBound = 0`: `K = 0`.  The hypotheses are the same per-`m`
integrability budget consumed by `hlap_tendsto_zero_of_curlSqError_tendsto_zero`,
so the two commutators are closed by one common hypothesis set.

Citation: Temam, *Navier–Stokes Equations*, Chapter III, Section 3. -/
theorem intervalIntegral_convectionTestProjectionCommutator_tendsto_zero_of_curlSqError_tendsto_zero
    (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (φ : ℝ → SchwartzVelocity) (hφ : ∀ t, DivergenceFreeInitial (φ t))
    (T energyBound enstrophyBound M : ℝ) (hT : 0 ≤ T)
    (hE : ∀ (m : ℕ) (t : ℝ),
      ∫ x : Space, officialEuclideanNorm ((⇑(W.coefficientField (c m t))) x) ^ 2 ≤
        energyBound)
    (henstrophy : ∀ m,
      (∫ t in Set.Ioc (0 : ℝ) T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound)
    (henstrophyIntegrable : ∀ m, IntegrableOn
      (fun t => W.coefficientEnstrophy (c m t)) (Set.Ioc (0 : ℝ) T))
    (hfM : ∀ (m : ℕ) (t : ℝ),
      ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ≤ M)
    (errorSqIntegrable : ∀ m, IntegrableOn (fun t =>
      ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2) (Set.Ioc (0 : ℝ) T))
    (pairingIntervalIntegrable : ∀ m, IntervalIntegrable (fun t =>
      schwartzL2Inner (W.coefficientField (c m t))
        (W.convectionTestProjectionCommutator m (W.coefficientField (c m t)) (φ t)))
      volume (0 : ℝ) T)
    (hcurlError : Filter.Tendsto (fun m =>
      ∫ t in Set.Ioc (0 : ℝ) T,
        ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m =>
      ∫ t in (0 : ℝ)..T, schwartzL2Inner (W.coefficientField (c m t))
        (W.convectionTestProjectionCommutator m (W.coefficientField (c m t)) (φ t)))
      Filter.atTop (nhds 0) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := Navier.Analysis.SobolevGNS.exists_ladyzhenskaya_official
  set K := Real.sqrt (Real.sqrt (2187 * C₀ * energyBound))
  have hK0 : 0 ≤ K := by positivity
  have hΩ0 : ∀ (m : ℕ) (t : ℝ), 0 ≤ W.coefficientEnstrophy (c m t) := by
    intro m t
    unfold GalerkinBasisFamily.coefficientEnstrophy
    exact integral_nonneg fun _ => by positivity
  have hpoint : ∀ (m : ℕ) (t : ℝ),
      |schwartzL2Inner (W.coefficientField (c m t))
          (W.convectionTestProjectionCommutator m (W.coefficientField (c m t)) (φ t))| ≤
        K * (W.coefficientEnstrophy (c m t)) ^ (3 / 4 : ℝ) *
          ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ :=
    convectionTestProjectionCommutator_abs_le_pointwise_sub W c φ hφ energyBound M
      C₀ hC₀0 hC₀ hE hfM
  have hbnd : ∀ m : ℕ,
      |∫ t in (0 : ℝ)..T, schwartzL2Inner (W.coefficientField (c m t))
          (W.convectionTestProjectionCommutator m (W.coefficientField (c m t)) (φ t))| ≤
        K * Real.sqrt enstrophyBound * Real.sqrt (Real.sqrt enstrophyBound * M) *
          Real.sqrt (Real.sqrt
            (∫ t in Set.Ioc (0 : ℝ) T,
              ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)) := by
    intro m
    refine convectionTestProjectionCommutator_intervalIntegral_abs_le_sub T enstrophyBound
      M K hT hK0 (fun t => W.coefficientEnstrophy (c m t))
      (fun t => ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖)
      (fun t => schwartzL2Inner (W.coefficientField (c m t))
        (W.convectionTestProjectionCommutator m (W.coefficientField (c m t)) (φ t)))
      (fun t => hΩ0 m t) (fun t => norm_nonneg _) (fun t => hpoint m t)
      (henstrophy m) (henstrophyIntegrable m) (fun t => hfM m t) (errorSqIntegrable m)
      (pairingIntervalIntegrable m)
  apply squeeze_zero_norm (a := fun m =>
    K * Real.sqrt enstrophyBound * Real.sqrt (Real.sqrt enstrophyBound * M) *
      Real.sqrt (Real.sqrt
        (∫ t in Set.Ioc (0 : ℝ) T,
          ‖toL2 (curlSchwartzCLM (W.proj m (φ t) - φ t))‖ ^ 2)))
  · intro m
    rw [Real.norm_eq_abs]
    exact hbnd m
  · have hsqrt := (hcurlError.sqrt).sqrt
    simpa using hsqrt.const_mul
      (K * Real.sqrt enstrophyBound * Real.sqrt (Real.sqrt enstrophyBound * M))

end Navier.Analysis.GalerkinBasis
