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

end Navier.Analysis.GalerkinBasis
