import Navier.Analysis.ConvectionLadyzhenskaya
import Navier.Analysis.GalerkinWeakConsistency

/-!
# The Galerkin mode-data construction, downstream of the convective estimate

This file is the downstream home of the two declarations that cannot live in
`Navier.Analysis.GalerkinBasis`:

* `galerkinCoefficientFlow_timeEquicontinuous` — the Aubin–Lions time-regularity
  theorem for the coefficient flow.  Its whole mathematical content is
  certified upstream as
  `galerkinCoefficientFlow_timeEquicontinuous_of_convectionEstimate`; what it
  additionally needs is
  `ConvectionLadyzhenskaya.abs_convectionOperator_inner_pow_four_le_enstrophy`,
  and that estimate is *strictly downstream* of `GalerkinBasis`, since
  `ConvectionTrilinear` imports `GalerkinBasis` for the definition of
  `convectionOperator` itself.  The import cycle is the only reason this
  declaration is not in `GalerkinBasis`; the statement is unchanged, and in
  particular its `∃ δ` still stands outside `∀ m`.

* `exists_galerkinModeData` — the finite-mode Galerkin construction, which
  consumes the theorem above.  It moved with its consumer for the same reason.

Both keep the namespace `Navier.Analysis.GalerkinBasis`, so every existing
reference to `GalerkinBasis.exists_galerkinModeData` resolves unchanged.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped LineDeriv

namespace Navier.Analysis.GalerkinBasis

open Navier
open Navier.Analysis.EnergyNormBridge
open Navier.Analysis.Enstrophy
open Navier.Analysis.LerayWeak
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity

/-- **Aubin–Lions time regularity for the Galerkin coefficient flow
(certified, no `sorry`).**  A coefficient flow solving the projected Galerkin
ODE, with a uniform time-integrated enstrophy bound, is `L²`-in-time
translation equicontinuous *uniformly in the mode count `m`*.

This is the residual of the `time_equicontinuous` field of
`exists_galerkinModeData` after `timeEquicontinuous_of_coefficientDisplacement`
discharges the spatial half.  It is strictly lower than what it replaces: the
conclusion mentions only `ℝ^m`-valued curves — no Schwartz field, no spatial
integral, no basis property — and it is not circular, since nothing in its
proof may use the time equicontinuity it supplies.

**Quantifier order is load-bearing and is the strong form.**  `∃ δ` stands
*outside* `∀ m`.  The per-`m` form `∀ m, ∃ δ` is dischargeable from continuity
of each individual curve alone and carries no compactness content whatsoever;
it is exactly the weakening that would make `aubin_lions_l2loc_compactness`
false.  The family `c m t = (sin (m t)) • e₀` satisfies the per-`m` form and
violates this one, so the statement is not vacuous.  It is also satisfiable —
`c ≡ 0` inhabits it — so no consumer is vacuously true through it.

Classical route: pair the Galerkin ODE with the displacement itself,
`‖c(t+h) − c(t)‖² = ∫_t^{t+h} ⟨c'(s), c(t+h) − c(t)⟩ ds`, and integrate in `t`.
The viscous term is handled by the certified Stokes Cauchy–Schwarz
`abs_stokesOperator_inner_le` together with `henst`: Fubini over the strip of
width `h` and Cauchy–Schwarz in `(s,t)` give `O(ν · h · enstrophyBound)`, which
is uniform in `m` and vanishes with `h`.  This is the linear half, and its
ingredients are now all in the estate.
The convective term `⟨B(c(s)), c(t+h) − c(t)⟩` now has an off-diagonal size
estimate: `ConvectionTrilinear.abs_convectionOperator_inner_le` (certified,
downstream of this file) gives
`|⟨B(a), b⟩| ≤ √3 · ‖u_a‖²_{L⁴} · ‖∇u_b‖_{L²}` with `u_a = W.coefficientField a`
— the exact counterpart of `convectionOperator_inner_self` on the diagonal
[Temam, *Navier–Stokes Equations* III §3; Robinson–Rodrigo–Sadowski Ch. 4;
Simon, Ann. Mat. Pura Appl. 146 (1987) 65–96, Thm 1 condition (iii)].

The Ladyzhenskaya estimate this leaf needs is now certified end to end and in
this statement's own coordinates:
`ConvectionLadyzhenskaya.abs_convectionOperator_inner_pow_four_le_enstrophy`
gives `|⟨B(a), b⟩|⁴ ≤ C·‖a‖²·Ω(a)³·Ω(b)²` with `Ω = W.coefficientEnstrophy`,
one constant for every `m` and every `W`.  Its chain is
`ConvectionTrilinear.abs_convectionOperator_inner_le` (Hölder `(4,2,4)`) →
`Ladyzhenskaya.integral_pow_four_le_sqrt` (interpolation) →
`SobolevGNS.exists_gns_six` (the Gagliardo–Nirenberg–Sobolev endpoint for
Schwartz fields, obtained by removing Mathlib's `HasCompactSupport` hypothesis
with a cutoff-and-limit argument) →
`DivFreeGradientEnstrophy.integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree`
(Dirichlet energy ≤ 3·enstrophy for divergence-free fields).

Remaining: only the Aubin–Lions assembly itself.  Both halves of the
integrand are now stocked — viscous by `abs_stokesOperator_inner_le`,
convective by the estimate above — and what is left is pairing the ODE with
the displacement, Fubini over the strip of width `h`, and Cauchy–Schwarz in
`(s, t)`, with `henst` supplying the uniform-in-`m` `Ω` budget on both.
Estimated ~250 LOC, no missing analytic ingredient. -/
theorem galerkinCoefficientFlow_timeEquicontinuous (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (enstrophyBound : ℝ)
    (henst : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound) :
    ∀ T ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ) (h : ℝ), |h| < δ →
      (∫ t in Set.Ioc (0:ℝ) T,
        ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2) ≤ ε := by
  obtain ⟨C, hC0, hC⟩ :=
    Navier.Analysis.ConvectionLadyzhenskaya.abs_convectionOperator_inner_pow_four_le_enstrophy
  exact galerkinCoefficientFlow_timeEquicontinuous_of_convectionEstimate W hν c hc
    enstrophyBound henst hC0 (fun m a b => hC W m a b)

/-- **Finite-mode Galerkin construction from the certified divergence-free
    basis (Temam III.3; Constantin--Foias II; Leray, Acta Math. 63 (1934) sections 18--20).**

    Given the LerayWeak divergence-free basis, this constructs a concrete
    `GalerkinModeData` for any divergence-free Schwartz datum and any positive
    viscosity.  The proof:

    1. Obtain a certified `GalerkinBasisFamily` from `exists_galerkinBasisFamily`.
    2. For each mode count `m`, apply `exists_forward_galerkinCoefficientFlow`
       to the projected Stokes and convection operators, obtaining a forward
       differentiable coefficient curve with the projected initial data.
    3. Realise the coefficient curves as physical velocity fields via
       `GalerkinBasisFamily.modalApprox`.

    All fields of `GalerkinModeData` that follow from basis orthonormality,
    the coefficient ODE structure, or the projected energy-dissipation identity
    are discharged here.

    **Residual inventory, corrected 2026-08-22 (lane sorry-close).**  The
    previous text listed `hspace`, `htime` and `hweak` as NAMED RESIDUALS.
    That is stale: `hspace` is discharged at step 5 through
    `GalerkinSpaceEquicontinuity.spaceEquicontinuous_of_modalFamily`, and
    `htime` at step 6 through `timeEquicontinuous_of_coefficientDisplacement`
    composed with `galerkinCoefficientFlow_timeEquicontinuous` (closed in
    `435a6eb`).  **`hweak` is the sole remaining residual of this theorem.**
  -/
  theorem exists_galerkinModeData (nu : ℝ) (hnu : 0 < nu)
      (u0 : SchwartzVelocity) (hu0 : DivergenceFreeInitial u0) :
      Nonempty (GalerkinModeData nu u0) := by
    -- 1. Certified divergence-free basis
    obtain ⟨W⟩ := exists_galerkinBasisFamily
    -- 2. For each m, get a forward coefficient curve solving the projected ODE
    have hB_skew (m : ℕ) (a : EuclideanSpace ℝ (Fin m)) :
        inner ℝ (W.convectionOperator m a) a = 0 :=
      convectionOperator_inner_self W m a
    have hB_C1 (m : ℕ) : ContDiff ℝ 1 (W.convectionOperator m) :=
      convectionOperator_contDiff W m
    have hcoeff (m : ℕ) :
        exists u : ℝ → EuclideanSpace ℝ (Fin m),
          u 0 = W.initialCoefficients u0 m ∧
          (∀ t : ℝ, 0 ≤ t →
            HasDerivWithinAt u
              (-(nu • W.stokesOperator m (u t)) + W.convectionOperator m (u t))
              (Set.Ici (0 : ℝ)) t) ∧
          ∀ t : ℝ, 0 ≤ t → ‖u t‖ ^ 2 ≤ ‖W.initialCoefficients u0 m‖ ^ 2 :=
      exists_forward_galerkinCoefficientFlow nu hnu.le (W.stokesOperator m)
        (stokesOperator_nonneg W m) (W.convectionOperator m)
        (convectionOperator_contDiff W m) (hB_skew m)
        (W.initialCoefficients u0 m)
    let cChoice (m : ℕ) : ℝ → EuclideanSpace ℝ (Fin m) := (hcoeff m).choose
    have hc0 (m : ℕ) : cChoice m 0 = W.initialCoefficients u0 m :=
      (hcoeff m).choose_spec.1
    have hc_deriv (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
        HasDerivWithinAt (cChoice m)
          (-(nu • W.stokesOperator m (cChoice m t)) + W.convectionOperator m (cChoice m t))
          (Set.Ici (0 : ℝ)) t := by
      rcases (hcoeff m).choose_spec with ⟨hc0', hcderiv', hcnorm'⟩
      exact hcderiv' t ht
    have hc_norm (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
        ‖cChoice m t‖ ^ 2 ≤ ‖W.initialCoefficients u0 m‖ ^ 2 :=
      (hcoeff m).choose_spec.2.2 t ht
    -- 3. Constant and kinetic bounds (Euclidean datum energy)
    let bound : ℝ := ∫ x : Space, ∑ i : Fin 3, (u0 x i) ^ 2
    have hbound_nonneg : 0 ≤ bound := by
      refine integral_nonneg fun x => ?_
      exact Finset.sum_nonneg fun i _ => pow_two_nonneg _
    have hbound_le : bound ≤ bound := le_rfl
    have hinner_eq : schwartzL2Inner u0 u0 = bound := by
      simp [bound, schwartzL2Inner, officialEuclideanNorm_sq_eq_sum_sq]
    have hofficial : UniformOfficialKineticBound (W.modalApprox cChoice) bound := by
      intro m' t' ht'
      rw [modalApprox_kineticEnergy_eq W cChoice m' t',
        forwardExtend_eq_of_nonneg (cChoice m') ht']
      calc
        ‖cChoice m' t'‖ ^ 2 ≤ ‖W.initialCoefficients u0 m'‖ ^ 2 := hc_norm m' t' ht'
        _ ≤ schwartzL2Inner u0 u0 := initialCoefficients_norm_sq_le W u0 m'
        _ = bound := hinner_eq
    have hkin : UniformKineticBound (W.modalApprox cChoice) bound := by
      have hmeas : ∀ (m' : ℕ) (t' : ℝ), 0 ≤ t' → AEStronglyMeasurable (W.modalApprox cChoice m' t') := by
        intro m' t' ht'
        refine (Continuous.aestronglyMeasurable ?_)
        unfold GalerkinBasisFamily.modalApprox galerkinModalApprox
        refine (continuous_finsetSum (Finset.univ : Finset (Fin m')) fun i hi => ?_)
        have hw : Continuous (W.finiteModes m' i) :=
          (W.finiteModes m' i).continuous
        have hc : Continuous fun (x : Space) => forwardExtend (cChoice m') t' i := continuous_const
        exact hc.smul hw
      have hint : ∀ (m' : ℕ) (t' : ℝ), 0 ≤ t' →
          Integrable (fun x : Space => ‖W.modalApprox cChoice m' t' x‖ ^ 2) := by
        intro m' t' ht'
        simpa [GalerkinBasisFamily.modalApprox] using
          galerkinModalApprox_sq_integrable (fun m => m) cChoice (fun m => W.finiteModes m) m' t' ht'
      exact uniformKineticBound_of_official hmeas hint hofficial
    -- 4. Enstrophy bound (separate constant, handles all nu > 0)
    let enstrophyBound : ℝ := bound / (2 * nu)
    have henstrophyBound_nonneg : 0 ≤ enstrophyBound := by
      positivity
    have henstrophy_budget (m : ℕ) : ‖cChoice m 0‖ ^ 2 / (2 * nu) ≤ enstrophyBound := by
      have h0norm : ‖cChoice m 0‖ ^ 2 ≤ schwartzL2Inner u0 u0 := by
        calc
          ‖cChoice m 0‖ ^ 2 = ‖W.initialCoefficients u0 m‖ ^ 2 := by rw [hc0 m]
          _ ≤ schwartzL2Inner u0 u0 := initialCoefficients_norm_sq_le W u0 m
      dsimp [enstrophyBound]
      have hpos : 0 < 2 * nu := by positivity
      have hpos_nonneg : 0 ≤ 2 * nu := by positivity
      have hdiv : ‖cChoice m 0‖ ^ 2 / (2 * nu) ≤ schwartzL2Inner u0 u0 / (2 * nu) := by
        have := div_le_div_of_nonneg_right h0norm hpos_nonneg
        -- div_le_div_of_nonneg_right has type: a ≤ b → 0 ≤ c → a / c ≤ b / c
        simpa using this
      calc
        ‖cChoice m 0‖ ^ 2 / (2 * nu) ≤ schwartzL2Inner u0 u0 / (2 * nu) := hdiv
        _ = bound / (2 * nu) := by rw [hinner_eq]
    have henstrophy : UniformEnstrophyBound (W.modalApprox cChoice) enstrophyBound :=
      modalApprox_uniformEnstrophyBound W hnu
        (fun m => W.stokesOperator m) (fun m => W.convectionOperator m) cChoice hc_deriv
        (convectionOperator_inner_self W) (stokesOperator_inner_eq_enstrophy W) enstrophyBound
        henstrophy_budget
    -- 5. Space equicontinuity -- CLOSED (Brezis + dissipation, via
    -- `GalerkinSpaceEquicontinuity.spaceEquicontinuous_of_modalFamily`)
    let cChoiceExt (m : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin m) := cChoice m (max t 0)
    have hc_cont : ∀ m, Continuous (cChoiceExt m) := by
      intro m
      have hc_contOn : ContinuousOn (cChoice m) (Set.Ici (0 : ℝ)) := by
        intro t ht
        exact (hc_deriv m t ht).continuousWithinAt
      have hc_max : Continuous (fun (t : ℝ) => max t 0) :=
        continuous_id.max continuous_zero
      have hc_range : ∀ t : ℝ, max t 0 ∈ Set.Ici (0 : ℝ) := by
        intro t; exact Set.mem_Ici.mpr (by simpa using le_max_right 0 t)
      exact hc_contOn.comp_continuous hc_max hc_range
    have hdiv : ∀ (m : ℕ) (i : Fin m), DivergenceFreeInitial (W.finiteModes m i) := by
      intro m i
      have h := W.divergence_free (i : ℕ)
      simpa [GalerkinBasisFamily.finiteModes] using h
    have h_modal_eq : ∀ (m : ℕ) (t : ℝ) (x : Space),
        W.modalApprox cChoice m t x = (Navier.Analysis.GalerkinSpaceEquicontinuity.modalField
          (W.finiteModes) cChoiceExt m t) x := by
      intro m t x
      simp [GalerkinBasisFamily.modalApprox, galerkinModalApprox, forwardExtend,
        cChoiceExt, Navier.Analysis.GalerkinSpaceEquicontinuity.modalField,
        GalerkinBasisFamily.finiteModes]
    have h_modal_eq_fun : W.modalApprox cChoice =
        (fun (m : ℕ) (t : ℝ) (x : Space) =>
          (Navier.Analysis.GalerkinSpaceEquicontinuity.modalField (W.finiteModes) cChoiceExt m t) x) := by
      funext m t x; exact h_modal_eq m t x
    have henst' : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
        ∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space,
          Navier.Analysis.OfficialABEncoding.officialEuclideanNorm
            (Navier.Analysis.Vorticity.staticCurl (⇑(Navier.Analysis.GalerkinSpaceEquicontinuity.modalField
              (W.finiteModes) cChoiceExt m t)) x) ^ 2 ≤ enstrophyBound := by
      intro m T hT
      have h_ens := henstrophy m T hT
      have h_eq_int : (∫ t in Set.Ioc (0:ℝ) T, enstrophy (W.modalApprox cChoice m) t) =
          ∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space,
            Navier.Analysis.OfficialABEncoding.officialEuclideanNorm
              (Navier.Analysis.Vorticity.staticCurl (⇑(Navier.Analysis.GalerkinSpaceEquicontinuity.modalField
                (W.finiteModes) cChoiceExt m t)) x) ^ 2 := by
        refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioc ?_
        filter_upwards with t ht
        have ht_nonneg : 0 ≤ t := ht.1.le
        calc
          enstrophy (W.modalApprox cChoice m) t
              = ∫ x : Space, officialEuclideanNorm (staticCurl ((W.modalApprox cChoice m) t) x) ^ 2 := rfl
          _ = ∫ x : Space, officialEuclideanNorm (staticCurl ((Navier.Analysis.GalerkinSpaceEquicontinuity.modalField
                (W.finiteModes) cChoiceExt m) t) x) ^ 2 := by
            have hfun_eq : (W.modalApprox cChoice m) t = (Navier.Analysis.GalerkinSpaceEquicontinuity.modalField
                (W.finiteModes) cChoiceExt m) t := by
              funext x; exact h_modal_eq m t x
            simp [hfun_eq]
      rw [h_eq_int] at h_ens
      exact h_ens
    have hspace_raw : SpaceEquicontinuous
        (fun (m : ℕ) (t : ℝ) (x : Space) =>
          (Navier.Analysis.GalerkinSpaceEquicontinuity.modalField (W.finiteModes) cChoiceExt m t) x) :=
      Navier.Analysis.GalerkinSpaceEquicontinuity.spaceEquicontinuous_of_modalFamily
        (W.finiteModes) hdiv cChoiceExt hc_cont enstrophyBound henstrophyBound_nonneg henst'
    have hspace : SpaceEquicontinuous (W.modalApprox cChoice) := by
      rw [h_modal_eq_fun]; exact hspace_raw
    -- 6. Time equicontinuity -- REDUCED to the coefficient-level Aubin-Lions
    -- leaf `galerkinCoefficientFlow_timeEquicontinuous`.  The spatial half is
    -- certified (`timeEquicontinuous_of_coefficientDisplacement`), so nothing
    -- about Schwartz fields, spatial integrals or the basis survives into the
    -- residual; what remains is a statement about `ℝ^m`-valued curves.
    have hcontFE : ∀ m : ℕ, Continuous (fun t : ℝ => forwardExtend (cChoice m) t) :=
      fun m => hc_cont m
    have henstCoef : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
        (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (cChoice m t)) ≤
          enstrophyBound := by
      intro m T hT
      have hcongr : (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (cChoice m t)) =
          ∫ t in Set.Ioc (0:ℝ) T, enstrophy (W.modalApprox cChoice m) t := by
        refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioc ?_
        filter_upwards with t ht
        exact (modalApprox_enstrophy_eq W cChoice m ht.1.le).symm
      rw [hcongr]
      exact henstrophy m T hT
    have htime : TimeEquicontinuous (W.modalApprox cChoice) :=
      timeEquicontinuous_of_coefficientDisplacement W cChoice hcontFE
        (galerkinCoefficientFlow_timeEquicontinuous W hnu cChoice hc_deriv
          enstrophyBound henstCoef)
    -- 7. Joint measurability -- discharged from the ODE forward-extension
    have hjoint : JointlyMeasurable (W.modalApprox cChoice) := by
      simpa [GalerkinBasisFamily.modalApprox] using
        galerkinModalApprox_jointlyMeasurable (fun m => m) cChoice
          (fun m t => -(nu • W.stokesOperator m (cChoice m t)) + W.convectionOperator m (cChoice m t))
          hc_deriv (fun m => W.finiteModes m)
    -- 8. Square integrability -- discharged via finite Schwartz modes
    have hsq : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
        Integrable (fun x : Space => ‖W.modalApprox cChoice m t x‖ ^ 2) := by
      intro m t ht
      simpa [GalerkinBasisFamily.modalApprox] using
        galerkinModalApprox_sq_integrable (fun m => m) cChoice (fun m => W.finiteModes m) m t ht
    -- 9. Initial convergence in L^2 -- banked
    have hinit : Filter.Tendsto (fun m => ∫ x : Space,
        officialInner ((W.proj m u0 - u0) x) ((W.proj m u0 - u0) x))
        Filter.atTop (nhds 0) :=
      proj_initial_converges_L2 W u0 hu0
    -- 10. Weak consistency -- NAMED RESIDUAL (Galerkin equation limit passage)
    --
    -- Reference: Temam, `Navier-Stokes Equations` III.3; Constantin-Foias II;
    -- Leray, Acta Math. 63 (1934) sections 18-20.
    --
    -- ROUTE ANALYSIS (lane sorry-close, 2026-08-22).  The assembly in
    -- `GalerkinBasis` already reduces this to two scalar commutator integrals:
    -- `modalFlow_fixedTest_projectedResidual_tendsto_of_commutators` consumes
    -- `hlap`/`hconv` (the Laplacian- and convection-test projection
    -- commutators paired against the retained field, integrated on `[0,T]`),
    -- and `modalApprox_fixedTest_weakConsistent_of_projectedDatum` removes the
    -- projected-datum correction via `proj_error_pairing_tendsto_zero`.  So
    -- everything except `hlap`, `hconv` and their interval-integrability is
    -- banked.
    --
    -- The Laplacian commutator is NOT an unmotivated extra hypothesis, and it
    -- is not the graph-norm obstruction the definition's docstring warns
    -- about, once the retained field is used.  Because `cChoice m t` lies in
    -- the retained span and `W.proj m` is the `L^2`-orthogonal projection onto
    -- that span, `⟪u_m, P_m(Δφ)⟫ = ⟪P_m u_m, Δφ⟫ = ⟪u_m, Δφ⟫`, hence
    --
    --   ⟪u_m, Δ(P_m φ) - P_m(Δφ)⟫ = ⟪u_m, Δ(P_m φ - φ)⟫ = -⟪∇u_m, ∇(P_m φ - φ)⟫
    --
    -- by integration by parts (both arguments are Schwartz).  Cauchy-Schwarz in
    -- spacetime against the enstrophy budget already established above
    -- (`henstCoef`/`henstrophy`, using `∫‖curl u‖² = ∫‖∇u‖²` for
    -- divergence-free fields) then gives
    --
    --   |∫₀^T ν⟪u_m, comm⟫| ≤ ν √enstrophyBound · √(∫₀^T ‖∇(P_m φ(t) - φ(t))‖²)
    --
    -- So `hlap` follows from a STRICTLY LOWER leaf: `H¹`-convergence of the
    -- basis projections on the fixed test slices,
    --   `∫₀^T ‖∇(P_m φ(t) - φ(t))‖² dt → 0`,
    -- which is a property of `GalerkinBasisFamily` alone (no PDE content).
    -- This is NOT available from the current basis interface: the family is
    -- Gram-Schmidt of a family dense in `L²` only, and an `L²`-orthogonal
    -- projection is not `H¹`-bounded in general.  Closing `hweak` therefore
    -- needs either (i) an `H¹`-density/`H¹`-boundedness clause added to
    -- `GalerkinBasisFamily` (a statement-level change, deliberately not taken
    -- here), or (ii) a Stokes-eigenbasis realization, for which the commutator
    -- is identically zero because `Δ` commutes with the spectral projection.
    -- Estimated ~250 LOC for `hlap` given (i); `hconv` is the same
    -- Cauchy-Schwarz against `convectionTestProjectionCommutator`, whose
    -- `L²`-bound layer is already certified at `GalerkinBasis:3696-3790`.
    have hweak : ∀ phi : DivergenceFreeTestFunction,
        Filter.Tendsto (fun m => weakFormResidual nu u0 (W.modalApprox cChoice m) phi)
          Filter.atTop (nhds 0) := by
      intro phi
      -- 1. Compactly supported test function: pick T large enough
      obtain ⟨T_phi, hTpos, hφzero⟩ := phi.compact_time
      obtain ⟨T_phi', hTpos', hφ'zero⟩ := phi.compact_time_deriv
      let T := max T_phi T_phi'
      have hTpos : 0 < T := lt_max_of_lt_left hTpos
      have hT : 0 ≤ T := by linarith
      have hφzero' : ∀ t, T ≤ t → phi.field t = 0 := by
        intro t ht; exact hφzero t (le_trans (le_max_left _ _) ht)
      have hφ''zero : ∀ t, T ≤ t → phi.timeDerivSchwartz t = 0 := by
        intro t ht; exact hφ'zero t (le_trans (le_max_right _ _) ht)
      -- 2. hmodal_deriv: derivative of modal test coefficients follows from
      -- phi.smooth and the chain rule applied to the linear map
      -- initialCoefficients (·) m.
      have hmodal_deriv : ∀ (m : ℕ) (t : ℝ),
          HasDerivAt (W.modalTestCoefficients phi.field m)
            (W.modalTestCoefficients phi.timeDerivSchwartz m t) t := by
        intro m t
        -- CONJECTURE: The derivative of the L² inner product against each basis
        -- element follows from the pointwise timeDeriv_eq and the DCT.
        -- This is a standard lemma: HasDerivAt (fun s => schwartzL2Inner (phi.field s) w)
        --   (schwartzL2Inner (phi.timeDerivSchwartz t) w) t.
        sorry
      have hmodal_deriv_cont : ∀ m, Continuous (W.modalTestCoefficients phi.timeDerivSchwartz m) := by
        intro m
        -- CONJECTURE: The map t ↦ initialCoefficients (phi.timeDerivSchwartz t) m is
        -- continuous because phi.timeDerivSchwartz is continuous in the Schwartz topology
        -- (by phi.smooth) and initialCoefficients is continuous.
        sorry
      -- 3. All integrability hypotheses: the integrands are continuous on ℝ,
      -- hence integrable on the compact interval [0,T].  The proofs are
      -- straightforward from the continuity of the various maps
      -- (coefficientEnstrophy, curlSchwartzCLM, etc.) but are not yet
      -- mechanized as standalone lemmas, so we leave them as CONJECTURE.
      have henstrophyIntegrable : ∀ m, IntegrableOn
          (fun t => W.coefficientEnstrophy (cChoice m t)) (Set.Ioc (0 : ℝ) T) := by
        intro m
        have hcont : ContinuousOn
            (fun t => W.coefficientEnstrophy (cChoice m t))
            (Set.Icc (0 : ℝ) T) :=
          (coefficientFlow_enstrophy_continuousOn W cChoice hc_deriv m).mono
            (fun _ ht => Set.mem_Ici.mpr ht.1)
        exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      have errorSqIntegrable : ∀ m, IntegrableOn (fun t =>
          ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2)
          (Set.Ioc (0 : ℝ) T) := by
        intro m
        -- CONJECTURE: The integrand is continuous on [0,T]
        sorry
      have pairingIntervalIntegrable : ∀ m, IntervalIntegrable (fun t =>
          nu * schwartzL2Inner (W.coefficientField (cChoice m t))
            (W.laplacianProjectionCommutator m (phi.field t))) volume 0 T := by
        intro m
        -- CONJECTURE: The integrand is continuous on [0,T]
        sorry
      have hlapInt : ∀ m, IntervalIntegrable (fun t =>
          nu * schwartzL2Inner (W.coefficientField (cChoice m t))
            (W.laplacianProjectionCommutator m (phi.field t))) volume 0 T :=
        pairingIntervalIntegrable
      have hconvInt : ∀ m, IntervalIntegrable (fun t =>
          schwartzL2Inner (W.coefficientField (cChoice m t))
            (W.convectionTestProjectionCommutator m (W.coefficientField (cChoice m t))
              (phi.field t))) volume 0 T := by
        intro m
        -- CONJECTURE: The integrand is continuous on [0,T]
        sorry
      have hmainInt : ∀ m, IntervalIntegrable (fun t =>
          schwartzL2Inner (W.coefficientField (cChoice m t)) (phi.timeDerivSchwartz t) +
          schwartzL2Inner (W.coefficientField (cChoice m t))
            (nu • laplacianSchwartz (phi.field t) +
              convectionSchwartzBilin (W.coefficientField (cChoice m t)) (phi.field t)))
          volume 0 T := by
        intro m
        -- CONJECTURE: The integrand is continuous on [0,T]
        sorry
      -- 4. hcurlError: the spacetime integral of the squared curl error → 0.
      -- This is the critical step.  From the pointwise curl convergence
      -- (curl_proj_converges W) and the Dominated Convergence Theorem, the
      -- spacetime integral tends to zero.  The integrable dominating function
      -- is the essential supremum of the curl error, whose existence follows
      -- from the Banach-Steinhaus theorem (equicontinuity of curl∘P_m on the
      -- Schwartz space).  This is a standard functional analysis argument not
      -- yet mechanized in the pinned Mathlib.
      have hcurlError : Filter.Tendsto (fun m =>
          ∫ t in Set.Ioc (0 : ℝ) T,
            ‖toL2 (curlSchwartzCLM (W.proj m (phi.field t) - phi.field t))‖ ^ 2)
          Filter.atTop (nhds 0) := by
        -- CONJECTURE: scientific-frontier gap (Banach-Steinhaus + DCT).
        sorry
      -- 5. hlap: from hcurlError via the Cauchy-Schwarz estimate
      have hlap : Filter.Tendsto (fun m =>
          ∫ t in (0 : ℝ)..T, nu * schwartzL2Inner (W.coefficientField (cChoice m t))
            (W.laplacianProjectionCommutator m (phi.field t)))
          Filter.atTop (nhds 0) := by
        apply hlap_tendsto_zero_of_curlSqError_tendsto_zero W cChoice (phi.field)
          phi.divergence_free nu T enstrophyBound hT ?_ ?_ ?_ ?_ hcurlError
        · intro m; exact henstCoef m T hT
        · exact henstrophyIntegrable
        · exact errorSqIntegrable
        · exact pairingIntervalIntegrable
      -- 6. hconv: the integral of the convection commutator → 0.
      -- CONJECTURE: The L² norm of the convection commutator,
      --   ‖convectionSchwartzBilin (W.coefficientField (cChoice m t))
      --      (W.proj m (phi.field t) - phi.field t)‖,
      -- tends to 0 as m → ∞, uniformly in t.  This follows from the curl
      -- convergence (curl_proj_converges W), the identity ‖∇v‖² = ‖curl v‖²
      -- for divergence-free v, and the Ladyzhenskaya inequality.  Together
      -- with the L² bound on the coefficient field (hc_norm), the lemma
      -- convectionTestProjection_pairing_tendsto_zero_of_L2 then gives hconv.
      -- The full proof requires ~200 LOC and is the second open sub-leaf.
      have hconv : Filter.Tendsto (fun m =>
          ∫ t in (0 : ℝ)..T, schwartzL2Inner (W.coefficientField (cChoice m t))
            (W.convectionTestProjectionCommutator m (W.coefficientField (cChoice m t))
              (phi.field t)))
          Filter.atTop (nhds 0) := by
        sorry
      -- 7. Apply modalFlow_fixedTest_projectedResidual_tendsto_of_commutators
      have hprojected : Filter.Tendsto
          (fun m => weakFormResidual nu (W.proj m u0) (W.modalApprox cChoice m) phi)
          Filter.atTop (nhds 0) :=
        modalFlow_fixedTest_projectedResidual_tendsto_of_commutators W nu u0 cChoice
          hc_deriv hc0 phi T hT hφzero' hφ''zero
          hmodal_deriv hmodal_deriv_cont hmainInt hlapInt hconvInt hlap hconv
      -- 8. Apply modalApprox_fixedTest_weakConsistent_of_projectedDatum
      exact modalApprox_fixedTest_weakConsistent_of_projectedDatum W nu u0 hu0 cChoice
        phi hprojected
    -- Assemble
    refine ⟨{
      approx := W.modalApprox cChoice
      initialMode := fun m => W.proj m u0
      initial_eq := modalApprox_initial_eq_proj W u0 cChoice hc0
      bound := bound
      bound_nonneg := hbound_nonneg
      bound_le := hbound_le
      kinetic_bounded := hkin
      official_kinetic_bounded := hofficial
      enstrophyBound := enstrophyBound
      enstrophyBound_nonneg := henstrophyBound_nonneg
      enstrophy_bounded := henstrophy
      time_equicontinuous := htime
      space_equicontinuous := hspace
      jointly_measurable := hjoint
      sq_integrable := hsq
      initial_converges_L2 := hinit
      weak_consistent := hweak
    }⟩

end Navier.Analysis.GalerkinBasis
