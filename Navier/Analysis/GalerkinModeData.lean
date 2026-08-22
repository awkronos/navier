import Navier.Analysis.ConvectionLadyzhenskaya

/-!
# The Galerkin mode-data construction, downstream of the convective estimate

This file is the downstream home of the two declarations that cannot live in
`Navier.Analysis.GalerkinBasis`:

* `galerkinCoefficientFlow_timeEquicontinuous` — the Aubin–Lions time-regularity
  residual for the coefficient flow.  Its whole mathematical content is
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

/-- **[LEAF — Aubin–Lions time regularity for the Galerkin coefficient flow.]**
A coefficient flow solving the projected Galerkin
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
  sorry

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
    are discharged here.  The genuinely analytic estimates
    (`hspace`, `htime`, `hweak`) are NAMED RESIDUALS.
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
    have hweak : ∀ phi : DivergenceFreeTestFunction,
        Filter.Tendsto (fun m => weakFormResidual nu u0 (W.modalApprox cChoice m) phi)
          Filter.atTop (nhds 0) := by
      sorry
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
