import Navier.Analysis.ScaledCutoff

/-!
# The `R → ∞` layer: the enstrophy differential inequality (integral layer, part c)

The final layer of ladder rung 6.  Along a classical solution with a gradient
majorant `G` and the two named Pattern-A domination hypotheses, the enstrophy
`E(t) = ∫ |ω(t,x)|² dx` is continuous on `[0,T)`, differentiable on `(0,T)`,
and satisfies `E' ≤ 2·G·E` — the vortex-stretching estimate of
Majda–Bertozzi §3.3.

Route (all inputs already established):

1. `enstrophy_hasDerivAt` gives `E'(t₀) = ∫ 2⟨ω, ∂ₜω⟩` (`χ ≡ 1`).
2. For each `R > 0`, the crown and capstone rates at `χ_R = scaledCutoff R`
   are derivatives of the SAME function at the same point, so
   (`HasDerivAt.unique`)

     `∫ χ_R·2⟨ω,∂ₜω⟩ = ∫ χ_R·2⟨ω,(ω·∇)u⟩ + ∫ (u·∇χ_R)|ω|²
        + ν ∫ (Δχ_R)|ω|² − 2ν ∫ χ_R|∇ω|²`.

3. As `R → ∞`: the left side and the stretching term converge by dominated
   convergence (`χ_R → 1` pointwise, majorants from the domination
   hypotheses); the `∇χ_R` remainder is `O(R⁻¹)` against the `L¹` majorant of
   `‖u‖|ω|²` (`TransportDominatedEnstrophy`) and the `Δχ_R` remainder is
   `O(R⁻²)` against the `LocallyDominatedEnstrophy` majorant — both vanish
   (Step-0e: numerically confirmed on a Gaussian vorticity with a bounded
   divergence-free advecting field; the remainders decay super-polynomially).
4. The dissipation term `2ν ∫ χ_R|∇ω|²` is nonnegative, so its limit
   `∫2⟨ω,(ω·∇)u⟩ − E'` is nonnegative: `E' ≤ ∫ 2⟨ω,(ω·∇)u⟩`.
5. `stretching_pointwise_bound` under the integral: `E' ≤ 2·G·E`.
6. Continuity on `[0,T)` (including one-sidedly at `0`) by
   `continuousWithinAt_of_dominated`.

`enstrophyDifferentialInequality` here is the Pattern-A-strengthened closure
of the former `Enstrophy.enstrophyDifferentialInequality` skeleton: the bare
per-time integrability hypothesis (which cannot support the derivative
interchange) is replaced by the two named domination hypotheses, both
automatic for `H^m`/Schwartz-class solutions and both anchored non-vacuous by
the zero solution.  `enstrophy_apriori_bound` is the Grönwall wiring on top —
now fully unconditional (no `sorryAx`) — producing the `M₂` majorant the BKM
assembly consumes.

Reference: Majda–Bertozzi, *Vorticity and Incompressible Flow*, §3.3.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open MeasureTheory Set Filter

namespace Navier.Analysis.EnstrophyLimit

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.Enstrophy
open Navier.Analysis.EnstrophyPointwise
open Navier.Analysis.LocalEnstrophyBalance
open Navier.Analysis.CutoffEnstrophy
open Navier.Analysis.CutoffIntegrationByParts
open Navier.Analysis.ScaledCutoff

/-!
## The transport domination hypothesis
-/

/-- **Transport domination hypothesis** (Pattern-A, sibling of
`LocallyDominatedEnstrophy`): at each time an `L¹` majorant dominates
`‖u‖·|ω|²` — the density of the transport remainder.  Automatic for
`H^m`/Schwartz-class solutions; not carried by `IsClassicalSolution`, hence
explicit. -/
def TransportDominatedEnstrophy (u : VelocityEvolution) (T : ℝ) : Prop :=
  ∀ t ∈ Set.Ico (0:ℝ) T, ∃ h : Space → ℝ, Integrable h ∧
    ∀ x : Space,
      ‖u t x‖ * officialEuclideanNorm (vorticity u t x) ^ 2 ≤ h x

/-- Non-vacuity anchor: the zero velocity satisfies the transport domination
hypothesis with the zero majorant. -/
theorem transportDominatedEnstrophy_zero (T : ℝ) :
    TransportDominatedEnstrophy (fun _ _ => 0) T := by
  intro t _
  refine ⟨fun _ => 0, integrable_zero _ _ _, fun x => ?_⟩
  simp

/-!
## Vanishing of the cutoff remainders
-/

/-- The transport remainder vanishes: `∫ (u·∇χ_R)|ω|² = O(R⁻¹) → 0` under the
transport domination hypothesis. -/
theorem tendsto_transport_remainder
    {u : VelocityEvolution} {t₀ : ℝ} {h : Space → ℝ} (hInt : Integrable h)
    (hdomh : ∀ x : Space,
      ‖u t₀ x‖ * officialEuclideanNorm (vorticity u t₀ x) ^ 2 ≤ h x) :
    Tendsto (fun R : ℝ => ∫ x : Space,
        fderiv ℝ (scaledCutoff R) x (u t₀ x) *
          officialEuclideanNorm (vorticity u t₀ x) ^ 2)
      atTop (nhds 0) := by
  obtain ⟨M, hMnn, hM⟩ := exists_fderiv_opNorm_bound _
    standardBump.contDiff standardBump.hasCompactSupport
  apply squeeze_zero_norm'
    (a := fun R : ℝ => R⁻¹ * (M * ∫ x : Space, h x))
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hRinvnn : (0:ℝ) ≤ R⁻¹ := inv_nonneg.mpr hR.le
    calc ‖∫ x : Space, fderiv ℝ (scaledCutoff R) x (u t₀ x) *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2‖
        ≤ ∫ x : Space, ‖fderiv ℝ (scaledCutoff R) x (u t₀ x) *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x : Space, R⁻¹ * M * h x := by
          apply integral_mono_of_nonneg
          · filter_upwards with x
            positivity
          · exact hInt.const_mul (R⁻¹ * M)
          · filter_upwards with x
            have hd : |fderiv ℝ (scaledCutoff R) x (u t₀ x)| ≤
                R⁻¹ * M * ‖u t₀ x‖ :=
              abs_fderiv_scaled_le _ standardBump.contDiff hM hR x (u t₀ x)
            have hsq : (0:ℝ) ≤
                officialEuclideanNorm (vorticity u t₀ x) ^ 2 := sq_nonneg _
            calc ‖fderiv ℝ (scaledCutoff R) x (u t₀ x) *
                  officialEuclideanNorm (vorticity u t₀ x) ^ 2‖
                = |fderiv ℝ (scaledCutoff R) x (u t₀ x)| *
                    (officialEuclideanNorm (vorticity u t₀ x) ^ 2) := by
                  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
                    abs_of_nonneg hsq]
              _ ≤ (R⁻¹ * M * ‖u t₀ x‖) *
                    (officialEuclideanNorm (vorticity u t₀ x) ^ 2) :=
                  mul_le_mul_of_nonneg_right hd hsq
              _ = R⁻¹ * M * (‖u t₀ x‖ *
                    officialEuclideanNorm (vorticity u t₀ x) ^ 2) := by ring
              _ ≤ R⁻¹ * M * h x :=
                  mul_le_mul_of_nonneg_left (hdomh x)
                    (mul_nonneg hRinvnn hMnn)
      _ = R⁻¹ * (M * ∫ x : Space, h x) := by
          rw [integral_const_mul]
          ring
  · simpa using tendsto_inv_atTop_zero.mul_const (M * ∫ x : Space, h x)

/-- The viscous remainder vanishes: `∫ (Δχ_R)|ω|² = O(R⁻²) → 0` under the
`L¹` domination of `|ω|²`. -/
theorem tendsto_viscous_remainder
    {u : VelocityEvolution} {t₀ : ℝ} {g : Space → ℝ} (hgInt : Integrable g)
    (hgSq : ∀ x : Space,
      officialEuclideanNorm (vorticity u t₀ x) ^ 2 ≤ g x) :
    Tendsto (fun R : ℝ => ∫ x : Space,
        (∑ i : Fin 3, fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z
          (basisVector i)) x (basisVector i)) *
          officialEuclideanNorm (vorticity u t₀ x) ^ 2)
      atTop (nhds 0) := by
  choose M₂f hM₂nn hM₂ using fun i : Fin 3 =>
    exists_fderiv_fderiv_bound _ standardBump.contDiff
      standardBump.hasCompactSupport (basisVector i) (basisVector i)
  set M₂ : ℝ := ∑ i : Fin 3, M₂f i with hM₂def
  have hM₂sum : (0:ℝ) ≤ M₂ := Finset.sum_nonneg fun i _ => hM₂nn i
  have hgnn : ∀ x : Space, (0:ℝ) ≤ g x := fun x =>
    le_trans (sq_nonneg _) (hgSq x)
  apply squeeze_zero_norm'
    (a := fun R : ℝ => R⁻¹ * (R⁻¹ * (M₂ * ∫ x : Space, g x)))
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hRinvnn : (0:ℝ) ≤ R⁻¹ := inv_nonneg.mpr hR.le
    have hlapbd : ∀ x : Space,
        |∑ i : Fin 3, fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z
          (basisVector i)) x (basisVector i)| ≤ R⁻¹ * R⁻¹ * M₂ := by
      intro x
      calc |∑ i : Fin 3, fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z
            (basisVector i)) x (basisVector i)|
          ≤ ∑ i : Fin 3, |fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z
              (basisVector i)) x (basisVector i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin 3, R⁻¹ * R⁻¹ * M₂f i :=
            Finset.sum_le_sum fun i _ =>
              abs_fderiv_fderiv_scaled_le _ standardBump.contDiff
                (hM₂ i) hR x
        _ = R⁻¹ * R⁻¹ * M₂ := by
            rw [hM₂def, Finset.mul_sum]
    calc ‖∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z
              (basisVector i)) x (basisVector i)) *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2‖
        ≤ ∫ x : Space, ‖(∑ i : Fin 3,
            fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z
              (basisVector i)) x (basisVector i)) *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x : Space, R⁻¹ * R⁻¹ * M₂ * g x := by
          apply integral_mono_of_nonneg
          · filter_upwards with x
            positivity
          · exact hgInt.const_mul (R⁻¹ * R⁻¹ * M₂)
          · filter_upwards with x
            have hsq : (0:ℝ) ≤
                officialEuclideanNorm (vorticity u t₀ x) ^ 2 := sq_nonneg _
            calc ‖(∑ i : Fin 3, fderiv ℝ (fun z =>
                    fderiv ℝ (scaledCutoff R) z (basisVector i)) x
                    (basisVector i)) *
                  officialEuclideanNorm (vorticity u t₀ x) ^ 2‖
                = |∑ i : Fin 3, fderiv ℝ (fun z =>
                    fderiv ℝ (scaledCutoff R) z (basisVector i)) x
                    (basisVector i)| *
                    (officialEuclideanNorm (vorticity u t₀ x) ^ 2) := by
                  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
                    abs_of_nonneg hsq]
              _ ≤ (R⁻¹ * R⁻¹ * M₂) *
                    (officialEuclideanNorm (vorticity u t₀ x) ^ 2) :=
                  mul_le_mul_of_nonneg_right (hlapbd x) hsq
              _ ≤ (R⁻¹ * R⁻¹ * M₂) * g x :=
                  mul_le_mul_of_nonneg_left (hgSq x)
                    (mul_nonneg (mul_nonneg hRinvnn hRinvnn) hM₂sum)
      _ = R⁻¹ * (R⁻¹ * (M₂ * ∫ x : Space, g x)) := by
          rw [integral_const_mul]
          ring
  · have h1 : Tendsto (fun R : ℝ => R⁻¹ * (M₂ * ∫ x : Space, g x))
        atTop (nhds 0) := by
      simpa using tendsto_inv_atTop_zero.mul_const (M₂ * ∫ x : Space, g x)
    have h2 := tendsto_inv_atTop_zero.mul h1
    simpa using h2

/-!
## Continuity of the enstrophy on `[0,T)`
-/

/-- **Continuity clause**: the enstrophy is continuous on `[0,T)` (one-sided
at `0`) under the domination hypothesis, by dominated continuity of the
parametric integral along the time curves. -/
theorem enstrophy_continuousOn
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    {T : ℝ} (hdom : LocallyDominatedEnstrophy u T) :
    ContinuousOn (enstrophy u) (Set.Ico 0 T) := by
  intro t ht
  have hmid : t < (t + T) / 2 := by
    have := ht.2
    linarith
  have hmidT : (t + T) / 2 < T := by
    have := ht.2
    have := ht.1
    linarith
  have hKsub : Set.Icc (0:ℝ) ((t + T) / 2) ⊆ Set.Ico 0 T := fun s hs =>
    ⟨hs.1, lt_of_le_of_lt hs.2 hmidT⟩
  obtain ⟨g, hgInt, hgSq, _⟩ :=
    hdom (Set.Icc 0 ((t + T) / 2)) isCompact_Icc hKsub
  have hIio : Set.Iio ((t + T) / 2) ∈ nhdsWithin t (Set.Ico 0 T) :=
    Filter.le_def.mp nhdsWithin_le_nhds _ (Iio_mem_nhds hmid)
  apply continuousWithinAt_of_dominated (bound := g)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (continuous_officialNormSq_comp
      (vorticity_contDiff hsol hs.1).continuous).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, hIio] with s hs hslt
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hgSq s ⟨hs.1, le_of_lt hslt⟩ x
  · exact hgInt
  · filter_upwards with x
    have hcw : ContinuousWithinAt (fun s => vorticity u s x)
        (Set.Ico 0 T) t :=
      ((differentiableWithinAt_vorticity_timeCurve u hsol.velocity_smooth
        ht.1 x).continuousWithinAt).mono (fun s hs => hs.1)
    exact ((continuous_officialNormSq_comp
      continuous_id).continuousAt).comp_continuousWithinAt hcw

/-!
## The derivative bound `E' ≤ 2·G·E`
-/

/-- **The enstrophy rate bound**: the derivative value `∫ 2⟨ω, ∂ₜω⟩` is at
most `2·G·E`, by the `R → ∞` limit of the cutoff rate identity. -/
theorem enstrophy_rate_le
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p) (hν : 0 ≤ ν)
    {T : ℝ} {G : ℝ → ℝ}
    (hG : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x v : Space,
      officialEuclideanNorm (spatialDerivative u t x v) ≤
        G t * officialEuclideanNorm v)
    (hdom : LocallyDominatedEnstrophy u T)
    (htr : TransportDominatedEnstrophy u T)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 T) :
    (∫ x : Space, 2 * officialInner (vorticity u t₀ x)
      (timeDerivative (fun s => vorticity u s) t₀ x)) ≤
      2 * G t₀ * enstrophy u t₀ := by
  have ht₀Ico : t₀ ∈ Set.Ico (0:ℝ) T := ⟨ht₀.1.le, ht₀.2⟩
  have hKsub : Set.Icc t₀ t₀ ⊆ Set.Ico 0 T := by
    intro s hs
    have hst : s = t₀ := le_antisymm hs.2 hs.1
    rw [hst]
    exact ht₀Ico
  obtain ⟨g, hgInt, hgSqK, hgDK⟩ := hdom (Set.Icc t₀ t₀) isCompact_Icc hKsub
  have ht₀K : t₀ ∈ Set.Icc t₀ t₀ := Set.mem_Icc.mpr ⟨le_refl _, le_refl _⟩
  have hgSq : ∀ x : Space,
      officialEuclideanNorm (vorticity u t₀ x) ^ 2 ≤ g x :=
    fun x => hgSqK t₀ ht₀K x
  have hgD : ∀ x : Space,
      |2 * officialInner (vorticity u t₀ x)
        (timeDerivative (fun s => vorticity u s) t₀ x)| ≤ g x :=
    fun x => hgDK t₀ ht₀K x
  obtain ⟨h, hInt, hdomh⟩ := htr t₀ ht₀Ico
  -- slice continuity inputs
  have hωC : ContDiff ℝ ∞ (vorticity u t₀) := vorticity_contDiff hsol ht₀.1.le
  have hωcont : Continuous (vorticity u t₀) := hωC.continuous
  have huAll : ContDiff ℝ ∞ (u t₀) := contDiff_iff_contDiffAt.mpr fun y =>
    VorticityTransport.contDiffAt_spatial_slice hsol.velocity_smooth
      ht₀.1.le y
  have hDtcont : Continuous
      (fun x => timeDerivative (fun s => vorticity u s) t₀ x) :=
    continuous_timeDerivative_vorticity hsol ht₀.1.le
  have hIcont : Continuous (fun x : Space => 2 * officialInner
      (vorticity u t₀ x)
      (timeDerivative (fun s => vorticity u s) t₀ x)) :=
    continuous_const.mul (continuous_officialInner_comp hωcont hDtcont)
  have hAcont : Continuous (fun x : Space => 2 * officialInner
      (vorticity u t₀ x)
      (spatialDerivative u t₀ x (vorticity u t₀ x))) :=
    continuous_const.mul (continuous_officialInner_comp hωcont
      ((huAll.continuous_fderiv (by norm_num)).clm_apply hωcont))
  -- pointwise bound on the stretching density
  have hApt : ∀ x : Space, |2 * officialInner (vorticity u t₀ x)
      (spatialDerivative u t₀ x (vorticity u t₀ x))| ≤ 2 * |G t₀| * g x := by
    intro x
    have hCS : |officialInner (vorticity u t₀ x)
        (spatialDerivative u t₀ x (vorticity u t₀ x))| ≤
        officialEuclideanNorm (vorticity u t₀ x) *
          officialEuclideanNorm
            (spatialDerivative u t₀ x (vorticity u t₀ x)) :=
      abs_officialInner_le _ _
    have hGx : officialEuclideanNorm
        (spatialDerivative u t₀ x (vorticity u t₀ x)) ≤
        G t₀ * officialEuclideanNorm (vorticity u t₀ x) :=
      hG t₀ ht₀Ico x (vorticity u t₀ x)
    have hnn := officialEuclideanNorm_nonneg (vorticity u t₀ x)
    have hgx := hgSq x
    have habs : G t₀ ≤ |G t₀| := le_abs_self _
    have habsnn : (0:ℝ) ≤ |G t₀| := abs_nonneg _
    rw [abs_mul, abs_two]
    nlinarith [hCS, hGx, hnn, hgx, habs, habsnn, sq_nonneg
      (officialEuclideanNorm (vorticity u t₀ x))]
  -- the sequences and their limits
  have hbd1 : ∀ (R : ℝ) (x : Space), |scaledCutoff R x| ≤ (1:ℝ) := by
    intro R x
    exact abs_le.mpr ⟨by linarith [scaledCutoff_nonneg R x],
      scaledCutoff_le_one R x⟩
  -- I_R → I∞
  have hI : Tendsto (fun R : ℝ => ∫ x : Space, scaledCutoff R x *
      (2 * officialInner (vorticity u t₀ x)
        (timeDerivative (fun s => vorticity u s) t₀ x)))
      atTop (nhds (∫ x : Space, 2 * officialInner (vorticity u t₀ x)
        (timeDerivative (fun s => vorticity u s) t₀ x))) := by
    apply tendsto_integral_filter_of_dominated_convergence g
    · filter_upwards with R
      exact ((scaledCutoff_contDiff R).continuous.mul
        hIcont).aestronglyMeasurable
    · filter_upwards with R
      filter_upwards with x
      calc ‖scaledCutoff R x * (2 * officialInner (vorticity u t₀ x)
            (timeDerivative (fun s => vorticity u s) t₀ x))‖
          = |scaledCutoff R x| * |2 * officialInner (vorticity u t₀ x)
              (timeDerivative (fun s => vorticity u s) t₀ x)| := by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * |2 * officialInner (vorticity u t₀ x)
              (timeDerivative (fun s => vorticity u s) t₀ x)| :=
            mul_le_mul_of_nonneg_right (hbd1 R x) (abs_nonneg _)
        _ = |2 * officialInner (vorticity u t₀ x)
              (timeDerivative (fun s => vorticity u s) t₀ x)| := one_mul _
        _ ≤ g x := hgD x
    · exact hgInt
    · filter_upwards with x
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [scaledCutoff_eventually_one x] with R hR
      rw [hR, one_mul]
  -- S_R → S∞
  have hS : Tendsto (fun R : ℝ => ∫ x : Space, scaledCutoff R x *
      (2 * officialInner (vorticity u t₀ x)
        (spatialDerivative u t₀ x (vorticity u t₀ x))))
      atTop (nhds (∫ x : Space, 2 * officialInner (vorticity u t₀ x)
        (spatialDerivative u t₀ x (vorticity u t₀ x)))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => 2 * |G t₀| * g x)
    · filter_upwards with R
      exact ((scaledCutoff_contDiff R).continuous.mul
        hAcont).aestronglyMeasurable
    · filter_upwards with R
      filter_upwards with x
      calc ‖scaledCutoff R x * (2 * officialInner (vorticity u t₀ x)
            (spatialDerivative u t₀ x (vorticity u t₀ x)))‖
          = |scaledCutoff R x| * |2 * officialInner (vorticity u t₀ x)
              (spatialDerivative u t₀ x (vorticity u t₀ x))| := by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * |2 * officialInner (vorticity u t₀ x)
              (spatialDerivative u t₀ x (vorticity u t₀ x))| :=
            mul_le_mul_of_nonneg_right (hbd1 R x) (abs_nonneg _)
        _ = |2 * officialInner (vorticity u t₀ x)
              (spatialDerivative u t₀ x (vorticity u t₀ x))| := one_mul _
        _ ≤ 2 * |G t₀| * g x := hApt x
    · exact hgInt.const_mul (2 * |G t₀|)
    · filter_upwards with x
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [scaledCutoff_eventually_one x] with R hR
      rw [hR, one_mul]
  -- T_R → 0 and V_R → 0
  have hT := tendsto_transport_remainder (u := u) (t₀ := t₀) hInt hdomh
  have hV := tendsto_viscous_remainder (u := u) (t₀ := t₀) hgInt hgSq
  -- the finite-R identity via uniqueness of the derivative
  have hid : ∀ᶠ R : ℝ in atTop,
      (∫ x : Space, scaledCutoff R x * (2 * officialInner (vorticity u t₀ x)
        (timeDerivative (fun s => vorticity u s) t₀ x))) =
      (∫ x : Space, scaledCutoff R x * (2 * officialInner (vorticity u t₀ x)
          (spatialDerivative u t₀ x (vorticity u t₀ x))))
        + (∫ x : Space, fderiv ℝ (scaledCutoff R) x (u t₀ x) *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2)
        + ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z (basisVector i)) x
              (basisVector i)) *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2)
        - 2 * ν * (∫ x : Space, scaledCutoff R x * (∑ i : Fin 3,
            officialEuclideanNorm
              (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2)) := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact (cutoffEnstrophy_hasDerivAt hsol hdom
        (scaledCutoff_contDiff R).continuous (hbd1 R) ht₀).unique
      (cutoffEnstrophy_hasDerivAt_ibp hsol hdom (scaledCutoff_contDiff R)
        (scaledCutoff_hasCompactSupport hR) ht₀)
  -- the dissipation limit is nonnegative
  have hDlim : Tendsto (fun R : ℝ =>
      2 * ν * (∫ x : Space, scaledCutoff R x * (∑ i : Fin 3,
        officialEuclideanNorm
          (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2)))
      atTop (nhds ((∫ x : Space, 2 * officialInner (vorticity u t₀ x)
          (spatialDerivative u t₀ x (vorticity u t₀ x))) + 0 + ν * 0
        - (∫ x : Space, 2 * officialInner (vorticity u t₀ x)
          (timeDerivative (fun s => vorticity u s) t₀ x)))) := by
    apply Filter.Tendsto.congr' _ (((hS.add hT).add (hV.const_mul ν)).sub hI)
    filter_upwards [hid] with R hRid
    linarith [hRid]
  have hnn : ∀ᶠ R : ℝ in atTop, (0:ℝ) ≤
      2 * ν * (∫ x : Space, scaledCutoff R x * (∑ i : Fin 3,
        officialEuclideanNorm
          (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2)) := by
    filter_upwards with R
    have hint : (0:ℝ) ≤ ∫ x : Space, scaledCutoff R x * (∑ i : Fin 3,
        officialEuclideanNorm
          (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2) :=
      integral_nonneg fun x => mul_nonneg (scaledCutoff_nonneg R x)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)
    nlinarith [hν, hint]
  have hkey := ge_of_tendsto hDlim hnn
  -- E' value ≤ S∞
  have hIA : (∫ x : Space, 2 * officialInner (vorticity u t₀ x)
      (timeDerivative (fun s => vorticity u s) t₀ x)) ≤
      ∫ x : Space, 2 * officialInner (vorticity u t₀ x)
        (spatialDerivative u t₀ x (vorticity u t₀ x)) := by
    linarith [hkey]
  -- S∞ ≤ 2·G·E via the pointwise stretching bound
  have hωint : Integrable (fun x : Space =>
      officialEuclideanNorm (vorticity u t₀ x) ^ 2) := by
    refine hgInt.mono' (continuous_officialNormSq_comp
      hωcont).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hgSq x
  have hAint : Integrable (fun x : Space => 2 * officialInner
      (vorticity u t₀ x)
      (spatialDerivative u t₀ x (vorticity u t₀ x))) := by
    refine (hgInt.const_mul (2 * |G t₀|)).mono'
      hAcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hApt x
  have hSle : (∫ x : Space, 2 * officialInner (vorticity u t₀ x)
      (spatialDerivative u t₀ x (vorticity u t₀ x))) ≤
      2 * G t₀ * enstrophy u t₀ := by
    have hpt : (fun x : Space => 2 * officialInner (vorticity u t₀ x)
        (spatialDerivative u t₀ x (vorticity u t₀ x))) ≤
        (fun x : Space => 2 * G t₀ *
          officialEuclideanNorm (vorticity u t₀ x) ^ 2) := by
      intro x
      have := stretching_pointwise_bound (vorticity u t₀ x)
        (spatialDerivative u t₀ x (vorticity u t₀ x))
        (hG t₀ ht₀Ico x (vorticity u t₀ x))
      nlinarith [this]
    calc (∫ x : Space, 2 * officialInner (vorticity u t₀ x)
          (spatialDerivative u t₀ x (vorticity u t₀ x)))
        ≤ ∫ x : Space, 2 * G t₀ *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2 :=
          integral_mono hAint (hωint.const_mul (2 * G t₀)) hpt
      _ = 2 * G t₀ *
            ∫ x : Space, officialEuclideanNorm (vorticity u t₀ x) ^ 2 :=
          integral_const_mul _ _
      _ = 2 * G t₀ * enstrophy u t₀ := rfl
  linarith [hIA, hSle]

/-!
## The enstrophy differential inequality — closed
-/

/-- **Enstrophy differential inequality** (Majda–Bertozzi §3.3), the
Pattern-A-strengthened closure of the former `Enstrophy` skeleton.  Along a
classical solution with a gradient majorant `G` and the two named domination
hypotheses (both automatic for `H^m`/Schwartz-class solutions, both anchored
by the zero solution), the enstrophy is continuous on `[0,T)`, differentiable
on `(0,T)`, and satisfies `E' ≤ 2·G·E`. -/
theorem enstrophyDifferentialInequality
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p) (hν : 0 ≤ ν)
    {T : ℝ} (G : ℝ → ℝ)
    (hG : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x v : Space,
      officialEuclideanNorm (spatialDerivative u t x v) ≤
        G t * officialEuclideanNorm v)
    (hdom : LocallyDominatedEnstrophy u T)
    (htr : TransportDominatedEnstrophy u T) :
    ContinuousOn (enstrophy u) (Set.Ico 0 T) ∧
    ∀ t ∈ Set.Ioo (0:ℝ) T,
      ∃ E' : ℝ, HasDerivAt (enstrophy u) E' t ∧
        E' ≤ 2 * G t * enstrophy u t := by
  refine ⟨enstrophy_continuousOn hsol hdom, fun t ht => ?_⟩
  exact ⟨_, enstrophy_hasDerivAt hsol hdom ht,
    enstrophy_rate_le hsol hν hG hdom htr ht⟩

/-!
## The a-priori bound (Grönwall wiring, now unconditional)
-/

/-- **Enstrophy a-priori bound** (now fully unconditional): along a classical
solution with a continuous gradient majorant and the two domination
hypotheses,

  `E(t) ≤ (1 + E(0))·exp(2∫₀ᵗ G) − 1`  on `[0,T)`.

The differential inequality feeds the linear Grönwall engine
`gronwall_log_apriori` applied to `Y = 1 + E`.  This is the vorticity-`L²`
majorant `M₂` that the BKM assembly consumes. -/
theorem enstrophy_apriori_bound
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p) (hν : 0 ≤ ν)
    {T : ℝ} (G : ℝ → ℝ)
    (hGc : ContinuousOn G (Set.Ico 0 T))
    (hGnn : ∀ t ∈ Set.Ico (0:ℝ) T, 0 ≤ G t)
    (hG : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x v : Space,
      officialEuclideanNorm (spatialDerivative u t x v) ≤
        G t * officialEuclideanNorm v)
    (hdom : LocallyDominatedEnstrophy u T)
    (htr : TransportDominatedEnstrophy u T) :
    ∀ t ∈ Set.Ico (0:ℝ) T,
      enstrophy u t ≤
        (1 + enstrophy u 0) *
          Real.exp (∫ s in (0:ℝ)..t, 2 * G s) - 1 := by
  obtain ⟨hEc, hEderiv⟩ :=
    enstrophyDifferentialInequality hsol hν G hG hdom htr
  intro t ht
  have hIcc_sub : Set.Icc 0 t ⊆ Set.Ico 0 T := by
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hIoo_sub : Set.Ioo 0 t ⊆ Set.Ioo 0 T := by
    intro s hs
    exact ⟨hs.1, lt_trans hs.2 ht.2⟩
  set Y : ℝ → ℝ := fun s => 1 + enstrophy u s with hYdef
  have hYc : ContinuousOn Y (Set.Icc 0 t) :=
    continuousOn_const.add (hEc.mono hIcc_sub)
  have hYpos : ∀ s ∈ Set.Icc 0 t, 0 < Y s := by
    intro s _
    have := enstrophy_nonneg u s
    simp only [hYdef]
    linarith
  have hYfacts : ∀ s ∈ Set.Ioo 0 t,
      HasDerivAt Y (deriv Y s) s ∧
      deriv Y s ≤ (2 * G s) * Y s := by
    intro s hs
    obtain ⟨E', hE', hE'le⟩ := hEderiv s (hIoo_sub hs)
    have hYd : HasDerivAt Y E' s := hE'.const_add 1
    have hderiv : deriv Y s = E' := hYd.deriv
    rw [hderiv]
    refine ⟨hYd, ?_⟩
    have hsIco : s ∈ Set.Ico (0:ℝ) T :=
      ⟨le_of_lt hs.1, lt_trans hs.2 ht.2⟩
    have hGs : 0 ≤ G s := hGnn s hsIco
    have hEs : 0 ≤ enstrophy u s := enstrophy_nonneg u s
    calc E' ≤ 2 * G s * enstrophy u s := hE'le
      _ ≤ (2 * G s) * Y s := by
          simp only [hYdef]
          nlinarith
  have hgc : ContinuousOn (fun s => 2 * G s) (Set.Icc 0 t) :=
    continuousOn_const.mul (hGc.mono hIcc_sub)
  have hcore := gronwall_log_apriori (Y := Y) (Y' := deriv Y)
    (g := fun s => 2 * G s) (T := t) ht.1 hgc hYc
    (fun s hs => (hYfacts s hs).1) hYpos
    (fun s hs => (hYfacts s hs).2)
    t ⟨ht.1, le_rfl⟩
  have hY0 : Y 0 = 1 + enstrophy u 0 := rfl
  have hYt : Y t = 1 + enstrophy u t := rfl
  rw [hY0, hYt] at hcore
  linarith [hcore]

end Navier.Analysis.EnstrophyLimit
