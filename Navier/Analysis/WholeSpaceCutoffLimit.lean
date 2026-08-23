import Navier.Analysis.WholeSpaceDuhamel
import Navier.Analysis.PressurePoisson
import Navier.Analysis.ScaledCutoff

/-!
# Whole-space cutoff momentum: time integration

This module performs the first genuine composition after
`WholeSpaceDuhamel.cutoff_testedMomentum_coordinate`.  For every smooth,
compactly supported spatial test `χ`, it proves that the tested momentum

`M_{χ,j}(t) = ∫ χ(x) u_j(t,x) dx`

is differentiable at interior times.  Compact support supplies the uniform
spatial majorant needed to differentiate under the integral; it is derived
from the actual `PartialClassicalSolution` smoothness on a compact spacetime
window, rather than postulated as a decay hypothesis.  The fundamental theorem
of calculus and the finite-cutoff momentum identity then give the exact
time-integrated weak momentum balance on every `[a,b] ⊂ (0,T)`.

This is not yet the whole-space Duhamel formula.  The module now transports
the complete finite-cutoff balance to a Gaussian test through its endpoint
integrals and separately proves that every integrably dominated
first-derivative cutoff remainder is `O(R⁻¹)`.  Splitting the surviving
Gaussian-gradient, viscous, and pressure terms still needs their own spatial
and time-uniform domination; no Leray bound, pressure normalization, or
Duhamel representation is assumed here.

Pattern classification: `representationTransport`; the finite-cutoff time
integration, combined Gaussian transport, and cutoff-derivative tail lemma
are `kernelClosed`; the termwise Duhamel consumer remains `scientificFrontier`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff Interval
open MeasureTheory Set

namespace Navier.Analysis.WholeSpaceCutoffLimit

open Navier
open Navier.Breakdown
open Navier.Analysis.ParabolicCaccioppoli
open Navier.Analysis.PressurePoisson
open Navier.Analysis.WholeSpaceDuhamel
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.ScaledCutoff

/-! ### Time-slice regularity before the terminal time -/

/-- The within derivative of a fixed-space time curve on `[0,T)` is the joint
spacetime within derivative in direction `(1,0)`. -/
theorem fderivWithin_timeSlice_apply_before {β : Type*}
    [NormedAddCommGroup β] [NormedSpace ℝ β] {F : ℝ → Space → β} {T : ℝ}
    (hT : 0 < T)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Space => F z.1 z.2) (spacetimeBefore T))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) (y : Space) :
    fderivWithin ℝ (fun s => F s y) (Set.Ico 0 T) t 1 =
      fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (spacetimeBefore T) (t, y) (1, 0) := by
  have hmem : (t, y) ∈ spacetimeBefore T :=
    Set.mem_prod.mpr ⟨⟨ht0, htT⟩, Set.mem_univ y⟩
  have hG : HasFDerivWithinAt (fun z : ℝ × Space => F z.1 z.2)
      (fderivWithin ℝ (fun z : ℝ × Space => F z.1 z.2)
        (spacetimeBefore T) (t, y))
      (spacetimeBefore T) (t, y) :=
    ((hF (t, y) hmem).differentiableWithinAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)).hasFDerivWithinAt
  have hι : HasFDerivAt (fun s : ℝ => (s, y))
      (ContinuousLinearMap.inl ℝ ℝ Space) t := hasFDerivAt_prodMk_left t y
  have hmaps : Set.MapsTo (fun s : ℝ => (s, y)) (Set.Ico 0 T)
      (spacetimeBefore T) := fun s hs =>
    Set.mem_prod.mpr ⟨hs, Set.mem_univ y⟩
  have hcomp := HasFDerivWithinAt.comp t hG hι.hasFDerivWithinAt hmaps
  rw [show ((fun z : ℝ × Space => F z.1 z.2) ∘ (fun s : ℝ => (s, y))) =
      (fun s => F s y) from rfl] at hcomp
  have hUD : UniqueDiffWithinAt ℝ (Set.Ico 0 T) t :=
    (uniqueDiffOn_convex (convex_Ico 0 T)
      (by rw [interior_Ico]; exact nonempty_Ioo.mpr hT)) t
      (Set.mem_Ico.mpr ⟨ht0, htT⟩)
  rw [hcomp.fderivWithin hUD, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply]

/-- The one-sided `timeDerivative` component is jointly continuous on the
whole half-open spacetime domain of a partial classical solution. -/
theorem timeDerivative_component_continuousOn
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T) (j : Fin 3) :
    ContinuousOn (fun z : ℝ × Space =>
      timeDerivative sol.velocity z.1 z.2 j) (spacetimeBefore T) := by
  have hD : ContinuousOn
      (fun z : ℝ × Space =>
        fderivWithin ℝ (fun z : ℝ × Space => sol.velocity z.1 z.2)
          (spacetimeBefore T) z (1, 0)) (spacetimeBefore T) :=
    ((sol.velocity_smooth.continuousOn_fderivWithin
      (uniqueDiffOn_spacetimeBefore sol.terminalTime_pos) (by norm_num)).clm_apply
      continuousOn_const)
  have hDj : ContinuousOn
      (fun z : ℝ × Space =>
        (fderivWithin ℝ (fun z : ℝ × Space => sol.velocity z.1 z.2)
          (spacetimeBefore T) z (1, 0)) j) (spacetimeBefore T) :=
    (continuous_apply j).continuousOn.comp hD (fun _ _ => Set.mem_univ _)
  refine hDj.congr ?_
  rintro ⟨t, x⟩ ht
  have ht0 : 0 ≤ t := ht.1.1
  have htT : t < T := ht.1.2
  unfold timeDerivative
  change (fderivWithin ℝ (fun s : ℝ => sol.velocity s x) (Set.Ici 0) t 1) j = _
  rw [fderivWithin_Ici_eq_fderivWithin_Ico htT]
  exact congrArg (fun v : Space => v j)
    (fderivWithin_timeSlice_apply_before sol.terminalTime_pos
      sol.velocity_smooth ht0 htT x)

/-- At an interior time, a fixed-space velocity component has the repository's
one-sided `timeDerivative` as its ordinary two-sided derivative. -/
theorem velocityComponent_hasDerivAt_time
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) (j : Fin 3) :
    HasDerivAt (fun s : ℝ => sol.velocity s x j)
      (timeDerivative sol.velocity t x j) t := by
  have hparam : ContDiffOn ℝ ∞ (fun s : ℝ => (s, x)) (Set.Ico 0 T) := by
    fun_prop
  have hcurve : ContDiffOn ℝ ∞ (fun s : ℝ => sol.velocity s x) (Set.Ico 0 T) := by
    change ContDiffOn ℝ ∞
      ((fun z : ℝ × Space => sol.velocity z.1 z.2) ∘ fun s : ℝ => (s, x))
      (Set.Ico 0 T)
    exact sol.velocity_smooth.comp hparam (by
      intro s hs
      exact ⟨hs, Set.mem_univ x⟩)
  have hnhds : Set.Ico (0 : ℝ) T ∈ nhds t := Ico_mem_nhds ht0 htT
  have hda : DifferentiableAt ℝ (fun s : ℝ => sol.velocity s x) t :=
    (hcurve.differentiableOn (by simp) t ⟨ht0.le, htT⟩).differentiableAt hnhds
  have hval : timeDerivative sol.velocity t x =
      fderiv ℝ (fun s : ℝ => sol.velocity s x) t 1 := by
    unfold timeDerivative
    rw [fderivWithin_of_mem_nhds (Ici_mem_nhds ht0)]
  have hv : HasDerivAt (fun s : ℝ => sol.velocity s x)
      (timeDerivative sol.velocity t x) t := by
    rw [hval]
    simpa [fderiv_apply_one_eq_deriv] using hda.hasDerivAt
  exact (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp_hasDerivAt t hv

/-! ### Differentiation and time integration of compactly tested momentum -/

/-- The `j`th momentum coordinate tested against a spatial cutoff `χ`. -/
def cutoffMomentumCoordinate
    (χ : Space → ℝ) (u : VelocityEvolution) (j : Fin 3) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * u t x j

/-- Compact support is enough to differentiate tested momentum under the
spatial integral at every interior time.  The required majorant is constructed
from continuity of `∂ₜu_j` on a compact time window times `tsupport χ`; it is
not an extra hypothesis. -/
theorem cutoffMomentumCoordinate_hasDerivAt
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    {t₀ : ℝ} (ht₀0 : 0 < t₀) (ht₀T : t₀ < T) (j : Fin 3) :
    HasDerivAt (cutoffMomentumCoordinate χ sol.velocity j)
      (∫ x : Space, χ x * timeDerivative sol.velocity t₀ x j) t₀ := by
  set ε : ℝ := min (t₀ / 2) ((T - t₀) / 2) with hεdef
  have hε1 : ε ≤ t₀ / 2 := min_le_left _ _
  have hε2 : ε ≤ (T - t₀) / 2 := min_le_right _ _
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hKsub : Set.Icc (t₀ - ε) (t₀ + ε) ⊆ Set.Ico 0 T := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hpos : ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε), (0 : ℝ) < s := by
    intro s hs
    linarith [hs.1]
  have hs_nhds : Set.Icc (t₀ - ε) (t₀ + ε) ∈ nhds t₀ :=
    Icc_mem_nhds (by linarith) (by linarith)
  have htdJoint := timeDerivative_component_continuousOn sol j
  have hproductSub :
      Set.Icc (t₀ - ε) (t₀ + ε) ×ˢ tsupport χ ⊆ spacetimeBefore T := by
    rintro ⟨s, x⟩ hs
    exact ⟨hKsub hs.1, Set.mem_univ x⟩
  have hcompact : IsCompact
      (Set.Icc (t₀ - ε) (t₀ + ε) ×ˢ tsupport χ) :=
    isCompact_Icc.prod hχsupp
  have htdNorm : ContinuousOn (fun z : ℝ × Space =>
      ‖timeDerivative sol.velocity z.1 z.2 j‖)
      (Set.Icc (t₀ - ε) (t₀ + ε) ×ˢ tsupport χ) :=
    htdJoint.norm.mono hproductSub
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image htdNorm
  let B : ℝ := max C 0
  have htd_le : ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε), ∀ x ∈ tsupport χ,
      ‖timeDerivative sol.velocity s x j‖ ≤ B := by
    intro s hs x hx
    have hz : (s, x) ∈
        Set.Icc (t₀ - ε) (t₀ + ε) ×ˢ tsupport χ := ⟨hs, hx⟩
    exact (hC (Set.mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hF_meas : ∀ᶠ s in nhds t₀, AEStronglyMeasurable
      (fun x : Space => χ x * sol.velocity s x j) volume := by
    filter_upwards [hs_nhds] with s hs
    have hu := (velocity_slice_contDiff sol (hKsub hs).1 (hKsub hs).2).continuous
    exact (hχ.continuous.mul ((continuous_apply j).comp hu)).aestronglyMeasurable
  have hu₀ := (velocity_slice_contDiff sol ht₀0.le ht₀T).continuous
  have hF_int : Integrable (fun x : Space => χ x * sol.velocity t₀ x j) volume :=
    (hχ.continuous.mul ((continuous_apply j).comp hu₀)
      ).integrable_of_hasCompactSupport hχsupp.mul_right
  have htd₀ : Continuous (fun x : Space =>
      timeDerivative sol.velocity t₀ x j) := by
    rw [← continuousOn_univ]
    exact htdJoint.comp (Continuous.prodMk continuous_const continuous_id).continuousOn
      (by intro x _; exact ⟨⟨ht₀0.le, ht₀T⟩, Set.mem_univ x⟩)
  have hF'_meas : AEStronglyMeasurable
      (fun x : Space => χ x * timeDerivative sol.velocity t₀ x j) volume :=
    (hχ.continuous.mul htd₀).aestronglyMeasurable
  have hboundInt : Integrable (fun x : Space => B * ‖χ x‖) volume :=
    (hχ.continuous.norm.integrable_of_hasCompactSupport hχsupp.norm).const_mul B
  have h_bound : ∀ᵐ x ∂(volume : Measure Space),
      ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      ‖χ x * timeDerivative sol.velocity s x j‖ ≤ B * ‖χ x‖ := by
    filter_upwards with x s hs
    by_cases hx0 : χ x = 0
    · simp [hx0]
    · have hx : x ∈ tsupport χ :=
        subset_closure (by simpa [Function.mem_support] using hx0)
      rw [norm_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (htd_le s hs x hx) (norm_nonneg _)
  have h_diff : ∀ᵐ x ∂(volume : Measure Space),
      ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun s' : ℝ => χ x * sol.velocity s' x j)
        (χ x * timeDerivative sol.velocity s x j) s := by
    filter_upwards with x s hs
    exact (velocityComponent_hasDerivAt_time sol
      (hpos s hs) (hKsub hs).2 x j).const_mul (χ x)
  change HasDerivAt (fun t : ℝ =>
    ∫ x : Space, χ x * sol.velocity t x j ∂volume)
      (∫ x : Space, χ x * timeDerivative sol.velocity t₀ x j ∂volume) t₀
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds hF_meas
    hF_int hF'_meas h_bound hboundInt h_diff).2

/-- The compactly tested time-derivative integral varies continuously on every
closed interior time interval. -/
theorem cutoffTimeDerivative_continuousOn
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    {a b : ℝ} (ha0 : 0 < a) (hbT : b < T) (j : Fin 3) :
    ContinuousOn (fun t : ℝ =>
      ∫ x : Space, χ x * timeDerivative sol.velocity t x j) (Set.Icc a b) := by
  have htdJoint := timeDerivative_component_continuousOn sol j
  have hsub : Set.Icc a b ×ˢ (Set.univ : Set Space) ⊆ spacetimeBefore T := by
    rintro ⟨t, x⟩ ht
    exact ⟨⟨ha0.le.trans ht.1.1, ht.1.2.trans_lt hbT⟩, Set.mem_univ x⟩
  have hf : ContinuousOn (Function.uncurry (fun t (x : Space) =>
      χ x * timeDerivative sol.velocity t x j))
      (Set.Icc a b ×ˢ (Set.univ : Set Space)) := by
    exact ((hχ.continuous.comp continuous_snd).continuousOn.mul
      (htdJoint.mono hsub))
  apply continuousOn_integral_of_compact_support hχsupp hf
  intro t x _ht hx
  have hx0 : χ x = 0 := by
    by_contra hne
    exact hx (subset_closure (by simpa [Function.mem_support] using hne))
  simp [hx0]

/-- **Time-integrated finite-cutoff momentum identity.**  On every closed
interior interval `[a,b] ⊂ (0,T)`, the increment of compactly tested momentum
equals the time integral of the transport, viscous, and pressure pairings with
derivatives transferred onto `χ`:

`M_{χ,j}(b) - M_{χ,j}(a) = ∫ₐᵇ [∫(u·∇χ)u_j + ν∫(Δχ)u_j + ∫(∂_jχ)p] dt`.

This theorem genuinely consumes
`WholeSpaceDuhamel.cutoff_testedMomentum_coordinate`; the separate
differentiation-under-the-integral theorem above turns its left side into the
momentum increment. -/
theorem cutoffMomentumCoordinate_timeIntegrated
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hbT : b < T) (j : Fin 3) :
    cutoffMomentumCoordinate χ sol.velocity j b -
        cutoffMomentumCoordinate χ sol.velocity j a =
      ∫ t in a..b,
        (∫ x : Space,
          fderiv ℝ χ x (sol.velocity t x) * sol.velocity t x j) +
        ν * (∫ x : Space, (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i)) *
            sol.velocity t x j) +
        (∫ x : Space,
          fderiv ℝ χ x (basisVector j) * sol.pressure t x) := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (cutoffMomentumCoordinate χ sol.velocity j)
        (∫ x : Space, χ x * timeDerivative sol.velocity t x j) t := by
    intro t ht
    have ht' : t ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using ht
    exact cutoffMomentumCoordinate_hasDerivAt sol hχ hχsupp
      (ha0.trans_le ht'.1) (ht'.2.trans_lt hbT) j
  have hcont : ContinuousOn (fun t : ℝ =>
      ∫ x : Space, χ x * timeDerivative sol.velocity t x j) (Set.uIcc a b) := by
    simpa [uIcc_of_le hab] using
      cutoffTimeDerivative_continuousOn sol hχ hχsupp ha0 hbT j
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  calc
    cutoffMomentumCoordinate χ sol.velocity j b -
        cutoffMomentumCoordinate χ sol.velocity j a =
        ∫ t in a..b, ∫ x : Space,
          χ x * timeDerivative sol.velocity t x j := hftc.symm
    _ = ∫ t in a..b,
        (∫ x : Space,
          fderiv ℝ χ x (sol.velocity t x) * sol.velocity t x j) +
        ν * (∫ x : Space, (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i)) *
            sol.velocity t x j) +
        (∫ x : Space,
          fderiv ℝ χ x (basisVector j) * sol.pressure t x) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using ht
      exact cutoff_testedMomentum_coordinate sol hχ hχsupp
        (ha0.le.trans ht'.1) (ht'.2.trans_lt hbT) j

/-! ### The actual cutoff-to-Gaussian limit -/

/-- The first-derivative cutoff tail vanishes against every integrably
dominated vector/scalar product.  This is the exact `Dχ_R(v) · f` remainder
created when the derivative in a tested momentum term is expanded across
`χ_R G`; unlike the combined-balance transport below, it identifies one
termwise limit and records the sharp `O(R⁻¹)` rate.

Reference: Majda--Bertozzi, *Vorticity and Incompressible Flow*, §3.3. -/
theorem scaledCutoff_fderiv_remainder_tendsto_zero
    (v : Space → Space) (f h : Space → ℝ) (hInt : Integrable h)
    (hdom : ∀ x : Space, ‖v x‖ * |f x| ≤ h x) :
    Filter.Tendsto (fun R : ℝ => ∫ x : Space,
        fderiv ℝ (scaledCutoff R) x (v x) * f x)
      Filter.atTop (nhds 0) := by
  obtain ⟨M, hMnn, hM⟩ := exists_fderiv_opNorm_bound _
    standardBump.contDiff standardBump.hasCompactSupport
  apply squeeze_zero_norm'
    (a := fun R : ℝ => R⁻¹ * (M * ∫ x : Space, h x))
  · filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    have hRinvnn : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.mpr hR.le
    calc
      ‖∫ x : Space, fderiv ℝ (scaledCutoff R) x (v x) * f x‖
          ≤ ∫ x : Space, ‖fderiv ℝ (scaledCutoff R) x (v x) * f x‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x : Space, R⁻¹ * M * h x := by
        apply integral_mono_of_nonneg
        · filter_upwards with x
          positivity
        · exact hInt.const_mul (R⁻¹ * M)
        · filter_upwards with x
          have hd : |fderiv ℝ (scaledCutoff R) x (v x)| ≤
              R⁻¹ * M * ‖v x‖ :=
            abs_fderiv_scaled_le _ standardBump.contDiff hM hR x (v x)
          calc
            ‖fderiv ℝ (scaledCutoff R) x (v x) * f x‖
                = |fderiv ℝ (scaledCutoff R) x (v x)| * |f x| := by
                  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
            _ ≤ (R⁻¹ * M * ‖v x‖) * |f x| :=
              mul_le_mul_of_nonneg_right hd (abs_nonneg _)
            _ = R⁻¹ * M * (‖v x‖ * |f x|) := by ring
            _ ≤ R⁻¹ * M * h x :=
              mul_le_mul_of_nonneg_left (hdom x)
                (mul_nonneg hRinvnn hMnn)
      _ = R⁻¹ * (M * ∫ x : Space, h x) := by
        rw [integral_const_mul]
        ring
  · simpa using
      tendsto_inv_atTop_zero.mul_const (M * ∫ x : Space, h x)

/-- Multiplication by the concrete scaled cutoff converges under every
integrable spatial integral.  The standard bump is pointwise eventually one
and lies in `[0,1]`, so `‖f‖` is the global dominating function. -/
theorem scaledCutoff_integral_tendsto (f : Space → ℝ) (hf : Integrable f) :
    Filter.Tendsto (fun R : ℝ => ∫ y : Space, scaledCutoff R y * f y)
      Filter.atTop (nhds (∫ y : Space, f y)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖)
  · filter_upwards with R
    exact (scaledCutoff_contDiff R).continuous.aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · filter_upwards with R
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg (f y)) (by
      rw [Real.norm_eq_abs, abs_of_nonneg (scaledCutoff_nonneg R y)]
      exact scaledCutoff_le_one R y)
  · exact hf.norm
  · filter_upwards with y
    have heq : (fun R : ℝ => scaledCutoff R y * f y) =ᶠ[Filter.atTop]
        (fun _ => f y) := by
      filter_upwards [scaledCutoff_eventually_one y] with R hR
      simp [hR]
    exact tendsto_const_nhds.congr' heq.symm

/-- Every fixed Gaussian translate is smooth in its spatial variable. -/
theorem heatKernel_translate_contDiff (ν τ : ℝ) (x : Space) :
    ContDiff ℝ ∞ (fun y : Space => heatKernel ν τ (x - y)) := by
  unfold heatKernel
  fun_prop

/-- The time-integrated right-hand side of the finite-cutoff coordinate
momentum identity. -/
def cutoffMomentumCoordinateTimeRhs
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (χ : Space → ℝ) (a b : ℝ) (j : Fin 3) : ℝ :=
  ∫ t in a..b,
    (∫ x : Space,
      fderiv ℝ χ x (sol.velocity t x) * sol.velocity t x j) +
    ν * (∫ x : Space, (∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i)) *
        sol.velocity t x j) +
    (∫ x : Space,
      fderiv ℝ χ x (basisVector j) * sol.pressure t x)

/-- **Cutoff-to-Gaussian convergence of the full tested momentum balance.**
For the concrete tests

`χ_R(y) G^κ_τ(x₀-y)`,

the complete time-integrated finite-cutoff PDE right-hand side converges to
the increment of Gaussian-tested momentum.  Endpoint integrability is the
only domination used: the finite-cutoff momentum identity transports the
right-hand side as one gauge-invariant package, while dominated convergence
acts on its momentum endpoints.

This is deliberately not a termwise Duhamel formula.  Splitting the limit
into convection, viscosity, pressure/Leray pieces still requires the missing
space-time tail bounds; the theorem isolates that remaining residual without
assuming the desired representation. -/
theorem gaussianCutoffMomentumRhs_tendsto
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hbT : b < T) (j : Fin 3)
    (κ τ : ℝ) (x₀ : Space)
    (hint_a : Integrable (fun y : Space =>
      heatKernel κ τ (x₀ - y) * sol.velocity a y j))
    (hint_b : Integrable (fun y : Space =>
      heatKernel κ τ (x₀ - y) * sol.velocity b y j)) :
    Filter.Tendsto (fun R : ℝ => cutoffMomentumCoordinateTimeRhs sol
        (fun y : Space => scaledCutoff R y * heatKernel κ τ (x₀ - y)) a b j)
      Filter.atTop (nhds
        ((∫ y : Space, heatKernel κ τ (x₀ - y) * sol.velocity b y j) -
          ∫ y : Space, heatKernel κ τ (x₀ - y) * sol.velocity a y j)) := by
  have ha := scaledCutoff_integral_tendsto
    (fun y : Space => heatKernel κ τ (x₀ - y) * sol.velocity a y j) hint_a
  have hb := scaledCutoff_integral_tendsto
    (fun y : Space => heatKernel κ τ (x₀ - y) * sol.velocity b y j) hint_b
  have hleft := hb.sub ha
  apply hleft.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
  have htestDiff : ContDiff ℝ ∞
      (fun y : Space => scaledCutoff R y * heatKernel κ τ (x₀ - y)) :=
    (scaledCutoff_contDiff R).mul (heatKernel_translate_contDiff κ τ x₀)
  have htestSupp : HasCompactSupport
      (fun y : Space => scaledCutoff R y * heatKernel κ τ (x₀ - y)) :=
    (scaledCutoff_hasCompactSupport hR).mul_right
  have hfinite := cutoffMomentumCoordinate_timeIntegrated sol htestDiff
    htestSupp ha0 hab hbT j
  simpa [cutoffMomentumCoordinateTimeRhs, cutoffMomentumCoordinate, mul_assoc]
    using hfinite

end Navier.Analysis.WholeSpaceCutoffLimit
