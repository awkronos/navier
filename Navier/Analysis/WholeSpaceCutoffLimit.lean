import Navier.Analysis.WholeSpaceDuhamel
import Navier.Analysis.PressurePoisson

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

This is not yet the whole-space Duhamel formula.  A Gaussian translate has
noncompact support, so transporting the result below to that test still needs
a cutoff-to-Gaussian limit with tail domination.  No such domination, Leray
bound, pressure normalization, or Duhamel representation is assumed here.

Pattern classification: `representationTransport`; the finite-cutoff time
integration is `kernelClosed`; the Gaussian-limit consumer remains
`scientificFrontier`.
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

end Navier.Analysis.WholeSpaceCutoffLimit
