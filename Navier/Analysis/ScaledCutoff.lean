import Navier.Analysis.CutoffIntegrationByParts

/-!
# The scaled cutoff family `χ_R = χ(·/R)` (integral layer, part c input)

The concrete cutoff family consumed by the `R → ∞` layer of the enstrophy
estimate, with the derivative decay that makes the remainders of
`cutoffEnstrophy_hasDerivAt_ibp` vanish:

* `fderiv_scaled_apply` / `fderiv_fderiv_scaled_apply` — exact chain-rule
  scaling `∂_v(χ(·/R)) = R⁻¹ (∂_v χ)(·/R)` and
  `∂_w∂_v(χ(·/R)) = R⁻² (∂_w∂_v χ)(·/R)`.
* `contDiff_scaled` / `hasCompactSupport_scaled` — the scaled function stays
  smooth and compactly supported (`R > 0`), so every `χ_R` satisfies the
  hypotheses of the cutoff rate and IBP layer.
* `exists_fderiv_opNorm_bound` and the decay estimates `abs_fderiv_scaled_le`
  (`|∂_v χ_R| ≤ R⁻¹ M ‖v‖` — the transport remainder rate) and
  `abs_fderiv_fderiv_scaled_le` (`|∂_w∂_v χ_R| ≤ R⁻² M₂` — the viscous
  remainder rate).
* `scaled_eventually_one` — pointwise `χ_R(x) = 1` for all large `R`
  whenever the base equals `1` near the origin (the `E_{χ_R} → E`
  input for dominated convergence).
* `standardBump` / `scaledCutoff` — a concrete base (Mathlib's
  `ContDiffBump`, `rIn = 1`, `rOut = 2`) instantiating all of the above:
  `scaledCutoff_contDiff`, `scaledCutoff_hasCompactSupport`,
  `scaledCutoff_nonneg`, `scaledCutoff_le_one`,
  `scaledCutoff_eventually_one`.

Consumer (ladder rung 6, part (c), closed): `EnstrophyLimit` assembles these
decay rates with `cutoffEnstrophy_hasDerivAt_ibp` — the remainder integrals
are `O(R⁻¹)` against an `L¹` majorant of `‖u‖|ω|²` and `O(R⁻²)` against the
`LocallyDominatedEnstrophy` majorant, and the surviving terms converge by
dominated convergence — delivering `E' ≤ 2G·E`
(`EnstrophyLimit.enstrophyDifferentialInequality`) and the Grönwall bound
(`EnstrophyLimit.enstrophy_apriori_bound`).

Reference: Majda–Bertozzi, *Vorticity and Incompressible Flow*, §3.3.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open MeasureTheory Set

namespace Navier.Analysis.ScaledCutoff

open Navier
open Navier.Analysis.CutoffIntegrationByParts

/-!
## Chain-rule scaling of derivatives
-/

/-- First-derivative scaling: `∂_v(χ(·/R))(x) = R⁻¹ (∂_v χ)(x/R)`. -/
theorem fderiv_scaled_apply (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (R : ℝ) (x v : Space) :
    fderiv ℝ (fun y => χ (R⁻¹ • y)) x v = R⁻¹ * fderiv ℝ χ (R⁻¹ • x) v := by
  have hL : HasFDerivAt (fun y : Space => R⁻¹ • y)
      (R⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
    (R⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt
  have hχ' : HasFDerivAt χ (fderiv ℝ χ (R⁻¹ • x)) (R⁻¹ • x) :=
    ((hχ.differentiable (by norm_num)) (R⁻¹ • x)).hasFDerivAt
  have hc := hχ'.comp x hL
  rw [show ((fun y => χ (R⁻¹ • y))) = (χ ∘ fun y : Space => R⁻¹ • y) from rfl,
    hc.fderiv]
  simp [smul_eq_mul]

/-- The scaled function of a smooth function is smooth. -/
theorem contDiff_scaled (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (R : ℝ) :
    ContDiff ℝ ∞ (fun y : Space => χ (R⁻¹ • y)) :=
  hχ.comp (contDiff_const_smul R⁻¹)

/-- The scaled function of a compactly supported function is compactly
supported for `R > 0`. -/
theorem hasCompactSupport_scaled (χ : Space → ℝ) (hsupp : HasCompactSupport χ)
    {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fun y : Space => χ (R⁻¹ • y)) := by
  rw [hasCompactSupport_def]
  have hsub : Function.support (fun y : Space => χ (R⁻¹ • y)) ⊆
      (fun y : Space => R • y) '' tsupport χ := by
    intro y hy
    have hmem : R⁻¹ • y ∈ Function.support χ := hy
    refine ⟨R⁻¹ • y, subset_tsupport χ hmem, ?_⟩
    simp [smul_smul, mul_inv_cancel₀ hR.ne']
  exact IsCompact.of_isClosed_subset
    (IsCompact.image hsupp (continuous_const_smul R)) isClosed_closure
    (closure_minimal hsub
      (IsCompact.image hsupp (continuous_const_smul R)).isClosed)

/-- Second-derivative scaling:
`∂_w(∂_v(χ(·/R)))(x) = R⁻¹·(R⁻¹·(∂_w(∂_v χ))(x/R))`. -/
theorem fderiv_fderiv_scaled_apply (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (R : ℝ) (x v w : Space) :
    fderiv ℝ (fun z => fderiv ℝ (fun y => χ (R⁻¹ • y)) z v) x w =
      R⁻¹ * (R⁻¹ * fderiv ℝ (fun z => fderiv ℝ χ z v) (R⁻¹ • x) w) := by
  have hD : ContDiff ℝ ∞ (fun y => fderiv ℝ χ y v) := contDiff_fderiv_apply hχ v
  have hshape : (fun z => fderiv ℝ (fun y => χ (R⁻¹ • y)) z v) =
      (fun z => R⁻¹ * (fun y => fderiv ℝ χ y v) (R⁻¹ • z)) := by
    funext z
    exact fderiv_scaled_apply χ hχ R z v
  rw [hshape]
  have hDs : DifferentiableAt ℝ
      (fun z : Space => (fun y => fderiv ℝ χ y v) (R⁻¹ • z)) x :=
    ((contDiff_scaled _ hD R).differentiable (by norm_num)).differentiableAt
  rw [fderiv_const_mul hDs R⁻¹]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_scaled_apply _ hD R x w]

/-!
## Uniform bounds and the decay estimates
-/

/-- The operator norm of the derivative of a smooth compactly supported
function is uniformly bounded. -/
theorem exists_fderiv_opNorm_bound (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : HasCompactSupport χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Space, ‖fderiv ℝ χ x‖ ≤ M := by
  obtain ⟨x₀, hx₀⟩ :=
    ((hχ.continuous_fderiv (by norm_num)).norm
      ).exists_forall_ge_of_hasCompactSupport ((hsupp.fderiv (𝕜 := ℝ)).norm)
  exact ⟨‖fderiv ℝ χ x₀‖, norm_nonneg _, hx₀⟩

/-- The evaluated second derivative of a smooth compactly supported function
is uniformly bounded in each pair of directions. -/
theorem exists_fderiv_fderiv_bound (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : HasCompactSupport χ) (v w : Space) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : Space, |fderiv ℝ (fun z => fderiv ℝ χ z v) x w| ≤ M := by
  obtain ⟨x₀, hx₀⟩ :=
    ((contDiff_fderiv_apply (contDiff_fderiv_apply hχ v) w).continuous.abs
      ).exists_forall_ge_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply
        (hasCompactSupport_fderiv_apply hsupp v) w).abs)
  exact ⟨|fderiv ℝ (fun z => fderiv ℝ χ z v) x₀ w|, abs_nonneg _, hx₀⟩

/-- **Transport-remainder decay rate**: `|∂_v(χ(·/R))(x)| ≤ R⁻¹ M ‖v‖` for
`R > 0`, where `M` bounds `‖Dχ‖`.  Against an `L¹` majorant of `‖u‖|ω|²`
this makes the `∇χ_R` remainder of the cutoff enstrophy rate `O(R⁻¹)`. -/
theorem abs_fderiv_scaled_le (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {M : ℝ} (hM : ∀ y : Space, ‖fderiv ℝ χ y‖ ≤ M)
    {R : ℝ} (hR : 0 < R) (x v : Space) :
    |fderiv ℝ (fun y => χ (R⁻¹ • y)) x v| ≤ R⁻¹ * M * ‖v‖ := by
  rw [fderiv_scaled_apply χ hχ R x v, abs_mul, abs_inv, abs_of_pos hR]
  have h1 : |fderiv ℝ χ (R⁻¹ • x) v| ≤ M * ‖v‖ := by
    calc |fderiv ℝ χ (R⁻¹ • x) v| = ‖fderiv ℝ χ (R⁻¹ • x) v‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ χ (R⁻¹ • x)‖ * ‖v‖ :=
          (fderiv ℝ χ (R⁻¹ • x)).le_opNorm v
      _ ≤ M * ‖v‖ :=
          mul_le_mul_of_nonneg_right (hM _) (norm_nonneg v)
  calc R⁻¹ * |fderiv ℝ χ (R⁻¹ • x) v| ≤ R⁻¹ * (M * ‖v‖) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hR.le)
    _ = R⁻¹ * M * ‖v‖ := by ring

/-- **Viscous-remainder decay rate**:
`|∂_w(∂_v(χ(·/R)))(x)| ≤ R⁻² M₂` for `R > 0`, where `M₂` bounds the second
derivative in the directions `v, w`.  Against the `LocallyDominatedEnstrophy`
majorant this makes the `Δχ_R` remainder `O(R⁻²)`. -/
theorem abs_fderiv_fderiv_scaled_le (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {v w : Space} {M₂ : ℝ}
    (hM₂ : ∀ y : Space, |fderiv ℝ (fun z => fderiv ℝ χ z v) y w| ≤ M₂)
    {R : ℝ} (hR : 0 < R) (x : Space) :
    |fderiv ℝ (fun z => fderiv ℝ (fun y => χ (R⁻¹ • y)) z v) x w| ≤
      R⁻¹ * R⁻¹ * M₂ := by
  rw [fderiv_fderiv_scaled_apply χ hχ R x v w, abs_mul, abs_mul, abs_inv,
    abs_of_pos hR]
  have hRnn : (0:ℝ) ≤ R⁻¹ := inv_nonneg.mpr hR.le
  calc R⁻¹ * (R⁻¹ * |fderiv ℝ (fun z => fderiv ℝ χ z v) (R⁻¹ • x) w|)
      ≤ R⁻¹ * (R⁻¹ * M₂) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hM₂ _) hRnn) hRnn
    _ = R⁻¹ * R⁻¹ * M₂ := by ring

/-!
## The `R → ∞` pointwise recovery
-/

/-- If the base cutoff equals `1` on the closed ball of radius `r > 0`, the
scaled family equals `1` at every fixed point for all sufficiently large
scales: `χ(x/R) = 1` once `R ≥ ‖x‖/r`. -/
theorem scaled_eventually_one (χ : Space → ℝ) {r : ℝ} (hr : 0 < r)
    (hone : ∀ y : Space, ‖y‖ ≤ r → χ y = 1) (x : Space) :
    ∀ᶠ R : ℝ in Filter.atTop, χ (R⁻¹ • x) = 1 := by
  filter_upwards [Filter.eventually_ge_atTop (max 1 (‖x‖ / r))] with R hR
  have hR1 : (1:ℝ) ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : (0:ℝ) < R := lt_of_lt_of_le one_pos hR1
  apply hone
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hRpos]
  have hxr : ‖x‖ / r ≤ R := le_trans (le_max_right _ _) hR
  have hx : ‖x‖ ≤ R * r := by
    have := mul_le_mul_of_nonneg_right hxr hr.le
    rwa [div_mul_cancel₀ _ hr.ne'] at this
  calc R⁻¹ * ‖x‖ ≤ R⁻¹ * (R * r) :=
        mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hRpos.le)
    _ = r := by field_simp

/-!
## The concrete family: a scaled `ContDiffBump`
-/

/-- The standard base bump on `Space`: `1` on the closed unit ball,
supported in the ball of radius `2`. -/
def standardBump : ContDiffBump (0 : Space) :=
  ⟨1, 2, one_pos, one_lt_two⟩

/-- The concrete scaled cutoff family `χ_R(x) = χ(x/R)`. -/
def scaledCutoff (R : ℝ) : Space → ℝ :=
  fun x => standardBump (R⁻¹ • x)

theorem scaledCutoff_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (scaledCutoff R) :=
  contDiff_scaled _ standardBump.contDiff R

theorem scaledCutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (scaledCutoff R) :=
  hasCompactSupport_scaled _ standardBump.hasCompactSupport hR

theorem scaledCutoff_nonneg (R : ℝ) (x : Space) : 0 ≤ scaledCutoff R x :=
  standardBump.nonneg

theorem scaledCutoff_le_one (R : ℝ) (x : Space) : scaledCutoff R x ≤ 1 :=
  standardBump.le_one

/-- Pointwise recovery: at every fixed point the concrete family equals `1`
for all sufficiently large scales. -/
theorem scaledCutoff_eventually_one (x : Space) :
    ∀ᶠ R : ℝ in Filter.atTop, scaledCutoff R x = 1 := by
  refine scaled_eventually_one _ one_pos (fun y hy => ?_) x
  exact standardBump.one_of_mem_closedBall
    (by simpa [Metric.mem_closedBall, dist_zero_right, standardBump] using hy)

end Navier.Analysis.ScaledCutoff
