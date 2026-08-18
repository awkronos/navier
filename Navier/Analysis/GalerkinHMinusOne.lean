import Navier.Analysis.GalerkinBasis

/-!
# Infrastructure toward the `∂ₜu_m ∈ L^{4/3}(0,T; H⁻¹)` bound

This file banks the analytic infrastructure for the uniform time-derivative
bound for the Galerkin ODE in the dual `H⁻¹` (more precisely `V'`) norm, and
the Simon (1987) time-translation equicontinuity that follows from it.  The
payoff theorem (`modalApprox_timeEquicontinuous_of_dualBound`, discharging the
`htime` residual of `GalerkinBasis.exists_galerkinModeData`) is NOT yet here:
what is certified here is the form-level Cauchy–Schwarz layer and the
measure-theoretic window-Hölder layer that the dual bound consumes.

## Why the `H⁻¹` form is necessary

The banked `modalApprox_timeEquicontinuous_of_uniformDerivative` requires a
uniform-in-`(m,t)` bound on the projected vector field
`‖-(ν • A_m c) + B_m c‖ ≤ K` in the coefficient Euclidean norm.  No such
bound exists for the genuine Galerkin ODE: the Stokes operator `A_m` has
operator norm growing with `m` (the Dirichlet form of the retained modes is
unbounded), so the vector field is *not* uniformly `L²`-bounded in time.  The
classical repair (Leray 1934 §19; Temam *NSE* III §3; Simon, Ann. Mat. Pura
Appl. 146 (1987)) is to measure the time derivative in the *dual* norm: with
`⟨F_m(c), a⟩` tested against the `H¹` seminorm `√⟨A_m a, a⟩`,

* the viscous part satisfies `|⟨ν A_m c, a⟩| ≤ ν √⟨A_m c, c⟩ · √⟨A_m a, a⟩`
  (Cauchy–Schwarz for the Dirichlet form), an `L²`-in-time density;
* the convection part satisfies
  `|⟨B_m(c), a⟩| ≤ C ‖c‖^{1/2} ⟨A_m c, c⟩^{3/4} √⟨A_m a, a⟩`
  (skew-symmetry, Hölder `(4,4,2)` and the 3D Ladyzhenskaya inequality), an
  `L^{4/3}`-in-time density.

Both densities are uniformly budgeted by the Galerkin energy estimates
(`‖c_m(t)‖² ≤ ‖c_m(0)‖²`, `2ν ∫₀^T ⟨A_m c_m, c_m⟩ ≤ ‖c_m(0)‖²`), and the
`L^{4/3}` dual bound yields `TimeEquicontinuous` with the explicit modulus
`δ ~ ε⁴`.  That final assembly (`modalApprox_timeEquicontinuous_of_dualBound`)
remains a NAMED RESIDUAL: it additionally needs the convection dual estimate
(a 3D Ladyzhenskaya input, not yet banked for the coefficient fields) and the
Simon modulus assembly.

## Contents

* `abs_inner_le_sqrt_mul_sqrt_of_symm_nonneg` — Cauchy–Schwarz for a symmetric
  positive continuous bilinear form `⟨A·, ·⟩` (discriminant method).
* `inner_sub_le_two_mul_of_symm_nonneg` — the `⟨A(x−y), x−y⟩ ≤ 2⟨Ax,x⟩ + 2⟨Ay,y⟩`
  consequence.
* `memLp_of_nonneg_integrable_rpow`, `integrableOn_Ioc_of_nonneg_rpow` —
  `L^p` membership / integrability plumbing for nonnegative densities.
* `integral_Ioc_le_window_rpow` — the window Hölder estimate
  `∫_w g ≤ |w|^{1/4} (∫₀^{T₁} g^{4/3})^{3/4}` for `w ⊆ (0, T₁]`.

## Axiom policy

Everything here is proved from the banked ODE/basis layer and mathlib; the
audit target is `{propext, Classical.choice, Quot.sound}` only.
-/

open Set MeasureTheory Filter

namespace Navier.Analysis.GalerkinHMinusOne

open Navier Navier.Analysis.LerayWeak Navier.Analysis.GalerkinBasis

section FormCauchySchwarz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Cauchy–Schwarz for a symmetric positive form.**  If `A` is a continuous
linear operator whose bilinear form `B(x, y) = ⟨A x, y⟩` is symmetric and
positive semidefinite, then `|B(x, y)| ≤ √(B(x,x)) √(B(y,y))`.  Proved by the
discriminant method: `0 ≤ B(x + t•y, x + t•y)` is a quadratic in `t` bounded
below by `0`.  This is the exact estimate the viscous dual bound consumes —
the Stokes form `⟨A_m a, b⟩ = ⟨curl (field a), curl (field b)⟩_{L²}` is a Gram
form, hence symmetric positive. -/
theorem abs_inner_le_sqrt_mul_sqrt_of_symm_nonneg (A : E →L[ℝ] E)
    (hA_symm : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (hA_pos : ∀ x : E, 0 ≤ inner ℝ (A x) x) (x y : E) :
    |inner ℝ (A x) y| ≤
      Real.sqrt (inner ℝ (A x) x) * Real.sqrt (inner ℝ (A y) y) := by
  set Bxx := inner ℝ (A x) x with hBxx
  set Byy := inner ℝ (A y) y with hByy
  set Bxy := inner ℝ (A x) y with hBxy
  have hsymm' : inner ℝ (A y) x = Bxy := by
    rw [hA_symm y x, real_inner_comm]
  have hquad : ∀ t : ℝ, 0 ≤ Bxx + 2 * t * Bxy + t ^ 2 * Byy := by
    intro t
    have h := hA_pos (x + t • y)
    rw [map_add, map_smul] at h
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      conj_trivial] at h
    rw [hsymm'] at h
    nlinarith [h, hBxx, hByy, hBxy]
  have hBxx_nn : 0 ≤ Bxx := hA_pos x
  have hByy_nn : 0 ≤ Byy := hA_pos y
  rcases eq_or_lt_of_le hByy_nn with hB0 | hB0
  · -- `Byy = 0`: the bound is linear in `t`, forcing `Bxy = 0`.
    have hr0 : Bxy = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have := hquad (-(Bxx + 1) / Bxy)
        have hcalc : Bxx + 2 * (-(Bxx + 1) / Bxy) * Bxy + (-(Bxx + 1) / Bxy) ^ 2 * Byy
            = -Bxx - 2 := by
          rw [← hB0]
          field_simp
          ring
        rw [hcalc] at this
        linarith
      · have := hquad (-(Bxx + 1) / Bxy)
        have hcalc : Bxx + 2 * (-(Bxx + 1) / Bxy) * Bxy + (-(Bxx + 1) / Bxy) ^ 2 * Byy
            = -Bxx - 2 := by
          rw [← hB0]
          field_simp
          ring
        rw [hcalc] at this
        linarith
    rw [hr0, abs_zero]
    positivity
  · -- `Byy > 0`: evaluate at the vertex `t = -Bxy / Byy`.
    have hsq : Bxy ^ 2 ≤ Bxx * Byy := by
      have h := hquad (-Bxy / Byy)
      have hcalc : Bxx + 2 * (-Bxy / Byy) * Bxy + (-Bxy / Byy) ^ 2 * Byy
          = Bxx - Bxy ^ 2 / Byy := by
        field_simp
        ring
      rw [hcalc] at h
      have := (div_le_iff₀ hB0).mp (by linarith : Bxy ^ 2 / Byy ≤ Bxx)
      linarith
    calc |Bxy| = Real.sqrt (Bxy ^ 2) := (Real.sqrt_sq_eq_abs Bxy).symm
      _ ≤ Real.sqrt (Bxx * Byy) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt Bxx * Real.sqrt Byy := Real.sqrt_mul hBxx_nn Byy

/-- **Difference bound for a symmetric positive form.**
`⟨A(x−y), x−y⟩ ≤ 2⟨Ax,x⟩ + 2⟨Ay,y⟩` — the quadratic expansion plus
Cauchy–Schwarz plus `2√(ab) ≤ a + b`.  Consumed when the time-displaced
difference `c(t+h) − c(t)` has its Dirichlet form budgeted by the enstrophy
integrals at the two endpoints. -/
theorem inner_sub_le_two_mul_of_symm_nonneg (A : E →L[ℝ] E)
    (hA_symm : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (hA_pos : ∀ x : E, 0 ≤ inner ℝ (A x) x) (x y : E) :
    inner ℝ (A (x - y)) (x - y) ≤
      2 * inner ℝ (A x) x + 2 * inner ℝ (A y) y := by
  set Bxx := inner ℝ (A x) x with hBxx
  set Byy := inner ℝ (A y) y with hByy
  set Bxy := inner ℝ (A x) y with hBxy
  have hsymm' : inner ℝ (A y) x = Bxy := by
    rw [hA_symm y x, real_inner_comm]
  have hexp : inner ℝ (A (x - y)) (x - y) = Bxx - 2 * Bxy + Byy := by
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsymm']
    ring
  have hBxx_nn : 0 ≤ Bxx := hA_pos x
  have hByy_nn : 0 ≤ Byy := hA_pos y
  have hcs := abs_inner_le_sqrt_mul_sqrt_of_symm_nonneg A hA_symm hA_pos x y
  have hab : 2 * (Real.sqrt Bxx * Real.sqrt Byy) ≤ Bxx + Byy := by
    have hsq : (√Bxx - √Byy) ^ 2 ≥ 0 := sq_nonneg _
    have h1 : (√Bxx) ^ 2 = Bxx := Real.sq_sqrt hBxx_nn
    have h2 : (√Byy) ^ 2 = Byy := Real.sq_sqrt hByy_nn
    have h3 : √Bxx * √Byy = √(Bxx * Byy) := (Real.sqrt_mul hBxx_nn Byy).symm
    nlinarith [Real.sqrt_nonneg (Bxx * Byy)]
  rw [hexp]
  linarith [abs_le.mp hcs]

end FormCauchySchwarz

section MeasurePlumbing

/-- **`L^p` membership from integrability of the `p`-th power (nonnegative
densities).**  For a nonnegative measurable `f : ℝ → ℝ`, integrability of
`f ^ p` on `s` gives `MemLp f p` on the restriction.  This is the small
bridge from the Bochner-integrable budget hypotheses to mathlib's Hölder
inequality, which is phrased with `MemLp`. -/
theorem memLp_of_nonneg_integrable_rpow {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p) {s : Set ℝ}
    (hf_int : IntegrableOn (fun x => f x ^ p) s volume) :
    MemLp f (ENNReal.ofReal p) (volume.restrict s) := by
  refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top]
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  rw [htoReal]
  have hintegrand : ∀ x : ℝ, ‖f x‖ₑ ^ p = ENNReal.ofReal (f x ^ p) := by
    intro x
    rw [Real.enorm_eq_ofReal (hf_nonneg x),
      ← ENNReal.ofReal_rpow_of_nonneg (hf_nonneg x) hp.le]
  rw [lintegral_congr hintegrand, ← ofReal_integral_eq_lintegral_ofReal
    hf_int (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hf_nonneg x) p)]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top

/-- **Integrability from integrability of a higher power (nonnegative
densities, finite window).**  If `0 ≤ f` and `f ^ p` is integrable on
`(0, T]` with `p ≥ 1`, then `f` is integrable there: pointwise
`f ≤ 1 + f ^ p`. -/
theorem integrableOn_Ioc_of_nonneg_rpow {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 ≤ p) {T : ℝ}
    (hf_int : IntegrableOn (fun x => f x ^ p) (Set.Ioc 0 T) volume) :
    IntegrableOn f (Set.Ioc 0 T) volume := by
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 T) volume :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hle : ∀ x : ℝ, ‖f x‖ ≤ 1 + f x ^ p := by
    intro x
    rw [Real.norm_of_nonneg (hf_nonneg x)]
    rcases le_total (f x) 1 with hle1 | hge1
    · exact hle1.trans (le_add_of_nonneg_right (Real.rpow_nonneg (hf_nonneg x) p))
    · calc f x = f x ^ (1 : ℝ) := (Real.rpow_one (f x)).symm
        _ ≤ f x ^ p := Real.rpow_le_rpow_of_exponent_le hge1 hp
        _ ≤ 1 + f x ^ p := le_add_of_nonneg_left zero_le_one
  have hsum : IntegrableOn (fun x : ℝ => 1 + f x ^ p) (Set.Ioc 0 T) volume :=
    h1.add hf_int
  exact hsum.mono' hf_meas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hle x)

/-- **The window Hölder estimate.**  For a nonnegative measurable density `g`
with `g^{4/3}` integrable on `(0, T₁]`, and any sub-window `(a, b] ⊆ (0, T₁]`,
`∫_a^b g ≤ (b − a)^{1/4} (∫₀^{T₁} g^{4/3})^{3/4}`.  This is the
`L^{4/3}`–`L⁴` Hölder pairing of `g` with the window's indicator, followed by
monotonicity in the window.  It is the entire content of "`L^{4/3}` time
regularity gives a `|h|^{1/4}` modulus on time translates". -/
theorem integral_Ioc_le_window_rpow {g : ℝ → ℝ} (hg_meas : Measurable g)
    (hg_nonneg : ∀ t, 0 ≤ g t) {T₁ : ℝ}
    (hg_int : IntegrableOn (fun t => g t ^ (4 / 3 : ℝ)) (Set.Ioc 0 T₁) volume)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T₁) :
    ∫ t in Set.Ioc a b, g t ≤
      (b - a) ^ (1 / 4 : ℝ) *
        (∫ t in Set.Ioc 0 T₁, g t ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
  have hsub : Set.Ioc a b ⊆ Set.Ioc 0 T₁ := Set.Ioc_subset_Ioc ha hb
  have hg_int_w : IntegrableOn (fun t => g t ^ (4 / 3 : ℝ)) (Set.Ioc a b) volume :=
    hg_int.mono hsub le_rfl
  have hconj : (4 / 3 : ℝ).HolderConjugate 4 := by
    have h := Real.HolderConjugate.conjExponent (show (1 : ℝ) < 4 / 3 by norm_num)
    rwa [show Real.conjExponent (4 / 3 : ℝ) = 4 by norm_num [Real.conjExponent]] at h
  have hg_Lp : MemLp g (ENNReal.ofReal (4 / 3)) (volume.restrict (Set.Ioc a b)) :=
    memLp_of_nonneg_integrable_rpow hg_meas hg_nonneg (by norm_num) hg_int_w
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have h1_Lp : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 4)
      (volume.restrict (Set.Ioc a b)) := memLp_const 1
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (μ := volume.restrict (Set.Ioc a b))
    (f := g) (g := fun _ : ℝ => (1 : ℝ))
    (Filter.Eventually.of_forall fun x => hg_nonneg x)
    (Filter.Eventually.of_forall fun _ => zero_le_one) hg_Lp h1_Lp
  have hwindow43 : (∫ t in Set.Ioc a b, g t ^ (4 / 3 : ℝ)) ≤
      ∫ t in Set.Ioc 0 T₁, g t ^ (4 / 3 : ℝ) :=
    setIntegral_mono_set hg_int
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hg_nonneg x) _)
      (Filter.Eventually.of_forall fun _ hx => hsub hx)
  have hbase_nn : 0 ≤ ∫ t in Set.Ioc 0 T₁, g t ^ (4 / 3 : ℝ) :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hg_nonneg x) _)
  have hmeas : (volume.restrict (Set.Ioc a b)).real Set.univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  calc ∫ t in Set.Ioc a b, g t
      = ∫ t in Set.Ioc a b, g t * 1 := by simp
    _ ≤ (∫ t in Set.Ioc a b, g t ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3) : ℝ) *
          (∫ t in Set.Ioc a b, (1 : ℝ) ^ 4) ^ (1 / 4 : ℝ) := hHolder
    _ = (∫ t in Set.Ioc a b, g t ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) * (b - a) ^ (1 / 4 : ℝ) := by
        rw [show (1 / (4 / 3) : ℝ) = 3 / 4 by norm_num]
        congr 1
        simp [hmeas]
    _ ≤ (∫ t in Set.Ioc 0 T₁, g t ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) * (b - a) ^ (1 / 4 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
        exact Real.rpow_le_rpow
          (integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hg_nonneg x) _))
          hwindow43 (by norm_num)
    _ = (b - a) ^ (1 / 4 : ℝ) * (∫ t in Set.Ioc 0 T₁, g t ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) :=
        mul_comm _ _

end MeasurePlumbing
