import Navier.EnergyObstruction
import Navier.Scaling

/-!
# The mixed-norm exponent theorem for the parabolic rescaling

Two modules each carry one half of the same missing step, and both name it.

* `Navier.Scaling` defines the algebraic homogeneity exponent
  `mixedNormExponent p q = 1 - 3/p - 2/q` and the Serrin critical line, and
  states that the file asserts no analytic norm statement — that no Bochner,
  Lorentz, weak, endpoint or mixed Lebesgue norm is shown there to scale by
  this exponent, that separate measure-theoretic work being required.
* `Navier.EnergyObstruction` supplies the two layers separately — the spatial
  `lp_dilation_scaling` (factor `c ^ (p - 3)`) and the scalar
  `time_dilation_scaling` (factor `a⁻¹`) — and records of the second that it
  leaves the outer `L^q` norm undefined, does not connect `h` to a spatial
  `L^p` norm, and does not compose the two layers.

This module performs those steps.  For the Navier--Stokes parabolic rescaling

```
u_λ(t, x) = λ · u(λ² t, λ x)
```

of a velocity evolution on `ℝ × ℝ³`, the mixed `L^q_t L^x^p` `q`-power integral
scales by exactly `λ ^ (q * mixedNormExponent p q)`
(`mixedNormPowerIntegral_parabolicRescale`), and the `q`-rooted mixed norm by
exactly `λ ^ mixedNormExponent p q` (`mixedNorm_parabolicRescale`).  That is the
analytic statement the arithmetic file declined to assert: the exponent it
defined is now the measured homogeneity degree of a real mixed norm, not a
scalar guess.

Three consequences are proved here, and each is a sharpness claim about which
a-priori bounds can ever be scale-coercive:

* the Ladyzhenskaya--Prodi--Serrin critical line `3/p + 2/q = 1` is **exactly**
  the set of finite exponent pairs whose mixed norm is invariant under the
  rescaling (`mixedNorm_parabolicRescale_of_criticalLine`, with the canonical
  Serrin pair `(6,4)` as `mixedNorm_parabolicRescale_six_four`);
* strictly above the line (supercritical, `mixedNormExponent p q < 0`) focusing
  drives the mixed norm down, and strictly below it (subcritical) focusing drives
  the norm up (`mixedNorm_parabolicRescale_lt_of_negExponent`,
  `lt_mixedNorm_parabolicRescale_of_posExponent`);
* a supercritical mixed norm controls no critical-or-subcritical one: for every
  `ε > 0` there is a rescaling whose supercritical mixed norm is below `ε` while
  its critical-or-subcritical mixed norm has not shrunk at all
  (`exists_mixedNorm_lt_and_not_shrunk`).  This is the exponent-family form of
  `EnergyObstruction.energy_not_scale_coercive`, whose `(p,q) = (2,·)`/`(3,·)`
  spatial slices are exactly the `p = 2` and `p = 3` special cases of the layer
  composed here.

Naming.  The Navier--Stokes rescaling of a velocity field already has a name in
the analysis cone, `Navier.Analysis.Covariance.parabolicScaledVelocity`, which
spells the time homothety as `λ ^ 2 * t` with a natural-number power.  This file
serves the same map with the real power `λ ^ (2 : ℝ) • t`, because the two
layers compose in one `Real.rpow` exponent arithmetic; the spellings are proved
identical pointwise by `timeHomothety_eq_parabolic` below, so a consumer in the
analysis cone can transfer any statement here to the standard name in one
congruence step.  This module deliberately imports only the two parents it
composes (`Navier.Problem` reaches it through both), so that it stays in the
leaf cone where `Navier.EnergyObstruction` lives.

Scope.  Nothing in this file asserts existence, uniqueness, smoothness or
regularity of any Navier--Stokes solution, and no hypothesis of the Fefferman
alternatives A--D is consumed, restated or weakened: these are
change-of-variables identities for the integrals themselves, in the sense of
`docs/FALSIFICATION_LEDGER.md` entry `F-001`.  The identities are equalities of
Bochner integrals, so on a datum whose slice-norm profile is not
`volume`-measurable both sides read the junk value `0` and the equality still
holds; the content is for measurable fields, and the coercion corollaries are
non-degenerate exactly when the norms involved are strictly positive — the same
vacuity discipline `Analysis.ConditionalRegularity` records for the
interval-integral encoding of the Serrin bracket
(`serrinMixedNorm_vacuous_of_nonIntegrableTime`).  The whole-time-line integrals
used here are also not the finite-horizon Serrin quantity
`∫ s in (0)..T'`: no transport between the two encodings is claimed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.MixedNormScaling
open Navier

/-! ## The rescaling and the two-layer quantity -/

/-- The Navier--Stokes parabolic rescaling of a velocity evolution,
`u_λ(t, x) = λ · u(λ² t, λ x)`, the spacetime continuation of the spatial slice
`u_c(x) = c · u(c · x)` of `Navier.EnergyObstruction`.  No solution property is
assumed of `u`: this is a map on all of `VelocityEvolution`.  The time
homothety `λ²` is written as a real power so that the spatial and temporal
layers compose in one exponent arithmetic (`Real.rpow_add`). -/
def parabolicRescale (lambda : ℝ) (u : VelocityEvolution) : VelocityEvolution :=
  fun t x => lambda • u (lambda ^ (2 : ℝ) • t) (lambda • x)

/-- **The two spellings of the parabolic time homothety agree.**  For every
`λ : ℝ`, `fun t => λ ^ (2 : ℝ) • t` is `fun t => λ ^ 2 * t`, the spelling used by
`Navier.Analysis.Covariance.parabolicScaledVelocity`.  No positivity hypothesis
is needed: `Real.rpow_two` holds unconditionally.  Consequently
`parabolicRescale λ u` and `parabolicScaledVelocity λ u` are the same function
of `(t, x)`, and the rescaling whose norm is computed here is the one the CKN
and continuation-scaling files already move solutions by. -/
theorem timeHomothety_eq_parabolic (lambda : ℝ) :
    (fun t : ℝ => lambda ^ (2 : ℝ) • t) = (fun t : ℝ => lambda ^ 2 * t) := by
  funext t
  simp only [Real.rpow_two, pow_two, smul_eq_mul]

/-- Pointwise form of `timeHomothety_eq_parabolic` at the level of the rescaled
evolution: a `parabolicRescale` application reads with the analysis cone's
`λ ^ 2 * t` spelling. -/
theorem parabolicRescale_apply_eq (lambda : ℝ) (u : VelocityEvolution) (t : ℝ) (x : Space) :
    parabolicRescale lambda u t x = lambda • u (lambda ^ 2 * t) (lambda • x) :=
  congrArg (fun s : ℝ => lambda • u s (lambda • x))
    (congrFun (timeHomothety_eq_parabolic lambda) t)

/-- The mixed-norm `q`-power integral of a velocity evolution: the spatial
`L^p`-power integral of each time slice, raised to `q/p`, integrated in time.
This is the `q`-th power of the mixed norm below, written without any `L^p`
space or Bochner-space construction, so it is defined for every function. -/
noncomputable def mixedNormPowerIntegral (u : VelocityEvolution) (p q : ℝ) : ℝ :=
  ∫ t : ℝ, (∫ x : Space, ‖u t x‖ ^ p ∂volume) ^ (q / p) ∂volume

/-- The spatial-`L^p` temporal-`L^q` mixed norm of a velocity evolution, as the
`q`-th root of `mixedNormPowerIntegral`.  For `0 < p` and `0 < q` this is the
quantity the Ladyzhenskaya--Prodi--Serrin hypothesis `u ∈ L^q_t L^p_x` measures;
no local-in-time weight, no horizon truncation, and no `L^∞` endpoint is
asserted here. -/
noncomputable def mixedNorm (u : VelocityEvolution) (p q : ℝ) : ℝ :=
  mixedNormPowerIntegral u p q ^ (1 / q)

/-- The `q`-power integral is nonnegative: each slice integral is, being an
integral of a nonnegative function, and so is its real power.  Neither layer
needs a measurability hypothesis, because `MeasureTheory.integral_nonneg` holds
for the Bochner integral as defined (a non-measurable integrand gives `0`). -/
theorem mixedNormPowerIntegral_nonneg (u : VelocityEvolution) (p q : ℝ) :
    0 ≤ mixedNormPowerIntegral u p q :=
  integral_nonneg fun _ =>
    Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) p) _

/-- The mixed norm is nonnegative. -/
theorem mixedNorm_nonneg (u : VelocityEvolution) (p q : ℝ) :
    0 ≤ mixedNorm u p q :=
  Real.rpow_nonneg (mixedNormPowerIntegral_nonneg u p q) _

/-! ## The two layers, composed -/

/-- The spatial layer, applied slice by slice to the parabolic rescaling: the
inner `L^p`-power integral of `u_λ(t, ·)` is `λ ^ (p - 3)` times that of
`u(λ² t, ·)`.  This is `Navier.EnergyObstruction.lp_dilation_scaling` read at the
time `λ² t` rather than at `t`. -/
theorem inner_spatialLayer (lambda : ℝ) (hLambda : 0 < lambda) (p : ℝ)
    (u : VelocityEvolution) (t : ℝ) :
    (∫ x : Space, ‖parabolicRescale lambda u t x‖ ^ p ∂volume)
      = lambda ^ (p - 3) • ∫ x : Space, ‖u (lambda ^ (2 : ℝ) • t) x‖ ^ p ∂volume := by
  simp only [parabolicRescale]
  exact Navier.EnergyObstruction.lp_dilation_scaling lambda p hLambda
    (u (lambda ^ (2 : ℝ) • t))

/-- **The composed two-layer dilation.** One time slice of the rescaling
contributes the spatial factor `λ ^ (p - 3)`, and raising the slice quantity to
`q/p` turns it into `λ ^ ((p - 3) · q/p)`.  This is the step
`Navier.EnergyObstruction.time_dilation_scaling` declines to take: the arbitrary
observable there is here the spatial `L^p`-power integral of the same field. -/
theorem slice_dilation (lambda : ℝ) (hLambda : 0 < lambda) (p q : ℝ)
    (u : VelocityEvolution) (t : ℝ) :
    (∫ x : Space, ‖parabolicRescale lambda u t x‖ ^ p ∂volume) ^ (q / p)
      = lambda ^ ((p - 3) * (q / p)) •
        (∫ x : Space, ‖u (lambda ^ (2 : ℝ) • t) x‖ ^ p ∂volume) ^ (q / p) := by
  rw [inner_spatialLayer lambda hLambda p u t]
  have hb : 0 ≤ ∫ x : Space, ‖u (lambda ^ (2 : ℝ) • t) x‖ ^ p ∂volume := by positivity
  rw [show lambda ^ (p - 3) • _ = lambda ^ (p - 3) * _ from rfl,
    Real.mul_rpow (by positivity) hb, ← smul_eq_mul,
    Real.rpow_mul (le_of_lt hLambda)]

/-- **The mixed-norm exponent theorem, `q`-power form.** The mixed `q`-power
integral of `u_λ` is `λ ^ (q * Scaling.mixedNormExponent p q)` times that of `u`:
the spatial factor `λ ^ (p - 3)` raised to `q/p`, and the temporal factor
`(λ²)⁻¹ = λ ^ (-2)`, multiply to `λ ^ (q · (1 - 3/p - 2/q))`. -/
theorem mixedNormPowerIntegral_parabolicRescale (lambda : ℝ) (hLambda : 0 < lambda)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (u : VelocityEvolution) :
    mixedNormPowerIntegral (parabolicRescale lambda u) p q
      = lambda ^ (q * Scaling.mixedNormExponent p q) •
        mixedNormPowerIntegral u p q := by
  have hexp : (p - 3) * (q / p) + (-(2 : ℝ)) = q * Scaling.mixedNormExponent p q := by
    rw [Scaling.mixedNormExponent]
    field_simp [hp.ne', hq.ne']
    ring
  have htime :
      (∫ t : ℝ, (∫ x : Space, ‖u (lambda ^ (2 : ℝ) • t) x‖ ^ p ∂volume) ^ (q / p) ∂volume)
        = (lambda ^ (2 : ℝ))⁻¹ •
          ∫ t : ℝ, (∫ x : Space, ‖u t x‖ ^ p ∂volume) ^ (q / p) ∂volume := by
    simpa using Navier.EnergyObstruction.time_dilation_scaling (lambda ^ (2 : ℝ))
      (by positivity) (fun s : ℝ => (∫ x : Space, ‖u s x‖ ^ p ∂volume) ^ (q / p))
  calc mixedNormPowerIntegral (parabolicRescale lambda u) p q
      = ∫ t : ℝ, lambda ^ ((p - 3) * (q / p)) •
          (∫ x : Space, ‖u (lambda ^ (2 : ℝ) • t) x‖ ^ p ∂volume) ^ (q / p) ∂volume := by
          simp only [mixedNormPowerIntegral, slice_dilation lambda hLambda p q u]
    _ = lambda ^ ((p - 3) * (q / p)) •
        ∫ t : ℝ, (∫ x : Space, ‖u (lambda ^ (2 : ℝ) • t) x‖ ^ p ∂volume) ^ (q / p) ∂volume := by
          rw [integral_smul]
    _ = lambda ^ ((p - 3) * (q / p)) • (lambda ^ (2 : ℝ))⁻¹ •
        ∫ t : ℝ, (∫ x : Space, ‖u t x‖ ^ p ∂volume) ^ (q / p) ∂volume := by rw [htime]
    _ = lambda ^ (q * Scaling.mixedNormExponent p q) •
        ∫ t : ℝ, (∫ x : Space, ‖u t x‖ ^ p ∂volume) ^ (q / p) ∂volume := by
          rw [smul_smul, ← Real.rpow_neg (le_of_lt hLambda) (2 : ℝ),
            ← Real.rpow_add hLambda, hexp]
    _ = lambda ^ (q * Scaling.mixedNormExponent p q) • mixedNormPowerIntegral u p q := by
          simp only [mixedNormPowerIntegral]

/-- **The mixed-norm exponent theorem.** For `0 < p` and `0 < q`, the mixed
`L^q_t L^p_x` norm of the parabolic rescaling is exactly
`λ ^ Scaling.mixedNormExponent p q` times the original: the exponent that
`Navier.Scaling` defined arithmetically is the analytic homogeneity degree of
the norm. -/
theorem mixedNorm_parabolicRescale (lambda : ℝ) (hLambda : 0 < lambda)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (u : VelocityEvolution) :
    mixedNorm (parabolicRescale lambda u) p q
      = lambda ^ Scaling.mixedNormExponent p q * mixedNorm u p q := by
  have he : (q * Scaling.mixedNormExponent p q) * (1 / q) =
      Scaling.mixedNormExponent p q := by
    field_simp [hq.ne']
  rw [mixedNorm, mixedNormPowerIntegral_parabolicRescale lambda hLambda p q hp hq u,
    smul_eq_mul,
    Real.mul_rpow (by positivity) (mixedNormPowerIntegral_nonneg u p q),
    ← Real.rpow_mul (le_of_lt hLambda), he, mixedNorm]

/-! ## What the exponent is good for -/

/-- **Criticality is exactly scale invariance.** On the Serrin critical line
`3/p + 2/q = 1` the mixed norm of the parabolic rescaling equals the original,
for every positive `λ`; conversely the exponent vanishes only there
(`Scaling.mixedNormExponent_eq_zero_iff`).  This is the analytic content of the
critical line that `Navier.Scaling` could only state as field arithmetic. -/
theorem mixedNorm_parabolicRescale_of_criticalLine (lambda : ℝ) (hLambda : 0 < lambda)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hLine : Scaling.CriticalLine p q)
    (u : VelocityEvolution) :
    mixedNorm (parabolicRescale lambda u) p q = mixedNorm u p q := by
  rw [mixedNorm_parabolicRescale lambda hLambda p q hp hq u,
    (Scaling.mixedNormExponent_eq_zero_iff p q).mpr hLine, Real.rpow_zero, one_mul]

/-- The canonical finite Serrin pair `(p, q) = (6, 4)`: its mixed norm is
invariant under the full parabolic rescaling. -/
theorem mixedNorm_parabolicRescale_six_four (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) :
    mixedNorm (parabolicRescale lambda u) 6 4 = mixedNorm u 6 4 :=
  mixedNorm_parabolicRescale_of_criticalLine lambda hLambda 6 4 (by norm_num)
    (by norm_num) Scaling.criticalLine_six_four u

/-- **Supercritical quantities shrink under focusing.** If
`Scaling.mixedNormExponent p q < 0` (strictly supercritical: the energy-side of
the Serrin line) and the mixed norm is positive, then every rescaling with
`λ > 1` strictly decreases it. -/
theorem mixedNorm_parabolicRescale_lt_of_negExponent (lambda : ℝ) (hLambda : 1 < lambda)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (u : VelocityEvolution)
    (hγ : Scaling.mixedNormExponent p q < 0) (hu : 0 < mixedNorm u p q) :
    mixedNorm (parabolicRescale lambda u) p q < mixedNorm u p q := by
  rw [mixedNorm_parabolicRescale lambda (by linarith) p q hp hq u]
  have hrpow : lambda ^ Scaling.mixedNormExponent p q < 1 := by
    rw [← Real.rpow_zero lambda]
    exact Real.rpow_lt_rpow_of_exponent_lt (by linarith) hγ
  have := mul_lt_mul_of_pos_right hrpow hu
  rwa [one_mul] at this

/-- **Subcritical quantities grow under focusing.** If
`Scaling.mixedNormExponent p q > 0` (strictly subcritical) and the mixed norm is
positive, then every rescaling with `λ > 1` strictly increases it.  Together
with the supercritical case this is the trichotomy the exponent induces on the
a-priori quantity, and it is the direction in which no subcritical bound can
control a supercritical one. -/
theorem lt_mixedNorm_parabolicRescale_of_posExponent (lambda : ℝ) (hLambda : 1 < lambda)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (u : VelocityEvolution)
    (hγ : 0 < Scaling.mixedNormExponent p q) (hu : 0 < mixedNorm u p q) :
    mixedNorm u p q < mixedNorm (parabolicRescale lambda u) p q := by
  rw [mixedNorm_parabolicRescale lambda (by linarith) p q hp hq u]
  have hrpow : 1 < lambda ^ Scaling.mixedNormExponent p q := by
    rw [← Real.rpow_zero lambda]
    exact Real.rpow_lt_rpow_of_exponent_lt (by linarith) hγ
  have := mul_lt_mul_of_pos_right hrpow hu
  rwa [one_mul] at this

/-! ## Real-power plumbing

The exponent arithmetic below runs through `Real.rpow`, so the two directions of
negating an exponent are stated once here rather than re-derived per use site.
Mathlib's `Real.rpow_neg` reads `x ^ (-y) = (x ^ y)⁻¹`; the corollaries needed
for a *fixed negative* exponent are the inverted-base form and its strict
monotonicity, which this Mathlib revision does not supply under a single name. -/

/-- `x ^ y = (x ^ (-y))⁻¹` for positive `x`: the same power read through
negating the exponent twice. -/
private lemma rpow_neg_inv (x : ℝ) (hx : 0 < x) (y : ℝ) : x ^ y = (x ^ (-y))⁻¹ := by
  have h : x ^ (- -y) = (x ^ (-y))⁻¹ := Real.rpow_neg (le_of_lt hx) (-y)
  rwa [neg_neg] at h

/-- A fixed strictly negative real power is strictly decreasing on the positive
reals: this is `Real.rpow_lt_rpow` at the negated exponent, read back through
`rpow_neg_inv`.  The final step inverts the two powers; this Mathlib revision
has no `inv_lt_inv` for the real line, so the inversion is cleared by
`field_simp`, which reduces it to the already-proved comparison at `-γ`. -/
private lemma rpow_lt_rpow_of_neg {x y γ : ℝ} (hx : 0 < x) (hxy : x < y) (hγ : γ < 0) :
    y ^ γ < x ^ γ := by
  have hn : 0 < -γ := by linarith
  have hpos : 0 < y := by linarith
  have hA : x ^ (-γ) < y ^ (-γ) := Real.rpow_lt_rpow (le_of_lt hx) hxy hn
  have hxA : 0 < x ^ (-γ) := Real.rpow_pos_of_pos hx (-γ)
  have hyA : 0 < y ^ (-γ) := Real.rpow_pos_of_pos hpos (-γ)
  rw [rpow_neg_inv y hpos γ, rpow_neg_inv x hx γ]
  field_simp
  linarith

/-- **A supercritical mixed norm can be driven below any budget by a rescaling
that does not move the datum off the positive cone.** For `0 < p`, `0 < q` and
`Scaling.mixedNormExponent p q < 0`, and every `ε > 0`, there is a rescaling
factor `λ ≥ 1` with `mixedNorm u_λ p q < ε`.  No positivity hypothesis on `u` is
needed: the degenerate `mixedNorm u p q = 0` case is served by `λ = 1`, and the
content is the strictly positive datum, which the rescaling flattens. -/
theorem exists_ge_one_and_mixedNorm_lt (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hγ : Scaling.mixedNormExponent p q < 0) (u : VelocityEvolution)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ lambda : ℝ, 1 ≤ lambda ∧ mixedNorm (parabolicRescale lambda u) p q < ε := by
  set γ := Scaling.mixedNormExponent p q with hγd
  set C := mixedNorm u p q with hCd
  have hγ0 : γ ≠ 0 := ne_of_lt hγ
  have hC0 : 0 ≤ C := mixedNorm_nonneg u p q
  set a := ((C + 1) / ε) ^ (1 / -γ) with had
  have ha0 : (0 : ℝ) < a :=
    Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (C + 1) / ε) (1 / -γ)
  have hag : a ^ γ = ε / (C + 1) := by
    rw [had, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (C + 1) / ε),
      show (1 / -γ) * γ = -1 by field_simp [hγ0], Real.rpow_neg_one]
    field_simp [hε.ne']
  refine ⟨a + 1, by linarith, ?_⟩
  rw [mixedNorm_parabolicRescale (a + 1) (by linarith) p q hp hq u, ← hγd, ← hCd]
  have hdec : (a + 1) ^ γ < ε / (C + 1) :=
    lt_of_lt_of_eq (rpow_lt_rpow_of_neg ha0 (by linarith) hγ) hag
  by_cases hCz : C = 0
  · rw [hCz, mul_zero]
    exact hε
  · have hCp : 0 < C := lt_of_le_of_ne hC0 fun h => hCz h.symm
    have hb : 0 < C + 1 := by positivity
    calc (a + 1) ^ γ * C < ε / (C + 1) * C := mul_lt_mul_of_pos_right hdec hCp
      _ = ε * C / (C + 1) := by field_simp
      _ < ε := by
        rw [div_lt_iff₀ hb]
        nlinarith

/-- **No supercritical mixed norm controls a critical or subcritical one.** Let
`0 < p, q` be strictly supercritical (`mixedNormExponent p q < 0`) and
`0 < p₀, q₀` critical-or-subcritical (`mixedNormExponent p₀ q₀ ≥ 0`).  Then for
every `ε > 0` some parabolic rescaling drives the `(p,q)` mixed norm below `ε`
while the `(p₀,q₀)` mixed norm does not decrease at all.  In particular no
bound of the form `mixedNorm u p₀ q₀ ≤ Φ (mixedNorm u p q)` with
`Φ(y) → 0` as `y → 0⁺` can hold on any class of data closed under the parabolic
rescaling: the critical quantity is blind to the supercritical one at small
scales.

This is the exponent-family sharpening of
`Navier.EnergyObstruction.energy_not_scale_coercive`, which is the same argument
in the two spatial slices `p = 2` (energy, supercritical) and `p = 3`
(critical) at a fixed time.  It constrains exactly the routes that try to read
regularity off a supercritical integral; it says nothing about the endpoints
A--D, and consumes no hypothesis of them. -/
theorem exists_mixedNorm_lt_and_not_shrunk
    (p q p₀ q₀ : ℝ) (hp : 0 < p) (hq : 0 < q) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hsup : Scaling.mixedNormExponent p q < 0)
    (hcrit : 0 ≤ Scaling.mixedNormExponent p₀ q₀) (u : VelocityEvolution) :
    ∀ ε > 0, ∃ lambda : ℝ, 0 < lambda
      ∧ mixedNorm (parabolicRescale lambda u) p q < ε
      ∧ mixedNorm u p₀ q₀ ≤ mixedNorm (parabolicRescale lambda u) p₀ q₀ := by
  intro ε hε
  obtain ⟨lambda, hlambda, hlt⟩ := exists_ge_one_and_mixedNorm_lt p q hp hq hsup u ε hε
  refine ⟨lambda, by linarith, hlt, ?_⟩
  rw [mixedNorm_parabolicRescale lambda (by linarith) p₀ q₀ hp₀ hq₀ u]
  have h1 : 1 ≤ lambda ^ Scaling.mixedNormExponent p₀ q₀ := by
    rw [← Real.rpow_zero lambda]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hcrit
  have := mul_le_mul_of_nonneg_right h1 (mixedNorm_nonneg u p₀ q₀)
  rwa [one_mul] at this

end Navier.MixedNormScaling
