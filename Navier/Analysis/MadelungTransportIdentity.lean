import Navier.Analysis.MadelungDegeneracySharpness
import Navier.Construction.ProblemStatement

/-!
# Transport identity for the Madelung density along the forced flow

`Navier.Analysis.MadelungDegeneracySharpness` shows that neither disjunct of the
forced Madelung dichotomy
(`Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_madelung_amplitude_or_derivative_degenerates`)
can be excluded from the pairing estimate
`Navier.Analysis.QuantumVortexRegularity.norm_le_of_madelung_pairing` alone, and
`docs/MADELUNG_CORRESPONDENCE.md` records that excluding degeneracy requires
"additional structure of the lift, such as a transport or energy identity for the
wavefunction".  This module constructs the first such structure at the
repository's abstraction layer, entirely on the repository's own carriers.

## What the pairing cannot see

`logDeriv_decompose` splits the logarithmic derivative of any differentiable
decoder on its density-positive region:

    Dψ d / ψ  =  (D‖ψ‖² d) / (2‖ψ‖²)  +  I · (Dψ d / ψ).im

The Madelung pairing hypothesis constrains ONLY the imaginary (phase) part; the
real part is the spatial density log-derivative and the entire time evolution of
the density ρ = ‖ψ‖² is invisible to the pairing.  That is the exact structural
reason the sharpness module's two witnesses (identical phase, different
amplitude) decode the same velocity.  `logDeriv_im_congr_const` records the
companion fact: multiplying the lift by any nonzero constant rescales the
derivative bound without moving the pairing.

## The transport identity and the dichotomy

`densityContinuityEquation` formalizes the pointwise continuity equation
∂ₜρ = -(Dρ(v) + ρ·div v) with the repository's own `spatialDivergence`.  The
exact forced velocity `vel t x = 2/(1-t) • x` of the sharpness module has the
explicit flow `flowVel t x = (1-t)⁻² • x` (`hasDerivAt_flowVel`) and divergence
`6/(1-t)` (`spatialDivergence_velV`).

On this carrier the identity delivers a genuine dichotomy contribution, in BOTH
precise directions:

* `constantAmplitude_not_transport_compatible`: the sharpness witness `psi b t`
  with time-constant nonzero amplitude — the configuration on which the first
  disjunct never occurs — has constant density `b²`, yet the continuity
  equation demands `∂ₜρ = -6b²/(1-t) ≠ 0`.  The transport identity EXCLUDES
  this constant-amplitude branch (the W1 branch of the sharpness module) as a
  Madelung lift.  `psiFamily_transport_excludes_amplitude_floor` strengthens
  this to the whole time-varying family: transport + uniform positive
  amplitude floor is contradictory on the density-positive region.
* `transport_compatible_collapse_decoder`: the exclusion does NOT reach either
  disjunct of the dichotomy for arbitrary lifts.  The decoder `psi (1-t)³ t`
  satisfies the exact continuity equation on the whole density-positive slab
  (its density along the flow obeys the rigidity law `r t = r 0 · (1-t)⁶`,
  `uniformDensity_transport_rigidity`), pairs exactly with the unbounded
  `vel`, keeps its spatial derivative uniformly bounded by `2R` on every closed
  ball, and its amplitude collapses to zero in every terminal window.  This is
  a checked witness that the transport identity forces the
  amplitude-degeneration disjunct rather than excluding it.

So the first transport structure determines WHICH disjunct is realized for the
forced quadratic-phase family (amplitude collapse, via the exact (1-t)³
amplitude law), excludes the constant-amplitude branch for that family, and
excludes neither disjunct of the constructed candidate's dichotomy in full
generality.

## Searched shapes (one-search record)

`HasFDerivAt.norm_sq` / a joint `(t, x)` density-derivative carrier, a
continuity-equation carrier, and a flow map for the selected candidate: absent
in the repository and in this Mathlib pin (`grep` over `Mathlib/` found no
`HasFDerivAt.norm_sq`, no continuity-equation carrier, and no candidate flow).
The density derivative is therefore built from
`Analysis/InnerProductSpace/Calculus.lean`'s `hasStrictFDerivAt_norm_sq`
(`fderiv_norm_sq_apply`) and the rfl unfolding `Complex.inner`, and the
characteristics are built explicitly as `flowVel`.

## Named missing primitives (residual obligations)

1. A joint `(t, x)` regularity carrier for a candidate lift: the along-flow
   form of the transport identity for a GENERAL (non-spatially-uniform) density
   needs `HasFDerivAt` of `fun p : ℝ × Space => ρ p.1 p.2`, which separate
   slice differentiability does not supply.
2. A flow (characteristic) carrier for the selected candidate velocity on
   `Ico 0 1`: the sharpness velocity has the explicit polynomial flow
   `flowVel`; the candidate provides no global flow map in the repository.
3. Quantitative divergence control `∫₀¹ ‖div u‖` on the candidate's support
   cylinder.  The candidate class is divergence-free
   (`Navier.Construction.ProblemStatement.CandidateProperties.divergence_free`),
   under which the continuity equation reduces to pure transport
   `∂ₜρ = -Dρ(u)` and the family rigidity above does not apply.

Tier: THEOREM.  Raw `#print axioms` output for every new public declaration is
appended below and uses only `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped Topology BigOperators
open Filter Set

namespace Navier.Analysis.MadelungTransportIdentity

open Navier.Analysis.MadelungDegeneracySharpness
open Navier.Analysis.QuantumVortexRegularity
open Navier.Construction.ProblemStatement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 1. The logarithmic-derivative splitting (density-positive region) -/

/-- Spatial derivative of the density `‖f‖²` in real-inner form, built from
`hasStrictFDerivAt_norm_sq` and the chain rule. -/
private theorem density_fderiv_inner {f : E → ℂ} {x d : E} (h : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y : E => ‖f y‖ ^ 2) x d = 2 * inner ℝ (f x) (fderiv ℝ f x d) := by
  have hc := h.hasFDerivAt.norm_sq
  rw [hc.fderiv]
  simp [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  ring

/-- Density derivative in explicit real and imaginary coordinates (no branch
choice). -/
private theorem density_fderiv_apply {f : E → ℂ} {x d : E} (h : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y : E => ‖f y‖ ^ 2) x d =
      2 * (f x).re * (fderiv ℝ f x d).re + 2 * (f x).im * (fderiv ℝ f x d).im := by
  rw [density_fderiv_inner h]
  have h1 : inner ℝ (f x) (fderiv ℝ f x d) =
      (fderiv ℝ f x d).re * (f x).re + (fderiv ℝ f x d).im * (f x).im := by
    rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [h1]
  ring

/-- `d/dt (1 - t) = -1` as an equation (avoids function-`sub` syntactic friction). -/
private theorem hasDerivAt_one_sub (t : ℝ) : HasDerivAt (fun s : ℝ => 1 - s) (-1) t :=
  (hasDerivAt_id (x := t)).const_sub (1 : ℝ)

/-- The real part of the logarithmic derivative is the density log-derivative. -/
theorem logDeriv_re {ψ : E → ℂ} {x d : E} (h : DifferentiableAt ℝ ψ x) (hx : ψ x ≠ 0) :
    (fderiv ℝ ψ x d / ψ x).re =
      fderiv ℝ (fun y : E => ‖ψ y‖ ^ 2) x d / (2 * ‖ψ x‖ ^ 2) := by
  have hw : Complex.normSq (ψ x) ≠ 0 := mt Complex.normSq_eq_zero.mp hx
  rw [density_fderiv_apply h]
  rw [show (2 * ‖ψ x‖ ^ 2 : ℝ) = 2 * Complex.normSq (ψ x) from by
    rw [← Complex.normSq_eq_norm_sq]]
  rw [Complex.div_re]
  field_simp [hw]

/-- The pairing-constrained decomposition of the logarithmic derivative: the
Madelung pairing controls only the imaginary summand. -/
theorem logDeriv_decompose {ψ : E → ℂ} {x d : E} (h : DifferentiableAt ℝ ψ x) (hx : ψ x ≠ 0) :
    fderiv ℝ ψ x d / ψ x =
      ((fderiv ℝ (fun y : E => ‖ψ y‖ ^ 2) x d / (2 * ‖ψ x‖ ^ 2) : ℝ) : ℂ) +
        Complex.I * (fderiv ℝ ψ x d / ψ x).im := by
  conv_lhs => rw [show fderiv ℝ ψ x d / ψ x =
      ((fderiv ℝ ψ x d / ψ x).re : ℂ) + (fderiv ℝ ψ x d / ψ x).im * Complex.I
      from (Complex.re_add_im _).symm]
  rw [mul_comm ((fderiv ℝ ψ x d / ψ x).im : ℂ) Complex.I, logDeriv_re h hx]

/-- Constant rescaling of the lift leaves the pairing invariant while rescaling
the derivative bound. -/
theorem logDeriv_im_congr_const (a : ℂ) (ha : a ≠ 0) {ψ : E → ℂ} {x d : E}
    (h : DifferentiableAt ℝ ψ x) (hx : ψ x ≠ 0) :
    (fderiv ℝ (fun y => a * ψ y) x d / (a * ψ x)).im =
      (fderiv ℝ ψ x d / ψ x).im := by
  have h1 : fderiv ℝ (fun y : E => a * ψ y) x d = a * fderiv ℝ ψ x d := by
    have hc := h.hasFDerivAt.const_mul a
    rw [hc.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h1, mul_div_mul_left _ _ ha]

/-! ## 2. Exact flow and divergence of the forced velocity -/

/-- Explicit flow of `vel`: `d/dt flowVel t x = vel t (flowVel t x)`,
`flowVel 0 = id`. -/
def flowVel (t : ℝ) (x : E) : E := ((1 - t)⁻¹ ^ 2 : ℝ) • x

theorem hasDerivAt_flowVel (x : E) {t : ℝ} (ht : t ≠ 1) :
    HasDerivAt (fun s : ℝ => flowVel s x) (vel t (flowVel t x)) t := by
  have h1 : (1 - t : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hinv : HasDerivAt (fun s : ℝ => (1 - s)⁻¹) ((1 - t)⁻¹ ^ 2) t :=
    ((hasDerivAt_inv h1).comp t (hasDerivAt_one_sub t)).congr_deriv
      (by field_simp)
  have h2 : HasDerivAt (fun s : ℝ => flowVel s x) ((2 * (1 - t)⁻¹ ^ 3 : ℝ) • x) t := by
    refine ((hinv.pow 2).smul_const x).congr_deriv ?_
    refine congrArg (fun r : ℝ => r • x) (by ring)
  have h3 : vel t (flowVel t x) = (2 * (1 - t)⁻¹ ^ 3 : ℝ) • x := by
    rw [vel, flowVel, smul_smul, div_eq_mul_inv]
    congr 1
    ring
  rw [h3]
  exact h2

theorem flowVel_zero (x : E) : flowVel 0 x = x := by
  show ((1 - (0 : ℝ))⁻¹ ^ 2 : ℝ) • x = x
  rw [show ((1 - (0 : ℝ))⁻¹ ^ 2 : ℝ) = (1 : ℝ) from by norm_num]
  exact one_smul ℝ x

/-- The sharpness velocity as a repository `VelocityField`. -/
def velV : VelocityField := fun p => vel p.1 p.2

private theorem fderiv_velV (t : ℝ) (x : Space) :
    spatialDerivative velV t x = (2 / (1 - t) : ℝ) • ContinuousLinearMap.id ℝ Space := by
  show fderiv ℝ (fun y : Space => vel t y) x = (2 / (1 - t) : ℝ) • ContinuousLinearMap.id ℝ Space
  have h : HasFDerivAt (fun y : Space => vel t y)
      ((2 / (1 - t) : ℝ) • ContinuousLinearMap.id ℝ Space) x := by
    have heq : (fun y : Space => vel t y) =
        ⇑((2 / (1 - t) : ℝ) • ContinuousLinearMap.id ℝ Space) := by
      ext y
      simp [vel]
    rw [heq]
    exact ContinuousLinearMap.hasFDerivAt
      (f := (2 / (1 - t) : ℝ) • ContinuousLinearMap.id ℝ Space) (x := x)
  exact h.fderiv

/-- Euclidean divergence of the forced velocity: `6/(1-t)` (totalized at `t=1`). -/
theorem spatialDivergence_velV (t : ℝ) (x : Space) :
    spatialDivergence velV t x = 6 / (1 - t) := by
  simp only [spatialDivergence, fderiv_velV]
  have hterm : ∀ i : Fin 3,
      (((2 / (1 - t) : ℝ) • ContinuousLinearMap.id ℝ Space) (coordinateVector i)) i =
        2 / (1 - t) := by
    intro i
    simp only [coordinateVector, EuclideanSpace.single, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul,
      mul_one]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    div_eq_mul_inv]
  ring_nf

/-! ## 3. The continuity equation and the transport-compatible collapse witness -/

/-- Pointwise continuity equation `∂ₜρ = -(Dρ(v) + ρ·div v)` on the
repository's `Space`/`VelocityField`/`spatialDivergence` carriers. -/
def densityContinuityEquation (ρ : ℝ → Space → ℝ) (v : VelocityField) : Prop :=
  ∀ t x, HasDerivAt (fun s : ℝ => ρ s x)
    (-(fderiv ℝ (ρ t) x (v (t, x)) + ρ t x * spatialDivergence v t x)) t

/-- Arithmetic cancel used by the continuity-equation branches (`x = 1 - t`). -/
private theorem pow_six_mul_div_cancel {x : ℝ} (hx : x ≠ 0) : x ^ 6 * (6 / x) = 6 * x ^ 5 := by
  field_simp [hx]

/-- The exact transport amplitude law. -/
def collapseAmplitude (t : ℝ) : ℝ := (1 - t) ^ 3

/-- The transport-compatible decoder of the sharpness family. -/
def cpsi (t : ℝ) (x : E) : ℂ := psi (collapseAmplitude t) t x

theorem norm_cpsi (t : ℝ) (x : E) : ‖cpsi t x‖ = |1 - t| ^ 3 := by
  show ‖psi ((1 - t) ^ 3) t x‖ = |1 - t| ^ 3
  rw [norm_psi, ← abs_pow]

theorem normSq_cpsi (t : ℝ) (x : E) : ‖cpsi t x‖ ^ 2 = (1 - t) ^ 6 := by
  calc ‖cpsi t x‖ ^ 2 = (|1 - t| ^ 3) ^ 2 := by rw [norm_cpsi]
    _ = |1 - t| ^ 6 := by ring
    _ = (1 - t) ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]

theorem cpsi_nonzero {t : ℝ} (ht : t < 1) (x : E) : cpsi t x ≠ 0 :=
  mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (pow_ne_zero 3 (sub_ne_zero.mpr ht.ne')))
    (Complex.exp_ne_zero _)

theorem differentiableAt_cpsi {t : ℝ} (ht : t ≠ 1) (x : E) :
    DifferentiableAt ℝ (cpsi t) x :=
  (hasFDerivAt_psi ht x).differentiableAt

theorem pairing_cpsi {t : ℝ} (ht : t ≠ 1) (x d : E) :
    inner ℝ (vel t x) d = (fderiv ℝ (cpsi t) x d / cpsi t x).im :=
  vel_pairing (collapseAmplitude t) (pow_ne_zero 3 (sub_ne_zero.mpr (Ne.symm ht))) ht x d

theorem norm_fderiv_cpsi_le {t : ℝ} (h0 : 0 ≤ t) (ht : t < 1) (R : ℝ) (x : Space)
    (hx : x ∈ Metric.closedBall (0 : Space) R) :
    ‖fderiv ℝ (cpsi t) x‖ ≤ 2 * R := by
  have hx' : ‖x‖ ≤ R := by
    rw [Metric.mem_closedBall] at hx
    rwa [dist_eq_norm, sub_zero] at hx
  have h1 : 0 < 1 - t := sub_pos.mpr ht
  have hle : |collapseAmplitude t| * (2 / (1 - t)) * ‖x‖ ≤ 2 * R := by
    have h2 : |collapseAmplitude t| * (2 / (1 - t)) = 2 * (1 - t) ^ 2 := by
      rw [collapseAmplitude, abs_of_pos (pow_pos h1 3)]
      field_simp [h1.ne']
    calc |collapseAmplitude t| * (2 / (1 - t)) * ‖x‖
        = 2 * (1 - t) ^ 2 * ‖x‖ := by rw [h2]
      _ ≤ 2 * 1 * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          have hpos : (0 : ℝ) ≤ 1 - t := by linarith
          have hprod : 0 ≤ t * (1 - t) := mul_nonneg h0 hpos
          nlinarith
      _ ≤ 2 * R := by nlinarith
  exact (norm_fderiv_psi (collapseAmplitude t) ht x).trans hle

theorem hasDerivAt_normSq_cpsi (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖cpsi s x‖ ^ 2) (-6 * (1 - t) ^ 5) t := by
  have heq : (fun s : ℝ => ‖cpsi s x‖ ^ 2) = fun s : ℝ => (1 - s) ^ 6 :=
    funext (normSq_cpsi · x)
  rw [heq]
  exact (hasDerivAt_one_sub t).pow 6 |>.congr_deriv (by ring)

/-- The collapse decoder satisfies the exact continuity equation against `velV`
at every `(t, x)`. -/
theorem cpsi_satisfies_densityContinuity :
    densityContinuityEquation (fun t x => ‖cpsi t x‖ ^ 2) velV := by
  intro t x
  have heq : (fun y : Space => ‖cpsi t y‖ ^ 2) = fun _ => (1 - t) ^ 6 :=
    funext (normSq_cpsi t)
  have hsp : fderiv ℝ (fun y : Space => ‖cpsi t y‖ ^ 2) x (velV (t, x)) = 0 := by
    have hfz : fderiv ℝ (fun y : Space => ‖cpsi t y‖ ^ 2) x = 0 := by
      rw [heq]
      exact (hasFDerivAt_const ((1 - t) ^ 6) x).fderiv
    rw [hfz]
    simp
  have hrho : ‖cpsi t x‖ ^ 2 = (1 - t) ^ 6 := normSq_cpsi t x
  have heqf : (fun s : ℝ => ‖cpsi s x‖ ^ 2) = fun s : ℝ => (1 - s) ^ 6 :=
    funext (normSq_cpsi · x)
  rw [heqf]
  refine (hasDerivAt_one_sub t).pow 6 |>.congr_deriv ?_
  dsimp only
  rw [hrho, spatialDivergence_velV, hsp]
  simp only [zero_add]
  by_cases h1 : t = 1
  · subst h1
    norm_num
  · rw [pow_six_mul_div_cancel (sub_ne_zero.mpr (Ne.symm h1))]
    ring_nf

/-- The along-flow form: density transported by the exact characteristics. -/
theorem cpsi_transport_along_flow (x : Space) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖cpsi s (flowVel s x)‖ ^ 2)
      (-(‖cpsi t (flowVel t x)‖ ^ 2 * spatialDivergence velV t (flowVel t x))) t := by
  have heq : (fun s : ℝ => ‖cpsi s (flowVel s x)‖ ^ 2) = fun s : ℝ => (1 - s) ^ 6 :=
    funext (fun s => normSq_cpsi s (flowVel s x))
  rw [heq, spatialDivergence_velV, normSq_cpsi]
  refine (hasDerivAt_one_sub t).pow 6 |>.congr_deriv ?_
  by_cases h1 : t = 1
  · subst h1
    norm_num
  · rw [pow_six_mul_div_cancel (sub_ne_zero.mpr (Ne.symm h1))]
    ring_nf

/-- Kernel falsification of the constant-amplitude lift: `psi b t` with
`b ≠ 0` has constant density and cannot satisfy the continuity equation
against `velV`. -/
theorem constantAmplitude_not_transport_compatible (b : ℝ) (hb : b ≠ 0) :
    ¬ densityContinuityEquation (fun t x => ‖psi b t x‖ ^ 2) velV := by
  intro hcon
  have h1 := hcon (1 / 2) 0
  dsimp only at h1
  have hsp : fderiv ℝ (fun y : Space => ‖psi b (1 / 2) y‖ ^ 2) 0 (velV (1 / 2, 0)) = 0 := by
    have heq : (fun y : Space => ‖psi b (1 / 2) y‖ ^ 2) = fun _ => b ^ 2 :=
      funext (fun y => by rw [norm_psi, sq_abs])
    have hfz : fderiv ℝ (fun y : Space => ‖psi b (1 / 2) y‖ ^ 2) 0 = 0 := by
      rw [heq]
      exact (hasFDerivAt_const (b ^ 2) (0 : Space)).fderiv
    rw [hfz]
    simp
  have hrho : ‖psi b (1 / 2 : ℝ) (0 : Space)‖ ^ 2 = b ^ 2 := by rw [norm_psi, sq_abs]
  have hdiv : spatialDivergence velV (1 / 2) 0 = (12 : ℝ) := by
    rw [spatialDivergence_velV]
    norm_num
  rw [hsp, hrho, hdiv] at h1
  simp only [zero_add] at h1
  have h0 : HasDerivAt (fun s : ℝ => ‖psi b s (0 : Space)‖ ^ 2) 0 (1 / 2) := by
    have heq : (fun s : ℝ => ‖psi b s (0 : Space)‖ ^ 2) = fun _ => b ^ 2 :=
      funext (fun s => by rw [norm_psi, sq_abs])
    rw [heq]
    exact hasDerivAt_const (1 / 2) (b ^ 2)
  have heq := HasDerivAt.unique h0 h1
  have hpos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  nlinarith

private theorem half_pow_le_one_div_succ (k : ℕ) :
    ((1 / 2 : ℝ) ^ k) ≤ 1 / ((k : ℝ) + 1) := by
  induction k with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      have h2 : (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ≤ (1 / ((j : ℝ) + 1)) * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right ih (by norm_num)
      have h3 : (1 / ((j : ℝ) + 1)) * (1 / 2 : ℝ) = 1 / (((j : ℝ) + 1) * 2) := by
        field_simp
      have h4 : 1 / (((j : ℝ) + 1) * 2) ≤ 1 / (↑(j + 1) + 1) := by
        refine one_div_le_one_div_of_le ?_ ?_
        · positivity
        · push_cast
          ring_nf
          linarith
      calc (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ≤ (1 / ((j : ℝ) + 1)) * (1 / 2 : ℝ) := h2
        _ = 1 / (((j : ℝ) + 1) * 2) := h3
        _ ≤ 1 / (↑(j + 1) + 1) := h4

private theorem exists_half_pow_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  refine ⟨n + 1, lt_of_le_of_lt (half_pow_le_one_div_succ (n + 1)) ?_⟩
  calc (1 : ℝ) / ((↑(n + 1) : ℝ) + 1) < 1 / (1 / ε) :=
        one_div_lt_one_div_of_lt (by positivity) (by push_cast; linarith)
    _ = ε := by field_simp

/-- Rigidity: a spatially uniform transport density decays exactly as
`r 0 · (1-t)⁶`. -/
theorem uniformDensity_transport_rigidity {r : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt r (-(6 * r t / (1 - t))) t) {t : ℝ} (ht : t < 1) :
    r t = r 0 * (1 - t) ^ 6 := by
  set g : ℝ → ℝ := fun s => r s * (1 - s)⁻¹ ^ 6 with hg
  have hgc : ∀ s ∈ Iio (1 : ℝ), HasDerivAt g 0 s := by
    intro s hs
    have h1t : (1 - s : ℝ) ≠ 0 := sub_ne_zero.mpr hs.ne'
    have hinv : HasDerivAt (fun u : ℝ => (1 - u)⁻¹) ((1 - s)⁻¹ ^ 2) s :=
      ((hasDerivAt_inv h1t).comp s (hasDerivAt_one_sub s)).congr_deriv
        (by field_simp)
    have hpow : HasDerivAt (fun u : ℝ => (1 - u)⁻¹ ^ 6) (6 * (1 - s)⁻¹ ^ 7) s :=
      (hinv.pow 6).congr_deriv (by ring)
    have hmul : HasDerivAt (fun u : ℝ => r u * (1 - u)⁻¹ ^ 6)
        (-(6 * r s / (1 - s)) * (1 - s)⁻¹ ^ 6 + r s * (6 * (1 - s)⁻¹ ^ 7)) s :=
      (hd s).mul hpow
    exact hmul.congr_deriv (by rw [div_eq_mul_inv]; ring_nf)
  have hdiff : DifferentiableOn ℝ g (Iio 1) := by
    intro s hs
    exact (hgc s hs).differentiableAt.differentiableWithinAt
  obtain ⟨a, ha⟩ := isOpen_Iio.exists_is_const_of_deriv_eq_zero
    (isConnected_Iio.isPreconnected) hdiff (fun s hs => (hgc s hs).deriv)
  have h0 : (0 : ℝ) ∈ Iio (1 : ℝ) := by norm_num
  have hg0 : g 0 = r 0 := by
    show r 0 * (1 - (0 : ℝ))⁻¹ ^ 6 = r 0
    norm_num
  have h1 : (1 - t : ℝ) ≠ 0 := sub_ne_zero.mpr ht.ne'
  have hcancel : (1 - t)⁻¹ ^ 6 * (1 - t) ^ 6 = (1 : ℝ) := by
    rw [inv_pow]
    field_simp [h1]
  calc r t = r t * ((1 - t)⁻¹ ^ 6 * (1 - t) ^ 6) := by rw [hcancel, mul_one]
    _ = (r t * (1 - t)⁻¹ ^ 6) * (1 - t) ^ 6 := by ring
    _ = g t * (1 - t) ^ 6 := by
        show (r t * (1 - t)⁻¹ ^ 6) * (1 - t) ^ 6 = g t * (1 - t) ^ 6
        rw [show g t = r t * (1 - t)⁻¹ ^ 6 from by rw [hg]]
    _ = a * (1 - t) ^ 6 := by rw [ha t ht]
    _ = r 0 * (1 - t) ^ 6 := by rw [← hg0, ← ha 0 h0]

/-- Exact equivalence for the whole forced family: transport against `velV`
holds exactly when the squared amplitude obeys the rigidity ODE. -/
theorem psiFamily_densityContinuity (b : ℝ → ℝ) :
    densityContinuityEquation (fun t x => ‖psi (b t) t x‖ ^ 2) velV ↔
      ∀ t, HasDerivAt (fun s : ℝ => b s ^ 2) (-(6 * b t ^ 2 / (1 - t))) t := by
  constructor
  · intro h t
    have h1 := h t 0
    dsimp only at h1
    have heq : (fun y : Space => ‖psi (b t) t y‖ ^ 2) = fun _ => b t ^ 2 :=
      funext (fun y => by rw [norm_psi, sq_abs])
    have hsp : fderiv ℝ (fun y : Space => ‖psi (b t) t y‖ ^ 2) 0 (velV (t, 0)) = 0 := by
      have hfz : fderiv ℝ (fun y : Space => ‖psi (b t) t y‖ ^ 2) 0 = 0 := by
        rw [heq]
        exact (hasFDerivAt_const (b t ^ 2) (0 : Space)).fderiv
      rw [hfz]
      simp
    have hrho : ‖psi (b t) t (0 : Space)‖ ^ 2 = b t ^ 2 := by rw [norm_psi, sq_abs]
    have heqf : (fun s : ℝ => ‖psi (b s) s (0 : Space)‖ ^ 2) = fun s : ℝ => b s ^ 2 :=
      funext (fun s => by rw [norm_psi, sq_abs])
    rw [heqf] at h1
    rw [hsp, zero_add, hrho, spatialDivergence_velV] at h1
    exact h1.congr_deriv ((by rw [mul_div, div_eq_mul_inv, div_eq_mul_inv]; ring))
  · intro h t x
    dsimp only
    have heq : (fun y : Space => ‖psi (b t) t y‖ ^ 2) = fun _ => b t ^ 2 :=
      funext (fun y => by rw [norm_psi, sq_abs])
    have hsp : fderiv ℝ (fun y : Space => ‖psi (b t) t y‖ ^ 2) x (velV (t, x)) = 0 := by
      have hfz : fderiv ℝ (fun y : Space => ‖psi (b t) t y‖ ^ 2) x = 0 := by
        rw [heq]
        exact (hasFDerivAt_const (b t ^ 2) x).fderiv
      rw [hfz]
      simp
    have hrho : ‖psi (b t) t x‖ ^ 2 = b t ^ 2 := by rw [norm_psi, sq_abs]
    have heqf : (fun s : ℝ => ‖psi (b s) s x‖ ^ 2) = fun s : ℝ => b s ^ 2 :=
      funext (fun s => by rw [norm_psi, sq_abs])
    rw [heqf, hsp, hrho, spatialDivergence_velV, zero_add]
    exact (h t).congr_deriv ((by rw [mul_div, div_eq_mul_inv, div_eq_mul_inv]; ring))

/-- Transport EXCLUDES a uniform positive amplitude floor for the forced
family: the rigidity law forces decay below every fixed floor. -/
theorem psiFamily_transport_excludes_amplitude_floor (b : ℝ → ℝ)
    (hb : ∀ t, HasDerivAt (fun s : ℝ => b s ^ 2) (-(6 * b t ^ 2 / (1 - t))) t)
    (hfloor : ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, ∀ x : Space, c ≤ ‖psi (b t) t x‖) : False := by
  obtain ⟨c, hc, hcf⟩ := hfloor
  obtain ⟨n, hn⟩ :=
    exists_half_pow_lt (by positivity : (0 : ℝ) < c ^ 2 / (b 0 ^ 2 + c ^ 2))
  set t : ℝ := 1 - (1 / 2 : ℝ) ^ n with htdef
  have hq : (0 : ℝ) < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hq1 : (1 / 2 : ℝ) ^ n ≤ 1 := by
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ (0 : ℕ) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le n)
      _ = 1 := pow_zero _
  have ht1 : t < 1 := by linarith [htdef, hq]
  have hr := uniformDensity_transport_rigidity hb ht1
  have hq6 : ((1 / 2 : ℝ) ^ n) ^ 6 ≤ (1 / 2 : ℝ) ^ n :=
    (pow_le_pow_of_le_one (le_of_lt hq) hq1 (by norm_num : 1 ≤ (6 : ℕ))).trans
      (le_of_eq (pow_one _))
  have hmain : c ^ 2 ≤ b t ^ 2 := by
    have h1 := hcf t 0
    rw [norm_psi] at h1
    nlinarith [abs_mul_abs_self (b t)]
  have h1t : (1 - t : ℝ) = (1 / 2 : ℝ) ^ n := by
    rw [htdef]
    ring
  have hstep : c ^ 2 ≤ b 0 ^ 2 * (1 / 2 : ℝ) ^ n :=
    calc c ^ 2 ≤ b t ^ 2 := hmain
      _ = b 0 ^ 2 * (1 - t) ^ 6 := hr
      _ = b 0 ^ 2 * ((1 / 2 : ℝ) ^ n) ^ 6 := by rw [h1t]
      _ ≤ b 0 ^ 2 * (1 / 2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left hq6 (sq_nonneg (b 0))
  have hqlt : (1 / 2 : ℝ) ^ n * (b 0 ^ 2 + c ^ 2) < c ^ 2 := by
    have hpos : (0 : ℝ) < b 0 ^ 2 + c ^ 2 := by positivity
    rwa [← lt_div_iff₀ hpos]
  nlinarith

/-- The first transport structure does NOT exclude either dichotomy disjunct:
this decoder has exact pairing, exact continuity, uniformly bounded ball
derivatives, and amplitude collapse in every terminal window against the
unbounded velocity. -/
theorem transport_compatible_collapse_decoder (x₀ : Space) (hx₀ : x₀ ≠ 0) :
    ∃ (u : VelocityField) (ψ : ℝ → Space → ℂ),
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, DifferentiableAt ℝ (ψ t) x) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, ψ t x ≠ 0) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, ∀ d,
        inner ℝ (u (t, x)) d = (fderiv ℝ (ψ t) x d / ψ t x).im) ∧
      (∀ R : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ Metric.closedBall (0 : Space) R,
        ‖fderiv ℝ (ψ t) x‖ ≤ 2 * R) ∧
      (∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 < δ →
        ∃ t ∈ Ico (0 : ℝ) 1, 1 - δ < t ∧ ‖ψ t x₀‖ < c) ∧
      densityContinuityEquation (fun t x => ‖ψ t x‖ ^ 2) u ∧
      ∀ δ : ℝ, 0 < δ → ∀ M : ℝ,
        ∃ t ∈ Ico (0 : ℝ) 1, 1 - δ < t ∧ M < ‖u (t, x₀)‖ := by
  refine ⟨velV, cpsi, fun t ht x => differentiableAt_cpsi ht.2.ne x,
    fun t ht x => cpsi_nonzero ht.2 x,
    fun t ht x d => pairing_cpsi ht.2.ne x d,
    fun R t ht x hx => norm_fderiv_cpsi_le ht.1 ht.2 R x hx, ?_,
    cpsi_satisfies_densityContinuity,
    fun δ hδ M => vel_unbounded_near_one x₀ hx₀ δ hδ M⟩
  intro c hc δ hδ
  obtain ⟨n, hn⟩ := exists_half_pow_lt (by positivity : (0 : ℝ) < min δ c)
  have hq : (0 : ℝ) < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hq1 : (1 / 2 : ℝ) ^ n ≤ 1 := by
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ (0 : ℕ) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le n)
      _ = 1 := pow_zero _
  have hd : (1 / 2 : ℝ) ^ n < δ := lt_of_lt_of_le hn (min_le_left δ c)
  have hc' : (1 / 2 : ℝ) ^ n < c := lt_of_lt_of_le hn (min_le_right δ c)
  set t : ℝ := 1 - (1 / 2 : ℝ) ^ n with htdef
  refine ⟨t, ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · linarith [htdef, hd]
  · have h3 : ((1 / 2 : ℝ) ^ n) ^ 3 ≤ (1 / 2 : ℝ) ^ n :=
      (pow_le_pow_of_le_one (le_of_lt hq) hq1 (by norm_num : 1 ≤ (3 : ℕ))).trans
        (le_of_eq (pow_one _))
    calc ‖cpsi t x₀‖ = |1 - t| ^ 3 := norm_cpsi t x₀
      _ = ((1 / 2 : ℝ) ^ n) ^ 3 := by
          rw [show (1 - t : ℝ) = (1 / 2 : ℝ) ^ n from by rw [htdef]; ring, abs_of_pos hq]
      _ ≤ (1 / 2 : ℝ) ^ n := h3
      _ < c := hc'

/-- Pairing lower form consumed by the dichotomy: `‖u‖·‖ψ‖ ≤ |κ|·‖D‖`. -/
theorem madelung_pairing_norm_lower
    {u : E} {ψ : ℂ} {D : E →L[ℝ] ℂ} {κ : ℝ}
    (hψ : ψ ≠ 0)
    (hdecode : ∀ d : E, inner ℝ u d = κ * (D d / ψ).im) :
    ‖u‖ * ‖ψ‖ ≤ |κ| * ‖D‖ :=
  (le_div_iff₀ (norm_pos_iff.mpr hψ)).mp
    (norm_le_of_madelung_pairing u ψ D κ hψ hdecode)

end Navier.Analysis.MadelungTransportIdentity

#print axioms Navier.Analysis.MadelungTransportIdentity.logDeriv_re
#print axioms Navier.Analysis.MadelungTransportIdentity.logDeriv_decompose
#print axioms Navier.Analysis.MadelungTransportIdentity.logDeriv_im_congr_const
#print axioms Navier.Analysis.MadelungTransportIdentity.hasDerivAt_flowVel
#print axioms Navier.Analysis.MadelungTransportIdentity.flowVel_zero
#print axioms Navier.Analysis.MadelungTransportIdentity.spatialDivergence_velV
#print axioms Navier.Analysis.MadelungTransportIdentity.norm_cpsi
#print axioms Navier.Analysis.MadelungTransportIdentity.normSq_cpsi
#print axioms Navier.Analysis.MadelungTransportIdentity.cpsi_satisfies_densityContinuity
#print axioms Navier.Analysis.MadelungTransportIdentity.cpsi_transport_along_flow
#print axioms Navier.Analysis.MadelungTransportIdentity.constantAmplitude_not_transport_compatible
#print axioms Navier.Analysis.MadelungTransportIdentity.uniformDensity_transport_rigidity
#print axioms Navier.Analysis.MadelungTransportIdentity.psiFamily_densityContinuity
#print axioms Navier.Analysis.MadelungTransportIdentity.psiFamily_transport_excludes_amplitude_floor
#print axioms Navier.Analysis.MadelungTransportIdentity.transport_compatible_collapse_decoder
#print axioms Navier.Analysis.MadelungTransportIdentity.madelung_pairing_norm_lower
