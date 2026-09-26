import Navier.Problem
import Navier.Analysis.MadelungDecoderCurlObstruction

/-!
# Spinor (multi-field) Madelung decoders stay locally exact off the joint zeros

`MadelungDecoderCurlObstruction` kernelizes the single-scalar wall: a smooth
`ψ` with `ψ 0 ≠ 0` decodes a field that is `κ · dΘ` for a local `C^∞` phase,
so the decoded datum has commuting mixed partials and the rotational datum
`rotationalDatum lam` admits no scalar lift (`lam > 0`).  This file expands the
decoder to `n` components — the spinor / Clebsch-style ansatz
`u = Σₐ κₐ · Im(ψ̄ₐ Dψₐ)/|ψₐ|²` — and settles the `n = 1 → n = 2` jump.

**The jump does not happen at nonvanishing amplitude.**  Each component with
`ψₐ x ≠ 0` contributes, eventually near `x`, the exact form `κₐ · dΘₐ`; a
constant-coefficient sum of exact forms is the exact form of the combined
phase `Φ = Σₐ κₐ Θₐ`.  Hence for every `n` (`madelung_multi_decoder_mixed_partial_comm`)
the decoded field has commuting mixed partials at every point where all
components are nonzero, and `staticCurl` vanishes there
(`madelung_multi_decoder_staticCurl_eq_zero`).  Consequently
`no_multi_madelung_initial_lift_of_rotational_data` kernel-falsifies the lift
of `rotationalDatum lam` (`lam > 0`) for **all** `n`, including the two-field
spinor (`no_two_field_madelung_initial_lift_of_rotational_data`) and, at
`n = 1`, recovering the scalar obstruction through the new mechanism.

**Named next obstruction.**  The only way this carrier class reaches
rotational data is through component *zeros*: there the logarithmic
derivative `Im(Dψₐ/ψₐ)` is a closed non-exact form (quantized circulation
about the vortex locus — the regime kernelized in `QuantumVortexRegularity`
by `unitVortex`).  A lift of `rotationalDatum lam` must therefore place a
zero of some component at (and rotating through) the evaluation region;
this file settles the nonvanishing-amplitude case and leaves the
vanishing-amplitude classification OPEN (exact residual: whether a smooth
`n`-tuple with prescribed zero locus can satisfy the decoder relation
pointwise where components vanish — see RESIDUALS below).  Spatially
varying mixing coefficients (Clebsch `u = ∇α + β ∇γ`) are a *different*
decoder law, not this one, and are not claimed here.

Estimates (the pairing-estimate extension): `Space` carries the sup norm
(the `kineticEnergy` note in `Navier/Problem.lean` records Euclidean ≠ sup),
so the Euclidean pairing lemma `norm_le_of_madelung_pairing` does not
transfer verbatim; `madelung_multi_decoder_norm_le` gives the sup-norm
triangle form `‖u x‖ ≤ Σₐ |κₐ| · ‖Dψₐ x‖ / ‖ψₐ x‖` off the zeros.

Status: multi-component nonvanishing spinor lift FALSIFIED for
`rotationalDatum lam`, `lam > 0`; curl-free-off-zeros boundary theorem
proved; vanishing-amplitude decode classification OPEN.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators ContDiff

namespace Navier.Analysis.MadelungSpinorDecoder

open Navier Filter Set Metric Function
open Navier.Analysis.MadelungDecoderCurlObstruction
open Navier.Analysis.CurlIdentities
open Navier.Analysis.Vorticity

private theorem real_smul_eq_mul (r x : ℝ) : r • x = r * x := by simp

/-- **Pointwise local-phase extraction for one scalar component.**  If `ψ` is
`C^∞` and `ψ x ≠ 0`, then eventually near `x` the decoded 1-form
`v ↦ (Dψ y v / ψ y).im` is the differential of the arctangent phase `Θ` of the
phase-rotated `c₀ψ` (with `c₀` rotating `ψ x` to the positive real axis), and
`Θ` is differentiable on that neighbourhood.  This is
`madelung_decoder_mixed_partial_comm`'s internal mechanism (`c₀`, `φ`, `Θ`,
`hphase`) factored out at a general point and generalized from basis
directions to all vectors. -/
private theorem exists_local_im_logderiv_phase {ψ : Space → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    {x : Space} (hx : ψ x ≠ 0) :
    ∃ Θ, ContDiffAt ℝ ∞ Θ x ∧
      ∀ᶠ y in nhds x, ∀ v : Space,
        (fderiv ℝ ψ y v / ψ y).im = fderiv ℝ Θ y v ∧ DifferentiableAt ℝ Θ y := by
  -- Rotate ψ by a constant phase so that its value at x is a positive real.
  set c0 : ℂ := Complex.exp (-(Complex.I * (ψ x).arg)) with hc0d
  have hc0 : c0 ≠ 0 := Complex.exp_ne_zero _
  have hpol : ‖ψ x‖ * Complex.exp (Complex.I * (ψ x).arg) = ψ x := by
    have h := Complex.norm_mul_exp_arg_mul_I (ψ x)
    rwa [← mul_comm Complex.I ((ψ x).arg)] at h
  have hkey : c0 * Complex.exp (Complex.I * (ψ x).arg) = 1 := by
    rw [show c0 = Complex.exp (-(Complex.I * (ψ x).arg)) from rfl, ← Complex.exp_add,
      neg_add_cancel, Complex.exp_zero]
  have hrot : c0 * ψ x = (‖ψ x‖ : ℂ) := by
    conv_lhs => rw [← hpol]
    rw [mul_left_comm c0, hkey, mul_one]
  set φ : Space → ℂ := fun y => c0 * ψ y with hφdef
  set Θ : Space → ℝ := fun y => Real.arctan ((φ y).im / (φ y).re) with hΘdef
  have hre0 : 0 < (φ x).re := by
    show 0 < (c0 * ψ x).re
    rw [hrot, Complex.ofReal_re]
    exact norm_pos_iff.mpr hx
  have hφc : ContDiff ℝ ∞ φ :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => (c0 : ℂ))).mul hψ
  have hΘ : ContDiffAt ℝ ∞ Θ x := by
    have hi : ContDiffAt ℝ ∞ (fun z : ℂ => z.im) (φ x) :=
      (Complex.imCLM : ℂ →L[ℝ] ℝ).contDiff.contDiffAt (x := φ x)
    have hinv : ContDiffAt ℝ ∞ (fun z : ℂ => (z.re)⁻¹) (φ x) :=
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).contDiff.contDiffAt (x := φ x)).inv (ne_of_gt hre0)
    have hratio : ContDiffAt ℝ ∞ (fun z : ℂ => z.im / z.re) (φ x) := hi.mul hinv
    have hcomp : ContDiffAt ℝ ∞ (fun y : Space => (φ y).im / (φ y).re) x :=
      ContDiffAt.comp x hratio hφc.contDiffAt
    have hmain :
        ContDiffAt ℝ ∞
          ((fun t : ℝ => Real.arctan t) ∘ fun y : Space => (φ y).im / (φ y).re) x :=
      ContDiffAt.comp x
        (Real.contDiff_arctan.contDiffAt :
          ContDiffAt ℝ ∞ (fun t : ℝ => Real.arctan t) ((φ x).im / (φ x).re)) hcomp
    exact hmain
  have hreC : ContinuousAt (fun y : Space => (φ y).re) x :=
    ((Complex.reCLM : ℂ →L[ℝ] ℝ).continuous.continuousAt (x := φ x)).comp
      (hφc.continuous.continuousAt (x := x))
  have hev : ∀ᶠ y in nhds x, (φ y).re ≠ 0 :=
    hreC.tendsto.eventually_ne (ne_of_gt hre0)
  -- Pointwise: the phase's differential is the decoded 1-form.
  have hDphi' (y : Space) : fderiv ℝ φ y = c0 • fderiv ℝ ψ y := by
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
      ((hψ.differentiable (by norm_num)).differentiableAt (x := y)).hasFDerivAt
    have h : HasFDerivAt φ _ y := (hasFDerivAt_const c0 y).mul hψd
    rw [h.fderiv]
    refine ContinuousLinearMap.ext fun w => ?_
    simp
  have hdφ (y : Space) : HasFDerivAt φ (fderiv ℝ φ y) y :=
    ((hφc.differentiable (by norm_num)).differentiableAt (x := y)).hasFDerivAt
  have hphase (y : Space) (hy : (φ y).re ≠ 0) (v : Space) :
      (fderiv ℝ Θ y v = (fderiv ℝ ψ y v / ψ y).im) ∧ DifferentiableAt ℝ Θ y := by
    have hi : HasFDerivAt (fun z : ℂ => z.im) (Complex.imCLM : ℂ →L[ℝ] ℝ) (φ y) :=
      (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt
    have hr : HasFDerivAt (fun z : ℂ => z.re) (Complex.reCLM : ℂ →L[ℝ] ℝ) (φ y) :=
      (Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt
    have hinv : HasFDerivAt (fun z : ℂ => (z.re)⁻¹) _ (φ y) :=
      ((hasDerivAt_inv hy).hasFDerivAt).comp (φ y) hr
    have hratio : HasFDerivAt (fun z : ℂ => z.im / z.re) _ (φ y) := hi.mul hinv
    have harct : HasFDerivAt (fun z : ℂ => Real.arctan (z.im / z.re)) _ (φ y) :=
      ((Real.hasDerivAt_arctan _).hasFDerivAt).comp (φ y) hratio
    have hden : (φ y).re * (φ y).re + (φ y).im * (φ y).im ≠ 0 := by
      nlinarith [mul_self_pos.mpr hy]
    have h : HasFDerivAt Θ _ y := harct.comp y (hdφ y)
    have hDΘ : fderiv ℝ Θ y v = (fderiv ℝ φ y v / φ y).im := by
      rw [h.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.toSpanSingleton_apply,
        Complex.reCLM_apply, Complex.imCLM_apply, real_smul_eq_mul, pow_two,
        Complex.div_im, Complex.normSq_apply]
      field_simp [hy, hden]
      ring
    have hf : fderiv ℝ φ y v = c0 * fderiv ℝ ψ y v := by
      rw [hDphi' y, ContinuousLinearMap.smul_apply]
      simp only [smul_eq_mul, Algebra.smul_def, id_eq]
    refine ⟨hDΘ.trans <| by
        rw [hf, show φ y = c0 * ψ y from rfl,
          mul_div_mul_left (fderiv ℝ ψ y v) (ψ y) hc0],
      h.differentiableAt⟩
  refine ⟨Θ, hΘ, hev.mono fun y hy v => ⟨(hphase y hy v).1.symm, (hphase y hy (0 : Space)).2⟩⟩

/-! ## The multi-field (spinor) decoder relation -/

/-- **Multi-field Madelung decoder.**  `n` components `ψ a : Space → ℂ` with
constant mixing coefficients `κ a` decode `u` by the component form of
`u = Σₐ κₐ · Im(ψ̄ₐ Dψₐ)/|ψₐ|²`, i.e. `u x i = Σₐ κₐ · (Dψₐ(x) eᵢ / ψₐ x).im`
(component form, as in `MadelungInitialDecoder`, since both sides are linear
in the direction).  At `n = 1` a one-term sum is the scalar relation verbatim;
`MadelungSpinorInitialDecoder` is the two-component specialization. -/
def MadelungMultiInitialDecoder (n : ℕ) (κ : Fin n → ℝ) (ψ : Fin n → (Space → ℂ))
    (u : VelocityField) : Prop :=
  ∀ (x : Space) (i : Fin 3),
    u x i = ∑ a : Fin n, κ a * ((fderiv ℝ (ψ a) x (basisVector i)) / ψ a x).im

/-- The two-component spinor Madelung decoder law:
`u = κ₀ · Im(ψ̄₀ Dψ₀)/|ψ₀|² + κ₁ · Im(ψ̄₁ Dψ₁)/|ψ₁|²` in component form. -/
def MadelungSpinorInitialDecoder (κ : Fin 2 → ℝ) (ψ : Fin 2 → (Space → ℂ))
    (u : VelocityField) : Prop :=
  MadelungMultiInitialDecoder 2 κ ψ u

/-! ## Boundary theorem: nonvanishing spinor data is locally exact -/

/-- **The spinor expansion buys nothing at nonvanishing amplitude.**  If every
component satisfies `ψ a x ≠ 0`, the decoded field is, eventually near `x`,
the gradient of the single combined phase `Φ = Σₐ κₐ Θₐ`.  Each component
contributes an exact form `κₐ · dΘₐ` (`exists_local_im_logderiv_phase`);
constant coefficients preserve exactness. -/
theorem madelung_multi_decoder_locally_exact (n : ℕ) (κ : Fin n → ℝ)
    (ψ : Fin n → (Space → ℂ)) (hψ : ∀ a, ContDiff ℝ ∞ (ψ a))
    {x : Space} (hx : ∀ a, ψ a x ≠ 0) (u : VelocityField)
    (hdec : MadelungMultiInitialDecoder n κ ψ u) :
    ∃ Φ : Space → ℝ, ContDiffAt ℝ ∞ Φ x ∧
      ∀ᶠ y in nhds x, ∀ i : Fin 3, u y i = fderiv ℝ Φ y (basisVector i) := by
  -- per-component local phases
  have hph (a : Fin n) :
      ∃ Θ, ContDiffAt ℝ ∞ Θ x ∧
        ∀ᶠ y in nhds x, ∀ v : Space,
          (fderiv ℝ (ψ a) y v / ψ a y).im = fderiv ℝ Θ y v ∧ DifferentiableAt ℝ Θ y :=
    exists_local_im_logderiv_phase (hψ a) (hx a)
  let Θ : Fin n → (Space → ℝ) := fun a => Classical.choose (hph a)
  have hspec (a : Fin n) : ContDiffAt ℝ ∞ (Θ a) x ∧
      ∀ᶠ y in nhds x, ∀ v : Space,
        (fderiv ℝ (ψ a) y v / ψ a y).im = fderiv ℝ (Θ a) y v ∧ DifferentiableAt ℝ (Θ a) y :=
    Classical.choose_spec (hph a)
  set Φ : Space → ℝ := fun y => ∑ a : Fin n, κ a * Θ a y with hΦdef
  have hΦc : ContDiffAt ℝ ∞ Φ x := by
    rw [hΦdef]
    refine ContDiffAt.sum (fun a _ => ?_)
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Space => κ a) x).mul (hspec a).1
  have hev : ∀ᶠ y in nhds x, ∀ a : Fin n, ∀ v : Space,
      (fderiv ℝ (ψ a) y v / ψ a y).im = fderiv ℝ (Θ a) y v ∧ DifferentiableAt ℝ (Θ a) y := by
    have h := (Finset.univ : Finset (Fin n)).eventually_all.mpr (fun a _ => (hspec a).2)
    exact h.mono (fun y hy a v => hy a (Finset.mem_univ a) v)
  refine ⟨Φ, hΦc, hev.mono fun y hy i => ?_⟩
  calc u y i = ∑ a : Fin n, κ a * (fderiv ℝ (ψ a) y (basisVector i) / ψ a y).im := hdec y i
    _ = ∑ a : Fin n, κ a * fderiv ℝ (Θ a) y (basisVector i) :=
        Finset.sum_congr rfl fun a _ => congrArg (κ a * ·) ((hy a (basisVector i)).1)
    _ = fderiv ℝ Φ y (basisVector i) := by
      have hd (a : Fin n) : HasFDerivAt (fun z : Space => κ a * Θ a z)
          (κ a • fderiv ℝ (Θ a) y) y :=
        ((hy a (0 : Space)).2).hasFDerivAt.const_mul (κ a)
      have hf (a : Fin n) :
          fderiv ℝ (fun z : Space => κ a * Θ a z) y = κ a • fderiv ℝ (Θ a) y := (hd a).fderiv
      rw [hΦdef, fderiv_fun_sum (fun a _ => (hd a).differentiableAt)]
      simp only [hf, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- **Mixed partials commute wherever all components are nonzero** — for every
field count `n`.  This is the exact invariant the spinor carrier cannot
change: at any point `x` with `ψ a x ≠ 0` for all `a`, the decoded field has
`∂ᵢuⱼ = ∂ⱼuᵢ` for all coordinate pairs.  At `n = 1` this reproves
`madelung_decoder_mixed_partial_comm` at the origin through the combined-phase
mechanism. -/
theorem madelung_multi_decoder_mixed_partial_comm (n : ℕ) (κ : Fin n → ℝ)
    (ψ : Fin n → (Space → ℂ)) (hψ : ∀ a, ContDiff ℝ ∞ (ψ a))
    {x : Space} (hx : ∀ a, ψ a x ≠ 0) (u : VelocityField)
    (hdec : MadelungMultiInitialDecoder n κ ψ u) (i j : Fin 3) :
    fderiv ℝ (fun y : Space => u y j) x (basisVector i) =
      fderiv ℝ (fun y : Space => u y i) x (basisVector j) := by
  obtain ⟨Φ, hΦc, hev⟩ := madelung_multi_decoder_locally_exact n κ ψ hψ hx u hdec
  have heq (k : Fin 3) : (fun y : Space => u y k) =ᶠ[nhds x]
      fun y : Space => fderiv ℝ Φ y (basisVector k) := hev.mono (fun y hy => hy k)
  have hΦ2 : ContDiffAt ℝ 2 Φ x := hΦc.of_le (by simp)
  have hL : fderiv ℝ (fun y : Space => u y j) x (basisVector i) =
      fderiv ℝ (fun y : Space => fderiv ℝ Φ y (basisVector j)) x (basisVector i) := by
    rw [(heq j).fderiv_eq]
  have hR : fderiv ℝ (fun y : Space => u y i) x (basisVector j) =
      fderiv ℝ (fun y : Space => fderiv ℝ Φ y (basisVector i)) x (basisVector j) := by
    rw [(heq i).fderiv_eq]
  rw [hL, hR]
  exact hΦ2.hasSymmetricMixedPartialAt i j

/-- **The curl of a nonvanishing spinor decoding vanishes pointwise** at every
`x` with `ψ a x ≠ 0` for all `a`: the decoded field agrees eventually with a
gradient, and `staticCurl` of a gradient vanishes at the point.  The invariant
the pair carrier cannot carry is therefore the rotational content of
`rotationalDatum`: curl concentrates only where components vanish. -/
theorem madelung_multi_decoder_staticCurl_eq_zero (n : ℕ) (κ : Fin n → ℝ)
    (ψ : Fin n → (Space → ℂ)) (hψ : ∀ a, ContDiff ℝ ∞ (ψ a))
    {x : Space} (hx : ∀ a, ψ a x ≠ 0) (u : VelocityField)
    (hdec : MadelungMultiInitialDecoder n κ ψ u) : staticCurl u x = 0 := by
  obtain ⟨Φ, hΦc, hev⟩ := madelung_multi_decoder_locally_exact n κ ψ hψ hx u hdec
  have hΦ2 : ContDiffAt ℝ 2 Φ x := hΦc.of_le (by simp)
  have hg : DifferentiableAt ℝ (fun y : Space => staticGradient Φ y) x := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ Φ) x := hΦ2.fderiv_right le_rfl
    have hdiff : DifferentiableAt ℝ (fderiv ℝ Φ) x :=
      h1.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    refine differentiableAt_pi'' (fun i => ?_)
    have hcomp : (fun y : Space => (fun z : Space => staticGradient Φ z) y i) =
        ((ContinuousLinearMap.apply ℝ ℝ (basisVector i) :
            (Space →L[ℝ] ℝ) →L[ℝ] ℝ) ∘ (fderiv ℝ Φ)) := rfl
    rw [hcomp]
    exact (ContinuousLinearMap.apply ℝ ℝ (basisVector i)).differentiableAt.comp x hdiff
  have hge : u =ᶠ[nhds x] fun y : Space => staticGradient Φ y :=
    hev.mono (fun y hy => funext hy)
  have hfdu : fderiv ℝ u x = fderiv ℝ (fun y : Space => staticGradient Φ y) x := hge.fderiv_eq
  have hc : staticCurl u x = staticCurl (fun y : Space => staticGradient Φ y) x := by
    unfold staticCurl
    rw [hfdu]
  rw [hc, staticCurl_staticGradient_eq_zero Φ x hΦ2]

/-! ## Kernel-falsification of the spinor lift of the rotational datum -/

/-- **No `n`-field Madelung lift of `rotationalDatum lam` at nonvanishing
amplitude, for any `n`** (`lam > 0`): the two mixed partials of the datum at
the origin are `lam` and `-lam`, while any all-nonzero decoding has commuting
mixed partials by `madelung_multi_decoder_mixed_partial_comm`; the datum's
second curl component at the origin is `∂₀u₁ - ∂₁u₀ = 2·lam`.  The `n = 1` instance is the scalar wall
(`no_scalar_madelung_initial_lift_of_rotational_data`); `n = 2` closes the
spinor jump (see `no_two_field_madelung_initial_lift_of_rotational_data`);
`n = 0` forces the zero field against `rotationalDatum_ne_zero` through the
same commutation. -/
theorem no_multi_madelung_initial_lift_of_rotational_data (n : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    ¬ ∃ (κ : Fin n → ℝ) (ψ : Fin n → (Space → ℂ)), (∀ a, ContDiff ℝ ∞ (ψ a)) ∧
      (∀ a, ψ a 0 ≠ 0) ∧ MadelungMultiInitialDecoder n κ ψ ⇑(rotationalDatum lam) := by
  intro hex
  obtain ⟨κ, ψ, hψ, h0, hdec⟩ := hex
  have h := madelung_multi_decoder_mixed_partial_comm n κ ψ hψ h0
    (⇑(rotationalDatum lam)) hdec 0 1
  rw [fderiv_rotationalDatum_one_zero, fderiv_rotationalDatum_zero_one] at h
  linarith

/-- **The n = 1 → n = 2 jump is settled NEGATIVE for rotational data at
nonvanishing amplitude:** no two-component smooth spinor with both components
nonzero at the origin decodes `rotationalDatum lam` for `lam > 0`.  Named
next obstruction (not closed here): a lift must vanish one component at the
evaluation region, where the logarithmic derivative becomes a closed
*non-exact* form — quantized circulation about the joint zero locus, the
`unitVortex` regime of `QuantumVortexRegularity`. -/
theorem no_two_field_madelung_initial_lift_of_rotational_data (lam : ℝ) (hlam : 0 < lam) :
    ¬ ∃ (κ : Fin 2 → ℝ) (ψ : Fin 2 → (Space → ℂ)), (∀ a, ContDiff ℝ ∞ (ψ a)) ∧
      ψ 0 0 ≠ 0 ∧ ψ 1 0 ≠ 0 ∧ MadelungSpinorInitialDecoder κ ψ ⇑(rotationalDatum lam) := by
  intro hex
  obtain ⟨κ, ψ, hψ, h00, h01, hdec⟩ := hex
  refine no_multi_madelung_initial_lift_of_rotational_data 2 lam hlam
    ⟨κ, ψ, hψ, ?_, hdec⟩
  intro a
  fin_cases a <;> assumption

/-! ## Pairing-estimate extension to the multi-field decoder -/

private theorem norm_basisVector_one (i : Fin 3) : ‖basisVector i‖ = 1 := by
  rw [basisVector, Pi.norm_single, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]

/-- **Component bound for the multi-field decoder** (extension of
`norm_le_of_madelung_pairing` to this carrier): off the zeros,
`|u x i| ≤ Σₐ |κₐ| · ‖Dψₐ x‖ / ‖ψₐ x‖`.  The Euclidean pairing lemma itself
does not transfer to `Space = Fin 3 → ℝ`, whose norm is the sup norm — see the
`kineticEnergy` note in `Navier/Problem.lean` (Euclidean ≠ sup, provably) — so
the estimate is stated in the coordinate/sup-norm form the carrier actually
uses. -/
theorem madelung_multi_decoder_component_norm_le (n : ℕ) (κ : Fin n → ℝ)
    (ψ : Fin n → (Space → ℂ)) (u : VelocityField) (x : Space) (i : Fin 3)
    (hx : ∀ a, ψ a x ≠ 0) (hdec : MadelungMultiInitialDecoder n κ ψ u) :
    ‖u x i‖ ≤ ∑ a : Fin n, |κ a| * ‖fderiv ℝ (ψ a) x‖ / ‖ψ a x‖ := by
  rw [Real.norm_eq_abs, hdec x i]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  have h₁ : |(fderiv ℝ (ψ a) x (basisVector i) / ψ a x).im| ≤ ‖fderiv ℝ (ψ a) x‖ / ‖ψ a x‖ :=
    calc |(fderiv ℝ (ψ a) x (basisVector i) / ψ a x).im|
        ≤ ‖fderiv ℝ (ψ a) x (basisVector i) / ψ a x‖ := Complex.abs_im_le_norm _
      _ = ‖fderiv ℝ (ψ a) x (basisVector i)‖ / ‖ψ a x‖ := norm_div _ _
      _ ≤ ‖fderiv ℝ (ψ a) x‖ * ‖basisVector i‖ / ‖ψ a x‖ :=
          div_le_div_of_nonneg_right ((fderiv ℝ (ψ a) x).le_opNorm _) (norm_nonneg _)
      _ = ‖fderiv ℝ (ψ a) x‖ / ‖ψ a x‖ := by
          rw [norm_basisVector_one, mul_one]
  calc |κ a| * |(fderiv ℝ (ψ a) x (basisVector i) / ψ a x).im|
      ≤ |κ a| * (‖fderiv ℝ (ψ a) x‖ / ‖ψ a x‖) := mul_le_mul_of_nonneg_left h₁ (abs_nonneg (κ a))
    _ = |κ a| * ‖fderiv ℝ (ψ a) x‖ / ‖ψ a x‖ := mul_div _ _ _

/-- Sup-norm form: `‖u x‖ ≤ Σₐ |κₐ| · ‖Dψₐ x‖ / ‖ψₐ x‖` off the joint zeros. -/
theorem madelung_multi_decoder_norm_le (n : ℕ) (κ : Fin n → ℝ)
    (ψ : Fin n → (Space → ℂ)) (u : VelocityField) (x : Space)
    (hx : ∀ a, ψ a x ≠ 0) (hdec : MadelungMultiInitialDecoder n κ ψ u) :
    ‖u x‖ ≤ ∑ a : Fin n, |κ a| * ‖fderiv ℝ (ψ a) x‖ / ‖ψ a x‖ := by
  have hr : 0 ≤ ∑ a : Fin n, |κ a| * ‖fderiv ℝ (ψ a) x‖ / ‖ψ a x‖ :=
    Finset.sum_nonneg fun a _ =>
      div_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hr).mpr fun i => ?_
  exact madelung_multi_decoder_component_norm_le n κ ψ u x i hx hdec

end Navier.Analysis.MadelungSpinorDecoder

#print axioms Navier.Analysis.MadelungSpinorDecoder.no_two_field_madelung_initial_lift_of_rotational_data
#print axioms Navier.Analysis.MadelungSpinorDecoder.no_multi_madelung_initial_lift_of_rotational_data
#print axioms Navier.Analysis.MadelungSpinorDecoder.madelung_multi_decoder_staticCurl_eq_zero
#print axioms
  Navier.Analysis.MadelungSpinorDecoder.madelung_multi_decoder_norm_le

#check @Navier.Analysis.MadelungSpinorDecoder.MadelungMultiInitialDecoder
#check @Navier.Analysis.MadelungSpinorDecoder.MadelungSpinorInitialDecoder
#check @Navier.Analysis.MadelungSpinorDecoder.madelung_multi_decoder_locally_exact
#check @Navier.Analysis.MadelungSpinorDecoder.madelung_multi_decoder_mixed_partial_comm
#check @Navier.Analysis.MadelungSpinorDecoder.no_multi_madelung_initial_lift_of_rotational_data
#check @Navier.Analysis.MadelungSpinorDecoder.no_two_field_madelung_initial_lift_of_rotational_data
#check @Navier.Analysis.MadelungSpinorDecoder.madelung_multi_decoder_staticCurl_eq_zero
#check @Navier.Analysis.MadelungSpinorDecoder.madelung_multi_decoder_norm_le
