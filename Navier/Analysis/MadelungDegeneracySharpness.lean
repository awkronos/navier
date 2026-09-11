import Navier.Analysis.QuantumVortexRegularity

/-!
# Sharpness of the forced Madelung degeneracy dichotomy

`Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_madelung_amplitude_or_derivative_degenerates`
forces, on the selected forced finite-energy candidate in every terminal window,
the disjunction "amplitude below the chosen floor, or spatial derivative above
the chosen cap".  This module exhibits explicit everywhere-nonzero
differentiable decoders, over any real inner-product space and against one
fixed unbounded velocity, showing that neither disjunct can be dropped by any
argument that uses only the pointwise Madelung pairing
(`Navier.Analysis.QuantumVortexRegularity.norm_le_of_madelung_pairing`):

* With amplitude identically one (`fun t => psi 1 t`), the pairing is exact,
  the amplitude never degenerates, and the decoded velocity is unbounded in
  every terminal window.  The natural strengthening
  "pairing + positive amplitude floor ⇒ bounded velocity" is FALSE; the
  derivative alternative is genuine and cannot be excluded by the pairing
  estimate alone.
* With collapsing amplitude (`fun t => psi (1 - t) t`), the pairing is exact
  against the same unbounded velocity, the wavefunction never vanishes on
  `[0, 1)`, and the spatial Fréchet derivative is uniformly bounded by `2R` on
  every fixed closed ball.  The dual natural strengthening
  "pairing + nonzero decoder + terminal velocity blowup ⇒ derivative
  degeneration" is also FALSE; the amplitude alternative is genuine.

Consequently any exclusion of the degeneracy alternative for the selected
candidate must use additional structure of the lift (for example a transport
or energy identity for the wavefunction itself), not the pairing estimate
alone.  The witnesses are constructive.  Tier: THEOREM; the raw
`#print axioms` output appended below uses only `propext`, `Classical.choice`,
and `Quot.sound`.
-/

open scoped Topology
open Filter


set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Navier.Analysis.MadelungDegeneracySharpness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The shared decoder family `ψ b t x = b · exp(‖x‖²/(1-t) · I)`. -/
def psi (b : ℝ) (t : ℝ) (x : E) : ℂ :=
  (b : ℂ) * Complex.exp ((‖x‖ ^ 2 / (1 - t) : ℝ) * Complex.I)

/-- The shared decoded velocity `u t x = (2/(1-t)) • x`. -/
def vel (t : ℝ) (x : E) : E := (2 / (1 - t : ℝ)) • x

theorem one_sub_ne_zero {t : ℝ} (ht : t ≠ 1) : (1 - t : ℝ) ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm ht)

/-- Amplitude of the shared decoder family. -/
theorem norm_psi (b : ℝ) (t : ℝ) (x : E) : ‖psi b t x‖ = |b| := by
  have he : ‖Complex.exp ((‖x‖ ^ 2 / (1 - t) : ℝ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  rw [psi, norm_mul, he, mul_one]
  exact by simp

private theorem hnorm_sq {x : E} :
    HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
  have hX := ((differentiableAt_id (x := x)).norm_sq (𝕜 := ℝ)).hasFDerivAt
  have heq : (fun y : E => ‖y‖ ^ 2) = fun y : E => ‖id y‖ ^ 2 := rfl
  rw [← heq] at hX
  rw [fderiv_norm_sq_apply] at hX
  exact hX

private theorem hphase {t : ℝ} (ht : t ≠ 1) (x : E) :
    HasFDerivAt (fun y : E => ‖y‖ ^ 2 / (1 - t))
      ((2 / (1 - t) : ℝ) • innerSL ℝ x) x := by
  have h1t := one_sub_ne_zero ht
  have h := (hnorm_sq (x := x)).const_mul ((1 : ℝ) / (1 - t))
  have hfun : (fun y : E => ‖y‖ ^ 2 / (1 - t)) =ᶠ[𝓝 x]
      fun y => (1 : ℝ) / (1 - t) * ‖y‖ ^ 2 :=
    Eventually.of_forall fun y => by field_simp
  have h1 := h.congr_of_eventuallyEq hfun
  have hclm : ((1 / (1 - t) : ℝ) • (2 • innerSL ℝ x) : E →L[ℝ] ℝ) =
      (2 / (1 - t) : ℝ) • innerSL ℝ x := by
    ext d
    simp only [smul_apply, innerSL_apply_apply]
    ring
  rw [hclm] at h1
  exact h1

private theorem hexpStep (b : ℝ) (s : ℝ) :
    HasFDerivAt (fun r : ℝ => (b : ℂ) * Complex.exp ((r : ℝ) * Complex.I))
      ((Complex.I * ((b : ℂ) * Complex.exp ((s : ℝ) * Complex.I))) •
        (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)) s := by
  have hof : HasFDerivAt (fun r : ℝ => (r : ℂ)) Complex.ofRealCLM s :=
    ContinuousLinearMap.hasFDerivAt (f := Complex.ofRealCLM)
  have hI : HasFDerivAt (fun z : ℂ => Complex.I * z)
      ((Complex.I : ℂ) • (1 : ℂ →L[ℝ] ℂ)) (s : ℂ) := by
    have h0 := ContinuousLinearMap.hasFDerivAt
      (f := (Complex.I : ℂ) • (1 : ℂ →L[ℝ] ℂ)) (x := (s : ℂ))
    exact (h0 : HasFDerivAt _ _ _).congr_of_eventuallyEq
      (Eventually.of_forall fun z => by simp)
  have he0 := (hasFDerivAt_exp (𝕂 := ℝ) (𝔸 := ℂ) (x := Complex.I * (s : ℂ))).comp
    (x := (s : ℂ)) hI
  have he1 : HasFDerivAt (fun z : ℂ => Complex.exp (Complex.I * z))
      ((Complex.exp (Complex.I * (s : ℂ))) •
        ((Complex.I : ℂ) • (1 : ℂ →L[ℝ] ℂ))) (s : ℂ) := by
    have hclm : (NormedSpace.exp (Complex.I * (s : ℂ)) • (1 : ℂ →L[ℝ] ℂ))
        ∘L ((Complex.I : ℂ) • (1 : ℂ →L[ℝ] ℂ)) =
        (Complex.exp (Complex.I * (s : ℂ)) : ℂ) •
          ((Complex.I : ℂ) • (1 : ℂ →L[ℝ] ℂ)) := by
      ext z
      simp [Complex.exp_eq_exp_ℂ]
    have h := he0
    rw [hclm] at h
    exact h.congr_of_eventuallyEq
      (Eventually.of_forall fun z => by simp [Complex.exp_eq_exp_ℂ])
  have hb := he1.const_mul (b : ℂ)
  have hg := hb.comp (x := s) hof
  have hfun : (fun r : ℝ => (b : ℂ) * Complex.exp ((r : ℝ) * Complex.I)) =ᶠ[𝓝 s]
      fun r => (b : ℂ) * Complex.exp (Complex.I * (r : ℂ)) :=
    Eventually.of_forall fun r => by simp [mul_comm]
  have h1 := hg.congr_of_eventuallyEq hfun
  have hclm : (((b : ℂ) : ℂ) •
      ((Complex.exp (Complex.I * (s : ℂ)) : ℂ) •
        ((Complex.I : ℂ) • (1 : ℂ →L[ℝ] ℂ)))) ∘L Complex.ofRealCLM =
      (Complex.I * ((b : ℂ) * Complex.exp ((s : ℝ) * Complex.I))) •
        (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) := by
    ext r
    simp only [ContinuousLinearMap.comp_apply, smul_apply, Algebra.smul_def,
      Complex.ofRealCLM_apply]
    rw [show (Complex.I : ℂ) * (s : ℂ) = (s : ℂ) * Complex.I from mul_comm _ _]
    simp
    ring
  rw [hclm] at h1
  exact h1

/-- Real Fréchet derivative of the shared decoder family. -/
theorem hasFDerivAt_psi {b : ℝ} {t : ℝ} (ht : t ≠ 1) (x : E) :
    HasFDerivAt (psi b t)
      ((Complex.I * ((b : ℂ) * Complex.exp ((‖x‖ ^ 2 / (1 - t) : ℝ) * Complex.I))) •
        (Complex.ofRealCLM ∘L ((2 / (1 - t) : ℝ) • innerSL ℝ x))) x := by
  have h := (hexpStep b (‖x‖ ^ 2 / (1 - t))).comp (x := x) (hphase ht x)
  have hfun : psi b t =ᶠ[𝓝 x] fun y : E =>
      (b : ℂ) * Complex.exp ((‖y‖ ^ 2 / (1 - t) : ℝ) * Complex.I) :=
    Eventually.of_forall fun y => rfl
  have h1 := h.congr_of_eventuallyEq hfun
  have hclm : ((Complex.I * ((b : ℂ) *
      Complex.exp ((‖x‖ ^ 2 / (1 - t) : ℝ) * Complex.I))) •
      Complex.ofRealCLM) ∘L ((2 / (1 - t) : ℝ) • innerSL ℝ x) =
      (Complex.I * ((b : ℂ) *
        Complex.exp ((‖x‖ ^ 2 / (1 - t) : ℝ) * Complex.I))) •
        (Complex.ofRealCLM ∘L ((2 / (1 - t) : ℝ) • innerSL ℝ x)) := by
      ext d
      simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply]
  rw [hclm] at h1
  exact h1

/-- Closed form of the Fréchet derivative. -/
theorem fderiv_psi (b : ℝ) {t : ℝ} (ht : t ≠ 1) (x d : E) :
    fderiv ℝ (psi b t) x d =
      Complex.I * (b : ℂ) *
        (Complex.exp ((‖x‖ ^ 2 / (1 - t) : ℝ) * Complex.I) : ℂ) *
        (↑(2 / (1 - t) * inner ℝ x d) : ℂ) := by
  have h1t := one_sub_ne_zero ht
  rw [(hasFDerivAt_psi ht x).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    Algebra.smul_def, Complex.ofRealCLM_apply]
  rw [Algebra.algebraMap_self_apply]
  rw [Algebra.algebraMap_self_apply]
  ring

/-- Exact pairing value. -/
theorem psi_pairing (b : ℝ) (hb : b ≠ 0) {t : ℝ} (ht : t ≠ 1) (x d : E) :
    (fderiv ℝ (psi b t) x d / psi b t x).im = 2 / (1 - t) * inner ℝ x d := by
  have h1t := one_sub_ne_zero ht
  rw [fderiv_psi b ht, psi]
  field_simp [Complex.ofReal_ne_zero.mpr hb, Complex.exp_ne_zero,
    Complex.ofReal_ne_zero.mpr h1t, h1t]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
    Complex.ofReal_re]
  field_simp [h1t]
  ring

/-- The shared velocity satisfies the dichotomy's directional pairing with
every nonzero member of the family (with `κ = 1`). -/
theorem vel_pairing (b : ℝ) (hb : b ≠ 0) {t : ℝ} (ht : t ≠ 1) (x d : E) :
    inner ℝ (vel t x) d = (fderiv ℝ (psi b t) x d / psi b t x).im := by
  rw [psi_pairing b hb ht, vel, inner_smul_left]
  rw [show (starRingEnd ℝ) (2 / (1 - t)) = (2 / (1 - t)) from rfl]

/-- Operator-norm bound for the spatial derivative of the family. -/
theorem norm_fderiv_psi (b : ℝ) {t : ℝ} (ht : t < 1) (x : E) :
    ‖fderiv ℝ (psi b t) x‖ ≤ |b| * (2 / (1 - t)) * ‖x‖ := by
  have h1 : 0 < 1 - t := sub_pos.mpr ht
  have hc : ‖Complex.I * ((b : ℂ) *
      Complex.exp ((‖x‖ ^ 2 / (1 - t) : ℝ) * Complex.I))‖ = |b| := by
    rw [norm_mul, Complex.norm_I, one_mul, norm_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact by simp
  rw [(hasFDerivAt_psi ht.ne x).fderiv]
  calc ‖(Complex.I * ((b : ℂ) *
        Complex.exp ((‖x‖ ^ 2 / (1 - t) : ℝ) * Complex.I))) •
      (Complex.ofRealCLM ∘L ((2 / (1 - t) : ℝ) • innerSL ℝ x))‖
      ≤ ‖Complex.I * ((b : ℂ) *
          Complex.exp ((‖x‖ ^ 2 / (1 - t) : ℝ) * Complex.I))‖
        * ‖Complex.ofRealCLM ∘L ((2 / (1 - t) : ℝ) • innerSL ℝ x)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ |b| * (1 * (2 / (1 - t) * ‖x‖)) := by
        rw [hc]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg b)
        refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        rw [Complex.ofRealCLM_norm, one_mul]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos two_pos h1)]
        rw [innerSL_apply_norm ℝ x, one_mul]
    _ = |b| * (2 / (1 - t)) * ‖x‖ := by ring

/-- Terminal-window unboundedness of the shared velocity. -/
theorem vel_unbounded_near_one (x₀ : E) (hx₀ : x₀ ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (M : ℝ) :
    ∃ t ∈ Set.Ico (0 : ℝ) 1, 1 - δ < t ∧ M < ‖vel t x₀‖ := by
  obtain hnx : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
  set t : ℝ := max (max (1 - δ / 2) ((1 : ℝ) / 2))
    (1 - ‖x₀‖ / (max M 0 + 2)) with htdef
  have hD : 0 < max M 0 + 2 := by positivity
  have hpos : 0 < ‖x₀‖ / (max M 0 + 2) := div_pos hnx hD
  have ht1 : t < 1 := by
    refine max_lt (max_lt ?_ (by norm_num)) ?_
    · linarith
    · linarith
  have ht0 : 0 ≤ t := by
    have h12 : (1 : ℝ) / 2 ≤ max (1 - δ / 2) ((1 : ℝ) / 2) :=
      le_max_right _ _
    have hA : max (1 - δ / 2) ((1 : ℝ) / 2) ≤ t := le_max_left _ _
    linarith
  have hsub : 0 < 1 - t := by linarith
  have hle : 1 - t ≤ ‖x₀‖ / (max M 0 + 2) := by
    have : 1 - ‖x₀‖ / (max M 0 + 2) ≤ t := le_max_right _ _
    linarith
  have hge : max M 0 + 2 ≤ ‖x₀‖ / (1 - t) := by
    refine (le_div_iff₀ hsub).mpr ?_
    have h : (1 - t) * (max M 0 + 2) ≤ ‖x₀‖ := (le_div_iff₀ hD).mp hle
    linarith
  refine ⟨t, ⟨ht0, ht1⟩, ?_, ?_⟩
  · have : 1 - δ / 2 ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  · rw [vel, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos two_pos hsub)]
    have hcalc : 2 * (max M 0 + 2) ≤ 2 * ‖x₀‖ / (1 - t) := by
      have h : 2 * (max M 0 + 2) ≤ 2 * (‖x₀‖ / (1 - t)) :=
        mul_le_mul_of_nonneg_left hge (by norm_num : (0 : ℝ) ≤ 2)
      have h2 : 2 * (‖x₀‖ / (1 - t)) = 2 * ‖x₀‖ / (1 - t) := by field_simp
      linarith
    have key : 2 * ‖x₀‖ / (1 - t) = (2 / (1 - t)) * ‖x₀‖ := by field_simp
    have hM0 : M ≤ max M 0 := le_max_left M 0
    linarith [hcalc, key, hM0]

/-- A positive amplitude floor is not an obstruction to the Madelung pairing
with a velocity that is unbounded in every terminal window. -/
theorem pairing_and_amplitude_floor_are_not_an_obstruction
    (x₀ : E) (hx₀ : x₀ ≠ 0) :
    ∃ (u : ℝ → E → E) (ψ : ℝ → E → ℂ),
      (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ x, DifferentiableAt ℝ (ψ t) x) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ x, 1 ≤ ‖ψ t x‖) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ x d,
        inner ℝ (u t x) d = (fderiv ℝ (ψ t) x d / ψ t x).im) ∧
      ∀ (δ : ℝ) (hδ : 0 < δ) (M : ℝ),
        ∃ t ∈ Set.Ico (0 : ℝ) 1, 1 - δ < t ∧ M < ‖u t x₀‖ := by
  refine ⟨vel, fun t => psi 1 t, ?_, ?_, ?_, vel_unbounded_near_one x₀ hx₀⟩
  · intro t ht x
    exact (hasFDerivAt_psi ht.2.ne x).differentiableAt
  · intro t _ x
    rw [norm_psi]
    simp
  · intro t ht x d
    exact vel_pairing 1 one_ne_zero ht.2.ne x d

/-- The natural strengthening "pairing + positive amplitude floor ⇒ bounded
velocity" is FALSE. -/
theorem not_pairing_floor_implies_bounded_velocity (x₀ : E) (hx₀ : x₀ ≠ 0) :
    ¬ (∀ (u : ℝ → E → E) (ψ : ℝ → E → ℂ) (c : ℝ), 0 < c →
        (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ x, c ≤ ‖ψ t x‖) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ x d,
          inner ℝ (u t x) d = (fderiv ℝ (ψ t) x d / ψ t x).im) →
        ∃ M, ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ x, ‖u t x‖ ≤ M) := by
  intro hall
  obtain ⟨M, hM⟩ := hall vel (fun t => psi 1 t) 1 zero_lt_one
    ⟨fun t _ x => by rw [norm_psi]; simp,
      fun t ht x d => vel_pairing 1 one_ne_zero ht.2.ne x d⟩
  obtain ⟨t, ht, _, hlt⟩ := vel_unbounded_near_one x₀ hx₀ 1 zero_lt_one M
  have hb := hM t ht x₀
  linarith

/-- The dual natural strengthening is also FALSE: nonzero decoder + terminal
velocity blowup need not degenerate in spatial derivative. -/
theorem unbounded_velocity_admits_bounded_derivative_decoder
    (R : ℝ) (hR : 0 < R) (x₀ : E) (hx₀ : x₀ ≠ 0)
    (hx₀R : x₀ ∈ Metric.closedBall (0 : E) R) :
    ∃ (u : ℝ → E → E) (ψ : ℝ → E → ℂ),
      (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ x, ψ t x ≠ 0) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ x ∈ Metric.closedBall (0 : E) R,
        DifferentiableAt ℝ (ψ t) x) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ x ∈ Metric.closedBall (0 : E) R,
        ‖fderiv ℝ (ψ t) x‖ ≤ 2 * R) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ x ∈ Metric.closedBall (0 : E) R, ∀ d,
        inner ℝ (u t x) d = (fderiv ℝ (ψ t) x d / ψ t x).im) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) 1, ‖ψ t x₀‖ = 1 - t) ∧
      ∀ (δ : ℝ) (hδ : 0 < δ) (M : ℝ),
        ∃ t ∈ Set.Ico (0 : ℝ) 1, 1 - δ < t ∧ M < ‖u t x₀‖ := by
  refine ⟨vel, fun t => psi (1 - t) t, ?nx, ?diff, ?db, ?pair, ?amp,
    vel_unbounded_near_one x₀ hx₀⟩
  · intro t ht x
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (one_sub_ne_zero ht.2.ne))
      (Complex.exp_ne_zero _)
  · intro t ht x _
    exact (hasFDerivAt_psi ht.2.ne x).differentiableAt
  · intro t ht x hx
    have hxb : ‖x‖ ≤ R := by
      rw [Metric.mem_closedBall] at hx
      rwa [dist_eq_norm, sub_zero] at hx
    have hbnd := norm_fderiv_psi (1 - t) ht.2 (x := x)
    have h1 : 0 < 1 - t := sub_pos.mpr ht.2
    have hcancel : |1 - t| * (2 / (1 - t)) * ‖x‖ = 2 * ‖x‖ := by
      rw [abs_of_pos h1]
      field_simp [one_sub_ne_zero ht.2.ne]
    linarith
  · intro t ht x _ d
    exact vel_pairing (1 - t) (one_sub_ne_zero ht.2.ne) ht.2.ne x d
  · intro t ht
    rw [norm_psi, abs_of_pos (sub_pos.mpr ht.2)]

end Navier.Analysis.MadelungDegeneracySharpness

#print axioms Navier.Analysis.MadelungDegeneracySharpness.pairing_and_amplitude_floor_are_not_an_obstruction
#print axioms Navier.Analysis.MadelungDegeneracySharpness.not_pairing_floor_implies_bounded_velocity
#print axioms Navier.Analysis.MadelungDegeneracySharpness.unbounded_velocity_admits_bounded_derivative_decoder
#print axioms Navier.Analysis.MadelungDegeneracySharpness.psi_pairing
#print axioms Navier.Analysis.MadelungDegeneracySharpness.vel_unbounded_near_one
