import Navier.Analysis.LeiLinBilinear

/-!
# The Picard fixed point behind the Lei-Lin threshold

Step 4 of the Lei-Lin assembly, in abstract form.  Once the bilinear estimate
of `LeiLinBilinear` is available with constant `C`, small-data global existence
is a fixed point of `x ↦ y + B(x,x)` on a ball whose radius is controlled by the
datum.  This module proves that fixed-point statement in an arbitrary Banach
space, using Mathlib's Banach fixed-point theorem on a complete subset
(`ContractingWith.efixedPoint'`) rather than a hand-rolled iteration.

`picard_small_data` : if `‖B(a,b)‖ ≤ C‖a‖‖b‖`, if `B` satisfies the bilinear
difference identity, and if `4C‖y‖ < 1`, then `x = y + B(x,x)` has a solution
with `‖x‖ ≤ 2‖y‖`.

With `C = 1/(4ν)` from `LeiLinBilinear.bilinear_mixed_le`, the smallness
condition `4C‖y‖ < 1` reads `‖y‖ < ν`, where `y` is the free evolution measured
in the mixed norm.  `LeiLinLinearEstimate.heat_contracts_Xm1` and
`heat_L1_time_eq` bound that mixed norm by `2‖u₀‖_{𝒳^{-1}}` (the `L^∞_t`
factor is at most `‖u₀‖_{𝒳^{-1}}` and the `ν L¹_t` factor is exactly
`‖u₀‖_{𝒳^{-1}}`), so this route yields the threshold
`‖u₀‖_{𝒳^{-1}} < ν/2`.  Lei-Lin's sharper `ν` comes from the time-integrated
form of the bilinear estimate rather than the fixed-time form proved in
`LeiLinBilinear`; the factor of two is an honest loss of this route, not a
transcription of the paper.

Scope.  This is the abstract Picard step.  Instantiating it requires the mixed
space `L^∞_t 𝒳^{-1} ∩ L¹_t 𝒳¹` as a Banach space together with the
time-integrated bilinear estimate; that instantiation is not performed here, so
no solution of Navier-Stokes is constructed and no global-regularity claim is
made.

Reference: Z. Lei and F. Lin, CPAM 64 (2011) 1297-1304; the abstract lemma is
the standard Picard/Kato scheme (P.-G. Lemarié-Rieusset, *Recent Developments
in the Navier-Stokes Problem*, Lemma 15.1).
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.LeiLinFixedPoint

/-- **Abstract small-data Picard fixed point.**

In a Banach space `X`, let `B : X → X → X` satisfy `‖B a b‖ ≤ C‖a‖‖b‖` together
with the bilinear difference identity
`B a a - B b b = B (a-b) a + B b (a-b)`.  If `4C‖y‖ < 1`, then `x = y + B(x,x)`
has a solution in the closed ball of radius `2‖y‖`.

The map `x ↦ y + B(x,x)` sends that ball to itself because
`‖y‖ + C(2‖y‖)² ≤ 2‖y‖` exactly when `4C‖y‖ ≤ 1`, and it is Lipschitz there
with constant `4C‖y‖ < 1`. -/
theorem picard_small_data {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {B : X → X → X} {C : ℝ} (hC : 0 < C)
    (hB : ∀ a b : X, ‖B a b‖ ≤ C * (‖a‖ * ‖b‖))
    (hdiff : ∀ a b : X, B a a - B b b = B (a - b) a + B b (a - b))
    (y : X) (hsmall : 4 * C * ‖y‖ < 1) :
    ∃ x : X, ‖x‖ ≤ 2 * ‖y‖ ∧ x = y + B x x := by
  classical
  set R : ℝ := 2 * ‖y‖ with hR
  set f : X → X := fun x => y + B x x with hf
  have hy0 : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
  have hRnn : (0:ℝ) ≤ R := by rw [hR]; linarith
  have hs : IsComplete (Metric.closedBall (0:X) R) := Metric.isClosed_closedBall.isComplete
  have hkey : (4 * C * ‖y‖) * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hsmall.le hy0
  have hmaps : Set.MapsTo f (Metric.closedBall (0:X) R) (Metric.closedBall (0:X) R) := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hx0 : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
    have h1 : ‖f x‖ ≤ ‖y‖ + C * (‖x‖ * ‖x‖) := by
      rw [hf]
      exact (norm_add_le _ _).trans (by linarith [hB x x])
    have h2 : C * (‖x‖ * ‖x‖) ≤ C * (R * R) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hxR hxR hx0 hRnn) hC.le
    have h3 : C * (R * R) ≤ ‖y‖ := by
      rw [show C * (R * R) = (4 * C * ‖y‖) * ‖y‖ by rw [hR]; ring]
      linarith
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [hR]
    linarith
  set K : NNReal := ⟨4 * C * ‖y‖, by positivity⟩ with hK
  have hKcoe : (K : ℝ) = 4 * C * ‖y‖ := rfl
  have hK1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe, NNReal.coe_one]
    exact hsmall
  have hlip : LipschitzWith K (Set.MapsTo.restrict f _ _ hmaps) := by
    refine LipschitzWith.of_dist_le_mul ?_
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have haR : ‖a‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using ha
    have hbR : ‖b‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hb
    have hfd : f a - f b = B (a - b) a + B b (a - b) := by
      rw [hf]
      simp only [add_sub_add_left_eq_sub]
      exact hdiff a b
    have hnorm : ‖f a - f b‖ ≤ C * (‖a - b‖ * ‖a‖) + C * (‖b‖ * ‖a - b‖) := by
      rw [hfd]
      exact (norm_add_le _ _).trans (add_le_add (hB _ _) (hB _ _))
    have hab : (0:ℝ) ≤ ‖a - b‖ := norm_nonneg _
    have hfinal : ‖f a - f b‖ ≤ (4 * C * ‖y‖) * ‖a - b‖ := by
      have hbound : C * (‖a - b‖ * ‖a‖) + C * (‖b‖ * ‖a - b‖)
          ≤ C * (‖a - b‖ * R) + C * (R * ‖a - b‖) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left haR hab) hC.le)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbR hab) hC.le)
      have hRR : C * (‖a - b‖ * R) + C * (R * ‖a - b‖) = (4 * C * ‖y‖) * ‖a - b‖ := by
        rw [hR]; ring
      linarith [hnorm, hbound, hRR.le, hRR.ge]
    simpa [Subtype.dist_eq, dist_eq_norm, hKcoe] using hfinal
  have hedist : edist (0:X) (f 0) ≠ ⊤ := edist_ne_top _ _
  have h0mem : (0:X) ∈ Metric.closedBall (0:X) R := by
    simpa [Metric.mem_closedBall] using hRnn
  refine ⟨ContractingWith.efixedPoint' f hs hmaps ⟨hK1, hlip⟩ 0 h0mem hedist, ?_, ?_⟩
  · have hmem := ContractingWith.efixedPoint_mem' hs hmaps ⟨hK1, hlip⟩ h0mem hedist
    simpa [Metric.mem_closedBall, dist_zero_right, hR] using hmem
  · have hfix := ContractingWith.efixedPoint_isFixedPt' hs hmaps ⟨hK1, hlip⟩ h0mem hedist
    exact hfix.symm

end Navier.Analysis.LeiLinFixedPoint

#print axioms Navier.Analysis.LeiLinFixedPoint.picard_small_data
