import Navier.Analysis.ViscosityAdmissibility

/-!
# Rapid-decay force transport across viscosity scaling

The viscosity force rescaling is

`f_a(t,x) = a^2 f(a t,x)`.

For `a > 0`, its spacetime dilation is a continuous linear map whose preimage
of the closed nonnegative-time half-space is that same half-space.  The exact
iterated within-derivative formula therefore gives the norm loss
`‖a^2‖ * ‖L_a‖^n`.  The time-polynomial weights cost at most the additional
factor `(1 + a⁻¹)^K`.  These explicit constants prove preservation of both
official rapid-decay force predicates.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff

namespace Navier.Analysis.ViscosityForceDecay

open Navier
open ViscosityTransport
open ViscosityAdmissibility

/-- The linear spacetime dilation `(t,x) ↦ (a*t,x)`. -/
def viscosityTimeCLM (a : ℝ) : (ℝ × Space) →L[ℝ] (ℝ × Space) :=
  (a • ContinuousLinearMap.fst ℝ ℝ Space).prod
    (ContinuousLinearMap.snd ℝ ℝ Space)

@[simp] theorem viscosityTimeCLM_apply
    (a t : ℝ) (x : Space) :
    viscosityTimeCLM a (t, x) = (a * t, x) := by
  rfl

/-- Positive time dilation preserves and reflects nonnegative time. -/
theorem viscosityTimeCLM_preimage_nonnegativeSpacetime
    (a : ℝ) (ha : 0 < a) :
    viscosityTimeCLM a ⁻¹' nonnegativeSpacetime = nonnegativeSpacetime := by
  ext z
  simp only [Set.mem_preimage, nonnegativeSpacetime, Set.mem_prod,
    Set.mem_Ici, Set.mem_univ, and_true]
  change 0 ≤ a * z.1 ↔ 0 ≤ z.1
  exact mul_nonneg_iff_of_pos_left ha

/-- The closed nonnegative-time spacetime domain has unique within
differentials. -/
theorem uniqueDiffOn_nonnegativeSpacetime :
    UniqueDiffOn ℝ nonnegativeSpacetime := by
  exact (uniqueDiffOn_Ici 0).prod
    (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set Space))

/-- Exact iterated within-derivative formula for the scaled force. -/
theorem iteratedFDerivWithin_viscosityScaledForce
    (a : ℝ) (ha : 0 < a) (f : ForceField)
    (hf : SmoothForceOnNonnegativeTime f)
    (n : ℕ) (z : ℝ × Space) (hz : z ∈ nonnegativeSpacetime) :
    iteratedFDerivWithin ℝ n
        (fun w : ℝ × Space => viscosityScaledForce a f w.1 w.2)
        nonnegativeSpacetime z =
      a ^ 2 •
        (iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
          nonnegativeSpacetime (viscosityTimeCLM a z)).compContinuousLinearMap
            (fun _ => viscosityTimeCLM a) := by
  have hpre := viscosityTimeCLM_preimage_nonnegativeSpacetime a ha
  have hmap : viscosityTimeCLM a z ∈ nonnegativeSpacetime := by
    rcases hz with ⟨ht, hx⟩
    exact ⟨mul_nonneg ha.le ht, hx⟩
  have hpreUnique :
      UniqueDiffOn ℝ (viscosityTimeCLM a ⁻¹' nonnegativeSpacetime) := by
    rw [hpre]
    exact uniqueDiffOn_nonnegativeSpacetime
  have hcompSmooth :
      ContDiffOn ℝ ∞
        ((fun w : ℝ × Space => f w.1 w.2) ∘ viscosityTimeCLM a)
        nonnegativeSpacetime := by
    rw [← hpre]
    exact hf.comp_continuousLinearMap (viscosityTimeCLM a)
  have hcomp :
      iteratedFDerivWithin ℝ n
          ((fun w : ℝ × Space => f w.1 w.2) ∘ viscosityTimeCLM a)
          nonnegativeSpacetime z =
        (iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
          nonnegativeSpacetime
          (viscosityTimeCLM a z)).compContinuousLinearMap
            (fun _ => viscosityTimeCLM a) := by
    have h :=
      (viscosityTimeCLM a).iteratedFDerivWithin_comp_right hf
        uniqueDiffOn_nonnegativeSpacetime hpreUnique hmap
        (show n ≤ ∞ from mod_cast le_top)
    simpa only [hpre] using h
  have hscaled :
      (fun w : ℝ × Space => viscosityScaledForce a f w.1 w.2) =
        a ^ 2 •
          ((fun w : ℝ × Space => f w.1 w.2) ∘ viscosityTimeCLM a) := by
    funext w
    rfl
  rw [hscaled]
  rw [iteratedFDerivWithin_const_smul_apply
    ((hcompSmooth z hz).of_le (show n ≤ ∞ from mod_cast le_top))
    uniqueDiffOn_nonnegativeSpacetime hz]
  rw [hcomp]

/-- Operator-norm consequence of the exact iterated derivative formula. -/
theorem norm_iteratedFDerivWithin_viscosityScaledForce_le
    (a : ℝ) (ha : 0 < a) (f : ForceField)
    (hf : SmoothForceOnNonnegativeTime f)
    (n : ℕ) (z : ℝ × Space) (hz : z ∈ nonnegativeSpacetime) :
    ‖iteratedFDerivWithin ℝ n
        (fun w : ℝ × Space => viscosityScaledForce a f w.1 w.2)
        nonnegativeSpacetime z‖ ≤
      (‖a ^ 2‖ * ‖viscosityTimeCLM a‖ ^ n) *
        ‖iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
          nonnegativeSpacetime (viscosityTimeCLM a z)‖ := by
  rw [iteratedFDerivWithin_viscosityScaledForce a ha f hf n z hz,
    norm_smul]
  have hcomp :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
        nonnegativeSpacetime (viscosityTimeCLM a z))
      (fun _ : Fin n => viscosityTimeCLM a)
  calc
    ‖a ^ 2‖ *
          ‖(iteratedFDerivWithin ℝ n
              (fun w : ℝ × Space => f w.1 w.2)
              nonnegativeSpacetime
              (viscosityTimeCLM a z)).compContinuousLinearMap
            (fun _ => viscosityTimeCLM a)‖
        ≤ ‖a ^ 2‖ *
            (‖iteratedFDerivWithin ℝ n
                (fun w : ℝ × Space => f w.1 w.2)
                nonnegativeSpacetime (viscosityTimeCLM a z)‖ *
              ∏ _ : Fin n, ‖viscosityTimeCLM a‖) :=
          mul_le_mul_of_nonneg_left hcomp (norm_nonneg _)
    _ = (‖a ^ 2‖ * ‖viscosityTimeCLM a‖ ^ n) *
          ‖iteratedFDerivWithin ℝ n
            (fun w : ℝ × Space => f w.1 w.2)
            nonnegativeSpacetime (viscosityTimeCLM a z)‖ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- Comparison of whole-space polynomial weights before and after positive
time dilation. -/
theorem wholeSpace_decayWeight_le
    (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    1 + ‖x‖ + t ≤ (1 + a⁻¹) * (1 + ‖x‖ + a * t) := by
  have hainv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hcancel : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
  nlinarith [norm_nonneg x]

/-- Comparison of periodic time-decay weights before and after positive time
dilation. -/
theorem periodic_decayWeight_le
    (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t) :
    1 + t ≤ (1 + a⁻¹) * (1 + a * t) := by
  have hainv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hcancel : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
  nlinarith

/-- Positive viscosity scaling preserves the complete whole-space force
rapid-decay predicate. -/
theorem forcedDataRapidDecay_viscosityScaled
    (a : ℝ) (ha : 0 < a) (f : ForceField)
    (hf : ForcedDataRapidDecay f) :
    ForcedDataRapidDecay (viscosityScaledForce a f) := by
  rcases hf with ⟨hsmooth, hdecay⟩
  constructor
  · exact smoothForce_viscosityScaled a ha f hsmooth
  · intro n K
    rcases hdecay n K with ⟨C, hC, hbound⟩
    let A : ℝ := ‖a ^ 2‖ * ‖viscosityTimeCLM a‖ ^ n
    let B : ℝ := (1 + a⁻¹) ^ K
    have hA : 0 ≤ A :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) n)
    have hB : 0 ≤ B := pow_nonneg (by positivity) K
    refine ⟨A * B * C, mul_nonneg (mul_nonneg hA hB) hC, ?_⟩
    intro t ht x
    have hz : (t, x) ∈ nonnegativeSpacetime := ⟨ht, Set.mem_univ x⟩
    have hd :=
      norm_iteratedFDerivWithin_viscosityScaledForce_le
        a ha f hsmooth n (t, x) hz
    rw [viscosityTimeCLM_apply] at hd
    have hweight := wholeSpace_decayWeight_le a ha t ht x
    have hpow :
        (1 + ‖x‖ + t) ^ K ≤
          ((1 + a⁻¹) * (1 + ‖x‖ + a * t)) ^ K := by
      gcongr
    have horig := hbound (a * t) (mul_nonneg ha.le ht) x
    calc
      (1 + ‖x‖ + t) ^ K *
            ‖iteratedFDerivWithin ℝ n
              (fun z : ℝ × Space => viscosityScaledForce a f z.1 z.2)
              nonnegativeSpacetime (t, x)‖
          ≤ (1 + ‖x‖ + t) ^ K *
              (A * ‖iteratedFDerivWithin ℝ n
                (fun z : ℝ × Space => f z.1 z.2)
                nonnegativeSpacetime (a * t, x)‖) := by
            exact mul_le_mul_of_nonneg_left (by simpa only [A] using hd)
              (pow_nonneg (by positivity) K)
      _ = A * ((1 + ‖x‖ + t) ^ K *
            ‖iteratedFDerivWithin ℝ n
              (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (a * t, x)‖) := by ring
      _ ≤ A * (((1 + a⁻¹) * (1 + ‖x‖ + a * t)) ^ K *
            ‖iteratedFDerivWithin ℝ n
              (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (a * t, x)‖) := by
            gcongr
      _ = (A * B) * ((1 + ‖x‖ + a * t) ^ K *
            ‖iteratedFDerivWithin ℝ n
              (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (a * t, x)‖) := by
            simp only [mul_pow, B]
            ring
      _ ≤ (A * B) * C := mul_le_mul_of_nonneg_left horig
            (mul_nonneg hA hB)
      _ = A * B * C := by ring

/-- Positive viscosity scaling preserves the periodic force rapid-decay
predicate, including spatial periodicity. -/
theorem periodicForcedDataRapidDecay_viscosityScaled
    (a : ℝ) (ha : 0 < a) (f : ForceField)
    (hf : PeriodicForcedDataRapidDecay f) :
    PeriodicForcedDataRapidDecay (viscosityScaledForce a f) := by
  rcases hf with ⟨hperiodic, hsmooth, hdecay⟩
  refine ⟨spatiallyPeriodicForce_viscosityScaled a ha f hperiodic,
    smoothForce_viscosityScaled a ha f hsmooth, ?_⟩
  intro n K
  rcases hdecay n K with ⟨C, hC, hbound⟩
  let A : ℝ := ‖a ^ 2‖ * ‖viscosityTimeCLM a‖ ^ n
  let B : ℝ := (1 + a⁻¹) ^ K
  have hA : 0 ≤ A :=
    mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) n)
  have hB : 0 ≤ B := pow_nonneg (by positivity) K
  refine ⟨A * B * C, mul_nonneg (mul_nonneg hA hB) hC, ?_⟩
  intro t ht x
  have hz : (t, x) ∈ nonnegativeSpacetime := ⟨ht, Set.mem_univ x⟩
  have hd :=
    norm_iteratedFDerivWithin_viscosityScaledForce_le
      a ha f hsmooth n (t, x) hz
  rw [viscosityTimeCLM_apply] at hd
  have hweight := periodic_decayWeight_le a ha t ht
  have hpow :
      (1 + t) ^ K ≤ ((1 + a⁻¹) * (1 + a * t)) ^ K := by
    gcongr
  have horig := hbound (a * t) (mul_nonneg ha.le ht) x
  calc
    (1 + t) ^ K *
          ‖iteratedFDerivWithin ℝ n
            (fun z : ℝ × Space => viscosityScaledForce a f z.1 z.2)
            nonnegativeSpacetime (t, x)‖
        ≤ (1 + t) ^ K *
            (A * ‖iteratedFDerivWithin ℝ n
              (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (a * t, x)‖) := by
          exact mul_le_mul_of_nonneg_left (by simpa only [A] using hd)
            (pow_nonneg (by positivity) K)
    _ = A * ((1 + t) ^ K *
          ‖iteratedFDerivWithin ℝ n
            (fun z : ℝ × Space => f z.1 z.2)
            nonnegativeSpacetime (a * t, x)‖) := by ring
    _ ≤ A * (((1 + a⁻¹) * (1 + a * t)) ^ K *
          ‖iteratedFDerivWithin ℝ n
            (fun z : ℝ × Space => f z.1 z.2)
            nonnegativeSpacetime (a * t, x)‖) := by
          gcongr
    _ = (A * B) * ((1 + a * t) ^ K *
          ‖iteratedFDerivWithin ℝ n
            (fun z : ℝ × Space => f z.1 z.2)
            nonnegativeSpacetime (a * t, x)‖) := by
          simp only [mul_pow, B]
          ring
    _ ≤ (A * B) * C := mul_le_mul_of_nonneg_left horig
          (mul_nonneg hA hB)
    _ = A * B * C := by ring

end Navier.Analysis.ViscosityForceDecay
