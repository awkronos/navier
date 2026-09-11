import Navier.Analysis.Covariance
import Navier.Analysis.ViscosityForceDecay
import Navier.Analysis.ViscosityTransport
import Navier.Analysis.ViscosityAdmissibility
import Navier.Analysis.EuclideanPDETransport
import Navier.Analysis.SelectedCandidateEnergy
import Navier.Analysis.ConstructedFiniteTimeObstruction
import Navier.Construction.R3FiniteEnergyComparison
import Navier.OfficialProblem

/-!
# Deadline-parameterized whole-space breakdown on the native carrier

For every prescribed deadline `T > 0` and every viscosity `nu > 0`, the
selected compact blowup candidate yields an admissible whole-space force
`f_{nu,T}` — smooth on the nonnegative-time half-space, rapidly decaying,
compactly supported in time, and nonzero strictly before `T` — for which no
global classical solution exists.  The proof is the exact rescaling bijection:
any hypothetical solution at force `f_{nu,T}` transports, first through the
viscosity bridge back to viscosity one and then through the parabolic bridge
back to the deadline-one force `nativeForce f`, producing the forbidden
global competitor of the selected candidate.

The exact support-endpoint law is `T * T0`, where `T0` is the raw candidate
force endpoint obtained from `R3CompactCandidate.force_time_support`; a bound
by `T` itself is NOT claimed and is false for the selected candidate.  What
is claimed is: `f_{nu,T} t = 0` for all `T0 * T ≤ t`, and `f_{nu,T}` is
nonzero at some spacetime point with time in `Ioo 0 T`.  The velocity
profile with speed blowup exactly as `t -> T-` and uniformly bounded energy
on `[0, T)` is the Euclidean-carrier package of
`Navier.Analysis.ScaledConstructedBreakdown`; this module transports the
force-data and nonexistence conjuncts to the official native carrier.
No unforced regularity and no spatial-periodicity preservation is claimed.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff
open Set MeasureTheory

namespace Navier.Breakdown.DeadlineParameterizedWholeSpaceBreakdown

open Navier
open Navier.Analysis.Covariance
open Navier.Analysis.ViscosityTransport
open Navier.Analysis.ViscosityForceDecay
open Navier.Analysis.ViscosityAdmissibility
open Navier.Analysis.EuclideanPDETransport

/-! ## The parabolic spacetime dilation as a continuous linear map -/

/-- The linear spacetime dilation `(t,x) ↦ (lambda^2 * t, lambda • x)`. -/
def parabolicCLM (lambda : ℝ) : (ℝ × Space) →L[ℝ] (ℝ × Space) :=
  (lambda ^ 2 • ContinuousLinearMap.fst ℝ ℝ Space).prod
    (lambda • ContinuousLinearMap.snd ℝ ℝ Space)

@[simp] theorem parabolicCLM_apply
    (lambda : ℝ) (t : ℝ) (x : Space) :
    parabolicCLM lambda (t, x) = (lambda ^ 2 * t, lambda • x) := by
  rfl

/-- Positive parabolic dilation preserves and reflects nonnegative time. -/
theorem parabolicCLM_preimage_nonnegativeSpacetime
    (lambda : ℝ) (hlambda : 0 < lambda) :
    parabolicCLM lambda ⁻¹' nonnegativeSpacetime = nonnegativeSpacetime := by
  ext z
  simp only [Set.mem_preimage, nonnegativeSpacetime, Set.mem_prod,
    Set.mem_Ici, Set.mem_univ, and_true]
  change 0 ≤ lambda ^ 2 * z.1 ↔ 0 ≤ z.1
  exact mul_nonneg_iff_of_pos_left (sq_pos_of_pos hlambda)

/-! ## Iterated within-derivative transfer and the rapid-decay predicate -/

/-- Exact iterated within-derivative formula for the parabolically scaled
force, mirroring `iteratedFDerivWithin_viscosityScaledForce`. -/
theorem iteratedFDerivWithin_parabolicScaledForce
    (lambda : ℝ) (hlambda : 0 < lambda) (f : ForceField)
    (hf : SmoothForceOnNonnegativeTime f)
    (n : ℕ) (z : ℝ × Space) (hz : z ∈ nonnegativeSpacetime) :
    iteratedFDerivWithin ℝ n
        (fun w : ℝ × Space => parabolicScaledForce lambda f w.1 w.2)
        nonnegativeSpacetime z =
      lambda ^ 3 •
        (iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
          nonnegativeSpacetime (parabolicCLM lambda z)).compContinuousLinearMap
            (fun _ => parabolicCLM lambda) := by
  have hpre := parabolicCLM_preimage_nonnegativeSpacetime lambda hlambda
  have hmap : parabolicCLM lambda z ∈ nonnegativeSpacetime := by
    rcases hz with ⟨ht, hx⟩
    exact ⟨mul_nonneg (sq_nonneg lambda) ht, hx⟩
  have hpreUnique :
      UniqueDiffOn ℝ (parabolicCLM lambda ⁻¹' nonnegativeSpacetime) := by
    rw [hpre]
    exact uniqueDiffOn_nonnegativeSpacetime
  have hcompSmooth :
      ContDiffOn ℝ ∞
        ((fun w : ℝ × Space => f w.1 w.2) ∘ parabolicCLM lambda)
        nonnegativeSpacetime := by
    rw [← hpre]
    exact hf.comp_continuousLinearMap (parabolicCLM lambda)
  have hcomp :
      iteratedFDerivWithin ℝ n
          ((fun w : ℝ × Space => f w.1 w.2) ∘ parabolicCLM lambda)
          nonnegativeSpacetime z =
        (iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
          nonnegativeSpacetime
          (parabolicCLM lambda z)).compContinuousLinearMap
            (fun _ => parabolicCLM lambda) := by
    have h :=
      (parabolicCLM lambda).iteratedFDerivWithin_comp_right hf
        uniqueDiffOn_nonnegativeSpacetime hpreUnique hmap
        (show n ≤ ∞ from mod_cast le_top)
    simpa only [hpre] using h
  have hscaled :
      (fun w : ℝ × Space => parabolicScaledForce lambda f w.1 w.2) =
        lambda ^ 3 •
          ((fun w : ℝ × Space => f w.1 w.2) ∘ parabolicCLM lambda) := by
    funext w
    rfl
  rw [hscaled]
  rw [iteratedFDerivWithin_const_smul_apply
    ((hcompSmooth z hz).of_le (show n ≤ ∞ from mod_cast le_top))
    uniqueDiffOn_nonnegativeSpacetime hz]
  rw [hcomp]

/-- Operator-norm consequence of the exact iterated derivative formula. -/
theorem norm_iteratedFDerivWithin_parabolicScaledForce_le
    (lambda : ℝ) (hlambda : 0 < lambda) (f : ForceField)
    (hf : SmoothForceOnNonnegativeTime f)
    (n : ℕ) (z : ℝ × Space) (hz : z ∈ nonnegativeSpacetime) :
    ‖iteratedFDerivWithin ℝ n
        (fun w : ℝ × Space => parabolicScaledForce lambda f w.1 w.2)
        nonnegativeSpacetime z‖ ≤
      (‖lambda ^ 3‖ * ‖parabolicCLM lambda‖ ^ n) *
        ‖iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
          nonnegativeSpacetime (parabolicCLM lambda z)‖ := by
  rw [iteratedFDerivWithin_parabolicScaledForce lambda hlambda f hf n z hz,
    norm_smul]
  have hcomp :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
        nonnegativeSpacetime (parabolicCLM lambda z))
      (fun _ : Fin n => parabolicCLM lambda)
  calc
    ‖lambda ^ 3‖ *
          ‖ContinuousMultilinearMap.compContinuousLinearMap
              (iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
                nonnegativeSpacetime (parabolicCLM lambda z))
              (fun _ => parabolicCLM lambda)‖
        ≤ ‖lambda ^ 3‖ *
            (‖iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
                nonnegativeSpacetime (parabolicCLM lambda z)‖ *
              ∏ _ : Fin n, ‖parabolicCLM lambda‖) :=
          mul_le_mul_of_nonneg_left hcomp (norm_nonneg _)
    _ = (‖lambda ^ 3‖ * ‖parabolicCLM lambda‖ ^ n) *
          ‖iteratedFDerivWithin ℝ n (fun w : ℝ × Space => f w.1 w.2)
            nonnegativeSpacetime (parabolicCLM lambda z)‖ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- Comparison of whole-space polynomial weights before and after positive
parabolic dilation.  The three summands of the raw weight are each absorbed
by a distinct term of the constant `1 + lambda⁻¹ + (lambda⁻¹) ^ 2`, so this
holds for every positive scale without any lower bound on `lambda`. -/
theorem parabolic_decayWeight_le
    (lambda : ℝ) (hlambda : 0 < lambda) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    1 + ‖x‖ + t ≤ (1 + lambda⁻¹ + (lambda⁻¹) ^ 2) *
      (1 + ‖lambda • x‖ + lambda ^ 2 * t) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
  have hc : lambda⁻¹ * lambda = 1 := inv_mul_cancel₀ hlambda.ne'
  have hsq : (lambda⁻¹) ^ 2 * lambda ^ 2 = 1 := by
    rw [← mul_pow, hc, one_pow]
  have hw' : lambda⁻¹ * (lambda * ‖x‖) = ‖x‖ := by
    rw [← mul_assoc, hc, one_mul]
  have hw : (lambda⁻¹) ^ 2 * (lambda ^ 2 * t) = t := by
    rw [← mul_assoc, hsq, one_mul]
  have hn : 0 ≤ lambda⁻¹ := inv_nonneg.mpr hlambda.le
  have hC1 : 1 ≤ (1 + lambda⁻¹ + (lambda⁻¹) ^ 2) * 1 := by
    nlinarith [sq_nonneg (lambda⁻¹)]
  have hC2 : lambda⁻¹ * (lambda * ‖x‖) ≤
      (1 + lambda⁻¹ + (lambda⁻¹) ^ 2) * (lambda * ‖x‖) := by
    nlinarith [norm_nonneg x, mul_nonneg hlambda.le (norm_nonneg x),
      mul_nonneg hn (mul_nonneg hlambda.le (norm_nonneg x)),
      mul_nonneg (sq_nonneg (lambda⁻¹)) (mul_nonneg hlambda.le (norm_nonneg x))]
  have hC3 : (lambda⁻¹) ^ 2 * (lambda ^ 2 * t) ≤
      (1 + lambda⁻¹ + (lambda⁻¹) ^ 2) * (lambda ^ 2 * t) := by
    have h1 : 0 ≤ lambda ^ 2 * t := mul_nonneg (sq_nonneg lambda) ht
    have h2 : 0 ≤ lambda⁻¹ * (lambda ^ 2 * t) := mul_nonneg hn h1
    nlinarith [h1, h2, mul_nonneg (sq_nonneg (lambda⁻¹)) h1]
  calc
    1 + ‖x‖ + t
        = 1 + lambda⁻¹ * (lambda * ‖x‖) +
            ((lambda⁻¹) ^ 2 * (lambda ^ 2 * t)) := by rw [hw', hw]
    _ ≤ (1 + lambda⁻¹ + (lambda⁻¹) ^ 2) * 1 +
            (1 + lambda⁻¹ + (lambda⁻¹) ^ 2) * (lambda * ‖x‖) +
            (1 + lambda⁻¹ + (lambda⁻¹) ^ 2) * (lambda ^ 2 * t) :=
          add_le_add (add_le_add hC1 hC2) hC3
    _ = (1 + lambda⁻¹ + (lambda⁻¹) ^ 2) *
            (1 + lambda * ‖x‖ + lambda ^ 2 * t) := by ring

/-- Positive parabolic scaling preserves `C∞` half-space regularity. -/
theorem smoothForce_parabolicScaled
    (lambda : ℝ) (hlambda : 0 < lambda) (f : ForceField)
    (hf : SmoothForceOnNonnegativeTime f) :
    SmoothForceOnNonnegativeTime (parabolicScaledForce lambda f) := by
  have hpre := parabolicCLM_preimage_nonnegativeSpacetime lambda hlambda
  have hbase : ContDiffOn ℝ ∞
      (fun w : ℝ × Space => f w.1 w.2) nonnegativeSpacetime := hf
  have hcomp : ContDiffOn ℝ ∞
      ((fun w : ℝ × Space => f w.1 w.2) ∘ parabolicCLM lambda)
      nonnegativeSpacetime := by
    rw [← hpre]
    exact hbase.comp_continuousLinearMap (parabolicCLM lambda)
  have hscaled : (fun z : ℝ × Space =>
      parabolicScaledForce lambda f z.1 z.2) =
      (lambda ^ 3 : ℝ) •
        ((fun w : ℝ × Space => f w.1 w.2) ∘ parabolicCLM lambda) := by
    funext w
    rfl
  show ContDiffOn ℝ ∞
      (fun z : ℝ × Space => parabolicScaledForce lambda f z.1 z.2)
      nonnegativeSpacetime
  rw [hscaled]
  exact hcomp.const_smul (lambda ^ 3)

/-- Positive parabolic scaling preserves the complete whole-space force
rapid-decay predicate. -/
theorem forcedDataRapidDecay_parabolicScaled
    (lambda : ℝ) (hlambda : 0 < lambda) (f : ForceField)
    (hf : ForcedDataRapidDecay f) :
    ForcedDataRapidDecay (parabolicScaledForce lambda f) := by
  rcases hf with ⟨hsmooth, hdecay⟩
  constructor
  · exact smoothForce_parabolicScaled lambda hlambda f hsmooth
  · intro n K
    rcases hdecay n K with ⟨C, hC, hbound⟩
    let A : ℝ := ‖lambda ^ 3‖ * ‖parabolicCLM lambda‖ ^ n
    let B : ℝ := (1 + lambda⁻¹ + (lambda⁻¹) ^ 2) ^ K
    have hA : 0 ≤ A :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) n)
    have hB : 0 ≤ B := pow_nonneg (by positivity) K
    refine ⟨A * B * C, mul_nonneg (mul_nonneg hA hB) hC, ?_⟩
    intro t ht x
    have hz : (t, x) ∈ nonnegativeSpacetime := ⟨ht, Set.mem_univ x⟩
    have hd :=
      norm_iteratedFDerivWithin_parabolicScaledForce_le
        lambda hlambda f hsmooth n (t, x) hz
    rw [parabolicCLM_apply] at hd
    have hweight := parabolic_decayWeight_le lambda hlambda t ht x
    have hpow :
        (1 + ‖x‖ + t) ^ K ≤
          ((1 + lambda⁻¹ + (lambda⁻¹) ^ 2) *
            (1 + ‖lambda • x‖ + lambda ^ 2 * t)) ^ K := by
      gcongr
    have horig := hbound (lambda ^ 2 * t) (mul_nonneg (sq_nonneg lambda) ht)
      (lambda • x)
    calc
      (1 + ‖x‖ + t) ^ K *
            ‖iteratedFDerivWithin ℝ n
              (fun z : ℝ × Space => parabolicScaledForce lambda f z.1 z.2)
              nonnegativeSpacetime (t, x)‖
          ≤ (1 + ‖x‖ + t) ^ K *
              (A * ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
                nonnegativeSpacetime (lambda ^ 2 * t, lambda • x)‖) := by
            exact mul_le_mul_of_nonneg_left (by simpa only [A] using hd)
              (pow_nonneg (by positivity) K)
      _ = A * ((1 + ‖x‖ + t) ^ K *
            ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (lambda ^ 2 * t, lambda • x)‖) := by ring
      _ ≤ A * (((1 + lambda⁻¹ + (lambda⁻¹) ^ 2) *
            (1 + ‖lambda • x‖ + lambda ^ 2 * t)) ^ K *
            ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (lambda ^ 2 * t, lambda • x)‖) := by
            gcongr
      _ = (A * B) * ((1 + ‖lambda • x‖ + lambda ^ 2 * t) ^ K *
            ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
              nonnegativeSpacetime (lambda ^ 2 * t, lambda • x)‖) := by
            simp only [mul_pow, B]
            ring
      _ ≤ (A * B) * C := mul_le_mul_of_nonneg_left horig
            (mul_nonneg hA hB)
      _ = A * B * C := by ring

/-! ## Time-support and pointwise-nonzero transport -/

/-- Positive time dilation transports future vanishing with endpoint divided
by the dilation rate. -/
theorem viscosityScaledForce_vanishing_from
    (a : ℝ) (ha : 0 < a) {f : ForceField} {S : ℝ}
    (hf : ∀ t : ℝ, S ≤ t → ∀ x : Space, f t x = 0) :
    ∀ t : ℝ, a⁻¹ * S ≤ t → ∀ x : Space,
      viscosityScaledForce a f t x = 0 := by
  intro t ht x
  show (a ^ 2 : ℝ) • f (a * t) x = 0
  have harg : S ≤ a * t := by
    have hcancel : a * (a⁻¹ * S) = S := by
      rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    rw [← hcancel]
    exact mul_le_mul_of_nonneg_left ht ha.le
  rw [hf (a * t) harg, smul_zero]

/-- Positive parabolic dilation transports future vanishing with endpoint
divided by the squared dilation rate. -/
theorem parabolicScaledForce_vanishing_from
    (lambda : ℝ) (hlambda : 0 < lambda) {f : ForceField} {S : ℝ}
    (hf : ∀ t : ℝ, S ≤ t → ∀ x : Space, f t x = 0) :
    ∀ t : ℝ, (lambda⁻¹) ^ 2 * S ≤ t → ∀ x : Space,
      parabolicScaledForce lambda f t x = 0 := by
  intro t ht x
  show (lambda ^ 3 : ℝ) • f (lambda ^ 2 * t) (lambda • x) = 0
  have hsq : lambda ^ 2 * (lambda⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hlambda.ne', one_pow]
  have harg : S ≤ lambda ^ 2 * t := by
    have hcancel : lambda ^ 2 * ((lambda⁻¹) ^ 2 * S) = S := by
      rw [← mul_assoc, hsq, one_mul]
    rw [← hcancel]
    exact mul_le_mul_of_nonneg_left ht (sq_nonneg lambda)
  rw [hf (lambda ^ 2 * t) harg, smul_zero]

/-- Nonzero values survive positive viscosity rescaling at the dilated time. -/
theorem viscosityScaledForce_nonzero
    (a : ℝ) (ha : a ≠ 0) (f : ForceField)
    (s : ℝ) (x : Space) (hsx : f s x ≠ 0) :
    viscosityScaledForce a f (a⁻¹ * s) x ≠ 0 := by
  intro h
  have harg : a * (a⁻¹ * s) = s := by
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  rw [viscosityScaledForce, harg] at h
  exact smul_ne_zero (pow_ne_zero 2 ha) hsx h

/-- Nonzero values survive positive parabolic rescaling at the dilated point. -/
theorem parabolicScaledForce_nonzero
    (lambda : ℝ) (hlambda : lambda ≠ 0) (f : ForceField)
    (s : ℝ) (x : Space) (hsx : f s x ≠ 0) :
    parabolicScaledForce lambda f ((lambda⁻¹) ^ 2 * s) (lambda⁻¹ • x) ≠ 0 := by
  intro h
  have hsq : lambda ^ 2 * (lambda⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hlambda, one_pow]
  have ha1 : lambda ^ 2 * ((lambda⁻¹) ^ 2 * s) = s := by
    rw [← mul_assoc, hsq, one_mul]
  have ha2 : lambda • (lambda⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ hlambda, one_smul]
  rw [parabolicScaledForce, ha1, ha2] at h
  exact smul_ne_zero (pow_ne_zero 3 hlambda) hsx h

/-- Positive parabolic force rescaling is an involution across inverse scales. -/
theorem parabolicScaledForce_inv
    (lambda : ℝ) (hlambda : lambda ≠ 0) (f : ForceField) :
    parabolicScaledForce lambda⁻¹ (parabolicScaledForce lambda f) = f := by
  funext t x
  have hsq : lambda ^ 2 * (lambda⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hlambda, one_pow]
  have ha1 : lambda ^ 2 * ((lambda⁻¹) ^ 2 * t) = t := by
    rw [← mul_assoc, hsq, one_mul]
  have ha2 : lambda • (lambda⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ hlambda, one_smul]
  have hsm : ((lambda⁻¹) ^ 3 * lambda ^ 3 : ℝ) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hlambda, one_pow]
  show ((lambda⁻¹) ^ 3 : ℝ) •
      (parabolicScaledForce lambda f) ((lambda⁻¹) ^ 2 * t) (lambda⁻¹ • x) = f t x
  rw [show (parabolicScaledForce lambda f) ((lambda⁻¹) ^ 2 * t) (lambda⁻¹ • x) =
        (lambda ^ 3 : ℝ) • f (lambda ^ 2 * ((lambda⁻¹) ^ 2 * t))
          (lambda • (lambda⁻¹ • x)) from rfl]
  rw [ha1, ha2, smul_smul, hsm, one_smul]

/-- Viscosity and parabolic force rescalings commute. -/
theorem viscosity_parabolicForce_commute
    (a lambda : ℝ) (f : ForceField) :
    viscosityScaledForce a (parabolicScaledForce lambda f) =
      parabolicScaledForce lambda (viscosityScaledForce a f) := by
  funext t x
  show (a ^ 2 : ℝ) • (parabolicScaledForce lambda f) (a * t) x =
      (lambda ^ 3 : ℝ) • (viscosityScaledForce a f)
        (lambda ^ 2 * t) (lambda • x)
  rw [show (parabolicScaledForce lambda f) (a * t) x =
        (lambda ^ 3 : ℝ) • f (lambda ^ 2 * (a * t)) (lambda • x) from rfl]
  rw [show (viscosityScaledForce a f) (lambda ^ 2 * t) (lambda • x) =
        (a ^ 2 : ℝ) • f (a * (lambda ^ 2 * t)) (lambda • x) from rfl]
  rw [smul_smul, smul_smul,
    show (a ^ 2 * lambda ^ 3 : ℝ) = lambda ^ 3 * a ^ 2 by ring,
    show lambda ^ 2 * (a * t) = a * (lambda ^ 2 * t) by ring]

/-! ## Schwartz datum transport at the zero datum -/

theorem scaledSchwartzVelocity_zero (c : ℝ) :
    scaledSchwartzVelocity c (0 : SchwartzVelocity) = 0 := by
  ext x
  rw [scaledSchwartzVelocity_apply]
  simp

theorem viscosityScaledSchwartzDatum_zero (a : ℝ) :
    viscosityScaledSchwartzDatum a (0 : SchwartzVelocity) = 0 :=
  smul_zero _

/-! ## Smoothness and energy transfer for the rescaled velocity -/

theorem smoothVelocityOnNonnegativeTime_parabolicScaled
    {lambda : ℝ} (hlambda : 0 < lambda) {u : VelocityEvolution}
    (hu : SmoothVelocityOnNonnegativeTime u) :
    SmoothVelocityOnNonnegativeTime (parabolicScaledVelocity lambda u) := by
  have hpre := parabolicCLM_preimage_nonnegativeSpacetime lambda hlambda
  have hub : ContDiffOn ℝ ∞
      (fun z : ℝ × Space => u z.1 z.2) nonnegativeSpacetime := hu
  have hcomp : ContDiffOn ℝ ∞
      ((fun w : ℝ × Space => u w.1 w.2) ∘ parabolicCLM lambda)
      nonnegativeSpacetime := by
    rw [← hpre]
    exact hub.comp_continuousLinearMap (parabolicCLM lambda)
  have hscaled : (fun z : ℝ × Space =>
      parabolicScaledVelocity lambda u z.1 z.2) =
      (lambda : ℝ) •
        ((fun w : ℝ × Space => u w.1 w.2) ∘ parabolicCLM lambda) := by
    funext w
    rfl
  show ContDiffOn ℝ ∞
      (fun z : ℝ × Space => parabolicScaledVelocity lambda u z.1 z.2)
      nonnegativeSpacetime
  rw [hscaled]
  exact hcomp.const_smul lambda

theorem smoothPressureOnNonnegativeTime_parabolicScaled
    {lambda : ℝ} (hlambda : 0 < lambda) {p : PressureEvolution}
    (hp : SmoothPressureOnNonnegativeTime p) :
    SmoothPressureOnNonnegativeTime (parabolicScaledPressure lambda p) := by
  have hpre := parabolicCLM_preimage_nonnegativeSpacetime lambda hlambda
  have hub : ContDiffOn ℝ ∞
      (fun z : ℝ × Space => p z.1 z.2) nonnegativeSpacetime := hp
  have hcomp : ContDiffOn ℝ ∞
      ((fun w : ℝ × Space => p w.1 w.2) ∘ parabolicCLM lambda)
      nonnegativeSpacetime := by
    rw [← hpre]
    exact hub.comp_continuousLinearMap (parabolicCLM lambda)
  have hscaled : (fun z : ℝ × Space =>
      parabolicScaledPressure lambda p z.1 z.2) =
      (lambda ^ 2 : ℝ) •
        ((fun w : ℝ × Space => p w.1 w.2) ∘ parabolicCLM lambda) := by
    funext w
    rfl
  show ContDiffOn ℝ ∞
      (fun z : ℝ × Space => parabolicScaledPressure lambda p z.1 z.2)
      nonnegativeSpacetime
  rw [hscaled]
  exact hcomp.const_smul (lambda ^ 2)

/-- The native Euclidean kinetic energy of the parabolically rescaled
velocity at time `t` is `lambda⁻¹` times the raw energy at `lambda^2 * t`. -/
theorem kineticEnergy_parabolicScaled
    (lambda : ℝ) (hlambda : 0 < lambda)
    (u : VelocityEvolution) (t : ℝ) :
    kineticEnergy (parabolicScaledVelocity lambda u) t =
      lambda⁻¹ * kineticEnergy u (lambda ^ 2 * t) := by
  have hci : 0 < (lambda ^ 3)⁻¹ := inv_pos.mpr (pow_pos hlambda 3)
  have hdim : Module.finrank ℝ Space = 3 := by
    rw [Module.finrank_fin_fun]
  have hpoint : (fun x : Space =>
      ∑ i : Fin 3, (parabolicScaledVelocity lambda u t x i) ^ 2) =
      fun x : Space => (lambda ^ 2 : ℝ) •
        ((fun y : Space => ∑ i : Fin 3, (u (lambda ^ 2 * t) y i) ^ 2)
          (lambda • x)) := by
    funext x
    simp only [parabolicScaledVelocity, Pi.smul_apply, smul_eq_mul, mul_pow,
      ← Finset.mul_sum]
  unfold kineticEnergy
  rw [hpoint, integral_smul,
    MeasureTheory.Measure.integral_comp_smul volume
      (fun x : Space => ∑ i : Fin 3, (u (lambda ^ 2 * t) x i) ^ 2) lambda,
    hdim]
  simp only [abs_of_pos hci]
  rw [smul_smul]
  congr 1
  field_simp

/-! ## The rescaling bijection for complete classical solutions -/

/-- THEOREM (forward half of the rescaling bijection).  A complete classical
solution at viscosity `nu` transports to a complete classical solution at the
same viscosity `nu` for the parabolically rescaled force, datum, velocity,
and pressure.  Positivity of `lambda` is used exactly where the time
derivative must preserve the nonnegative-time half-space. -/
theorem isClassicalSolution_parabolicScaled
    {lambda : ℝ} (hlambda : 0 < lambda) {nu : ℝ} {f : ForceField}
    {u₀ : SchwartzVelocity} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsClassicalSolution nu f u₀ u p) :
    IsClassicalSolution nu (parabolicScaledForce lambda f)
      (scaledSchwartzVelocity lambda u₀) (parabolicScaledVelocity lambda u)
      (parabolicScaledPressure lambda p) := by
  obtain ⟨hv, hp, h0, hin, heq, hfe, hube⟩ := h
  have hvs : SmoothVelocityOnNonnegativeTime (parabolicScaledVelocity lambda u) :=
    smoothVelocityOnNonnegativeTime_parabolicScaled hlambda hv
  have hps : SmoothPressureOnNonnegativeTime (parabolicScaledPressure lambda p) :=
    smoothPressureOnNonnegativeTime_parabolicScaled hlambda hp
  refine ⟨hvs, hps, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show (lambda : ℝ) • u (lambda ^ 2 * 0) (lambda • x) =
        scaledSchwartzVelocity lambda u₀ x
    have : lambda ^ 2 * (0 : ℝ) = 0 := by ring
    rw [this, h0 (lambda • x), scaledSchwartzVelocity_apply]
  · intro t ht x
    rw [divergence_scaled,
      hin (lambda ^ 2 * t) (mul_nonneg (sq_nonneg lambda) ht)]
    exact mul_zero _
  · exact satisfiesNavierStokes_scaled lambda hlambda nu f u p heq
  · intro t ht
    have hlt : 0 ≤ lambda ^ 2 * t := mul_nonneg (sq_nonneg lambda) ht
    have hf := hfe (lambda ^ 2 * t) hlt
    have hp : (fun x : Space =>
        ‖parabolicScaledVelocity lambda u t x‖ ^ 2) =
        fun x : Space => (lambda ^ 2 : ℝ) •
          ((fun y : Space => ‖u (lambda ^ 2 * t) y‖ ^ 2) (lambda • x)) := by
      funext x
      simp only [parabolicScaledVelocity, norm_smul, Real.norm_eq_abs,
        abs_of_pos hlambda, pow_two, smul_eq_mul]
      ring
    rw [hp]
    exact MeasureTheory.Integrable.smul (lambda ^ 2)
      ((MeasureTheory.integrable_comp_smul_iff volume
          (fun y : Space => ‖u (lambda ^ 2 * t) y‖ ^ 2) hlambda.ne').mpr hf)
  · obtain ⟨E, hE, hb⟩ := hube
    refine ⟨lambda⁻¹ * E, mul_pos (inv_pos.mpr hlambda) hE, ?_⟩
    intro t ht
    rw [kineticEnergy_parabolicScaled lambda hlambda u t]
    exact mul_lt_mul_of_pos_left
      (hb (lambda ^ 2 * t) (mul_nonneg (sq_nonneg lambda) ht))
      (inv_pos.mpr hlambda)

/-! ## The deadline-parameterized breakdown -/

/-- THEOREM (deadline-parameterized whole-space breakdown, native carrier).
For every viscosity `nu > 0` and every prescribed deadline `T > 0` there are
an admissible rapid-decay force `f` and an endpoint `T0 ≥ 0` such that `f`
vanishes for all `T0 * T ≤ t`, is nonzero at some spacetime point with time
in `Ioo 0 T`, and admits no global classical solution at viscosity `nu` from
the zero datum.  The support endpoint is `T0 * T`, where `T0` is the raw
selected-candidate force endpoint; no bound by `T` is asserted. -/
theorem wholeSpaceBreakdown_deadlineT (nu T : ℝ)
    (hnu : 0 < nu) (hT : 0 < T) :
    ∃ f : ForceField, ∃ T₀ : ℝ,
      0 ≤ T₀ ∧
      ForcedDataRapidDecay f ∧
      (∀ t : ℝ, T₀ * T ≤ t → ∀ x : Space, f t x = 0) ∧
      (∃ t ∈ Ioo (0 : ℝ) T, ∃ x : Space, f t x ≠ 0) ∧
      ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
        IsClassicalSolution nu f (0 : SchwartzVelocity) u p := by
  obtain ⟨_, _, fraw, h, _, _⟩ :=
    Navier.Analysis.SelectedCandidateEnergy.selected_compact_candidate_with_energy
  obtain ⟨T₀, hT₀, hraw⟩ := h.force_time_support
  obtain ⟨s, hs, y, hy⟩ :=
    Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_force_nonzero_before_one h
  have hn0 : 0 < nu * T := mul_pos hnu hT
  let mu : ℝ := (Real.sqrt (nu * T))⁻¹
  have hmu : 0 < mu := inv_pos.mpr (Real.sqrt_pos.mpr hn0)
  have hmu2 : mu ^ 2 = (nu * T)⁻¹ := by
    show ((Real.sqrt (nu * T))⁻¹) ^ 2 = (nu * T)⁻¹
    have hsq : Real.sqrt (nu * T) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    field_simp
    rw [Real.sq_sqrt hn0.le]
  have hmuinv2 : (mu⁻¹) ^ 2 = nu * T := by
    rw [inv_pow, hmu2]
    field_simp
  let fT : ForceField :=
      parabolicScaledForce mu (viscosityScaledForce nu (nativeForce fraw))
  have hnf : ForcedDataRapidDecay (nativeForce fraw) :=
    R3CompactCandidate.nativeForce_forcedDataRapidDecay h
  have hdecay : ForcedDataRapidDecay fT :=
    forcedDataRapidDecay_parabolicScaled mu hmu _
      (forcedDataRapidDecay_viscosityScaled nu hnu _ hnf)
  have hnfzero : ∀ t, T₀ ≤ t → ∀ x : Space, nativeForce fraw t x = 0 :=
    nativeForce_futureTimeSupport hraw
  have hvanish : ∀ t : ℝ, T₀ * T ≤ t → ∀ x : Space, fT t x = 0 := by
    have hvz := viscosityScaledForce_vanishing_from nu hnu hnfzero
    have hpz := parabolicScaledForce_vanishing_from mu hmu hvz
    have hlaw : (mu⁻¹) ^ 2 * (nu⁻¹ * T₀) = T₀ * T := by
      rw [hmuinv2]
      field_simp
    intro t ht x
    rw [← hlaw] at ht
    exact hpz t ht x
  have hnonzero : ∃ t ∈ Ioo (0 : ℝ) T, ∃ x : Space, fT t x ≠ 0 := by
    have hn1 : nativeForce fraw s (toNative y) ≠ 0 := by
      intro hz
      rw [nativeForce_value fraw s y] at hz
      apply_fun Navier.Analysis.EuclideanPDETransport.toEuclidean at hz
      simp only [toEuclidean_toNative, map_zero] at hz
      exact hy hz
    have hv1 := viscosityScaledForce_nonzero nu hnu.ne'
      (nativeForce fraw) s (toNative y) hn1
    have hp1 := parabolicScaledForce_nonzero mu hmu.ne'
      (viscosityScaledForce nu (nativeForce fraw)) (nu⁻¹ * s) (toNative y) hv1
    have harg : (mu⁻¹) ^ 2 * (nu⁻¹ * s) = T * s := by
      rw [hmuinv2]
      field_simp
    rw [harg] at hp1
    exact ⟨T * s, ⟨mul_pos hT hs.1, by simpa using mul_lt_mul_of_pos_left hs.2 hT⟩,
      mu⁻¹ • toNative y, hp1⟩
  have hnonexist : ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution nu fT (0 : SchwartzVelocity) u p := by
    rintro ⟨w, q, hw⟩
    have h1 := isClassicalSolution_viscosity_to_one nu hnu
      fT (0 : SchwartzVelocity) w q hw
    rw [viscosityScaledSchwartzDatum_zero] at h1
    have hforce : viscosityScaledForce nu⁻¹ fT =
        parabolicScaledForce mu (nativeForce fraw) := by
      show viscosityScaledForce nu⁻¹
          (parabolicScaledForce mu (viscosityScaledForce nu (nativeForce fraw))) = _
      rw [viscosity_parabolicForce_commute]
      rw [viscosityScaledForce_inv nu hnu.ne' (nativeForce fraw)]
    rw [hforce] at h1
    have h2 := isClassicalSolution_parabolicScaled (inv_pos.mpr hmu) h1
    rw [parabolicScaledForce_inv mu hmu.ne' (nativeForce fraw),
      scaledSchwartzVelocity_zero (mu⁻¹)] at h2
    exact Navier.Construction.ComparatorBridge.compact_candidate_excludes_global_solution h
      (IsClassicalSolution.toGlobalSolutionRn h2)
  exact ⟨fT, T₀, hT₀, hdecay, hvanish, hnonzero, hnonexist⟩

#print axioms iteratedFDerivWithin_parabolicScaledForce
#print axioms forcedDataRapidDecay_parabolicScaled
#print axioms isClassicalSolution_parabolicScaled
#print axioms wholeSpaceBreakdown_deadlineT

end Navier.Breakdown.DeadlineParameterizedWholeSpaceBreakdown
