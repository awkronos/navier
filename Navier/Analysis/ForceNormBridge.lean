import Navier.OfficialProblem
import Navier.Analysis.EnergyNormBridge

/-!
# The force clauses in Fefferman's Euclidean norms

`Navier.Space = Fin 3 → ℝ` inherits Mathlib's finite-product **supremum** norm
while Fefferman's clauses measure `R^3` in the **Euclidean** norm.  The energy
clauses and the whole-space *data* decay clause were transported by
`Analysis.EnergyOfficialClause` and
`Analysis.EnergyNormBridge.feffermanRapidDecayBound_iff_fullyEuclidean`.  This
file transports the last clauses that discrepancy reached: the **force** decay
predicates `Navier.ForcedDataRapidDecay` (clause (5)) and
`Navier.PeriodicForcedDataRapidDecay` (clauses (8)--(9)).

## Why the force clauses were harder than the data clause

The data clause differentiates a map `Space → Space`, so its derivative bundle
has `Space` in every argument slot and the value.  The force clauses
differentiate on `ℝ × Space`, so their bundles are multilinear on the *product*
`ℝ × Space`, and the inherited operator norm

`‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2) _ (t, x)‖`

measures three separate things in the inherited norm: the spacetime weight
`(1 + ‖x‖ + t) ^ K`, the `n` argument slots, and the value.  Only the value half
was previously covered
(`EnergyNormBridge.officialEuclideanNorm_apply_le_sqrt_three_mul_opNorm`).

## Fefferman does not pick a spacetime slot norm, so we do not either

Fefferman's clause bounds coordinate derivatives, so his wording fixes the
Euclidean norm on the `R^3` *factor* but says nothing about how a spacetime
slot `(s, y) : ℝ × Space` should be measured.  Committing to one choice here
would smuggle a convention into a residual that is supposed to be about
`R^3` alone.  So the transports below are stated for an arbitrary `SlotNorm` —
any measurement pinched between the inherited product norm and `√3` times it —
and `officialEuclideanSlotNorm` is only one inhabitant.  `slotNorm_irrelevant`
records that the resulting decay class does not depend on the choice.

## What is and is not closed here

Closed: both force decay predicates are **equivalent** to fully Euclidean
forms (`forcedDataRapidDecay_iff_official`,
`periodicForcedDataRapidDecay_iff_official`), and Fefferman's alternatives C and
D are unchanged when the Euclidean force predicate is substituted
(`wholeSpaceBreakdown_iff_official`, `periodicBreakdown_iff_official`).  Every
constant is exhibited: `√3 ^ (K + 1)` forward, `√3 ^ n` backward, each a power
of the single attained pointwise factor of
`EnergyNormBridge.officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness`, so
none of them is proof slack.

Not closed, and untouched: Fefferman writes the force clause in coordinate
multi-index partial derivatives, not in total Fréchet bundles.  Everything below
compares two *measurements* of one fixed bundle and never changes which map is
differentiated, so the `forceFrechetCoordinatewiseEquivalence` and
`problemFrechetCoordinatePDEEquivalence` residuals are unaffected.  No a priori
estimate, and no analytic property of any force, is proved here.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ForceNormBridge

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.EnergyNormBridge

/-- `1 ≤ √3`, used to absorb the untouched time coordinate of a spacetime slot
into the spatial dimension factor. -/
theorem one_le_sqrt_three : (1 : ℝ) ≤ Real.sqrt 3 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by norm_num)

/-! ### Spacetime slot measurements compatible with Fefferman's spatial norm -/

/-- A way of measuring a spacetime derivative slot `(s, y) : ℝ × Space` that is
compatible with replacing the inherited sup norm on `Space` by Fefferman's
Euclidean norm: it dominates the inherited product norm and is dominated by
`√3` times it, exactly as `officialEuclideanNorm` is on `Space` itself.

Fefferman's text pins the norm on the `R^3` factor but not on spacetime slots,
so the transports below quantify over this structure rather than fixing one
representative; `slotNorm_irrelevant` shows the decay class is the same for
all of them. -/
structure SlotNorm where
  /-- The underlying measurement. -/
  toFun : ℝ × Space → ℝ
  /-- It is at least the inherited product norm. -/
  norm_le : ∀ z, ‖z‖ ≤ toFun z
  /-- It is at most `√3` times the inherited product norm. -/
  le_sqrt_three_mul : ∀ z, toFun z ≤ Real.sqrt 3 * ‖z‖

attribute [coe] SlotNorm.toFun

instance : CoeFun SlotNorm (fun _ => ℝ × Space → ℝ) := ⟨SlotNorm.toFun⟩

theorem SlotNorm.nonneg (N : SlotNorm) (z : ℝ × Space) : 0 ≤ N z :=
  le_trans (norm_nonneg z) (N.norm_le z)

/-- The slot measurement obtained by leaving the time coordinate alone and
replacing the inherited norm on the spatial factor by Fefferman's Euclidean
norm.  This is the canonical inhabitant of `SlotNorm`, but by
`slotNorm_irrelevant` nothing below depends on choosing it. -/
def officialEuclideanSlotNorm : SlotNorm where
  toFun z := max |z.1| (officialEuclideanNorm z.2)
  norm_le z := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact max_le_max le_rfl (norm_le_officialEuclideanNorm z.2)
  le_sqrt_three_mul z := by
    have hz : ‖z‖ = max ‖z.1‖ ‖z.2‖ := Prod.norm_def z
    have h1 : |z.1| ≤ ‖z‖ := by
      rw [hz, ← Real.norm_eq_abs]; exact le_max_left _ _
    have h2 : ‖z.2‖ ≤ ‖z‖ := by rw [hz]; exact le_max_right _ _
    refine max_le ?_ ?_
    · calc |z.1| ≤ ‖z‖ := h1
        _ = 1 * ‖z‖ := (one_mul _).symm
        _ ≤ Real.sqrt 3 * ‖z‖ :=
          mul_le_mul_of_nonneg_right one_le_sqrt_three (norm_nonneg z)
    · calc officialEuclideanNorm z.2 ≤ Real.sqrt 3 * ‖z.2‖ :=
          officialEuclideanNorm_le z.2
        _ ≤ Real.sqrt 3 * ‖z‖ := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)

@[simp] theorem officialEuclideanSlotNorm_apply (z : ℝ × Space) :
    officialEuclideanSlotNorm z = max |z.1| (officialEuclideanNorm z.2) := rfl

/-- **The slot inflation is not vacuous.**  A purely spatial slot is measured
strictly larger by `officialEuclideanSlotNorm` than by the inherited product
norm, so the `√3` in `SlotNorm.le_sqrt_three_mul` is doing real work rather
than padding an identity. -/
theorem norm_sq_lt_officialEuclideanSlotNorm_sq_witness :
    ∃ z : ℝ × Space, ‖z‖ ^ 2 < officialEuclideanSlotNorm z ^ 2 := by
  obtain ⟨x, hx⟩ := norm_sq_lt_officialEuclideanNorm_sq_witness
  refine ⟨(0, x), ?_⟩
  have h1 : ‖((0 : ℝ), x)‖ = ‖x‖ := by
    rw [Prod.norm_def]
    simp
  have h2 : officialEuclideanSlotNorm ((0 : ℝ), x) = officialEuclideanNorm x := by
    simp [max_eq_right (officialEuclideanNorm_nonneg x)]
  rw [h1, h2]
  exact hx

/-! ### The spacetime derivative bundle, measured Fefferman's way

`EnergyNormBridge.EuclideanBundleBound` compares the two norms of a bundle whose
slots are `Space`.  The force bundles have slots `ℝ × Space`, so both directions
are redone here against an arbitrary `SlotNorm`.
-/

/-- A fully Euclidean multilinear bound for a rank-`n` spacetime bundle: the
value is measured in Fefferman's Euclidean norm and the slots by `N`. -/
def SpacetimeBundleBound {n : ℕ} (N : SlotNorm)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Space) Space)
    (C : ℝ) : Prop :=
  ∀ v : Fin n → ℝ × Space,
    officialEuclideanNorm (L v) ≤ C * ∏ i : Fin n, N (v i)

/-- The inherited operator norm supplies a fully Euclidean spacetime bundle
bound at the cost of a single factor `√3`, independently of the rank: the value
costs `√3` and enlarging the slot measurements only weakens the conclusion. -/
theorem spacetimeBundleBound_sqrt_three_mul_opNorm {n : ℕ} (N : SlotNorm)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Space) Space) :
    SpacetimeBundleBound N L (Real.sqrt 3 * ‖L‖) := by
  intro v
  have hprod : (∏ i : Fin n, ‖v i‖) ≤ ∏ i : Fin n, N (v i) :=
    Finset.prod_le_prod (fun i _ => norm_nonneg (v i)) (fun i _ => N.norm_le (v i))
  refine (officialEuclideanNorm_apply_le_sqrt_three_mul_opNorm L v).trans ?_
  exact mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg L))

/-- Conversely a fully Euclidean spacetime bundle bound controls the inherited
operator norm at the rank-dependent cost `√3 ^ n`: each of the `n` slots must be
shrunk from `N` back to the inherited product norm. -/
theorem opNorm_le_of_spacetimeBundleBound {n : ℕ} (N : SlotNorm)
    {L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Space) Space} {C : ℝ}
    (hC : 0 ≤ C) (h : SpacetimeBundleBound N L C) :
    ‖L‖ ≤ Real.sqrt 3 ^ n * C := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 3) n) hC) fun v => ?_
  have hstep : (∏ i : Fin n, N (v i)) ≤ Real.sqrt 3 ^ n * ∏ i : Fin n, ‖v i‖ := by
    refine (Finset.prod_le_prod (fun i _ => N.nonneg (v i))
      (fun i _ => N.le_sqrt_three_mul (v i))).trans_eq ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  calc
    ‖L v‖ ≤ officialEuclideanNorm (L v) := norm_le_officialEuclideanNorm (L v)
    _ ≤ C * ∏ i : Fin n, N (v i) := h v
    _ ≤ C * (Real.sqrt 3 ^ n * ∏ i : Fin n, ‖v i‖) :=
      mul_le_mul_of_nonneg_left hstep hC
    _ = Real.sqrt 3 ^ n * C * ∏ i : Fin n, ‖v i‖ := by ring

/-! ### Weighted bundles

Both force clauses have the shape `weight * ‖bundle‖ ≤ C`, differing only in the
weight.  The two lemmas below carry an arbitrary weight through, so the
whole-space and periodic clauses are instances rather than repetitions.
-/

/-- **Forward weighted transport.**  If the inherited-norm bundle satisfies
`a * ‖L‖ ≤ C` and the Euclidean weight `b` is dominated by `c * a`, then the
fully Euclidean weighted multilinear bound holds with constant `c * √3 * C`. -/
theorem weightedBundle_official_le {n : ℕ} (N : SlotNorm)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Space) Space)
    {a b c C : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hba : b ≤ c * a)
    (hL : a * ‖L‖ ≤ C) (v : Fin n → ℝ × Space) :
    b * officialEuclideanNorm (L v) ≤
      c * Real.sqrt 3 * C * ∏ i : Fin n, N (v i) := by
  have hprod : (0 : ℝ) ≤ ∏ i : Fin n, N (v i) :=
    Finset.prod_nonneg fun i _ => N.nonneg (v i)
  calc
    b * officialEuclideanNorm (L v)
        ≤ c * a * (Real.sqrt 3 * ‖L‖ * ∏ i : Fin n, N (v i)) :=
      mul_le_mul hba (spacetimeBundleBound_sqrt_three_mul_opNorm N L v)
        (officialEuclideanNorm_nonneg _) (hb.trans hba)
    _ = c * Real.sqrt 3 * (a * ‖L‖) * ∏ i : Fin n, N (v i) := by ring
    _ ≤ c * Real.sqrt 3 * C * ∏ i : Fin n, N (v i) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL (mul_nonneg hc (Real.sqrt_nonneg 3))) hprod

/-- **Backward weighted transport.**  A fully Euclidean weighted multilinear
bound at the larger weight `b` recovers the inherited-norm bound at the smaller
weight `a`, at the rank cost `√3 ^ n`.  The weight is absorbed into the bundle
by scalar multiplication before `opNorm_le_of_spacetimeBundleBound` is applied. -/
theorem weightedOpNorm_le_of_official {n : ℕ} (N : SlotNorm)
    {L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Space) Space}
    {a b C : ℝ} (hab : a ≤ b) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (h : ∀ v : Fin n → ℝ × Space,
      b * officialEuclideanNorm (L v) ≤ C * ∏ i : Fin n, N (v i)) :
    a * ‖L‖ ≤ Real.sqrt 3 ^ n * C := by
  have hsmul : ∀ (c : ℝ) (y : Space),
      officialEuclideanNorm (c • y) = |c| * officialEuclideanNorm y := by
    intro c y
    simp [officialEuclideanNorm, officialEuclideanPoint, norm_smul,
      Real.norm_eq_abs]
  have hbound : SpacetimeBundleBound N (b • L) C := by
    intro v
    rw [ContinuousMultilinearMap.smul_apply, hsmul, abs_of_nonneg hb]
    exact h v
  have key := opNorm_le_of_spacetimeBundleBound N hC hbound
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb] at key
  exact le_trans (mul_le_mul_of_nonneg_right hab (norm_nonneg L)) key

/-! ### The whole-space spacetime weight -/

theorem officialWeight_nonneg (x : Space) {t : ℝ} (ht : 0 ≤ t) :
    (0 : ℝ) ≤ 1 + officialEuclideanNorm x + t := by
  have := officialEuclideanNorm_nonneg x
  linarith

/-- Fefferman's spacetime weight is dominated by `√3` times the inherited one.
The time coordinate is untouched by the norm change, so it is absorbed using
`1 ≤ √3` rather than by any spatial comparison. -/
theorem officialWeight_le (x : Space) {t : ℝ} (ht : 0 ≤ t) :
    1 + officialEuclideanNorm x + t ≤ Real.sqrt 3 * (1 + ‖x‖ + t) := by
  have h3 := one_le_sqrt_three
  have hx := officialEuclideanNorm_le x
  have htt : t ≤ Real.sqrt 3 * t := le_mul_of_one_le_left ht h3
  nlinarith [norm_nonneg x]

theorem officialWeight_pow_le (x : Space) {t : ℝ} (ht : 0 ≤ t) (K : ℕ) :
    (1 + officialEuclideanNorm x + t) ^ K ≤
      Real.sqrt 3 ^ K * (1 + ‖x‖ + t) ^ K := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (officialWeight_nonneg x ht) (officialWeight_le x ht) K

theorem weight_pow_le_officialWeight_pow (x : Space) {t : ℝ} (ht : 0 ≤ t) (K : ℕ) :
    (1 + ‖x‖ + t) ^ K ≤ (1 + officialEuclideanNorm x + t) ^ K := by
  refine pow_le_pow_left₀ (by have := norm_nonneg x; linarith) ?_ K
  have := norm_le_officialEuclideanNorm x
  linarith

/-! ### The force decay clauses -/

/-- The spacetime derivative bundle of a force at a nonnegative time, exactly
the object measured by `Navier.ForcedDataRapidDecay`. -/
def forceBundle (f : ForceField) (n : ℕ) (t : ℝ) (x : Space) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Space) Space :=
  iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
    nonnegativeSpacetime (t, x)

/-- Fefferman's whole-space force clause (5) with **every** `R^3` measurement
Euclidean: the spatial weight, the bundle value, and (via `N`) the spacetime
argument slots.  Compare `Navier.ForcedDataRapidDecay`, which measures all three
in the norm `Space` inherits. -/
def OfficialForcedDataRapidDecay (N : SlotNorm) (f : ForceField) : Prop :=
  SmoothForceOnNonnegativeTime f ∧
    ∀ (n K : ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ (x : Space) (v : Fin n → ℝ × Space),
        (1 + officialEuclideanNorm x + t) ^ K *
            officialEuclideanNorm (forceBundle f n t x v) ≤
          C * ∏ i : Fin n, N (v i)

/-- Fefferman's periodic force clauses (8)--(9) with the bundle value and
spacetime slots measured Fefferman's way.  Their weight `(1 + t) ^ K` involves
no spatial norm, so — unlike the whole-space clause — the weight needs no
transport at all and only the bundle contributes constants. -/
def OfficialPeriodicForcedDataRapidDecay (N : SlotNorm) (f : ForceField) : Prop :=
  SpatiallyPeriodicForce f ∧
    SmoothForceOnNonnegativeTime f ∧
      ∀ (n K : ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ t : ℝ, 0 ≤ t → ∀ (x : Space) (v : Fin n → ℝ × Space),
          (1 + t) ^ K * officialEuclideanNorm (forceBundle f n t x v) ≤
            C * ∏ i : Fin n, N (v i)

/-- **The whole-space force clause of the norm residual, discharged.**
Replacing the inherited sup norm by Fefferman's Euclidean norm in all three
places clause (5) uses it — spatial weight, bundle value, argument slots — does
not change the admissible-force class.

The forward direction spends `√3 ^ (K + 1)` (one factor per weight power, one on
the value) and the backward direction spends `√3 ^ n` (one per argument slot).
Both are powers of the single attained pointwise factor of
`EnergyNormBridge.officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness`, so
neither is slack; they are invisible in the statement only because the clause
quantifies existentially over `C`.  A consumer needing a pinned constant must
not route through here. -/
theorem forcedDataRapidDecay_iff_official (N : SlotNorm) (f : ForceField) :
    ForcedDataRapidDecay f ↔ OfficialForcedDataRapidDecay N f := by
  refine and_congr_right' ?_
  constructor
  · intro h n K
    obtain ⟨C, hC, hbound⟩ := h n K
    refine ⟨Real.sqrt 3 ^ K * Real.sqrt 3 * C,
      mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 3) K)
        (Real.sqrt_nonneg 3)) hC, fun t ht x v => ?_⟩
    exact weightedBundle_official_le N (forceBundle f n t x)
      (pow_nonneg (officialWeight_nonneg x ht) K)
      (pow_nonneg (Real.sqrt_nonneg 3) K)
      (officialWeight_pow_le x ht K) (hbound t ht x) v
  · intro h n K
    obtain ⟨C, hC, hbound⟩ := h n K
    refine ⟨Real.sqrt 3 ^ n * C,
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg 3) n) hC, fun t ht x => ?_⟩
    exact weightedOpNorm_le_of_official N (weight_pow_le_officialWeight_pow x ht K)
      (pow_nonneg (officialWeight_nonneg x ht) K) hC (hbound t ht x)

/-- **The periodic force clauses of the norm residual, discharged.**  Their
weight `(1 + t) ^ K` is norm-free, so the forward direction spends only the
single value factor `√3`; the backward direction still spends `√3 ^ n` on the
argument slots. -/
theorem periodicForcedDataRapidDecay_iff_official (N : SlotNorm) (f : ForceField) :
    PeriodicForcedDataRapidDecay f ↔ OfficialPeriodicForcedDataRapidDecay N f := by
  refine and_congr_right' (and_congr_right' ?_)
  constructor
  · intro h n K
    obtain ⟨C, hC, hbound⟩ := h n K
    refine ⟨Real.sqrt 3 * C, mul_nonneg (Real.sqrt_nonneg 3) hC,
      fun t ht x v => ?_⟩
    have hpow : (0 : ℝ) ≤ (1 + t) ^ K := pow_nonneg (by linarith) K
    simpa using weightedBundle_official_le N (forceBundle f n t x) hpow
      zero_le_one (by rw [one_mul]) (hbound t ht x) v
  · intro h n K
    obtain ⟨C, hC, hbound⟩ := h n K
    refine ⟨Real.sqrt 3 ^ n * C,
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg 3) n) hC, fun t ht x => ?_⟩
    exact weightedOpNorm_le_of_official N le_rfl
      (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + t) K) hC (hbound t ht x)

/-- **The spacetime slot convention is immaterial.**  Since every `SlotNorm`
transports to and from the single inherited-norm clause, any two of them define
the same admissible-force class.  This is why nothing above needed Fefferman's
text to pin a norm on spacetime slots, and why `officialEuclideanSlotNorm` is
recorded as a representative rather than as the definition. -/
theorem slotNorm_irrelevant (N M : SlotNorm) (f : ForceField) :
    OfficialForcedDataRapidDecay N f ↔ OfficialForcedDataRapidDecay M f :=
  (forcedDataRapidDecay_iff_official N f).symm.trans
    (forcedDataRapidDecay_iff_official M f)

theorem slotNorm_irrelevant_periodic (N M : SlotNorm) (f : ForceField) :
    OfficialPeriodicForcedDataRapidDecay N f ↔
      OfficialPeriodicForcedDataRapidDecay M f :=
  (periodicForcedDataRapidDecay_iff_official N f).symm.trans
    (periodicForcedDataRapidDecay_iff_official M f)

/-! ### The alternative surfaces are unchanged by the substitution

The transports above are only representation theorems until a consumer is
rewired.  The two statements below do that at the top level: Fefferman's
alternatives C and D are the *same proposition* whether their admissible-force
hypothesis is stated in the norm `Space` inherits or in Fefferman's Euclidean
norms.  No analytic content is added — a proof of either side is a proof of the
other — which is exactly what a discharged representation residual should mean.
-/

/-- Alternative C with Fefferman's Euclidean force clause substituted for the
inherited-norm one. -/
def OfficialWholeSpaceBreakdown (N : SlotNorm) : Prop :=
  ∀ nu : ℝ, 0 < nu →
    ∃ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ ∧
      ∃ f : ForceField, OfficialForcedDataRapidDecay N f ∧
        ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
          IsClassicalSolution nu f u₀ u p

/-- Alternative D with Fefferman's Euclidean periodic force clauses
substituted. -/
def OfficialPeriodicBreakdown (N : SlotNorm) : Prop :=
  ∀ nu : ℝ, 0 < nu →
    ∃ u₀ : VelocityField, PeriodicInitialDatum u₀ ∧
      ∃ f : ForceField, OfficialPeriodicForcedDataRapidDecay N f ∧
        ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
          IsPeriodicClassicalSolution nu f u₀ u p

/-- **Alternative C is norm-independent.**  The formal whole-space breakdown
surface does not change when its admissible-force clause is restated in
Fefferman's Euclidean norms. -/
theorem wholeSpaceBreakdown_iff_official (N : SlotNorm) :
    ProblemStatements.WholeSpaceBreakdown ↔ OfficialWholeSpaceBreakdown N := by
  simp only [ProblemStatements.WholeSpaceBreakdown, OfficialWholeSpaceBreakdown,
    forcedDataRapidDecay_iff_official N]

/-- **Alternative D is norm-independent**, for the same reason. -/
theorem periodicBreakdown_iff_official (N : SlotNorm) :
    ProblemStatements.PeriodicBreakdown ↔ OfficialPeriodicBreakdown N := by
  simp only [ProblemStatements.PeriodicBreakdown, OfficialPeriodicBreakdown,
    periodicForcedDataRapidDecay_iff_official N]

end Navier.Analysis.ForceNormBridge
