import Navier.Analysis.OfficialABEncoding

/-!
# Inherited sup-norm versus Euclidean norm: energy and derivative bundles

`Navier.Space = Fin 3 → ℝ` inherits Mathlib's finite-product **supremum** norm,
whereas Fefferman's clauses use the **Euclidean** norm on `R^3`.  This file
carries that single pointwise discrepancy up to integrability, to the uniform
energy bound, and — in the final section — to the operator norm of derivative
bundles, which is the last clause the
`currentSpaceNormEuclideanNormEquivalence` residual named.

## What changed, and why most of this file was rewritten

`Navier.kineticEnergy` is now defined as `∫ ∑ᵢ uᵢ²`, i.e. it is *already* the
Euclidean energy.  Consequently `officialKineticEnergy` and `kineticEnergy` are
provably **equal** (`officialKineticEnergy_eq_kineticEnergy`), and the former
`kineticEnergy_le_officialKineticEnergy` / `officialKineticEnergy_le_three_mul_
kineticEnergy` / `uniformlyBoundedEnergy_iff_official` trio degenerated into
`X ≤ X`, `X ≤ 3X` and `P ↔ P` — inequalities whose analytic-looking measurability
and integrability hypotheses did no work.  All three are now deleted in favour of
the equality: an inequality, or an `iff`, between two provably equal quantities
carries no information, and keeping one as a "transport shim" only disguises the
identity as an analytic step.  Consumers rewrite with
`officialKineticEnergy_eq_kineticEnergy` directly.

## Where the genuine content now lives

The surviving discrepancy is between the Euclidean `kineticEnergy` and the
**sup-norm** energy `supKineticEnergy = ∫ ‖u t x‖²`, which is the quantity that
`Navier.IsClassicalSolution.finite_energy` actually asserts integrable and that
`LerayWeak.UniformKineticBound` actually bounds.  That comparison is two-sided
but **asymmetric in the constant**: `supKineticEnergy ≤ kineticEnergy ≤
3 * supKineticEnergy`, and the factor `3` is attained
(`officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness`), so it cannot be
improved.  The strictness witness
(`norm_sq_lt_officialEuclideanNorm_sq_witness`) machine-checks that the two
norms really do differ, so none of the constants below is proof slack: each
transport is stated *with* its constant, rather than as an identity, precisely
because the pointwise gap is attained.

Nothing here proves an energy identity or any a priori estimate.  The remaining
representation step is to derive the slice measurability used below from the
official smooth spacetime solution predicate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.EnergyNormBridge

open Navier
open Navier.Analysis.OfficialABEncoding

/-- Fefferman's Euclidean kinetic-energy integral at one time. -/
def officialKineticEnergy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, officialEuclideanNorm (u t x) ^ 2

/-- The kinetic-energy integral in the norm `Space` actually inherits (the
finite-product supremum norm).  This is the integrand of
`Navier.IsClassicalSolution.finite_energy` and the quantity bounded by
`LerayWeak.UniformKineticBound`; it is *not* Fefferman's energy. -/
def supKineticEnergy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, ‖u t x‖ ^ 2

theorem continuous_officialEuclideanNorm :
    Continuous officialEuclideanNorm := by
  unfold officialEuclideanNorm officialEuclideanPoint
  fun_prop

/-- The inherited squared norm is bounded by the official squared norm. -/
theorem norm_sq_le_officialEuclideanNorm_sq (x : Space) :
    ‖x‖ ^ 2 ≤ officialEuclideanNorm x ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg x) (norm_le_officialEuclideanNorm x) 2

/-- In dimension three, the official squared norm is at most three times the
inherited squared norm. -/
theorem officialEuclideanNorm_sq_le_three_mul_norm_sq (x : Space) :
    officialEuclideanNorm x ^ 2 ≤ 3 * ‖x‖ ^ 2 := by
  calc
    officialEuclideanNorm x ^ 2 ≤
        (Real.sqrt 3 * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (officialEuclideanNorm_nonneg x)
        (officialEuclideanNorm_le x) 2
    _ = 3 * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- For a strongly measurable spatial field, the inherited and official
squared energy densities are integrable simultaneously. -/
theorem integrable_norm_sq_iff_officialEuclideanNorm_sq
    (f : Space → Space) (hf : AEStronglyMeasurable f) :
    Integrable (fun x => ‖f x‖ ^ 2) ↔
      Integrable (fun x => officialEuclideanNorm (f x) ^ 2) := by
  have hnorm :
      AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) :=
    hf.norm.pow 2
  have hoff :
      AEStronglyMeasurable
        (fun x => officialEuclideanNorm (f x) ^ 2) :=
    (continuous_officialEuclideanNorm.comp_aestronglyMeasurable hf).pow 2
  constructor
  · intro h
    apply (h.const_mul (3 : ℝ)).mono' hoff
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact officialEuclideanNorm_sq_le_three_mul_norm_sq (f x)
  · intro h
    apply h.mono' hnorm
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_sq_le_officialEuclideanNorm_sq (f x)

/-- The Euclidean norm squared equals the component-wise sum of squares. -/
theorem officialEuclideanNorm_sq_eq_sum_sq (x : Space) :
    officialEuclideanNorm x ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  simp [officialEuclideanNorm, officialEuclideanPoint,
    EuclideanSpace.real_norm_sq_eq]

/-- The sup norm squared is bounded by the sum of squares. -/
theorem norm_sq_le_sum_sq (x : Space) : ‖x‖ ^ 2 ≤ ∑ i : Fin 3, x i ^ 2 := by
  calc
    ‖x‖ ^ 2 ≤ officialEuclideanNorm x ^ 2 := norm_sq_le_officialEuclideanNorm_sq x
    _ = ∑ i : Fin 3, x i ^ 2 := officialEuclideanNorm_sq_eq_sum_sq x

/-! ### The two norms genuinely differ

The all-ones point is a single witness that settles both non-degeneracy
questions: it makes `norm_sq_le_officialEuclideanNorm_sq` strict, and it
*attains* the constant `3` in `officialEuclideanNorm_sq_le_three_mul_norm_sq`.
-/

/-- The inherited supremum norm of the all-ones point is `1`, not `√3`. -/
theorem norm_onesPoint : ‖(![1, 1, 1] : Space)‖ = 1 := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).2 ?_) ?_
  · intro i
    fin_cases i <;> simp
  · calc (1 : ℝ) = ‖(![1, 1, 1] : Space) 0‖ := by simp
      _ ≤ ‖(![1, 1, 1] : Space)‖ := norm_le_pi_norm _ 0

/-- **The sup/Euclidean gap is not vacuous.**  At the all-ones point the
inherited squared norm is `1` while the Euclidean squared norm is `3`, so
`norm_sq_le_officialEuclideanNorm_sq` is a strict inequality somewhere.  This is
the machine-checked reason the `currentSpaceNormEuclideanNormEquivalence`
residual of `Navier.Problem` may not be retired. -/
theorem norm_sq_lt_officialEuclideanNorm_sq_witness :
    ∃ x : Space, ‖x‖ ^ 2 < officialEuclideanNorm x ^ 2 := by
  refine ⟨![1, 1, 1], ?_⟩
  rw [norm_onesPoint, officialEuclideanNorm_sq_eq_sum_sq]
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-- **The dimension constant `3` is attained, hence sharp.**  No smaller
constant works in `officialEuclideanNorm_sq_le_three_mul_norm_sq`, so the
factor-`3` loss in `kineticEnergy_le_three_mul_supKineticEnergy` below is a real
feature of the encoding rather than proof slack. -/
theorem officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness :
    ∃ x : Space, officialEuclideanNorm x ^ 2 = 3 * ‖x‖ ^ 2 := by
  refine ⟨![1, 1, 1], ?_⟩
  rw [norm_onesPoint, officialEuclideanNorm_sq_eq_sum_sq]
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### Energy level

`kineticEnergy` is already Euclidean, so the comparison against
`officialKineticEnergy` is an identity.  The surviving comparison is against
`supKineticEnergy`.
-/

/-- **Fefferman's Euclidean energy is literally the project `kineticEnergy`.**
`kineticEnergy` integrates `∑ᵢ uᵢ²` and the squared Euclidean norm *is* that
sum, so no inequality, measurability hypothesis, or dimension constant is
involved.  This equality supersedes the former
`kineticEnergy_le_officialKineticEnergy` and
`officialKineticEnergy_le_three_mul_kineticEnergy`, which stated `X ≤ X` and
`X ≤ 3X` under hypotheses their proofs never used. -/
theorem officialKineticEnergy_eq_kineticEnergy (u : VelocityEvolution) (t : ℝ) :
    officialKineticEnergy u t = kineticEnergy u t := by
  simp only [officialKineticEnergy, kineticEnergy,
    officialEuclideanNorm_sq_eq_sum_sq]

/-- The sup-norm energy is dominated by the Euclidean energy at the **same**
constant.  Unlike the deleted `kineticEnergy_le_officialKineticEnergy`, this is
not a tautology: the two integrands differ, and
`norm_sq_lt_officialEuclideanNorm_sq_witness` shows the domination is somewhere
strict. -/
theorem supKineticEnergy_le_kineticEnergy
    (u : VelocityEvolution) (t : ℝ)
    (hmeas : AEStronglyMeasurable (u t))
    (hint : Integrable (fun x => ‖u t x‖ ^ 2)) :
    supKineticEnergy u t ≤ kineticEnergy u t := by
  have hsum : Integrable (fun x : Space => ∑ i : Fin 3, (u t x i) ^ 2) :=
    ((integrable_norm_sq_iff_officialEuclideanNorm_sq (u t) hmeas).1
      hint).congr
      (Filter.Eventually.of_forall fun x =>
        officialEuclideanNorm_sq_eq_sum_sq (u t x))
  unfold supKineticEnergy kineticEnergy
  exact integral_mono hint hsum fun x => norm_sq_le_sum_sq (u t x)

/-- The reverse domination costs exactly the dimension factor `3`, which
`officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness` shows is attained
pointwise and therefore not removable by a sharper argument. -/
theorem kineticEnergy_le_three_mul_supKineticEnergy
    (u : VelocityEvolution) (t : ℝ)
    (hmeas : AEStronglyMeasurable (u t))
    (hint : Integrable (fun x => ‖u t x‖ ^ 2)) :
    kineticEnergy u t ≤ 3 * supKineticEnergy u t := by
  have hsum : Integrable (fun x : Space => ∑ i : Fin 3, (u t x i) ^ 2) :=
    ((integrable_norm_sq_iff_officialEuclideanNorm_sq (u t) hmeas).1
      hint).congr
      (Filter.Eventually.of_forall fun x =>
        officialEuclideanNorm_sq_eq_sum_sq (u t x))
  unfold supKineticEnergy kineticEnergy
  calc
    (∫ x : Space, ∑ i : Fin 3, (u t x i) ^ 2) ≤
        ∫ x : Space, 3 * ‖u t x‖ ^ 2 := by
      refine integral_mono hsum (hint.const_mul 3) fun x => ?_
      have h := officialEuclideanNorm_sq_le_three_mul_norm_sq (u t x)
      rwa [officialEuclideanNorm_sq_eq_sum_sq (u t x)] at h
    _ = 3 * ∫ x : Space, ‖u t x‖ ^ 2 := integral_const_mul 3 _

/-- Under slice measurability and the existing integrability clause, uniform
boundedness of the **inherited sup-norm** energy and of Fefferman's Euclidean
energy are equivalent, the bound changing by at most the fixed dimension factor
three.  This is the load-bearing replacement for the former
`uniformlyBoundedEnergy_iff_official`, whose two sides had become the same
proposition.  The asymmetry is essential: the Euclidean-to-sup direction keeps
the constant, the sup-to-Euclidean direction cannot (see
`LerayWeak.UniformOfficialKineticBound` for the consequence). -/
theorem uniformlyBoundedEnergy_iff_sup
    (u : VelocityEvolution)
    (hmeas : ∀ t : ℝ, 0 ≤ t → AEStronglyMeasurable (u t))
    (hint : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun x => ‖u t x‖ ^ 2)) :
    (∃ E : ℝ, 0 < E ∧
      ∀ t : ℝ, 0 ≤ t → supKineticEnergy u t < E) ↔
      ∃ E : ℝ, 0 < E ∧
        ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E := by
  constructor
  · rintro ⟨E, hE, hbound⟩
    refine ⟨3 * E, mul_pos (by norm_num) hE, fun t ht => ?_⟩
    exact lt_of_le_of_lt
      (kineticEnergy_le_three_mul_supKineticEnergy u t (hmeas t ht) (hint t ht))
      (mul_lt_mul_of_pos_left (hbound t ht) (by norm_num))
  · rintro ⟨E, hE, hbound⟩
    refine ⟨E, hE, fun t ht => ?_⟩
    exact lt_of_le_of_lt
      (supKineticEnergy_le_kineticEnergy u t (hmeas t ht) (hint t ht))
      (hbound t ht)

/-! ### Beyond energy: the derivative-bundle operator norm

With the energy clauses transported above, and the *spatial weight* `‖x‖ ^ k` of
the data decay clause transported by
`OfficialABEncoding.feffermanRapidDecayBound_iff_euclideanWeight`, the clause the
`currentSpaceNormEuclideanNormEquivalence` residual still named for the data was
the **derivative bundle** itself: `‖iteratedFDeriv ℝ n f x‖` is the operator norm
induced by the inherited sup norm on the `n` argument slots *and* on the value,
so fixing the weight alone does not make it Fefferman's quantity.

The residual clause is about *measurement*, not about which map is
differentiated, so everything below compares two norms of one fixed continuous
multilinear map.  Stating it at that level — rather than for `iteratedFDeriv`
specifically — is deliberate: the value-half lemma applies verbatim to the
`iteratedFDerivWithin` spacetime bundles of the force clauses in
`Navier.OfficialProblem`.

The comparison costs `√3` on the value and a further `√3 ^ n` on the `n`
argument slots.  Both factors are the single attained pointwise factor of
`officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness`, so neither is slack.

**Not closed here, but closed downstream:** the force decay clauses of
`Navier.OfficialProblem`.  They differentiate on `ℝ × Space`, so their argument
slots carry the product norm of `ℝ` with the sup norm on `Space`, and their
weight `(1 + ‖x‖ + t) ^ K` still measures `x` in the sup norm.  Only the value
half of those bundles is covered below — `Analysis.ForceNormBridge` reuses that
value half, adds the weight and slot halves, and rewires alternatives C and D.
-/

/-- **Value half of the bundle comparison, for arbitrary argument types.**
Measuring the value of a continuous multilinear map in Fefferman's Euclidean
norm instead of the inherited sup norm costs one factor `√3`; the argument slots
are untouched.  Stated for an arbitrary index type and arbitrary slot spaces so
that it applies to the spacetime bundles `iteratedFDerivWithin ℝ n (fun
z : ℝ × Space => f z.1 z.2)` of the official force clauses, not just to the
`Space`-slot bundles of the data clause. -/
theorem officialEuclideanNorm_apply_le_sqrt_three_mul_opNorm
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (L : ContinuousMultilinearMap ℝ E Space) (v : ∀ i, E i) :
    officialEuclideanNorm (L v) ≤ Real.sqrt 3 * ‖L‖ * ∏ i, ‖v i‖ := by
  calc
    officialEuclideanNorm (L v) ≤ Real.sqrt 3 * ‖L v‖ :=
      officialEuclideanNorm_le (L v)
    _ ≤ Real.sqrt 3 * (‖L‖ * ∏ i, ‖v i‖) :=
      mul_le_mul_of_nonneg_left (L.le_opNorm v) (Real.sqrt_nonneg 3)
    _ = Real.sqrt 3 * ‖L‖ * ∏ i, ‖v i‖ := by ring

/-- Fefferman's fully Euclidean multilinear bound for a rank-`n` derivative
bundle on `Space`: the constant `C` controls the **Euclidean** norm of the value
against the product of the **Euclidean** norms of the arguments.  This is the
quantity Fefferman's decay clauses bound; `‖L‖` is the quantity the project's
clauses bound. -/
def EuclideanBundleBound {n : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) Space) (C : ℝ) :
    Prop :=
  ∀ v : Fin n → Space,
    officialEuclideanNorm (L v) ≤ C * ∏ i : Fin n, officialEuclideanNorm (v i)

/-- The inherited operator norm supplies a fully Euclidean bundle bound at the
cost of a single factor `√3`, independently of the rank `n`: enlarging the
argument norms only weakens the required conclusion. -/
theorem euclideanBundleBound_sqrt_three_mul_opNorm {n : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) Space) :
    EuclideanBundleBound L (Real.sqrt 3 * ‖L‖) := by
  intro v
  have hprod : (∏ i : Fin n, ‖v i‖) ≤ ∏ i : Fin n, officialEuclideanNorm (v i) :=
    Finset.prod_le_prod (fun i _ => norm_nonneg (v i))
      (fun i _ => norm_le_officialEuclideanNorm (v i))
  refine (officialEuclideanNorm_apply_le_sqrt_three_mul_opNorm L v).trans ?_
  exact mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg L))

/-- Conversely a fully Euclidean bundle bound controls the inherited operator
norm, now at the rank-dependent cost `√3 ^ n`: each of the `n` argument slots
must be shrunk from the Euclidean norm back to the sup norm. -/
theorem opNorm_le_of_euclideanBundleBound {n : ℕ}
    {L : ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) Space} {C : ℝ}
    (hC : 0 ≤ C) (h : EuclideanBundleBound L C) :
    ‖L‖ ≤ Real.sqrt 3 ^ n * C := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 3) n) hC) fun v => ?_
  have hstep : (∏ i : Fin n, officialEuclideanNorm (v i)) ≤
      Real.sqrt 3 ^ n * ∏ i : Fin n, ‖v i‖ := by
    refine (Finset.prod_le_prod
      (fun i _ => officialEuclideanNorm_nonneg (v i))
      (fun i _ => officialEuclideanNorm_le (v i))).trans_eq ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  calc
    ‖L v‖ ≤ officialEuclideanNorm (L v) := norm_le_officialEuclideanNorm (L v)
    _ ≤ C * ∏ i : Fin n, officialEuclideanNorm (v i) := h v
    _ ≤ C * (Real.sqrt 3 ^ n * ∏ i : Fin n, ‖v i‖) :=
      mul_le_mul_of_nonneg_left hstep hC
    _ = Real.sqrt 3 ^ n * C * ∏ i : Fin n, ‖v i‖ := by ring

/-- Fefferman's clause-(4) rapid decay with **every** norm Euclidean: the
spatial weight, the derivative-bundle arguments, and the bundle value.

Compare `OfficialABEncoding.FeffermanEuclideanWeightRapidDecayBound`, which
fixes only the weight and still measures the bundle in the operator norm
inherited from the sup norm.  That predicate discharged the `x`-half of the
decay clause of the norm residual; this one discharges the bundle half. -/
def FeffermanFullyEuclideanRapidDecayBound (f : Space → Space) : Prop :=
  ∀ (k n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Space) (v : Fin n → Space),
    officialEuclideanNorm x ^ k *
        officialEuclideanNorm (iteratedFDeriv ℝ n f x v) ≤
      C * ∏ i : Fin n, officialEuclideanNorm (v i)

/-- **The bundle clause of the norm residual, discharged.**  Replacing the
inherited sup norm by the Euclidean norm in *all three* places the decay clause
uses it — spatial weight, derivative-bundle arguments, bundle value — does not
change the rapid-decay class.

Neither direction is free: the forward one spends `√3 ^ (k + 1)` (one factor per
weight power, one on the value) and the backward one spends `√3 ^ n` (one per
argument slot).  The constants are invisible in the statement only because the
clause quantifies existentially over `C`; a consumer needing a pinned constant
must not route through here. -/
theorem feffermanRapidDecayBound_iff_fullyEuclidean (f : Space → Space) :
    Navier.ConventionBridges.FeffermanRapidDecayBound f ↔
      FeffermanFullyEuclideanRapidDecayBound f := by
  constructor
  · intro h k n
    obtain ⟨C, hC, hbound⟩ := h k n
    refine ⟨Real.sqrt 3 ^ (k + 1) * C,
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg 3) _) hC, ?_⟩
    intro x v
    have hprod : (0 : ℝ) ≤ ∏ i : Fin n, officialEuclideanNorm (v i) :=
      Finset.prod_nonneg fun i _ => officialEuclideanNorm_nonneg (v i)
    have hweight : officialEuclideanNorm x ^ k ≤ Real.sqrt 3 ^ k * ‖x‖ ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (officialEuclideanNorm_nonneg x)
        (officialEuclideanNorm_le x) k
    calc
      officialEuclideanNorm x ^ k *
            officialEuclideanNorm (iteratedFDeriv ℝ n f x v)
          ≤ (Real.sqrt 3 ^ k * ‖x‖ ^ k) *
              (Real.sqrt 3 * ‖iteratedFDeriv ℝ n f x‖ *
                ∏ i : Fin n, officialEuclideanNorm (v i)) :=
        mul_le_mul hweight
          (euclideanBundleBound_sqrt_three_mul_opNorm (iteratedFDeriv ℝ n f x) v)
          (officialEuclideanNorm_nonneg _)
          (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 3) k)
            (pow_nonneg (norm_nonneg x) k))
      _ = Real.sqrt 3 ^ (k + 1) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) *
              ∏ i : Fin n, officialEuclideanNorm (v i) := by ring
      _ ≤ Real.sqrt 3 ^ (k + 1) * C *
              ∏ i : Fin n, officialEuclideanNorm (v i) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbound x)
            (pow_nonneg (Real.sqrt_nonneg 3) _))
          hprod
  · intro h k n
    obtain ⟨C, hC, hbound⟩ := h k n
    refine ⟨Real.sqrt 3 ^ n * C,
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg 3) n) hC, ?_⟩
    intro x
    -- Absorb the spatial weight into the bundle, then apply the converse half of
    -- the bundle comparison to the weighted bundle.
    have hsmul : ∀ (c : ℝ) (y : Space),
        officialEuclideanNorm (c • y) = |c| * officialEuclideanNorm y := by
      intro c y
      simp [officialEuclideanNorm, officialEuclideanPoint, norm_smul,
        Real.norm_eq_abs]
    have hweighted :
        EuclideanBundleBound ((‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n f x) C := by
      intro v
      rw [ContinuousMultilinearMap.smul_apply, hsmul,
        abs_of_nonneg (pow_nonneg (norm_nonneg x) k)]
      refine le_trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg x) (norm_le_officialEuclideanNorm x) k)
        (officialEuclideanNorm_nonneg _)) ?_
      exact hbound x v
    have key := opNorm_le_of_euclideanBundleBound hC hweighted
    rwa [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg x) k)] at key

/-- Every Mathlib Schwartz field on `ℝ³` satisfies Fefferman's decay clause with
the spatial weight, the derivative-bundle arguments, and the bundle value all
measured in the Euclidean norm.  This is the clause-(4) consumer of
`feffermanRapidDecayBound_iff_fullyEuclidean`. -/
theorem schwartzmap_satisfies_fullyEuclidean_rapidDecay
    (s : SchwartzMap Space Space) :
    FeffermanFullyEuclideanRapidDecayBound s.toFun :=
  (feffermanRapidDecayBound_iff_fullyEuclidean s.toFun).1
    (Navier.ConventionBridges.schwartzmap_satisfies_fefferman_rapid_decay s)

end Navier.Analysis.EnergyNormBridge
