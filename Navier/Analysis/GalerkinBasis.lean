import Navier.Analysis.LerayWeak

/-!
# Divergence-free Galerkin basis (finite-mode projection layer)

The one obligation blocking the assembly of a
`Navier.Analysis.LerayWeak.GalerkinApproximation` — even to *state* the
per-mode objects — is the finite-mode divergence-free basis: an
`L²`-orthonormal sequence of divergence-free Schwartz fields whose span
approximates every divergence-free Schwartz datum in `L²`
[Temam, *Navier–Stokes Equations*, Ch. III §3; Robinson–Rodrigo–Sadowski,
*The Three-Dimensional Navier–Stokes Equations*, Ch. 4; Leray, Acta Math. 63
(1934); Constantin–Foias, *NSE*, Ch. II].  On the whole space `ℝ³` the Stokes
operator has no discrete spectrum, so — unlike the bounded-domain Temam
presentation — the basis is *any* orthonormalized countable dense family of
divergence-free fields (Galerkin needs orthonormality + density, not
eigenfunctions; Robinson–Rodrigo–Sadowski Ch. 4 runs exactly this way).

This file lays that layer over the repo's own objects:

## Certified here (no sorry)

* `schwartzL2Inner` — the `L²` pairing `∫ ⟨f x, g x⟩` of Schwartz fields in the
  official coordinates, with symmetry and `schwartzL2Inner_self_nonneg`.
* `staticDivergence_add` — additivity of the divergence (with
  `staticDivergence_const_smul` from `LerayWeak`, the linearity toolkit).
* `GalerkinBasisFamily.proj` — the `m`-mode projection
  `P_m u = ∑_{j<m} ⟨u, w_j⟩ • w_j`, with:
  - `proj_basis` — `P_m w_j = w_j` for `j < m` (orthonormality algebra);
  - `proj_divergence_free` — **the projection stays in the divergence-free
    class** (finite linear combinations of divergence-free fields are
    divergence-free; Clairaut-free, pure linearity);
  - `proj_zero` — non-degeneracy smoke.
* `schwartzPairing_integrable` — **integrability of the pairing density**
  (pointwise Cauchy–Schwarz + `‖·‖₂ ≤ √3‖·‖∞` + Schwartz boundedness of `g` +
  `SchwartzMap.integrable`), the load-bearing fact upgrading `schwartzL2Inner`
  to a bilinear form.
* `schwartzL2Inner_{add,smul,sum}_{left,right}` — **full bilinearity of the
  `L²` pairing** (via `schwartzPairing_integrable` + `integral_add`).
* `proj_self_adjoint` — **`⟨P_m u, v⟩ = ⟨u, P_m v⟩`** (orthonormality +
  bilinearity), and `proj_skew_transfer` — `⟨P_m B u, u⟩ = 0` on the span,
  reducing the projected nonlinearity's energy diagonal to the divergence-free
  transport identity `∫ (u·∇)u·u = 0` (`hB` input of `galerkin_apriori_bound`).
* `proj_best_approx` / `proj_error_antitone` / `proj_tendsto_self` — the **Bessel
  best-approximation tower**: `P_m u` minimizes the `L²`-seminorm error over the
  retained span (residual orthogonality + Pythagoras), the error is antitone in
  the mode count, and `dense_span` drives `‖u₀ − P_m u₀‖²_{L²} → 0` — the
  `initial_converges` field of `GalerkinApproximation`.
* `divergenceFreeInitial_sum_smul` — **finite `ℝ`-combinations of divergence-free
  fields are divergence-free** (the div-free preservation Gram–Schmidt needs).
* `gramSchmidt_residual_inner` / `schwartzL2Inner_normalize_self` — the **banked
  algebraic cores of Gram–Schmidt** (residual `⊥` orthonormal prefix; unit-seminorm
  normalization), consumed by `rawDivFree_orthonormalize`.
* `exists_galerkinBasisFamily` — now a **composition** of the two named leaves
  below (raw dense family ∘ Gram–Schmidt), no longer a monolithic sorry.

* `dense_span_of_member_approximation` — **the coefficient bookkeeping of
  `dense_span`**: approximation by a single family member implies approximation
  by a finite combination, so the remaining density obligation is stated in the
  coefficient-free form every construction produces.
* `rawDivFree_orthonormalize` — **Gram–Schmidt** of a raw dense family into a
  `GalerkinBasisFamily`, now a full composition of the banked recursion
  (`gramSchmidtField_orthonormal`, `gramSchmidtField_divergenceFree`,
  `gramSchmidtField_dense_span`) [RRS Ch. 4; Temam III §3].
* `proj_initial_converges_L2` / `proj_initial_converges` — the
  `initial_converges` field of `Navier.Analysis.LerayWeak.GalerkinApproximation`
  (and the `initial_converges_L2` field of `GalerkinModeData`) at
  `initialMode m := P_m u₀`, obtained from `proj_tendsto_self` through the
  coordinate-norm bridge in `LerayWeak`.
* `exists_rawDivFreeFamily` — now a **composition** of the single residual below
  with `dense_span_of_member_approximation`, no `sorry` of its own.

* `esCLM` / `toES` / `toL2` — the divergence-free Schwartz class mapped into
  `Lp (EuclideanSpace ℝ (Fin 3)) 2 volume`, with `toL2_sub` (linearity) and
  `norm_toL2_sq` (`‖toL2 u‖² = schwartzL2Inner u u`, exact: `officialInner` *is*
  the Euclidean inner product of `officialEuclideanPoint = WithLp.toLp 2`, so no
  sup-versus-Euclidean constant appears).
* `exists_dense_divFree_family` — **the density core, certified**: a countable
  family of divergence-free Schwartz fields `L²`-approximating every
  divergence-free Schwartz datum, from second-countability of `L²` (hereditary,
  so the dense sequence is drawn from the divergence-free image itself).

## Named residual (honest `sorry`, strictly-lower leaf)

* `exists_denseIndependentDivFreeFamily` — **independence reconciliation**.  Its
  density conjunct is now certified separately by `exists_dense_divFree_family`
  (see the separability section below), and its divergence-free and
  independence conjuncts hold for the disjoint-translate reservoir of
  `Navier.Analysis.GalerkinRawFamily`.  What is open is combining the two into a
  single family: greedy off-span perturbation of the dense family by vanishing
  multiples of the reservoir [RRS Ch. 4; Temam III §3; ~250 LOC].

With this layer, `galerkin_approximation_exists`'s remaining inputs are: the
projected Stokes/nonlinearity operators on `span{w_0, …, w_{m−1}}` (feeding
`finiteDim_dissipative_ode_global` + `galerkin_apriori_bound` +
`EnergyDissipation.dissipation_integral_le_forward`, all BANKED), and the
time-equicontinuity/weak-consistency bookkeeping.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter

namespace Navier.Analysis.GalerkinBasis

open Navier
open Navier.Analysis.Enstrophy
open Navier.Analysis.LerayWeak
open Navier.Analysis.OfficialABEncoding

/-!
## The `L²` pairing of Schwartz velocity fields
-/

/-- The `L²` inner product of two Schwartz velocity fields in the official
Euclidean coordinates: `⟨f, g⟩_{L²} = ∫ ⟨f x, g x⟩ dx`. -/
def schwartzL2Inner (f g : SchwartzVelocity) : ℝ :=
  ∫ x : Space, officialInner (f x) (g x)

/-- Symmetry of the official pointwise inner product. -/
theorem officialInner_comm (x y : Space) : officialInner x y = officialInner y x := by
  simp only [officialInner_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Symmetry of the `L²` pairing. -/
theorem schwartzL2Inner_comm (f g : SchwartzVelocity) :
    schwartzL2Inner f g = schwartzL2Inner g f := by
  unfold schwartzL2Inner
  congr 1; funext x; exact officialInner_comm _ _

/-- The `L²` pairing is positive-semidefinite (a seminorm squared). -/
theorem schwartzL2Inner_self_nonneg (f : SchwartzVelocity) :
    0 ≤ schwartzL2Inner f f :=
  integral_nonneg fun x => by
    rw [officialInner_self]; positivity

/-- **The pairing density of two Schwartz fields is integrable** (Leray weak
theory, Temam III §3).  Pointwise Cauchy–Schwarz `|⟨f x, g x⟩| ≤ ‖f x‖₂·‖g x‖₂`
(`abs_officialInner_le`), the coordinate-norm comparison `‖·‖₂ ≤ √3·‖·‖∞`
(`officialEuclideanNorm_le`), the uniform bound on the Schwartz field `g`, and
`SchwartzMap.integrable` (integrability of `‖f ·‖`) dominate the density by
`(3·Cg)·‖f x‖`.  This upgrades `schwartzL2Inner` from a raw Bochner integral to
a bilinear form (`∫ (a+b)·c = ∫ a·c + ∫ b·c` needs integrability of each part),
unlocking projection self-adjointness and the skew transfer `⟨P_m B u, u⟩ = 0`
on the span. -/
theorem schwartzPairing_integrable (f g : SchwartzVelocity) :
    Integrable (fun x : Space => officialInner (f x) (g x)) := by
  -- Uniform bound `Cg` on `‖g x‖` (Schwartz `k=0,n=0` decay).
  obtain ⟨Cg, hCg0, hCgraw⟩ :=
    (schwartzmap_satisfies_fefferman_euclidean_weight_rapid_decay g) 0 0
  have hCg : ∀ x : Space, ‖g x‖ ≤ Cg := by
    intro x
    have h := hCgraw x
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
    exact h
  -- `x ↦ ‖f x‖` is integrable (`SchwartzMap.integrable`).
  have hfint : Integrable (fun x : Space => ‖f x‖) volume := (SchwartzMap.integrable f).norm
  -- Dominate the pairing density by `(3·Cg)·‖f x‖`.
  refine Integrable.mono' (hfint.const_mul (3 * Cg)) ?_ ?_
  · -- Continuity ⇒ a.e.-strong-measurability (coordinate sum of products).
    apply Continuous.aestronglyMeasurable
    simp only [officialInner_eq_sum]
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp f.continuous).mul ((continuous_apply i).comp g.continuous))
  · -- Pointwise Cauchy–Schwarz + `‖·‖₂ ≤ √3‖·‖∞` + the uniform bound on `g`.
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]
    calc |officialInner (f x) (g x)|
        ≤ officialEuclideanNorm (f x) * officialEuclideanNorm (g x) := abs_officialInner_le _ _
      _ ≤ (Real.sqrt 3 * ‖f x‖) * (Real.sqrt 3 * ‖g x‖) := by
          refine mul_le_mul (officialEuclideanNorm_le _) (officialEuclideanNorm_le _)
            (officialEuclideanNorm_nonneg _) ?_
          positivity
      _ = 3 * (‖f x‖ * ‖g x‖) := by
          rw [show Real.sqrt 3 * ‖f x‖ * (Real.sqrt 3 * ‖g x‖)
                = (Real.sqrt 3 * Real.sqrt 3) * (‖f x‖ * ‖g x‖) by ring,
             Real.mul_self_sqrt (by norm_num)]
      _ ≤ 3 * (‖f x‖ * Cg) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (hCg x) (norm_nonneg _)
      _ = (3 * Cg) * ‖f x‖ := by ring

/-!
## Bilinearity of the `L²` pairing

With `schwartzPairing_integrable` in hand, `schwartzL2Inner` is a genuine
bilinear form: `∫ (a + b)·c = ∫ a·c + ∫ b·c` uses integrability of each part.
This is the algebra behind projection self-adjointness (Temam III §3).
-/

/-- Additivity of the official pointwise inner product in its left argument. -/
theorem officialInner_add_left (x y z : Space) :
    officialInner (x + y) z = officialInner x z + officialInner y z := by
  rw [officialInner_comm, officialInner_add_right, officialInner_comm z x, officialInner_comm z y]

/-- `ℝ`-homogeneity of the official pointwise inner product in its left argument. -/
theorem officialInner_smul_left (c : ℝ) (x y : Space) :
    officialInner (c • x) y = c * officialInner x y := by
  rw [officialInner_comm, officialInner_smul_right, officialInner_comm y x]

/-- The `L²` pairing of the zero field with anything vanishes. -/
theorem schwartzL2Inner_zero_left (g : SchwartzVelocity) : schwartzL2Inner 0 g = 0 := by
  unfold schwartzL2Inner
  have hz : (fun x : Space => officialInner ((0 : SchwartzVelocity) x) (g x)) = fun _ => 0 := by
    funext x; simp [officialInner_zero_left]
  rw [hz, integral_zero]

/-- **Left-additivity of the `L²` pairing** (needs `schwartzPairing_integrable`). -/
theorem schwartzL2Inner_add_left (f g h : SchwartzVelocity) :
    schwartzL2Inner (f + g) h = schwartzL2Inner f h + schwartzL2Inner g h := by
  unfold schwartzL2Inner
  rw [← integral_add (schwartzPairing_integrable f h) (schwartzPairing_integrable g h)]
  congr 1; funext x
  rw [SchwartzMap.add_apply, officialInner_add_left]

/-- **Right-additivity of the `L²` pairing.** -/
theorem schwartzL2Inner_add_right (f g h : SchwartzVelocity) :
    schwartzL2Inner f (g + h) = schwartzL2Inner f g + schwartzL2Inner f h := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_add_left, schwartzL2Inner_comm g f,
    schwartzL2Inner_comm h f]

/-- **Left-homogeneity of the `L²` pairing.** -/
theorem schwartzL2Inner_smul_left (c : ℝ) (f g : SchwartzVelocity) :
    schwartzL2Inner (c • f) g = c * schwartzL2Inner f g := by
  unfold schwartzL2Inner
  rw [← integral_const_mul]
  congr 1; funext x
  rw [SchwartzMap.smul_apply, officialInner_smul_left]

/-- **Right-homogeneity of the `L²` pairing.** -/
theorem schwartzL2Inner_smul_right (c : ℝ) (f g : SchwartzVelocity) :
    schwartzL2Inner f (c • g) = c * schwartzL2Inner f g := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_smul_left, schwartzL2Inner_comm g f]

/-- **Finite-sum left-linearity**: pulls a finite linear combination out of the
left slot (the algebra the projection's self-adjointness rides on). -/
theorem schwartzL2Inner_sum_left (s : Finset ℕ) (F : ℕ → SchwartzVelocity)
    (g : SchwartzVelocity) :
    schwartzL2Inner (∑ j ∈ s, F j) g = ∑ j ∈ s, schwartzL2Inner (F j) g := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, schwartzL2Inner_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, schwartzL2Inner_add_left, ih, Finset.sum_insert ha]

/-- **Finite-sum right-linearity.** -/
theorem schwartzL2Inner_sum_right (s : Finset ℕ) (f : SchwartzVelocity)
    (F : ℕ → SchwartzVelocity) :
    schwartzL2Inner f (∑ j ∈ s, F j) = ∑ j ∈ s, schwartzL2Inner f (F j) := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_sum_left]
  exact Finset.sum_congr rfl (fun j _ => schwartzL2Inner_comm _ _)

/-- **Left-negation of the `L²` pairing.** -/
theorem schwartzL2Inner_neg_left (f g : SchwartzVelocity) :
    schwartzL2Inner (-f) g = - schwartzL2Inner f g := by
  have h : (-f : SchwartzVelocity) = (-1 : ℝ) • f := by rw [neg_one_smul]
  rw [h, schwartzL2Inner_smul_left]; ring

/-- **Left-subtractivity of the `L²` pairing.** -/
theorem schwartzL2Inner_sub_left (f g h : SchwartzVelocity) :
    schwartzL2Inner (f - g) h = schwartzL2Inner f h - schwartzL2Inner g h := by
  rw [sub_eq_add_neg, schwartzL2Inner_add_left, schwartzL2Inner_neg_left, ← sub_eq_add_neg]

/-- **Pythagoras for the `L²` seminorm**: orthogonal parts add in the squared
seminorm, `Q(a+b) = Q a + Q b` when `⟨a,b⟩ = 0`. -/
theorem schwartzL2Inner_self_add_of_orthogonal (a b : SchwartzVelocity)
    (h : schwartzL2Inner a b = 0) :
    schwartzL2Inner (a + b) (a + b) = schwartzL2Inner a a + schwartzL2Inner b b := by
  rw [schwartzL2Inner_add_left, schwartzL2Inner_add_right, schwartzL2Inner_add_right,
      schwartzL2Inner_comm b a, h]; ring

/-!
## Divergence linearity toolkit
-/

/-- Every Schwartz velocity field is differentiable at every point. -/
theorem schwartz_differentiableAt (f : SchwartzVelocity) (x : Space) :
    DifferentiableAt ℝ (fun y => f y) x :=
  ((f.smooth 1).differentiable (by norm_num)).differentiableAt

/-- The static divergence is additive (on differentiable summands). -/
theorem staticDivergence_add (f g : VelocityField) (x : Space)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    staticDivergence (fun y => f y + g y) x = staticDivergence f x + staticDivergence g x := by
  unfold staticDivergence
  rw [← Finset.sum_add_distrib]
  congr 1; funext i
  rw [show (fun y => f y + g y) = f + g from rfl, fderiv_add hf hg]
  simp

/-- **Finite `ℝ`-linear combinations of divergence-free fields are
divergence-free.**  The structural fact letting every Galerkin/Gram–Schmidt
combination stay inside the divergence-free constraint manifold (pure
linearity of the divergence; Clairaut-free). -/
theorem divergenceFreeInitial_sum_smul (s : Finset ℕ) (c : ℕ → ℝ)
    (v : ℕ → SchwartzVelocity) (hv : ∀ j, DivergenceFreeInitial (v j)) :
    DivergenceFreeInitial (∑ j ∈ s, c j • v j) := by
  intro x
  induction s using Finset.induction_on with
  | empty => simp [staticDivergence]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hcoe : (fun y => (c a • v a + ∑ j ∈ s, c j • v j : SchwartzVelocity) y) =
        fun y => (c a • v a : SchwartzVelocity) y +
          (∑ j ∈ s, c j • v j : SchwartzVelocity) y := by
      funext y; simp
    rw [hcoe, staticDivergence_add _ _ x
      (schwartz_differentiableAt _ x) (schwartz_differentiableAt _ x)]
    have h1 : staticDivergence (fun y => (c a • v a : SchwartzVelocity) y) x = 0 := by
      have hcoe2 : (fun y => (c a • v a : SchwartzVelocity) y) =
          fun y => c a • (v a) y := by funext y; simp
      rw [hcoe2, staticDivergence_const_smul _ _ _ (schwartz_differentiableAt _ x),
        hv a x, mul_zero]
    rw [h1, ih, add_zero]

/-!
## The Galerkin family and its finite-mode projection
-/

/-- An **`L²`-orthonormal, divergence-free Galerkin family with dense span**:
the whole-space substitute for the bounded-domain Stokes eigenbasis
[Temam III §3; Robinson–Rodrigo–Sadowski Ch. 4].  `dense_span` quantifies over
divergence-free *Schwartz* data — exactly the datum class of
`leray_weak_existence` — in the `L²` seminorm `schwartzL2Inner (·) (·)` of the
error.  Inhabitedness is the `exists_galerkinBasisFamily` leaf below (this
structure is a rich object; its consumers are non-vacuous once that leaf
lands). -/
structure GalerkinBasisFamily where
  /-- The basis fields. -/
  w : ℕ → SchwartzVelocity
  /-- Every mode is divergence-free. -/
  divergence_free : ∀ j : ℕ, DivergenceFreeInitial (w j)
  /-- `L²`-orthonormality in the official coordinates. -/
  orthonormal : ∀ i j : ℕ, schwartzL2Inner (w i) (w j) = if i = j then 1 else 0
  /-- Finite spans `L²`-approximate every divergence-free Schwartz field. -/
  dense_span : ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
    ∃ (m : ℕ) (c : ℕ → ℝ),
      schwartzL2Inner (u - ∑ j ∈ Finset.range m, c j • w j)
        (u - ∑ j ∈ Finset.range m, c j • w j) < ε

/-- A **raw countable divergence-free family** whose finite spans are
`L²`-dense in the divergence-free Schwartz class and which is
`L²`-linearly-independent (no nonzero finite combination has zero `L²`
seminorm).  This is the pre-orthonormalization input to Gram–Schmidt
[Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3].  It carries the same
`dense_span` obligation as `GalerkinBasisFamily` but drops orthonormality,
replacing it by linear independence — exactly what Gram–Schmidt consumes. -/
structure RawDivFreeFamily where
  /-- The raw (non-orthonormal) fields. -/
  v : ℕ → SchwartzVelocity
  /-- Every raw mode is divergence-free. -/
  divergence_free : ∀ j : ℕ, DivergenceFreeInitial (v j)
  /-- `L²`-linear independence: a null finite combination has all-zero
  coefficients (continuity of Schwartz fields makes `L²`-independence ordinary
  linear independence).  This is what forces each Gram–Schmidt residual
  `u_n ≠ 0`, so the normalization `w_n = u_n / ‖u_n‖` is well-defined. -/
  independent : ∀ (n : ℕ) (c : ℕ → ℝ),
    schwartzL2Inner (∑ j ∈ Finset.range n, c j • v j)
      (∑ j ∈ Finset.range n, c j • v j) = 0 → ∀ j ∈ Finset.range n, c j = 0
  /-- Finite spans `L²`-approximate every divergence-free Schwartz field. -/
  dense_span : ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
    ∃ (m : ℕ) (c : ℕ → ℝ),
      schwartzL2Inner (u - ∑ j ∈ Finset.range m, c j • v j)
        (u - ∑ j ∈ Finset.range m, c j • v j) < ε

/-- **Member approximation implies span approximation.**  If every
divergence-free Schwartz field is `L²`-approximated by a *single member* of the
family `v`, then it is `L²`-approximated by a finite *combination* of the first
`m` members — take the one-term combination with coefficient `1` at the good
index.  This is the `dense_span` field of `RawDivFreeFamily`, reduced to the
coefficient-free statement that every construction of a countable `L²`-dense
subset of the divergence-free Schwartz class actually produces
[Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3]. -/
theorem dense_span_of_member_approximation (v : ℕ → SchwartzVelocity)
    (hmem : ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
      ∃ j : ℕ, schwartzL2Inner (u - v j) (u - v j) < ε) :
    ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
      ∃ (m : ℕ) (c : ℕ → ℝ),
        schwartzL2Inner (u - ∑ j ∈ Finset.range m, c j • v j)
          (u - ∑ j ∈ Finset.range m, c j • v j) < ε := by
  classical
  intro u hu ε hε
  obtain ⟨j, hj⟩ := hmem u hu ε hε
  refine ⟨j + 1, fun i => if i = j then 1 else 0, ?_⟩
  have hsum : (∑ i ∈ Finset.range (j + 1), (if i = j then (1:ℝ) else 0) • v i) = v j := by
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij])
      (fun hjm => absurd (Finset.mem_range.mpr (Nat.lt_succ_self j)) hjm)]
    simp
  rw [hsum]
  exact hj

/-!
## `L²` separability of the divergence-free Schwartz class

The density conjunct of the residual below is settled here, by separability
rather than by either of the two constructions the residual's docstring
previously proposed.  `Lp (EuclideanSpace ℝ (Fin 3)) 2 volume` over `ℝ³` is
second-countable (`Lp.SecondCountableTopology`, which needs only
`Fact (2 ≠ ⊤)` supplied by hand), second-countability is hereditary, so the
image of the divergence-free Schwartz class under `u ↦ toL2 u` carries a dense
sequence *drawn from the image itself* — i.e. from genuinely divergence-free
Schwartz fields.  Transporting back is exact, not lossy: `officialInner` is the
Euclidean inner product of `officialEuclideanPoint = WithLp.toLp 2`, so
`‖toL2 u‖² = schwartzL2Inner u u` on the nose (`norm_toL2_sq`), with no
sup-versus-Euclidean constant.

Reference: Robinson–Rodrigo–Sadowski, *The Three-Dimensional Navier–Stokes
Equations*, Ch. 4; Temam, *Navier–Stokes Equations*, AMS Chelsea 2001, Ch. III
§3; Reed–Simon I, Academic Press 1980, §II.1 (separability of `L²`).
-/

section Separability

/-- The `Space` coordinates as a continuous linear map into the Euclidean model;
`esCLM x = officialEuclideanPoint x` definitionally. -/
def esCLM : Space →L[ℝ] EuclideanSpace ℝ (Fin 3) := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap
example (x : Space) : esCLM x = officialEuclideanPoint x := rfl

def toES (u : SchwartzVelocity) : SchwartzMap Space (EuclideanSpace ℝ (Fin 3)) := SchwartzMap.postcompCLM (𝕜 := ℝ) esCLM u
example (u : SchwartzVelocity) (x : Space) : toES u x = officialEuclideanPoint (u x) := rfl

def toL2 (u : SchwartzVelocity) : Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space) := (toES u).toLp 2

theorem toL2_sub (u v : SchwartzVelocity) : toL2 (u - v) = toL2 u - toL2 v := by
  unfold toL2 toES
  rw [map_sub]
  exact SetLike.coe_eq_coe.mp rfl

theorem norm_toL2_sq (u : SchwartzVelocity) : ‖toL2 u‖ ^ 2 = schwartzL2Inner u u := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def, schwartzL2Inner]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (toES u) 2 (volume : Measure Space)] with x hx
  simp only [toL2]
  rw [hx]
  rfl

def divFreeL2Set : Set (Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space)) :=
  toL2 '' {u : SchwartzVelocity | DivergenceFreeInitial u}

theorem exists_dense_divFree_family :
    ∃ v : ℕ → SchwartzVelocity,
      (∀ j : ℕ, DivergenceFreeInitial (v j)) ∧
      (∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
        ∃ j : ℕ, schwartzL2Inner (u - v j) (u - v j) < ε) := by
  classical
  haveI : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI hsc : SecondCountableTopology (Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space)) := inferInstance
  haveI : Nonempty ↥divFreeL2Set :=
    ⟨⟨toL2 phiSchwartz, ⟨phiSchwartz, phiSchwartz_divfree, rfl⟩⟩⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq ↥divFreeL2Set
  have hex : ∀ j : ℕ, ∃ w : SchwartzVelocity, DivergenceFreeInitial w ∧ toL2 w = (d j : Lp (EuclideanSpace ℝ (Fin 3)) 2 _) :=
    fun j => (d j).2
  choose w hwdiv hwe using hex
  refine ⟨w, hwdiv, ?_⟩
  intro u hu ε hε
  have hmem : toL2 u ∈ divFreeL2Set := ⟨u, hu, rfl⟩
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp hd ⟨toL2 u, hmem⟩ (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  have hdist : ‖toL2 u - toL2 (w j)‖ < Real.sqrt ε := by
    rw [hwe j]
    simpa [Subtype.dist_eq, dist_eq_norm] using hj
  have : ‖toL2 (u - w j)‖ < Real.sqrt ε := by rw [toL2_sub]; exact hdist
  refine ⟨j, ?_⟩
  calc schwartzL2Inner (u - w j) (u - w j) = ‖toL2 (u - w j)‖ ^ 2 := (norm_toL2_sq _).symm
    _ < (Real.sqrt ε) ^ 2 := by
        have h0 : (0:ℝ) ≤ ‖toL2 (u - w j)‖ := norm_nonneg _
        nlinarith
    _ = ε := Real.sq_sqrt (le_of_lt hε)

end Separability

/-- **[NAMED RESIDUAL — independence reconciliation; est ~250 LOC.]**

**The density conjunct is now certified** by `exists_dense_divFree_family`
above: `Lp (EuclideanSpace ℝ (Fin 3)) 2 volume` is second-countable, second
countability is hereditary, so the image of the divergence-free Schwartz class
carries a dense sequence drawn from that image — a countable family of genuinely
divergence-free Schwartz fields that `L²`-approximates every divergence-free
Schwartz datum.  The transport back is exact (`norm_toL2_sq`).

*Correction of a previous estimate recorded here.*  This docstring used to assert
that density required either a Wiener-type theorem on translates or a
Helmholtz/Leray vector-potential construction, and that "both routes are
individually deep and Mathlib-absent".  That is wrong: a third route —
separability of `L²` plus hereditary second-countability — is neither, and is
what closes it above.  The only Mathlib friction was a missing
`Fact ((2:ENNReal) ≠ ⊤)` instance, supplied by hand.

Still correct, and still the reason a richer family is needed: the
disjoint-translate reservoir
`Navier.Analysis.GalerkinRawFamily.exists_countable_independent_divFree_family`
supplies divergence-free and `L²`-linearly-independent, but provably NOT dense —
every finite combination of disjoint-support translates of one fixed shape is
supported in a bounded union of disjoint balls, so it cannot approximate a datum
whose mass lies outside all of them.

**What remains is exactly the reconciliation of the two.**  A dense sequence may
repeat members or be linearly dependent, so it does not satisfy `independent` as
produced.  The route is greedy off-span perturbation: set
`v n = w n + δ n • p (k n)` with `w` the dense family above, `p` the reservoir,
and `δ n → 0` fast enough that density survives.  At step `n` the span of
`v 0, …, v (n−1)` is a finite-dimensional subspace `W` of `L²`; if two distinct
reservoir indices `k ≠ k'` both gave `w n + δ • p k ∈ W`, then
`δ • (p k − p k') ∈ W`, and independence of the `p`'s makes such differences an
infinite independent set, contradicting `finrank W ≤ n`.  So at most `n + 1`
indices are bad and a good one exists.  Formalizing this needs the bridge from
`schwartzL2Inner`-independence to `LinearIndependent ℝ` in `Lp`, plus
`Submodule.span` finite-dimensionality — mechanical, but not short.

**Form of the statement.**  The density conjunct here is *member* density
(approximation by one `v j`), not the *span* density of `RawDivFreeFamily`.
Member density is formally the stronger of the two — the implication is
`dense_span_of_member_approximation`, certified above — and it is the form the
separability route produces.

Reference: Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3; Leray, Acta Math. 63
(1934) §§18–20. -/
theorem exists_denseIndependentDivFreeFamily :
    ∃ v : ℕ → SchwartzVelocity,
      (∀ j : ℕ, DivergenceFreeInitial (v j)) ∧
      (∀ (n : ℕ) (c : ℕ → ℝ),
        schwartzL2Inner (∑ j ∈ Finset.range n, c j • v j)
            (∑ j ∈ Finset.range n, c j • v j) = 0 → ∀ j ∈ Finset.range n, c j = 0) ∧
      (∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
        ∃ j : ℕ, schwartzL2Inner (u - v j) (u - v j) < ε) := by
  sorry

/-- **Non-vacuity of `RawDivFreeFamily`** — now a composition of the density
residual with the certified coefficient bookkeeping
`dense_span_of_member_approximation`. -/
theorem exists_rawDivFreeFamily : Nonempty RawDivFreeFamily := by
  obtain ⟨v, hdiv, hindep, hmem⟩ := exists_denseIndependentDivFreeFamily
  exact ⟨{ v := v
           divergence_free := hdiv
           independent := hindep
           dense_span := dense_span_of_member_approximation v hmem }⟩

/-!
### Gram–Schmidt building blocks (banked)

The two algebraic cores of the orthonormalization recursion `w_n =
normalize(v_n − ∑_{k<n} ⟨v_n, w_k⟩ w_k)`, closed on the bilinearity toolkit —
independent of the recursion itself, so they are certified here and consumed by
`rawDivFree_orthonormalize` below [RRS Ch. 4; Temam III §3].
-/

/-- **Gram–Schmidt residual orthogonality.**  Against any orthonormal prefix
`w_0, …, w_{n−1}` (`⟨w_i, w_k⟩ = δ_ik` for `i, k < n`), the residual
`x − ∑_{k<n} ⟨x, w_k⟩ w_k` is `L²`-orthogonal to every `w_j`, `j < n` — the
orthogonality step of Gram–Schmidt. -/
theorem gramSchmidt_residual_inner (w : ℕ → SchwartzVelocity) (n : ℕ)
    (horth : ∀ i k, i < n → k < n → schwartzL2Inner (w i) (w k) = if i = k then 1 else 0)
    (x : SchwartzVelocity) {j : ℕ} (hj : j < n) :
    schwartzL2Inner (x - ∑ k ∈ Finset.range n, schwartzL2Inner x (w k) • w k) (w j) = 0 := by
  rw [schwartzL2Inner_sub_left, schwartzL2Inner_sum_left,
    Finset.sum_eq_single j
      (fun k _ hkj => by
        rw [schwartzL2Inner_smul_left, horth k j (Finset.mem_range.mp ‹_›) hj, if_neg hkj,
          mul_zero])
      (fun hjn => absurd (Finset.mem_range.mpr hj) hjn),
    schwartzL2Inner_smul_left, horth j j hj hj, if_pos rfl, mul_one, sub_self]

/-- **Gram–Schmidt normalization.**  A field with strictly positive `L²`
seminorm normalizes to unit seminorm: `⟨(1/√⟨x,x⟩)•x, (1/√⟨x,x⟩)•x⟩ = 1` — the
normalization step of Gram–Schmidt (well-defined precisely because
`RawDivFreeFamily.independent` forces each residual's seminorm positive). -/
theorem schwartzL2Inner_normalize_self (x : SchwartzVelocity)
    (hx : 0 < schwartzL2Inner x x) :
    schwartzL2Inner ((1 / Real.sqrt (schwartzL2Inner x x)) • x)
      ((1 / Real.sqrt (schwartzL2Inner x x)) • x) = 1 := by
  rw [schwartzL2Inner_smul_left, schwartzL2Inner_smul_right]
  have hsq : Real.sqrt (schwartzL2Inner x x) * Real.sqrt (schwartzL2Inner x x)
      = schwartzL2Inner x x := Real.mul_self_sqrt hx.le
  have hs : Real.sqrt (schwartzL2Inner x x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  field_simp
  nlinarith [hsq]

/-!
### The Gram–Schmidt recursion, realized

`w n = normalize (v n − ∑_{k<n} ⟨v n, w k⟩ w k)` by strong recursion, with the
span bookkeeping (`FinComb`) that feeds the `independent` field (residual
positivity), the divergence-free constraint, and the `dense_span` transfer
[Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3].
-/

/-- The Gram–Schmidt orthonormalized field family of a raw divergence-free
family, by strong recursion: `w n = normalize (v n − ∑_{k<n} ⟨v n, w k⟩ w k)`
with `normalize x = (1/√⟨x,x⟩) • x`. -/
noncomputable def gramSchmidtField (R : RawDivFreeFamily) (n : ℕ) : SchwartzVelocity :=
  let r := R.v n - ∑ k ∈ (Finset.range n).attach,
    schwartzL2Inner (R.v n) (gramSchmidtField R k.1) • gramSchmidtField R k.1
  (1 / Real.sqrt (schwartzL2Inner r r)) • r
termination_by n
decreasing_by all_goals exact Finset.mem_range.mp k.2

/-- The Gram–Schmidt residual at stage `n` (pre-normalization). -/
noncomputable def gsResidual (R : RawDivFreeFamily) (n : ℕ) : SchwartzVelocity :=
  R.v n - ∑ k ∈ Finset.range n,
    schwartzL2Inner (R.v n) (gramSchmidtField R k) • gramSchmidtField R k

/-- Unfolding: the field is the normalized residual. -/
theorem gramSchmidtField_eq (R : RawDivFreeFamily) (n : ℕ) :
    gramSchmidtField R n =
      (1 / Real.sqrt (schwartzL2Inner (gsResidual R n) (gsResidual R n))) •
        gsResidual R n := by
  rw [gramSchmidtField, Finset.sum_attach (Finset.range n)
    (fun k => schwartzL2Inner (R.v n) (gramSchmidtField R k) • gramSchmidtField R k)]
  rfl

/-- Membership in the finite-combination span of the first `m` members of a
field family. -/
def FinComb (f : ℕ → SchwartzVelocity) (m : ℕ) (x : SchwartzVelocity) : Prop :=
  ∃ c : ℕ → ℝ, x = ∑ j ∈ Finset.range m, c j • f j

theorem finComb_zero (f : ℕ → SchwartzVelocity) (m : ℕ) : FinComb f m 0 :=
  ⟨fun _ => 0, by simp⟩

theorem finComb_add {f : ℕ → SchwartzVelocity} {m : ℕ} {x y : SchwartzVelocity}
    (hx : FinComb f m x) (hy : FinComb f m y) : FinComb f m (x + y) := by
  obtain ⟨c, hc⟩ := hx
  obtain ⟨d, hd⟩ := hy
  refine ⟨fun j => c j + d j, ?_⟩
  rw [hc, hd, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp [add_smul]

theorem finComb_smul {f : ℕ → SchwartzVelocity} {m : ℕ} {x : SchwartzVelocity}
    (a : ℝ) (hx : FinComb f m x) : FinComb f m (a • x) := by
  obtain ⟨c, hc⟩ := hx
  refine ⟨fun j => a * c j, ?_⟩
  rw [hc, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [smul_smul]

theorem finComb_mono {f : ℕ → SchwartzVelocity} {m m' : ℕ} (h : m ≤ m')
    {x : SchwartzVelocity} (hx : FinComb f m x) : FinComb f m' x := by
  obtain ⟨c, hc⟩ := hx
  refine ⟨fun j => if j < m then c j else 0, ?_⟩
  rw [hc, ← Finset.sum_subset
      (fun j hj => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) h))
      (fun j _ hj => by
        simp only []
        rw [if_neg (fun hlt => hj (Finset.mem_range.mpr hlt)), zero_smul])]
  exact Finset.sum_congr rfl fun j hj => by
    simp only []
    rw [if_pos (Finset.mem_range.mp hj)]

theorem finComb_self (f : ℕ → SchwartzVelocity) {m j : ℕ} (hj : j < m) :
    FinComb f m (f j) := by
  classical
  refine ⟨fun i => if i = j then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single j
    (fun i _ hij => by simp [hij])
    (fun hjm => absurd (Finset.mem_range.mpr hj) hjm)]
  simp

theorem finComb_sum_smul {f : ℕ → SchwartzVelocity} {m : ℕ} (s : Finset ℕ)
    (a : ℕ → ℝ) (g : ℕ → SchwartzVelocity) (hg : ∀ k ∈ s, FinComb f m (g k)) :
    FinComb f m (∑ k ∈ s, a k • g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using finComb_zero f m
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact finComb_add (finComb_smul _ (hg i (Finset.mem_insert_self i s)))
      (ih fun k hk => hg k (Finset.mem_insert_of_mem hk))

/-- **Residual representation**: the stage-`n` residual is a combination of
`v 0, …, v n` whose `v n`-coefficient is `1` — the input to the independence
argument. -/
theorem gsResidual_repr (R : RawDivFreeFamily) : ∀ n : ℕ,
    ∃ c : ℕ → ℝ, gsResidual R n = ∑ j ∈ Finset.range (n + 1), c j • R.v j ∧ c n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hw : ∀ k, k < n → FinComb R.v n (gramSchmidtField R k) := by
      intro k hk
      obtain ⟨c, hc, -⟩ := ih k hk
      have hres : FinComb R.v n (gsResidual R k) := finComb_mono hk ⟨c, hc⟩
      rw [gramSchmidtField_eq]
      exact finComb_smul _ hres
    have hsum : FinComb R.v n (∑ k ∈ Finset.range n,
        schwartzL2Inner (R.v n) (gramSchmidtField R k) • gramSchmidtField R k) :=
      finComb_sum_smul _ _ _ (fun k hk => hw k (Finset.mem_range.mp hk))
    obtain ⟨e, he⟩ := hsum
    refine ⟨fun j => if j = n then 1 else -(e j), ?_, if_pos rfl⟩
    rw [Finset.sum_range_succ]
    have h1 : ∑ j ∈ Finset.range n, (if j = n then (1:ℝ) else -(e j)) • R.v j
        = ∑ j ∈ Finset.range n, (-(e j)) • R.v j :=
      Finset.sum_congr rfl fun j hj => by
        rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]
    simp only []
    rw [h1, if_true, one_smul]
    show R.v n - ∑ k ∈ Finset.range n,
        schwartzL2Inner (R.v n) (gramSchmidtField R k) • gramSchmidtField R k
      = ∑ j ∈ Finset.range n, -(e j) • R.v j + R.v n
    rw [he]
    simp only [neg_smul, Finset.sum_neg_distrib]
    exact sub_eq_neg_add _ _

/-- **Residual positivity**: `L²`-linear independence of the raw family forces
every Gram–Schmidt residual to have strictly positive `L²` seminorm — the
well-definedness of the normalization. -/
theorem gsResidual_inner_pos (R : RawDivFreeFamily) (n : ℕ) :
    0 < schwartzL2Inner (gsResidual R n) (gsResidual R n) := by
  rcases lt_or_eq_of_le (schwartzL2Inner_self_nonneg (gsResidual R n)) with h | h
  · exact h
  · exfalso
    obtain ⟨c, hc, hcn⟩ := gsResidual_repr R n
    have h0 : schwartzL2Inner (∑ j ∈ Finset.range (n+1), c j • R.v j)
        (∑ j ∈ Finset.range (n+1), c j • R.v j) = 0 := by rw [← hc, ← h]
    have hz := R.independent (n+1) c h0 n (Finset.self_mem_range_succ n)
    rw [hcn] at hz
    exact one_ne_zero hz

/-- **The orthonormality table**, by induction: below every horizon `n` the
Gram–Schmidt fields satisfy `⟨w i, w k⟩ = δ_ik`.  The inductive step is the
banked residual orthogonality (`gramSchmidt_residual_inner`) plus the banked
normalization identity (`schwartzL2Inner_normalize_self`). -/
theorem gramSchmidtField_orthonormal_table (R : RawDivFreeFamily) :
    ∀ n : ℕ, ∀ i k : ℕ, i < n → k < n →
      schwartzL2Inner (gramSchmidtField R i) (gramSchmidtField R k) =
        if i = k then 1 else 0 := by
  intro n
  induction n with
  | zero => intro i k hi _; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    have hwnj : ∀ j : ℕ, j < n →
        schwartzL2Inner (gramSchmidtField R n) (gramSchmidtField R j) = 0 := by
      intro j hj
      rw [gramSchmidtField_eq, schwartzL2Inner_smul_left]
      have hres : schwartzL2Inner (gsResidual R n) (gramSchmidtField R j) = 0 :=
        gramSchmidt_residual_inner (gramSchmidtField R) n ih (R.v n) hj
      rw [hres, mul_zero]
    intro i k hi hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hie
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hke
      · exact ih i k hi' hk'
      · rw [hke, if_neg (ne_of_lt hi'), schwartzL2Inner_comm]
        exact hwnj i hi'
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hke
      · rw [hie, if_neg (ne_of_gt hk')]
        exact hwnj k hk'
      · rw [hie, hke, if_pos rfl, gramSchmidtField_eq]
        exact schwartzL2Inner_normalize_self (gsResidual R n) (gsResidual_inner_pos R n)

/-- Full orthonormality of the Gram–Schmidt family. -/
theorem gramSchmidtField_orthonormal (R : RawDivFreeFamily) (i j : ℕ) :
    schwartzL2Inner (gramSchmidtField R i) (gramSchmidtField R j) =
      if i = j then 1 else 0 :=
  gramSchmidtField_orthonormal_table R (max i j + 1) i j
    (Nat.lt_succ_of_le (le_max_left i j)) (Nat.lt_succ_of_le (le_max_right i j))

/-- Each Gram–Schmidt field lies in the span of the first `n + 1` raw
fields. -/
theorem gramSchmidtField_inSpan (R : RawDivFreeFamily) (n : ℕ) :
    FinComb R.v (n + 1) (gramSchmidtField R n) := by
  obtain ⟨c, hc, -⟩ := gsResidual_repr R n
  rw [gramSchmidtField_eq]
  exact finComb_smul _ ⟨c, hc⟩

/-- The Gram–Schmidt fields stay inside the divergence-free constraint
manifold (pure linearity of the divergence). -/
theorem gramSchmidtField_divergenceFree (R : RawDivFreeFamily) (n : ℕ) :
    DivergenceFreeInitial (gramSchmidtField R n) := by
  obtain ⟨c, hc⟩ := gramSchmidtField_inSpan R n
  rw [hc]
  exact divergenceFreeInitial_sum_smul _ _ _ R.divergence_free

/-- **Span recovery**: each raw field lies in the span of the first `j + 1`
Gram–Schmidt fields (the normalization scalar is invertible by residual
positivity), so finite raw spans transfer to Gram–Schmidt spans. -/
theorem raw_inSpanW (R : RawDivFreeFamily) (j : ℕ) :
    FinComb (gramSchmidtField R) (j + 1) (R.v j) := by
  have hpos := gsResidual_inner_pos R j
  have hsq : Real.sqrt (schwartzL2Inner (gsResidual R j) (gsResidual R j)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hres : gsResidual R j =
      Real.sqrt (schwartzL2Inner (gsResidual R j) (gsResidual R j)) • gramSchmidtField R j := by
    rw [gramSchmidtField_eq, smul_smul, mul_one_div, div_self hsq, one_smul]
  have hv : R.v j = gsResidual R j + ∑ k ∈ Finset.range j,
      schwartzL2Inner (R.v j) (gramSchmidtField R k) • gramSchmidtField R k :=
    (sub_add_cancel _ _).symm
  rw [hv, hres]
  exact finComb_add (finComb_smul _ (finComb_self _ (Nat.lt_succ_self j)))
    (finComb_sum_smul _ _ _ fun k hk => finComb_self _
      (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))

/-- **Density transfer**: the raw family's `L²`-dense finite spans transfer
verbatim to the Gram–Schmidt family (the same approximant, re-expressed). -/
theorem gramSchmidtField_dense_span (R : RawDivFreeFamily) :
    ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
    ∃ (m : ℕ) (c : ℕ → ℝ),
      schwartzL2Inner (u - ∑ j ∈ Finset.range m, c j • gramSchmidtField R j)
        (u - ∑ j ∈ Finset.range m, c j • gramSchmidtField R j) < ε := by
  intro u hu ε hε
  obtain ⟨m, c, hc⟩ := R.dense_span u hu ε hε
  obtain ⟨d, hd⟩ : FinComb (gramSchmidtField R) m (∑ j ∈ Finset.range m, c j • R.v j) :=
    finComb_sum_smul _ _ _ fun j hj =>
      finComb_mono (Finset.mem_range.mp hj) (raw_inSpanW R j)
  exact ⟨m, d, by rw [← hd]; exact hc⟩

/-- **Gram–Schmidt orthonormalization in the `L²` seminorm** [Robinson–
Rodrigo–Sadowski Ch. 4; Temam III §3].  A raw dense divergence-free family
orthonormalizes into a `GalerkinBasisFamily`: the recursion
`w_n = normalize(v_n − ∑_{k<n} ⟨v_n, w_k⟩ w_k)` (realized as
`gramSchmidtField`) (i) preserves divergence-free — each `w_n` is a finite
`ℝ`-combination of the `v_j` (`gramSchmidtField_divergenceFree`); (ii) yields
`⟨w_i, w_j⟩ = δ_ij` (`gramSchmidtField_orthonormal`; the `independent` field
forces residual positivity via `gsResidual_repr`); and (iii) preserves the
finite spans, so `dense_span` transfers verbatim
(`gramSchmidtField_dense_span`). -/
theorem rawDivFree_orthonormalize (R : RawDivFreeFamily) : Nonempty GalerkinBasisFamily :=
  ⟨{ w := gramSchmidtField R
     divergence_free := gramSchmidtField_divergenceFree R
     orthonormal := gramSchmidtField_orthonormal R
     dense_span := gramSchmidtField_dense_span R }⟩

/-- **Existence of the Galerkin basis family**, reduced to the two named leaves:
a raw dense divergence-free family (`exists_rawDivFreeFamily`, the density core)
orthonormalized by Gram–Schmidt (`rawDivFree_orthonormalize`).  The divergence-
free preservation under the orthonormalization is already banked
(`divergenceFreeInitial_sum_smul`); the self-adjointness, skew transfer, and
`initial_converges` (Bessel) consumers of `GalerkinBasisFamily` are all
established above, so this witness is the last gate on the whole Galerkin
layer [Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3; Leray 1934]. -/
theorem exists_galerkinBasisFamily : Nonempty GalerkinBasisFamily :=
  rawDivFree_orthonormalize exists_rawDivFreeFamily.some

/-- The `j`-th Galerkin coefficient `⟨u, w_j⟩_{L²}`. -/
def GalerkinBasisFamily.coeff (W : GalerkinBasisFamily) (u : SchwartzVelocity) (j : ℕ) : ℝ :=
  schwartzL2Inner u (W.w j)

/-- The `m`-mode Galerkin projection `P_m u = ∑_{j<m} ⟨u, w_j⟩ • w_j`. -/
def GalerkinBasisFamily.proj (W : GalerkinBasisFamily) (m : ℕ) (u : SchwartzVelocity) :
    SchwartzVelocity :=
  ∑ j ∈ Finset.range m, W.coeff u j • W.w j

/-- **The projection fixes its own modes**: `P_m w_j = w_j` for `j < m`
(pure orthonormality algebra). -/
theorem proj_basis (W : GalerkinBasisFamily) {m j : ℕ} (hj : j < m) :
    W.proj m (W.w j) = W.w j := by
  unfold GalerkinBasisFamily.proj GalerkinBasisFamily.coeff
  rw [Finset.sum_eq_single j]
  · rw [W.orthonormal j j, if_pos rfl, one_smul]
  · intro i hi hij
    rw [W.orthonormal j i, if_neg (fun h => hij h.symm), zero_smul]
  · intro hj'
    exact absurd (Finset.mem_range.mpr hj) hj'

/-- **The projection stays in the divergence-free class.**  A finite linear
combination of divergence-free fields is divergence-free — the structural fact
letting the projected system evolve inside the constraint manifold, so the
finite-mode ODE of `galerkin_approximation_exists` never leaves the
divergence-free modes. -/
theorem proj_divergence_free (W : GalerkinBasisFamily) (m : ℕ) (u : SchwartzVelocity) :
    DivergenceFreeInitial (W.proj m u) := by
  unfold GalerkinBasisFamily.proj
  exact divergenceFreeInitial_sum_smul _ (W.coeff u) W.w W.divergence_free

/-- Non-degeneracy smoke: the projection of the zero field is zero. -/
theorem proj_zero (W : GalerkinBasisFamily) (m : ℕ) : W.proj m 0 = 0 := by
  unfold GalerkinBasisFamily.proj GalerkinBasisFamily.coeff
  apply Finset.sum_eq_zero
  intro j _
  have h0 : schwartzL2Inner 0 (W.w j) = 0 := by
    unfold schwartzL2Inner
    have hz : (fun x : Space => officialInner ((0 : SchwartzVelocity) x) ((W.w j) x)) =
        fun _ : Space => 0 := by
      funext x; simp [officialInner_zero_left]
    rw [hz, integral_zero]
  rw [h0, zero_smul]

/-- **The `m`-mode Galerkin projection is `L²`-self-adjoint**:
`⟨P_m u, v⟩ = ⟨u, P_m v⟩` (orthonormality algebra + bilinearity of
`schwartzL2Inner`).  Self-adjointness converts the *projected* nonlinearity
pairing `⟨P_m B u, u⟩` into the *bare* transport pairing `⟨B u, u⟩` on the span
— the mechanism behind the skew transfer below [Temam III §3;
Constantin–Foias II]. -/
theorem proj_self_adjoint (W : GalerkinBasisFamily) (m : ℕ) (u v : SchwartzVelocity) :
    schwartzL2Inner (W.proj m u) v = schwartzL2Inner u (W.proj m v) := by
  unfold GalerkinBasisFamily.proj
  rw [schwartzL2Inner_sum_left, schwartzL2Inner_sum_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [schwartzL2Inner_smul_left, schwartzL2Inner_smul_right]
  unfold GalerkinBasisFamily.coeff
  rw [schwartzL2Inner_comm (W.w j) v]
  ring

/-- **Skew transfer of the projected nonlinearity** `⟨P_m B u, u⟩ = 0`.  For a
finite-mode state `u` in the span (`P_m u = u`), self-adjointness of `P_m` turns
the projected pairing into the bare transport pairing `⟨B u, u⟩` (here `b = B u`),
which vanishes by the divergence-free transport energy identity
`∫ ((u·∇)u)·u = 0` — the whole-space integral of
`Navier.Analysis.EnergyConvectionCancellation.convection_work_eq_staticDivergence_of_incompressible`
[Temam III §3; Leray 1934].  This supplies the `hB` hypothesis of
`galerkin_apriori_bound` at the concrete `schwartzL2Inner` level: the Leray
projection kills the nonlinear transport term's diagonal, so it contributes
nothing to the energy balance.  The transport identity enters as `hskew`, a
strictly-different fact from the conclusion (which carries the projection). -/
theorem proj_skew_transfer (W : GalerkinBasisFamily) (m : ℕ) (b u : SchwartzVelocity)
    (hu : W.proj m u = u) (hskew : schwartzL2Inner b u = 0) :
    schwartzL2Inner (W.proj m b) u = 0 := by
  rw [proj_self_adjoint, hu]; exact hskew

/-- **The projection reproduces the datum's coefficients on the basis**:
`⟨P_m u, w_k⟩ = ⟨u, w_k⟩` for `k < m` (orthonormality). -/
theorem proj_inner_basis (W : GalerkinBasisFamily) {m k : ℕ} (hk : k < m)
    (u : SchwartzVelocity) :
    schwartzL2Inner (W.proj m u) (W.w k) = schwartzL2Inner u (W.w k) := by
  unfold GalerkinBasisFamily.proj
  rw [schwartzL2Inner_sum_left, Finset.sum_eq_single k]
  · rw [schwartzL2Inner_smul_left, W.orthonormal k k, if_pos rfl, mul_one]; rfl
  · intro j _ hjk
    rw [schwartzL2Inner_smul_left, W.orthonormal j k, if_neg hjk, mul_zero]
  · intro hkr; exact absurd (Finset.mem_range.mpr hk) hkr

/-- **The projection residual is orthogonal to every retained basis field**:
`⟨u − P_m u, w_k⟩ = 0` for `k < m`. -/
theorem residual_inner_basis (W : GalerkinBasisFamily) {m k : ℕ} (hk : k < m)
    (u : SchwartzVelocity) :
    schwartzL2Inner (u - W.proj m u) (W.w k) = 0 := by
  rw [schwartzL2Inner_sub_left, proj_inner_basis W hk u, sub_self]

/-- **The residual is orthogonal to the whole retained span**: `⟨u − P_m u, v⟩ = 0`
for any `v = ∑_{k<m} c_k w_k`. -/
theorem residual_inner_span (W : GalerkinBasisFamily) (m : ℕ) (u : SchwartzVelocity)
    (c : ℕ → ℝ) :
    schwartzL2Inner (u - W.proj m u) (∑ k ∈ Finset.range m, c k • W.w k) = 0 := by
  rw [schwartzL2Inner_sum_right]
  apply Finset.sum_eq_zero
  intro k hk
  rw [schwartzL2Inner_smul_right, residual_inner_basis W (Finset.mem_range.mp hk) u, mul_zero]

/-- **Best-approximation property** (Bessel).  Among all combinations
`v = ∑_{k<m} c_k w_k` of the first `m` modes, the projection `P_m u` minimizes
the `L²` seminorm error: `Q(u − P_m u) ≤ Q(u − v)`.  Pythagoras on the
orthogonal split `u − v = (u − P_m u) + (P_m u − v)` with the residual `⊥` the
span [Temam III §3; Robinson–Rodrigo–Sadowski Ch. 4]. -/
theorem proj_best_approx (W : GalerkinBasisFamily) (m : ℕ) (u : SchwartzVelocity)
    (c : ℕ → ℝ) :
    schwartzL2Inner (u - W.proj m u) (u - W.proj m u)
      ≤ schwartzL2Inner (u - ∑ k ∈ Finset.range m, c k • W.w k)
                        (u - ∑ k ∈ Finset.range m, c k • W.w k) := by
  have hPv : W.proj m u - (∑ k ∈ Finset.range m, c k • W.w k)
      = ∑ k ∈ Finset.range m, (W.coeff u k - c k) • W.w k := by
    unfold GalerkinBasisFamily.proj
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => (sub_smul _ _ _).symm)
  have horth : schwartzL2Inner (u - W.proj m u)
      (W.proj m u - ∑ k ∈ Finset.range m, c k • W.w k) = 0 := by
    rw [hPv]; exact residual_inner_span W m u (fun k => W.coeff u k - c k)
  have hsplit : u - (∑ k ∈ Finset.range m, c k • W.w k)
      = (u - W.proj m u) + (W.proj m u - ∑ k ∈ Finset.range m, c k • W.w k) := by abel
  rw [hsplit, schwartzL2Inner_self_add_of_orthogonal _ _ horth]
  have := schwartzL2Inner_self_nonneg (W.proj m u - ∑ k ∈ Finset.range m, c k • W.w k)
  linarith

/-- **The projection error is antitone in the mode count**: nested spans give
`Q(u − P_{m+1} u) ≤ Q(u − P_m u)` (best-approximation applied at level `m+1`
against `P_m u ∈ span{w_0,…,w_{m−1}} ⊆ span{w_0,…,w_m}`). -/
theorem proj_error_antitone (W : GalerkinBasisFamily) (u : SchwartzVelocity) :
    Antitone (fun m => schwartzL2Inner (u - W.proj m u) (u - W.proj m u)) := by
  apply antitone_nat_of_succ_le
  intro m
  have hkey := proj_best_approx W (m+1) u (fun k => if k < m then W.coeff u k else 0)
  have heq : (∑ k ∈ Finset.range (m+1), (if k < m then W.coeff u k else 0) • W.w k)
      = W.proj m u := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl m), zero_smul, add_zero]
    unfold GalerkinBasisFamily.proj
    exact Finset.sum_congr rfl (fun k hk => by rw [if_pos (Finset.mem_range.mp hk)])
  rw [heq] at hkey
  exact hkey

/-- **Projection convergence (Bessel).**  The `m`-mode projections converge to
the datum in the `L²` seminorm: `‖u₀ − P_m u₀‖²_{L²} → 0` [Temam III §3;
Robinson–Rodrigo–Sadowski Ch. 4; Leray 1934].  The error is nonnegative
(`schwartzL2Inner_self_nonneg`) and antitone (`proj_error_antitone`, nested
spans + best approximation); `dense_span` drives it below every `ε` via the
best-approximation bound `proj_best_approx`.  This is the `initial_converges`
field of `GalerkinApproximation` up to the coordinate-norm equivalence
bookkeeping on `Fin 3 → ℝ`. -/
theorem proj_tendsto_self (W : GalerkinBasisFamily) (u₀ : SchwartzVelocity)
    (hu₀ : DivergenceFreeInitial u₀) :
    Filter.Tendsto
      (fun m => schwartzL2Inner (u₀ - W.proj m u₀) (u₀ - W.proj m u₀))
      Filter.atTop (nhds 0) := by
  have hEnn : ∀ m, 0 ≤ schwartzL2Inner (u₀ - W.proj m u₀) (u₀ - W.proj m u₀) :=
    fun m => schwartzL2Inner_self_nonneg _
  have hanti := proj_error_antitone W u₀
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, c, hmc⟩ := W.dense_span u₀ hu₀ ε hε
  refine ⟨m, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hEnn n)]
  calc schwartzL2Inner (u₀ - W.proj n u₀) (u₀ - W.proj n u₀)
      ≤ schwartzL2Inner (u₀ - W.proj m u₀) (u₀ - W.proj m u₀) := hanti hn
    _ ≤ schwartzL2Inner (u₀ - ∑ k ∈ Finset.range m, c k • W.w k)
                        (u₀ - ∑ k ∈ Finset.range m, c k • W.w k) := proj_best_approx W m u₀ c
    _ < ε := hmc

/-!
## The `initial_converges` field, delivered

`proj_tendsto_self` above is the Bessel convergence in the Euclidean `L²`
seminorm; `GalerkinApproximation.initial_converges` is stated with the *product*
norm on `Space`.  `Navier.Analysis.LerayWeak.tendsto_integral_norm_sq_of_tendsto_officialInner_self`
is the bridge between them, so the two theorems below hand the Galerkin assembly
its `initial_converges` / `initial_converges_L2` field verbatim, with
`initialMode m := P_m u₀`.
-/

/-- The `L²` seminorm is invariant under negation. -/
theorem schwartzL2Inner_neg_neg (a : SchwartzVelocity) :
    schwartzL2Inner (-a) (-a) = schwartzL2Inner a a := by
  rw [schwartzL2Inner_neg_left, schwartzL2Inner_comm a (-a), schwartzL2Inner_neg_left, neg_neg]

/-- The `L²` seminorm of a difference is symmetric in its two arguments. -/
theorem schwartzL2Inner_sub_symm (a b : SchwartzVelocity) :
    schwartzL2Inner (a - b) (a - b) = schwartzL2Inner (b - a) (b - a) := by
  rw [show b - a = -(a - b) from (neg_sub _ _).symm, schwartzL2Inner_neg_neg]

/-- **`initial_converges_L2` for the Galerkin projection.**  Exactly the
`Navier.Analysis.LerayWeak.GalerkinModeData.initial_converges_L2` field with
`initialMode m := P_m u₀`: Bessel convergence (`proj_tendsto_self`) rewritten
with the error taken in the `P_m u₀ − u₀` orientation. -/
theorem proj_initial_converges_L2 (W : GalerkinBasisFamily) (u₀ : SchwartzVelocity)
    (hu₀ : DivergenceFreeInitial u₀) :
    Filter.Tendsto (fun m => ∫ x : Space,
        officialInner ((W.proj m u₀ - u₀) x) ((W.proj m u₀ - u₀) x))
      Filter.atTop (nhds 0) := by
  have h := proj_tendsto_self W u₀ hu₀
  have hfun : (fun m => schwartzL2Inner (u₀ - W.proj m u₀) (u₀ - W.proj m u₀))
      = fun m => ∫ x : Space,
          officialInner ((W.proj m u₀ - u₀) x) ((W.proj m u₀ - u₀) x) := by
    funext m
    rw [schwartzL2Inner_sub_symm u₀ (W.proj m u₀)]
    rfl
  rw [hfun] at h
  exact h

/-- **`initial_converges` for the Galerkin projection.**  Exactly the
`Navier.Analysis.LerayWeak.GalerkinApproximation.initial_converges` field with
`approx m 0 := P_m u₀`, obtained from the Euclidean-seminorm statement above
through the coordinate-norm bridge. -/
theorem proj_initial_converges (W : GalerkinBasisFamily) (u₀ : SchwartzVelocity)
    (hu₀ : DivergenceFreeInitial u₀) :
    Filter.Tendsto (fun m => ∫ x : Space, ‖(W.proj m u₀) x - u₀ x‖ ^ 2)
      Filter.atTop (nhds 0) := by
  have h := tendsto_integral_norm_sq_of_tendsto_officialInner_self
    (fun m => W.proj m u₀ - u₀) (proj_initial_converges_L2 W u₀ hu₀)
  simpa using h

end Navier.Analysis.GalerkinBasis
