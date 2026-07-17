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

## Skeletons (honest `sorry`, strictly-lower named leaves)

* `exists_galerkinBasisFamily` — existence of the family [countable `L²`-dense
  subfamily of divergence-free Schwartz fields + Gram–Schmidt;
  Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3; est ~400 LOC].  This is the
  non-vacuity witness for every `(W : GalerkinBasisFamily)`-consumer here.

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

/-- **[NAMED RESIDUAL — basis existence; countable `L²`-dense family of
divergence-free Schwartz fields (e.g. curls of bump towers) + Gram–Schmidt
orthonormalization; Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3; Leray 1934
§§18–20; est ~400 LOC.]**  The divergence-free Schwartz class is an
infinite-dimensional separable pre-Hilbert space under `schwartzL2Inner`
(`exists_nonzero_testFunction`'s curl-of-bump construction generates
infinitely many independent members at disjoint supports), so a Gram–Schmidt
pass over a countable dense subfamily produces the family.  Mathlib-absent:
the divergence-free-constrained density argument. -/
theorem exists_galerkinBasisFamily : Nonempty GalerkinBasisFamily := by
  sorry

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
  intro x
  suffices h : ∀ (s : Finset ℕ) (c : ℕ → ℝ),
      staticDivergence (fun y => (∑ j ∈ s, c j • W.w j : SchwartzVelocity) y) x = 0 by
    exact h (Finset.range m) (W.coeff u)
  intro s c
  induction s using Finset.induction_on with
  | empty => simp [staticDivergence]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hcoe : (fun y => (c a • W.w a + ∑ j ∈ s, c j • W.w j : SchwartzVelocity) y) =
        fun y => (c a • W.w a : SchwartzVelocity) y +
          (∑ j ∈ s, c j • W.w j : SchwartzVelocity) y := by
      funext y; simp
    rw [hcoe, staticDivergence_add _ _ x
      (schwartz_differentiableAt _ x) (schwartz_differentiableAt _ x)]
    have h1 : staticDivergence (fun y => (c a • W.w a : SchwartzVelocity) y) x = 0 := by
      have hcoe2 : (fun y => (c a • W.w a : SchwartzVelocity) y) =
          fun y => c a • (W.w a) y := by funext y; simp
      rw [hcoe2, staticDivergence_const_smul _ _ _ (schwartz_differentiableAt _ x),
        W.divergence_free a x, mul_zero]
    rw [h1, ih, add_zero]

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

end Navier.Analysis.GalerkinBasis
