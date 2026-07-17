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

## Skeletons (honest `sorry`, strictly-lower named leaves)

* `exists_galerkinBasisFamily` — existence of the family [countable `L²`-dense
  subfamily of divergence-free Schwartz fields + Gram–Schmidt;
  Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3; est ~400 LOC].  This is the
  non-vacuity witness for every `(W : GalerkinBasisFamily)`-consumer here.
* `proj_tendsto_self` — `P_m u₀ → u₀` in the `L²` seminorm [Bessel
  best-approximation on nested spans + `dense_span`; Temam III §3; est ~150
  LOC].  This is exactly the `initial_converges` field of
  `GalerkinApproximation` (up to the official-vs-sup coordinate-norm
  equivalence bookkeeping on `Fin 3 → ℝ`).

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

/-- **[NAMED RESIDUAL — projection convergence; Bessel best-approximation over
the nested spans + `dense_span`; Temam III §3; Robinson–Rodrigo–Sadowski
Ch. 4; est ~150 LOC.]**  The `m`-mode projections converge to the datum in the
`L²` seminorm: `‖u₀ − P_m u₀‖²_{L²} → 0`.  Bessel: `P_m u₀` minimizes the
`L²` error over `span{w_0, …, w_{m−1}}` (orthonormality + bilinearity via
`schwartzPairing_integrable`), the spans are nested, and `dense_span` drives
the infimum to `0`.  This is the `initial_converges` field of
`GalerkinApproximation` up to the coordinate-norm equivalence bookkeeping on
`Fin 3 → ℝ`. -/
theorem proj_tendsto_self (W : GalerkinBasisFamily) (u₀ : SchwartzVelocity)
    (hu₀ : DivergenceFreeInitial u₀) :
    Filter.Tendsto
      (fun m => schwartzL2Inner (u₀ - W.proj m u₀) (u₀ - W.proj m u₀))
      Filter.atTop (nhds 0) := by
  sorry

end Navier.Analysis.GalerkinBasis
