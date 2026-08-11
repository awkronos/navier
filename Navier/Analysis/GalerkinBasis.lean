import Navier.Analysis.GalerkinRawFamily
import Navier.Analysis.EnergyDissipation
import Navier.Analysis.EnergyConvectionIntegral
import Navier.Analysis.CurlIdentities

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
* `pert` / `nextIdx` / `nextV` / `accSet` / `vfam` and
  `vfam_divFree`, `vfam_not_mem_span`, `vfam_independent`, `vfam_dense`,
  `exists_denseIndependentDivFreeFamily_of_reservoir` — **the greedy off-span
  recursion**: perturbing the dense family by vanishing multiples of an
  independent reservoir yields one family that is at once divergence-free,
  `L²`-independent and `L²`-member-dense.
* `divergenceFreeInitial_add_smul` — divergence-free fields are closed under
  `a + c • b` (the two-term case the recursion needs).
* `exists_dense_divFree_family` — **the density core, certified**: a countable
  family of divergence-free Schwartz fields `L²`-approximating every
  divergence-free Schwartz datum, from second-countability of `L²` (hereditary,
  so the dense sequence is drawn from the divergence-free image itself).
* `toL2_smul` / `toL2_sum` / `independent_iff_toL2` — the residual's
  `independent` conjunct restated as ordinary linear independence of the `L²`
  images `toL2 ∘ v`.  `schwartzL2Inner` is only a seminorm on Schwartz fields,
  but `norm_toL2_sq` makes it the honest `Lp` norm, so the two notions coincide.

## Import-DAG placement note

* `exists_denseIndependentDivFreeFamily` — established here.
  `exists_denseIndependentDivFreeFamily_of_reservoir` derives the statement from
  any countable divergence-free `L²`-independent family, and
  `Navier.Analysis.GalerkinRawFamily.exists_countable_independent_divFree_family`
  builds one.  The two used to be mutually unreachable, because the reservoir
  file imported this one.  The shared `schwartzL2Inner` layer now lives in
  `Navier.Analysis.SchwartzL2Pairing`, upstream of both, so the chain reads
  `LerayWeak → SchwartzL2Pairing → GalerkinRawFamily → GalerkinBasis` and the
  instantiation is two lines.

With this layer, `galerkin_approximation_exists`'s remaining inputs are: the
projected Stokes/nonlinearity operators on `span{w_0, …, w_{m−1}}` (feeding
`finiteDim_dissipative_ode_global` + `galerkin_apriori_bound` +
`EnergyDissipation.dissipation_integral_le_forward`, all BANKED), and the
time-equicontinuity/weak-consistency bookkeeping.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped LineDeriv

namespace Navier.Analysis.GalerkinBasis

open Navier
open Navier.Analysis.Enstrophy
open Navier.Analysis.LerayWeak
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity

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
theorem divergenceFreeInitial_sum_smul {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ)
    (v : ι → SchwartzVelocity) (hv : ∀ j, DivergenceFreeInitial (v j)) :
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

/-- The concrete Schwartz pairing is exactly the real Hilbert inner product
after embedding both fields into `L²`. -/
theorem inner_toL2_eq_schwartzL2Inner (u v : SchwartzVelocity) :
    inner ℝ (toL2 u) (toL2 v) = schwartzL2Inner u v := by
  rw [MeasureTheory.L2.inner_def, schwartzL2Inner]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (toES u) 2 (volume : Measure Space),
    SchwartzMap.coeFn_toLp (toES v) 2 (volume : Measure Space)] with x hu hv
  simp only [toL2]
  rw [hu, hv]
  rfl

/-- Cauchy--Schwarz for the official Schwartz `L²` pairing. -/
theorem abs_schwartzL2Inner_le (u v : SchwartzVelocity) :
    |schwartzL2Inner u v| ≤ ‖toL2 u‖ * ‖toL2 v‖ := by
  rw [← inner_toL2_eq_schwartzL2Inner]
  exact abs_real_inner_le_norm _ _

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

theorem toL2_smul (c : ℝ) (u : SchwartzVelocity) : toL2 (c • u) = c • toL2 u := by
  unfold toL2 toES
  rw [map_smul]
  exact SetLike.coe_eq_coe.mp rfl

theorem toL2_sum (n : ℕ) (c : ℕ → ℝ) (v : ℕ → SchwartzVelocity) :
    toL2 (∑ j ∈ Finset.range n, c j • v j) = ∑ j ∈ Finset.range n, c j • toL2 (v j) := by
  induction n with
  | zero => simp [toL2, toES]; exact SetLike.coe_eq_coe.mp rfl
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih, ← toL2_smul]
      unfold toL2 toES
      rw [map_add]
      exact SetLike.coe_eq_coe.mp rfl

/-- `schwartzL2Inner`-independence is exactly linear independence of the `L²`
images: the seminorm is a genuine norm after `toL2`. -/
theorem independent_iff_toL2 (v : ℕ → SchwartzVelocity) :
    (∀ (n : ℕ) (c : ℕ → ℝ),
        schwartzL2Inner (∑ j ∈ Finset.range n, c j • v j)
          (∑ j ∈ Finset.range n, c j • v j) = 0 → ∀ j ∈ Finset.range n, c j = 0)
      ↔ (∀ (n : ℕ) (c : ℕ → ℝ),
        (∑ j ∈ Finset.range n, c j • toL2 (v j)) = 0 → ∀ j ∈ Finset.range n, c j = 0) := by
  constructor <;> intro h n c hc
  · refine h n c ?_
    rw [← norm_toL2_sq, toL2_sum, hc, norm_zero]; ring
  · refine h n c ?_
    have : ‖toL2 (∑ j ∈ Finset.range n, c j • v j)‖ ^ 2 = 0 := by rw [norm_toL2_sq]; exact hc
    rw [← toL2_sum]
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-!
### Off-span selection (the counting argument)

The two general facts the independence reconciliation runs on, stated for an
arbitrary `ℝ`-module so nothing here depends on `Lp` or on Schwartz decay.

`exists_not_mem_span_of_linearIndependent` is the load-bearing one: an
`ℕ`-indexed linearly independent family cannot lie entirely inside the span of a
finite set, because it would then be an infinite independent family in a
finite-dimensional (hence Noetherian) module.  This is what makes the greedy
step of the recursion well-defined — at each stage the already-chosen prefix
spans a finite-dimensional subspace, so some reservoir element escapes it.

`linearIndependent_of_range_form` converts this repo's `Finset.range`-indexed
independence statement into Mathlib's `LinearIndependent`; the converse
direction is immediate from `linearIndependent_iff'`.
-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Range-form independence implies `LinearIndependent`. -/
theorem linearIndependent_of_range_form (y : ℕ → V)
    (h : ∀ (n : ℕ) (c : ℕ → ℝ), (∑ j ∈ Finset.range n, c j • y j) = 0 →
      ∀ j ∈ Finset.range n, c j = 0) :
    LinearIndependent ℝ y := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  set n := s.sup id + 1 with hn
  have hsub : s ⊆ Finset.range n := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))
  set c : ℕ → ℝ := fun j => if j ∈ s then g j else 0 with hc
  have hsum : (∑ j ∈ Finset.range n, c j • y j) = 0 := by
    rw [← Finset.sum_subset hsub (fun x _ hxs => by simp [hc, hxs])]
    exact hs.symm ▸ Finset.sum_congr rfl (fun x hx => by simp [hc, hx])
  have := h n c hsum i (hsub hi)
  simpa [hc, hi] using this

/-- **The counting lemma.**  An `ℕ`-indexed linearly independent family cannot lie
entirely inside the span of a finite set. -/
theorem exists_not_mem_span_of_linearIndependent (y : ℕ → V)
    (hy : LinearIndependent ℝ y) (s : Finset V) :
    ∃ k : ℕ, y k ∉ Submodule.span ℝ (s : Set V) := by
  by_contra hcon
  push Not at hcon
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (s : Set V)) :=
    FiniteDimensional.span_of_finite ℝ s.finite_toSet
  have hy' : LinearIndependent ℝ (fun k : ℕ => (⟨y k, hcon k⟩ : Submodule.span ℝ (s : Set V))) :=
    LinearIndependent.of_comp (Submodule.span ℝ (s : Set V)).subtype (by exact hy)
  haveI := hy'.finite_of_isNoetherian
  exact _root_.not_finite ℕ


end Separability

/-!
### The greedy off-span recursion

Reconciles the dense family with linear independence.  At stage `n` we perturb
the dense member `w n` by a vanishing multiple of a reservoir element chosen off
the span of everything built so far:
`v n = w n + pert n k · p k` with `pert n k · ‖p k‖ < 1/(n+1)`.

The reservoir is a *hypothesis* of
`exists_denseIndependentDivFreeFamily_of_reservoir`, the strongest form the
recursion establishes on its own.  It is instantiated below at the concrete
disjoint-translate family
`Navier.Analysis.GalerkinRawFamily.exists_countable_independent_divFree_family`,
which this file imports — the shared `schwartzL2Inner` layer sits upstream of
both in `Navier.Analysis.SchwartzL2Pairing`.
-/

section IndependenceRecursion

open scoped Classical

local notation "L2Sp" => Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space)

theorem toL2_add (u v : SchwartzVelocity) : toL2 (u + v) = toL2 u + toL2 v := by
  unfold toL2 toES
  rw [map_add]
  exact SetLike.coe_eq_coe.mp rfl

/-- Divergence-free fields are closed under `a + c • b`. -/
theorem divergenceFreeInitial_add_smul (a b : SchwartzVelocity) (c : ℝ)
    (ha : DivergenceFreeInitial a) (hb : DivergenceFreeInitial b) :
    DivergenceFreeInitial (a + c • b) := by
  intro x
  have hcoe : (fun y => (a + c • b : SchwartzVelocity) y)
      = fun y => a y + (c • b : SchwartzVelocity) y := by funext y; simp
  rw [hcoe, staticDivergence_add _ _ x (schwartz_differentiableAt _ x)
    (schwartz_differentiableAt _ x)]
  have h1 : staticDivergence (fun y => (c • b : SchwartzVelocity) y) x = 0 := by
    have hcoe2 : (fun y => (c • b : SchwartzVelocity) y) = fun y => c • b y := by funext y; simp
    rw [hcoe2, staticDivergence_const_smul _ _ _ (schwartz_differentiableAt _ x), hb x, mul_zero]
  rw [h1, ha x, add_zero]

/-- Perturbation size at stage `n` with reservoir index `k`; positive, and small
enough that the perturbation moves the `L²` point by less than `1/(n+1)`. -/
def pert (p : ℕ → SchwartzVelocity) (n k : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) * (‖toL2 (p k)‖ + 1))

theorem pert_pos (p : ℕ → SchwartzVelocity) (n k : ℕ) : 0 < pert p n k := by
  have h : (0:ℝ) < ((n : ℝ) + 1) * (‖toL2 (p k)‖ + 1) := by positivity
  exact div_pos one_pos h

theorem pert_mul_norm_lt (p : ℕ → SchwartzVelocity) (n k : ℕ) :
    pert p n k * ‖toL2 (p k)‖ < 1 / ((n : ℝ) + 1) := by
  have h1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0:ℝ) < ‖toL2 (p k)‖ + 1 := by positivity
  have hlt : ‖toL2 (p k)‖ / (‖toL2 (p k)‖ + 1) < 1 := by
    rw [div_lt_one h2]; linarith
  rw [pert, div_mul_eq_mul_div, one_mul]
  calc ‖toL2 (p k)‖ / (((n : ℝ) + 1) * (‖toL2 (p k)‖ + 1))
      = (1 / ((n : ℝ) + 1)) * (‖toL2 (p k)‖ / (‖toL2 (p k)‖ + 1)) := by
        field_simp
    _ < (1 / ((n : ℝ) + 1)) * 1 :=
        mul_lt_mul_of_pos_left hlt (by positivity)
    _ = 1 / ((n : ℝ) + 1) := by ring

/-- The greedy reservoir index at stage `n`. -/
def nextIdx (w p : ℕ → SchwartzVelocity) (S : Finset L2Sp) (n : ℕ) : ℕ :=
  if h : ∃ k : ℕ, toL2 (p k) ∉ Submodule.span ℝ (↑(insert (toL2 (w n)) S) : Set L2Sp)
  then Classical.choose h else 0

theorem nextIdx_spec (w p : ℕ → SchwartzVelocity)
    (hp : LinearIndependent ℝ (fun k : ℕ => toL2 (p k))) (S : Finset L2Sp) (n : ℕ) :
    toL2 (p (nextIdx w p S n)) ∉ Submodule.span ℝ (↑(insert (toL2 (w n)) S) : Set L2Sp) := by
  have h : ∃ k : ℕ, toL2 (p k) ∉ Submodule.span ℝ (↑(insert (toL2 (w n)) S) : Set L2Sp) :=
    exists_not_mem_span_of_linearIndependent (fun k : ℕ => toL2 (p k)) hp _
  rw [nextIdx, dif_pos h]
  exact Classical.choose_spec h

/-- One stage of the recursion. -/
def nextV (w p : ℕ → SchwartzVelocity) (S : Finset L2Sp) (n : ℕ) : SchwartzVelocity :=
  w n + (pert p n (nextIdx w p S n)) • p (nextIdx w p S n)

/-- The `L²` points already produced. -/
def accSet (w p : ℕ → SchwartzVelocity) : ℕ → Finset L2Sp
  | 0 => ∅
  | n + 1 => insert (toL2 (nextV w p (accSet w p n) n)) (accSet w p n)

/-- The perturbed family. -/
def vfam (w p : ℕ → SchwartzVelocity) (n : ℕ) : SchwartzVelocity :=
  nextV w p (accSet w p n) n

theorem accSet_eq (w p : ℕ → SchwartzVelocity) (n : ℕ) :
    accSet w p n = (Finset.range n).image (fun j => toL2 (vfam w p j)) := by
  induction n with
  | zero => simp [accSet]
  | succ n ih =>
      have h : accSet w p (n + 1) = insert (toL2 (vfam w p n)) (accSet w p n) := rfl
      rw [h, ih, Finset.range_add_one, Finset.image_insert]

theorem toL2_vfam (w p : ℕ → SchwartzVelocity) (n : ℕ) :
    toL2 (vfam w p n)
      = toL2 (w n) + (pert p n (nextIdx w p (accSet w p n) n)) •
          toL2 (p (nextIdx w p (accSet w p n) n)) := by
  rw [vfam, nextV, toL2_add, toL2_smul]

theorem vfam_divFree (w p : ℕ → SchwartzVelocity)
    (hw : ∀ n, DivergenceFreeInitial (w n)) (hpd : ∀ k, DivergenceFreeInitial (p k)) (n : ℕ) :
    DivergenceFreeInitial (vfam w p n) :=
  divergenceFreeInitial_add_smul _ _ _ (hw n) (hpd _)

theorem norm_toL2_vfam_sub (w p : ℕ → SchwartzVelocity) (n : ℕ) :
    ‖toL2 (vfam w p n) - toL2 (w n)‖ < 1 / ((n : ℝ) + 1) := by
  rw [toL2_vfam, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pert_pos p n _)]
  exact pert_mul_norm_lt p n _

/-- **The greedy invariant**: each new member is off the span of its predecessors. -/
theorem vfam_not_mem_span (w p : ℕ → SchwartzVelocity)
    (hp : LinearIndependent ℝ (fun k : ℕ => toL2 (p k))) (n : ℕ) :
    toL2 (vfam w p n) ∉ Submodule.span ℝ (↑(accSet w p n) : Set L2Sp) := by
  intro hmem
  set k := nextIdx w p (accSet w p n) n with hk
  set W' := Submodule.span ℝ (↑(insert (toL2 (w n)) (accSet w p n)) : Set L2Sp) with hW'
  have hsub : Submodule.span ℝ (↑(accSet w p n) : Set L2Sp) ≤ W' :=
    Submodule.span_mono (by
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff]
      exact Or.inr hx)
  have h1 : toL2 (vfam w p n) ∈ W' := hsub hmem
  have h2 : toL2 (w n) ∈ W' := Submodule.subset_span (by simp)
  have h3 : (pert p n k) • toL2 (p k) ∈ W' := by
    have hd := W'.sub_mem h1 h2
    rwa [toL2_vfam, add_sub_cancel_left] at hd
  have h4 : toL2 (p k) ∈ W' := by
    have h5 := W'.smul_mem (pert p n k)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt (pert_pos p n k)), one_smul] at h5
  exact nextIdx_spec w p hp (accSet w p n) n h4

theorem vfam_independent (w p : ℕ → SchwartzVelocity)
    (hp : LinearIndependent ℝ (fun k : ℕ => toL2 (p k))) :
    ∀ (n : ℕ) (c : ℕ → ℝ), (∑ j ∈ Finset.range n, c j • toL2 (vfam w p j)) = 0 →
      ∀ j ∈ Finset.range n, c j = 0 := by
  intro n
  induction n with
  | zero => intro c _ j hj; simp at hj
  | succ n ih =>
      intro c hc j hj
      rw [Finset.sum_range_succ] at hc
      have hA : (∑ i ∈ Finset.range n, c i • toL2 (vfam w p i))
          ∈ Submodule.span ℝ (↑(accSet w p n) : Set L2Sp) := by
        refine Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
        rw [accSet_eq]
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      have hcn : c n = 0 := by
        by_contra hne
        refine vfam_not_mem_span w p hp n ?_
        have heq : c n • toL2 (vfam w p n)
            = -(∑ i ∈ Finset.range n, c i • toL2 (vfam w p i)) :=
          (neg_eq_of_add_eq_zero_right hc).symm
        have h5 := Submodule.smul_mem _ (c n)⁻¹ (Submodule.neg_mem _ hA)
        rwa [← heq, smul_smul, inv_mul_cancel₀ hne, one_smul] at h5
      rw [hcn, zero_smul, add_zero] at hc
      rcases lt_or_eq_of_le (Finset.mem_range_succ_iff.mp hj) with h | h
      · exact ih c hc j (Finset.mem_range.mpr h)
      · rw [h]; exact hcn

/-- **Density survives the perturbation**, provided the dense family recurs at
arbitrarily large indices (which the `Nat.pair` re-indexing below arranges):
the stage-`n` perturbation moves the `L²` point by less than `1/(n+1)`, so
choosing a good index far enough out absorbs it. -/
theorem vfam_dense (w p : ℕ → SchwartzVelocity)
    (hw : ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ δ : ℝ, 0 < δ → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ ‖toL2 u - toL2 (w n)‖ < δ) :
    ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
      ∃ j : ℕ, schwartzL2Inner (u - vfam w p j) (u - vfam w p j) < ε := by
  intro u hu ε hε
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  set δ := Real.sqrt ε / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  obtain ⟨n, hnN, hn⟩ := hw u hu δ hδ N
  refine ⟨n, ?_⟩
  have hstep : ‖toL2 (w n) - toL2 (vfam w p n)‖ < 1 / ((n : ℝ) + 1) := by
    rw [← norm_neg, neg_sub]
    exact norm_toL2_vfam_sub w p n
  have hmono : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hnN
    linarith
  have hsplit : toL2 (u - vfam w p n)
      = (toL2 u - toL2 (w n)) + (toL2 (w n) - toL2 (vfam w p n)) := by
    rw [toL2_sub]; abel
  have htot : ‖toL2 (u - vfam w p n)‖ < Real.sqrt ε := by
    calc ‖toL2 (u - vfam w p n)‖
        ≤ ‖toL2 u - toL2 (w n)‖ + ‖toL2 (w n) - toL2 (vfam w p n)‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ < δ + δ := by linarith
      _ = Real.sqrt ε := by rw [hδdef]; ring
  calc schwartzL2Inner (u - vfam w p n) (u - vfam w p n)
      = ‖toL2 (u - vfam w p n)‖ ^ 2 := (norm_toL2_sq _).symm
    _ < Real.sqrt ε ^ 2 := by nlinarith [norm_nonneg (toL2 (u - vfam w p n))]
    _ = ε := Real.sq_sqrt hε.le

/-- **The density core and the independence core, combined — modulo a reservoir.**
Given *any* countable divergence-free `L²`-independent family `p`, the greedy
off-span perturbation of the separability-dense family produces a single family
that is simultaneously divergence-free, `L²`-linearly-independent, and
`L²`-member-dense in the divergence-free Schwartz class.

This is the full content of `exists_denseIndependentDivFreeFamily`; only the
reservoir is hypothesised, and it is instantiated two declarations below from
`Navier.Analysis.GalerkinRawFamily.exists_countable_independent_divFree_family`.

Reference: Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3. -/
theorem exists_denseIndependentDivFreeFamily_of_reservoir
    (p : ℕ → SchwartzVelocity)
    (hpdiv : ∀ j : ℕ, DivergenceFreeInitial (p j))
    (hpindep : ∀ (n : ℕ) (c : ℕ → ℝ),
      schwartzL2Inner (∑ j ∈ Finset.range n, c j • p j)
          (∑ j ∈ Finset.range n, c j • p j) = 0 → ∀ j ∈ Finset.range n, c j = 0) :
    ∃ v : ℕ → SchwartzVelocity,
      (∀ j : ℕ, DivergenceFreeInitial (v j)) ∧
      (∀ (n : ℕ) (c : ℕ → ℝ),
        schwartzL2Inner (∑ j ∈ Finset.range n, c j • v j)
            (∑ j ∈ Finset.range n, c j • v j) = 0 → ∀ j ∈ Finset.range n, c j = 0) ∧
      (∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
        ∃ j : ℕ, schwartzL2Inner (u - v j) (u - v j) < ε) := by
  obtain ⟨w0, hw0div, hw0dense⟩ := exists_dense_divFree_family
  set w : ℕ → SchwartzVelocity := fun n => w0 n.unpair.1 with hwdef
  have hp : LinearIndependent ℝ (fun k : ℕ => toL2 (p k)) :=
    linearIndependent_of_range_form _ ((independent_iff_toL2 p).mp hpindep)
  refine ⟨vfam w p, vfam_divFree w p (fun n => hw0div _) hpdiv,
    (independent_iff_toL2 (vfam w p)).mpr (vfam_independent w p hp), ?_⟩
  refine vfam_dense w p ?_
  intro u hu δ hδ N
  obtain ⟨i, hi⟩ := hw0dense u hu (δ ^ 2) (by positivity)
  refine ⟨Nat.pair i N, Nat.right_le_pair i N, ?_⟩
  have hwn : w (Nat.pair i N) = w0 i := by rw [hwdef]; simp [Nat.unpair_pair]
  rw [hwn]
  have hnorm : ‖toL2 u - toL2 (w0 i)‖ ^ 2 = schwartzL2Inner (u - w0 i) (u - w0 i) := by
    rw [← toL2_sub, norm_toL2_sq]
  nlinarith [norm_nonneg (toL2 u - toL2 (w0 i)), hi, hnorm]

end IndependenceRecursion

/-- **A divergence-free, `L²`-independent, `L²`-member-dense family exists.**

`exists_denseIndependentDivFreeFamily_of_reservoir` above derives this exact
statement from *any* countable divergence-free `L²`-independent family `p`:

* density from `exists_dense_divFree_family` (second-countability of
  `Lp (EuclideanSpace ℝ (Fin 3)) 2 volume`, hereditary, so the dense sequence is
  drawn from the divergence-free image itself);
* independence by greedy off-span perturbation `v n = w n + pert n k • p k`,
  with `k` chosen by `exists_not_mem_span_of_linearIndependent` outside the span
  of everything built so far (`vfam_not_mem_span`, `vfam_independent`);
* density survives because `pert n k * ‖p k‖ < 1/(n+1)` and the `Nat.pair`
  re-indexing makes every dense member recur at arbitrarily large indices
  (`vfam_dense`).

The reservoir `p` is built by
`Navier.Analysis.GalerkinRawFamily.exists_countable_independent_divFree_family`
(pairwise-disjoint-support translates of `phiSchwartz`).  That file used to
begin `import Navier.Analysis.GalerkinBasis`, placing the reservoir *downstream*
of this statement, so naming it here was an import cycle and this declaration
stood open on import order alone — no mathematics was missing.  Hoisting the
shared `schwartzL2Inner` layer into `Navier.Analysis.SchwartzL2Pairing`,
upstream of both, reverses that edge; the reservoir is now in scope and the
proof below is its two-line instantiation.

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
  obtain ⟨p, hpdiv, hpindep⟩ := exists_countable_independent_divFree_family
  exact exists_denseIndependentDivFreeFamily_of_reservoir p hpdiv hpindep

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

/-- The first `m` fields of a Galerkin basis, indexed by `Fin m` for the
Euclidean coefficient-space ODE. -/
def GalerkinBasisFamily.finiteModes (W : GalerkinBasisFamily) (m : ℕ) :
    Fin m → SchwartzVelocity :=
  fun i => W.w i

/-- Realize a Euclidean coefficient vector as the corresponding finite
Schwartz modal field.  This is the actual coefficient-to-field map used by
`LerayWeak.galerkinModalApprox`. -/
noncomputable def GalerkinBasisFamily.coefficientField (W : GalerkinBasisFamily)
    {m : ℕ} (a : EuclideanSpace ℝ (Fin m)) : SchwartzVelocity :=
  ∑ i, a i • W.finiteModes m i

/-- The coefficient vector of the projected datum in the first `m` basis
modes. -/
noncomputable def GalerkinBasisFamily.initialCoefficients (W : GalerkinBasisFamily)
    (u : SchwartzVelocity) (m : ℕ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => W.coeff u i

private theorem schwartzL2Inner_finset_sum_left {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : ι → SchwartzVelocity) (g : SchwartzVelocity) :
    schwartzL2Inner (∑ i ∈ s, F i) g = ∑ i ∈ s, schwartzL2Inner (F i) g := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, schwartzL2Inner_zero_left]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, schwartzL2Inner_add_left, ih, Finset.sum_insert ha]

private theorem schwartzL2Inner_finset_sum_right {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : SchwartzVelocity) (G : ι → SchwartzVelocity) :
    schwartzL2Inner f (∑ i ∈ s, G i) = ∑ i ∈ s, schwartzL2Inner f (G i) := by
  rw [schwartzL2Inner_comm, schwartzL2Inner_finset_sum_left]
  exact Finset.sum_congr rfl (fun i _ => schwartzL2Inner_comm _ _)

/-- The finite coefficient realization is an exact Euclidean `L²` isometry:
orthonormality of the genuine Galerkin modes turns the field pairing into the
squared Euclidean coefficient norm. -/
theorem coefficientField_l2_isometry (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) :
    schwartzL2Inner (W.coefficientField a) (W.coefficientField a) = ‖a‖ ^ 2 := by
  have hinner : ∀ j : Fin m,
      schwartzL2Inner (W.w j) (W.coefficientField a) = a j := by
    intro j
    unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
    rw [schwartzL2Inner_finset_sum_right, Finset.sum_eq_single j]
    · rw [schwartzL2Inner_smul_right, W.orthonormal j j, if_pos rfl, mul_one]
    · intro i _ hij
      rw [schwartzL2Inner_smul_right, W.orthonormal j i,
        if_neg (fun h => hij (Fin.ext h.symm)), mul_zero]
    · exact fun hj => (hj (Finset.mem_univ j)).elim
  calc
    schwartzL2Inner (W.coefficientField a) (W.coefficientField a) =
        ∑ j : Fin m,
          schwartzL2Inner (a j • W.w j) (W.coefficientField a) := by
      unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
      rw [schwartzL2Inner_finset_sum_left]
    _ = ∑ j : Fin m, a j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [schwartzL2Inner_smul_left, hinner j]
      ring
    _ = ‖a‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq a).symm

/-- The finite coefficient realization preserves the full real inner product,
not only squared norms. -/
theorem coefficientField_l2_inner (W : GalerkinBasisFamily) {m : ℕ}
    (a b : EuclideanSpace ℝ (Fin m)) :
    schwartzL2Inner (W.coefficientField a) (W.coefficientField b) = inner ℝ a b := by
  have hinner : ∀ j : Fin m,
      schwartzL2Inner (W.w j) (W.coefficientField b) = b j := by
    intro j
    unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
    rw [schwartzL2Inner_finset_sum_right, Finset.sum_eq_single j]
    · rw [schwartzL2Inner_smul_right, W.orthonormal j j, if_pos rfl, mul_one]
    · intro i _ hij
      rw [schwartzL2Inner_smul_right, W.orthonormal j i,
        if_neg (fun h => hij (Fin.ext h.symm)), mul_zero]
    · exact fun hj => (hj (Finset.mem_univ j)).elim
  change schwartzL2Inner (∑ j : Fin m, a j • W.w j) (W.coefficientField b) =
    inner ℝ a b
  rw [schwartzL2Inner_finset_sum_left, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [schwartzL2Inner_smul_left, hinner j]
  simp [RCLike.inner_apply, mul_comm]

/-- The coefficient realization is additive under subtraction. -/
theorem coefficientField_sub (W : GalerkinBasisFamily) {m : ℕ}
    (a b : EuclideanSpace ℝ (Fin m)) :
    W.coefficientField (a - b) = W.coefficientField a - W.coefficientField b := by
  unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => sub_smul (a i) (b i) (W.w i))

/-- The coefficient realization preserves addition. -/
theorem coefficientField_add (W : GalerkinBasisFamily) {m : ℕ}
    (a b : EuclideanSpace ℝ (Fin m)) :
    W.coefficientField (a + b) = W.coefficientField a + W.coefficientField b := by
  unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => add_smul (a i) (b i) (W.w i))

/-- The coefficient realization preserves real scalar multiplication. -/
theorem coefficientField_smul (W : GalerkinBasisFamily) {m : ℕ}
    (r : ℝ) (a : EuclideanSpace ℝ (Fin m)) :
    W.coefficientField (r • a) = r • W.coefficientField a := by
  unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp [smul_smul])

/-- Realizing the datum's coefficient vector recovers its genuine Galerkin
projection. -/
theorem coefficientField_initialCoefficients_eq_proj (W : GalerkinBasisFamily)
    (u : SchwartzVelocity) (m : ℕ) :
    W.coefficientField (W.initialCoefficients u m) = W.proj m u := by
  unfold GalerkinBasisFamily.coefficientField GalerkinBasisFamily.initialCoefficients
    GalerkinBasisFamily.finiteModes GalerkinBasisFamily.proj
  change (∑ i : Fin m, W.coeff u i • W.w i) = _
  rw [← Fin.sum_univ_eq_sum_range (fun j => W.coeff u j • W.w j) m]

/-- The modal evolution obtained by realizing coefficient curves against the
first `m` fields of the certified Galerkin basis. -/
noncomputable def GalerkinBasisFamily.modalApprox (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) : ℕ → VelocityEvolution :=
  galerkinModalApprox (fun m => m) c (fun m => W.finiteModes m)

/-- Curl as a genuine continuous linear operator on Schwartz velocity fields.
Each summand differentiates in a coordinate direction and postcomposes with
the linear cross product by that basis vector. -/
noncomputable def curlSchwartzCLM : SchwartzVelocity →L[ℝ] SchwartzVelocity :=
  ∑ i : Fin 3,
    (SchwartzMap.postcompCLM (𝕜 := ℝ)
      (crossProduct (basisVector i)).toContinuousLinearMap).comp
      (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i))

/-- The Schwartz curl agrees pointwise with the project coordinate curl. -/
theorem curlSchwartzCLM_apply (u : SchwartzVelocity) (x : Space) :
    curlSchwartzCLM u x = staticCurl u x := by
  simp [curlSchwartzCLM, staticCurl, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- The componentwise Laplacian retained as a Schwartz velocity. -/
noncomputable def laplacianSchwartz (u : SchwartzVelocity) : SchwartzVelocity :=
  ∑ i : Fin 3, ∂_{basisVector i} (∂_{basisVector i} u)

theorem laplacianSchwartz_apply (u : SchwartzVelocity) (x : Space) :
    laplacianSchwartz u x = laplacian (fun _ => u) 0 x := by
  unfold laplacianSchwartz laplacian
  change (∑ i : Fin 3, (∂_{basisVector i} (∂_{basisVector i} u)) x) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  congr 2

/-- A coordinate of a Schwartz velocity field, retained as a scalar Schwartz
map. -/
noncomputable def componentSchwartz (u : SchwartzVelocity) (i : Fin 3) :
    SchwartzMap Space ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.proj i) u

@[simp] theorem componentSchwartz_apply (u : SchwartzVelocity) (i : Fin 3) (x : Space) :
    componentSchwartz u i x = u x i := by
  simp [componentSchwartz]

/-- Static divergence retained as a scalar Schwartz map. -/
noncomputable def divergenceSchwartz (u : SchwartzVelocity) : SchwartzMap Space ℝ :=
  ∑ i : Fin 3, componentSchwartz (∂_{basisVector i} u) i

@[simp] theorem divergenceSchwartz_apply (u : SchwartzVelocity) (x : Space) :
    divergenceSchwartz u x = staticDivergence u x := by
  simp [divergenceSchwartz, staticDivergence,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

private theorem lineDerivSchwartz_comm (u : SchwartzVelocity) (i j : Fin 3) :
    ∂_{basisVector i} (∂_{basisVector j} u) =
      ∂_{basisVector j} (∂_{basisVector i} u) := by
  ext x k
  have hmix := Navier.Analysis.CurlIdentities.ContDiffAt.hasSymmetricMixedPartialAt
    (x := x) ((componentSchwartz u k).smooth 2).contDiffAt i j
  have hcomponent (q : Fin 3) :
      (fun y => fderiv ℝ (componentSchwartz u k) y (basisVector q)) =
        fun y => (fderiv ℝ u y (basisVector q)) k := by
    funext y
    rw [show (componentSchwartz u k : Space → ℝ) = fun z => u z k by
      funext z
      simp]
    rw [fderiv_apply (schwartz_differentiableAt u y) k]
    rfl
  rw [hcomponent j, hcomponent i] at hmix
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [show ((∂_{basisVector j} u : SchwartzVelocity) : Space → Space) =
      fun y => fderiv ℝ u y (basisVector j) by
        funext y
        simp [SchwartzMap.lineDerivOp_apply_eq_fderiv],
    show ((∂_{basisVector i} u : SchwartzVelocity) : Space → Space) =
      fun y => fderiv ℝ u y (basisVector i) by
        funext y
        simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]]
  have hdj : DifferentiableAt ℝ (fun y => fderiv ℝ u y (basisVector j)) x := by
    rw [← show ((∂_{basisVector j} u : SchwartzVelocity) : Space → Space) =
      fun y => fderiv ℝ u y (basisVector j) by
        funext y
        simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]]
    exact schwartz_differentiableAt _ x
  have hdi : DifferentiableAt ℝ (fun y => fderiv ℝ u y (basisVector i)) x := by
    rw [← show ((∂_{basisVector i} u : SchwartzVelocity) : Space → Space) =
      fun y => fderiv ℝ u y (basisVector i) by
        funext y
        simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]]
    exact schwartz_differentiableAt _ x
  have hj := congrArg (fun L : Space →L[ℝ] ℝ => L (basisVector i))
    (fderiv_apply hdj k)
  have hi := congrArg (fun L : Space →L[ℝ] ℝ => L (basisVector j))
    (fderiv_apply hdi k)
  exact hj.symm.trans (hmix.trans hi)

private theorem lineDeriv_curlSchwartzCLM (u : SchwartzVelocity) (q : Fin 3) :
    ∂_{basisVector q} (curlSchwartzCLM u) =
      curlSchwartzCLM (∂_{basisVector q} u) := by
  unfold curlSchwartzCLM
  change (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector q))
      (∑ i : Fin 3,
        (SchwartzMap.postcompCLM
          (LinearMap.toContinuousLinearMap (crossProduct (basisVector i))))
          (∂_{basisVector i} u)) =
      ∑ i : Fin 3,
        (SchwartzMap.postcompCLM
          (LinearMap.toContinuousLinearMap (crossProduct (basisVector i))))
          (∂_{basisVector i} (∂_{basisVector q} u))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  ext x k
  change (fderiv ℝ
      (fun y => (LinearMap.toContinuousLinearMap (crossProduct (basisVector i)))
        ((∂_{basisVector i} u) y)) x) (basisVector q) k = _
  have hfd := congrArg
    (fun D : Space →L[ℝ] Space => D (basisVector q) k)
    (fderiv_comp x
      (LinearMap.toContinuousLinearMap (crossProduct (basisVector i))).differentiableAt
      (schwartz_differentiableAt (∂_{basisVector i} u) x))
  rw [ContinuousLinearMap.fderiv] at hfd
  have hc := congrArg (fun f : SchwartzVelocity => f x)
    (lineDerivSchwartz_comm u q i)
  calc
    _ = (crossProduct (basisVector i))
        ((∂_{basisVector q} (∂_{basisVector i} u)) x) k := by
      change _ = (crossProduct (basisVector i))
        ((fderiv ℝ ((∂_{basisVector i} u : SchwartzVelocity) : Space → Space) x)
          (basisVector q)) k
      convert hfd using 1 <;> rfl
    _ = _ := by
      simpa using congrArg (fun z : Space => (crossProduct (basisVector i)) z k) hc

private theorem lineDeriv_divergenceSchwartz (u : SchwartzVelocity) (q : Fin 3) :
    ∂_{basisVector q} (divergenceSchwartz u) =
      ∑ i : Fin 3, componentSchwartz
        (∂_{basisVector q} (∂_{basisVector i} u)) i := by
  unfold divergenceSchwartz
  change (LineDeriv.lineDerivOpCLM ℝ (SchwartzMap Space ℝ) (basisVector q))
      (∑ i : Fin 3, componentSchwartz (∂_{basisVector i} u) i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  ext x
  change (fderiv ℝ (componentSchwartz (∂_{basisVector i} u) i) x)
      (basisVector q) = _
  rw [show (componentSchwartz (∂_{basisVector i} u) i : Space → ℝ) =
      fun y => (∂_{basisVector i} u) y i by
        funext y
        simp]
  rw [fderiv_apply (schwartz_differentiableAt (∂_{basisVector i} u) x) i]
  rfl

/-- For a divergence-free Schwartz field, `curl (curl u) = -Δu` as a
Schwartz identity. -/
theorem curlCurlSchwartz_eq_neg_laplacian (u : SchwartzVelocity)
    (hu : DivergenceFreeInitial u) :
    curlSchwartzCLM (curlSchwartzCLM u) = -laplacianSchwartz u := by
  have hdiv : divergenceSchwartz u = 0 := by
    ext x
    simp [hu x]
  have hddiv (q : Fin 3) : ∂_{basisVector q} (divergenceSchwartz u) = 0 := by
    rw [hdiv]
    exact map_zero (LineDeriv.lineDerivOpCLM ℝ (SchwartzMap Space ℝ) (basisVector q))
  have hcomm (i j : Fin 3) := lineDerivSchwartz_comm u i j
  ext x k
  have hd0 := congrArg (fun f : SchwartzMap Space ℝ => f x) (hddiv 0)
  have hd1 := congrArg (fun f : SchwartzMap Space ℝ => f x) (hddiv 1)
  have hd2 := congrArg (fun f : SchwartzMap Space ℝ => f x) (hddiv 2)
  have hc01 := congrArg (fun f : SchwartzVelocity => f x) (hcomm 0 1)
  have hc02 := congrArg (fun f : SchwartzVelocity => f x) (hcomm 0 2)
  have hc10 := congrArg (fun f : SchwartzVelocity => f x) (hcomm 1 0)
  have hc12 := congrArg (fun f : SchwartzVelocity => f x) (hcomm 1 2)
  have hc20 := congrArg (fun f : SchwartzVelocity => f x) (hcomm 2 0)
  have hc21 := congrArg (fun f : SchwartzVelocity => f x) (hcomm 2 1)
  rw [lineDeriv_divergenceSchwartz] at hd0 hd1 hd2
  change ((∑ i : Fin 3,
      SchwartzMap.postcompCLM
        (LinearMap.toContinuousLinearMap (crossProduct (basisVector i)))
        (∂_{basisVector i} (curlSchwartzCLM u))) x) k = _
  simp_rw [lineDeriv_curlSchwartzCLM]
  fin_cases k <;>
    simp [curlSchwartzCLM, laplacianSchwartz, componentSchwartz,
      basisVector, cross_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons] at hd0 hd1 hd2 hc01 hc02 hc10 hc12 hc20 hc21 ⊢
  all_goals linarith

/-- The bilinear Schwartz representative of `(u · ∇)v`. -/
noncomputable def convectionSchwartzBilin (u v : SchwartzVelocity) : SchwartzVelocity :=
  ∑ i : Fin 3, SchwartzMap.pairing (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentSchwartz u i) (∂_{basisVector i} v)

/-- The Schwartz representative agrees pointwise with the project convection
operator on a static slice. -/
theorem convectionSchwartzBilin_apply (u v : SchwartzVelocity) (x : Space) :
    convectionSchwartzBilin u v x =
      spatialDerivative (fun _ => v) 0 x (u x) := by
  rw [show u x = ∑ i : Fin 3, (u x i) • basisVector i from
    pi_eq_sum_univ' (u x), map_sum]
  simp [convectionSchwartzBilin, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    spatialDerivative]

private theorem convectionSchwartzBilin_add_left (u v z : SchwartzVelocity) :
    convectionSchwartzBilin (u + v) z =
      convectionSchwartzBilin u z + convectionSchwartzBilin v z := by
  simp [convectionSchwartzBilin, componentSchwartz, Finset.sum_add_distrib]

private theorem convectionSchwartzBilin_add_right (u v z : SchwartzVelocity) :
    convectionSchwartzBilin u (v + z) =
      convectionSchwartzBilin u v + convectionSchwartzBilin u z := by
  have hderiv : ∀ i : Fin 3, ∂_{basisVector i} (v + z) =
      ∂_{basisVector i} v + ∂_{basisVector i} z := by
    intro i
    exact map_add (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i)) v z
  simp [convectionSchwartzBilin, hderiv, Finset.sum_add_distrib]

private theorem convectionSchwartzBilin_smul_left (r : ℝ) (u v : SchwartzVelocity) :
    convectionSchwartzBilin (r • u) v = r • convectionSchwartzBilin u v := by
  simp [convectionSchwartzBilin, componentSchwartz, Finset.smul_sum]

private theorem convectionSchwartzBilin_smul_right (r : ℝ) (u v : SchwartzVelocity) :
    convectionSchwartzBilin u (r • v) = r • convectionSchwartzBilin u v := by
  have hderiv : ∀ i : Fin 3, ∂_{basisVector i} (r • v) =
      r • ∂_{basisVector i} v := by
    intro i
    exact map_smul (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i)) r v
  simp [convectionSchwartzBilin, hderiv, Finset.smul_sum]

private theorem convectionSchwartzBilin_zero_left (v : SchwartzVelocity) :
    convectionSchwartzBilin 0 v = 0 := by
  simp [convectionSchwartzBilin, componentSchwartz]

private theorem convectionSchwartzBilin_zero_right (u : SchwartzVelocity) :
    convectionSchwartzBilin u 0 = 0 := by
  have hderiv : ∀ i : Fin 3, ∂_{basisVector i} (0 : SchwartzVelocity) = 0 := by
    intro i
    exact map_zero (LineDeriv.lineDerivOpCLM ℝ SchwartzVelocity (basisVector i))
  simp [convectionSchwartzBilin, hderiv]

private theorem convectionSchwartzBilin_sum_left {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → SchwartzVelocity) (v : SchwartzVelocity) :
    convectionSchwartzBilin (∑ i ∈ s, u i) v =
      ∑ i ∈ s, convectionSchwartzBilin (u i) v := by
  induction s using Finset.induction_on with
  | empty => simp [convectionSchwartzBilin_zero_left]
  | insert i s hi => simp [convectionSchwartzBilin_add_left, *]

private theorem convectionSchwartzBilin_sum_right {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : SchwartzVelocity) (v : ι → SchwartzVelocity) :
    convectionSchwartzBilin u (∑ i ∈ s, v i) =
      ∑ i ∈ s, convectionSchwartzBilin u (v i) := by
  induction s using Finset.induction_on with
  | empty => simp [convectionSchwartzBilin_zero_right]
  | insert i s hi => simp [convectionSchwartzBilin_add_right, *]

/-- The quadratic Schwartz convection field `(u · ∇)u`. -/
noncomputable def convectionSchwartz (u : SchwartzVelocity) : SchwartzVelocity :=
  convectionSchwartzBilin u u

private theorem convectionSchwartz_coefficientField (W : GalerkinBasisFamily)
    (m : ℕ) (a : EuclideanSpace ℝ (Fin m)) :
    convectionSchwartz (W.coefficientField a) =
      ∑ j : Fin m, ∑ k : Fin m,
        (a j * a k) • convectionSchwartzBilin (W.w j) (W.w k) := by
  unfold convectionSchwartz
  rw [show W.coefficientField a = ∑ i : Fin m, a i • W.w i from rfl,
    convectionSchwartzBilin_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [convectionSchwartzBilin_smul_left,
    convectionSchwartzBilin_sum_right, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [convectionSchwartzBilin_smul_right, smul_smul]

theorem convectionSchwartz_apply (u : SchwartzVelocity) (x : Space) :
    convectionSchwartz u x = convection (fun _ => u) 0 x := by
  rw [convectionSchwartz, convection, convectionSchwartzBilin_apply]

/-- The pointwise Euclidean pairing of two Schwartz velocities, retained as a
scalar Schwartz map. -/
noncomputable def velocityPairingSchwartz (u v : SchwartzVelocity) :
    SchwartzMap Space ℝ :=
  ∑ i : Fin 3, SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
    (componentSchwartz u i) (componentSchwartz v i)

@[simp] theorem velocityPairingSchwartz_apply
    (u v : SchwartzVelocity) (x : Space) :
    velocityPairingSchwartz u v x = officialInner (u x) (v x) := by
  simp [velocityPairingSchwartz, officialInner_eq_sum]

/-- Pointwise cross product retained in the Schwartz class. -/
noncomputable def crossSchwartz (u v : SchwartzVelocity) : SchwartzVelocity :=
  ∑ i : Fin 3,
    SchwartzMap.pairing (ContinuousLinearMap.lsmul ℝ ℝ)
      (componentSchwartz u i)
      (SchwartzMap.postcompCLM
        (LinearMap.toContinuousLinearMap (crossProduct (basisVector i))) v)

@[simp] theorem crossSchwartz_apply (u v : SchwartzVelocity) (x : Space) :
    crossSchwartz u v x = crossProduct (u x) (v x) := by
  ext k
  fin_cases k <;>
    simp [crossSchwartz, componentSchwartz, basisVector, cross_apply,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons] <;>
    ring

/-- Whole-space curl integration by parts for a divergence-free Schwartz test
field: the curl pairing equals the negative Laplacian pairing. -/
theorem schwartzL2Inner_curl_eq_neg_laplacian (u v : SchwartzVelocity)
    (hv : DivergenceFreeInitial v) :
    schwartzL2Inner (curlSchwartzCLM u) (curlSchwartzCLM v) =
      -schwartzL2Inner u (laplacianSchwartz v) := by
  let flux := crossSchwartz u (curlSchwartzCLM v)
  have hflux : ∀ i : Fin 3, Integrable (fun x => flux x i) := by
    intro i
    refine (componentSchwartz flux i).integrable.congr ?_
    filter_upwards with x
    simp [flux]
  have hfluxDeriv : ∀ i : Fin 3,
      Integrable (fun x => fderiv ℝ (fun y => flux y i) x (basisVector i)) := by
    intro i
    have hint : Integrable
        (fun x : Space => (∂_{basisVector i} (componentSchwartz flux i)) x)
        (volume : Measure Space) :=
      (∂_{basisVector i} (componentSchwartz flux i)).integrable
    refine hint.congr ?_
    filter_upwards with x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    congr 2
  have hzero :=
    Navier.Analysis.EnergyPressureIntegral.integral_staticDivergence_eq_zero
      flux flux.differentiable hflux hfluxDeriv
  have hpoint (x : Space) : staticDivergence flux x =
      officialInner (curlSchwartzCLM u x) (curlSchwartzCLM v x) +
        officialInner (u x) (laplacianSchwartz v x) := by
    rw [show (flux : Space → Space) =
        fun y => crossProduct (u y) (curlSchwartzCLM v y) by
      funext y
      simp [flux]]
    rw [Navier.Analysis.CurlIdentities.staticDivergence_cross u
      (curlSchwartzCLM v) x (schwartz_differentiableAt u x)
      (schwartz_differentiableAt (curlSchwartzCLM v) x)]
    rw [← curlSchwartzCLM_apply u x,
      ← curlSchwartzCLM_apply (curlSchwartzCLM v) x,
      curlCurlSchwartz_eq_neg_laplacian v hv]
    rw [officialInner_comm (curlSchwartzCLM u x) (curlSchwartzCLM v x)]
    simp [officialInner_eq_sum, dotProduct]
  have hrewrite : (fun x => staticDivergence flux x) = fun x =>
      officialInner (curlSchwartzCLM u x) (curlSchwartzCLM v x) +
        officialInner (u x) (laplacianSchwartz v x) := funext hpoint
  rw [hrewrite] at hzero
  have hcurl : Integrable (fun x =>
      officialInner (curlSchwartzCLM u x) (curlSchwartzCLM v x)) := by
    refine (velocityPairingSchwartz (curlSchwartzCLM u)
      (curlSchwartzCLM v)).integrable.congr ?_
    filter_upwards with x
    simp
  have hlap : Integrable (fun x =>
      officialInner (u x) (laplacianSchwartz v x)) := by
    refine (velocityPairingSchwartz u (laplacianSchwartz v)).integrable.congr ?_
    filter_upwards with x
    simp
  rw [MeasureTheory.integral_add hcurl hlap] at hzero
  unfold schwartzL2Inner
  linarith

/-- The Schwartz flux whose divergence implements skew-adjointness of
transport by a divergence-free field. -/
noncomputable def transportPairingFluxSchwartz (u v : SchwartzVelocity) :
    SchwartzVelocity :=
  SchwartzMap.pairing (ContinuousLinearMap.lsmul ℝ ℝ)
    (velocityPairingSchwartz u v) u

@[simp] theorem transportPairingFluxSchwartz_apply
    (u v : SchwartzVelocity) (x : Space) :
    transportPairingFluxSchwartz u v x = officialInner (u x) (v x) • u x := by
  simp [transportPairingFluxSchwartz]

private theorem fderiv_velocityPairingSchwartz
    (u v : SchwartzVelocity) (x h : Space) :
    fderiv ℝ (fun y => officialInner (u y) (v y)) x h =
      officialInner (fderiv ℝ u x h) (v x) +
        officialInner (u x) (fderiv ℝ v x h) := by
  simp only [officialInner_eq_sum]
  rw [fderiv_fun_sum]
  · simp only [fderiv_fun_mul
      (differentiableAt_pi.1 (schwartz_differentiableAt u x) _)
      (differentiableAt_pi.1 (schwartz_differentiableAt v x) _),
      add_apply, fderiv_apply (schwartz_differentiableAt u x),
      fderiv_apply (schwartz_differentiableAt v x),
      Finset.sum_add_distrib]
    simp
    rw [add_comm]
    apply congrArg₂ (· + ·)
    · exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    · rfl
  · intro i _
    exact (differentiableAt_pi.1 (schwartz_differentiableAt u x) i).mul
      (differentiableAt_pi.1 (schwartz_differentiableAt v x) i)

private theorem fderiv_apply_eq_sum_basis_schwartz
    (f : SchwartzMap Space ℝ) (x w : Space) :
    fderiv ℝ f x w = ∑ i : Fin 3, w i * fderiv ℝ f x (basisVector i) := by
  calc
    fderiv ℝ f x w = fderiv ℝ f x (∑ i : Fin 3, (w i) • basisVector i) := by
      congr 1
      simpa only [basisVector] using pi_eq_sum_univ' w
    _ = ∑ i : Fin 3, w i * fderiv ℝ f x (basisVector i) := by
      rw [map_sum]
      simp

/-- Pointwise transport pairing is a divergence: for divergence-free `u`,
`div (⟨u,v⟩u) = ⟨(u·∇)u,v⟩ + ⟨u,(u·∇)v⟩`. -/
theorem staticDivergence_transportPairingFluxSchwartz
    (u v : SchwartzVelocity) (hu : DivergenceFreeInitial u) (x : Space) :
    staticDivergence (transportPairingFluxSchwartz u v) x =
      officialInner (convectionSchwartz u x) (v x) +
        officialInner (u x) (convectionSchwartzBilin u v x) := by
  rw [show (transportPairingFluxSchwartz u v : Space → Space) =
      fun y => officialInner (u y) (v y) • u y by
        funext y
        simp]
  have hpairDiff : DifferentiableAt ℝ (fun y => officialInner (u y) (v y)) x := by
    rw [show (fun y => officialInner (u y) (v y)) =
      (velocityPairingSchwartz u v : Space → ℝ) by
        funext y
        simp]
    exact (velocityPairingSchwartz u v).differentiable.differentiableAt
  rw [staticDivergence_smul _ _ x hpairDiff
    (schwartz_differentiableAt u x), hu x, mul_zero, add_zero]
  have hgradient :
      (∑ i : Fin 3,
        staticGradient (fun y => officialInner (u y) (v y)) x i * u x i) =
        fderiv ℝ (velocityPairingSchwartz u v) x (u x) := by
    unfold staticGradient
    rw [fderiv_apply_eq_sum_basis_schwartz]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (fun y => officialInner (u y) (v y)) =
      (velocityPairingSchwartz u v : Space → ℝ) by
        funext y
        simp]
    ring
  rw [hgradient]
  rw [show (velocityPairingSchwartz u v : Space → ℝ) =
      fun y => officialInner (u y) (v y) by
        funext y
        simp,
    fderiv_velocityPairingSchwartz]
  rw [convectionSchwartz_apply, convectionSchwartzBilin_apply]
  rfl

/-- Whole-space skew-adjointness of convection on Schwartz fields:
`⟨u,(u·∇)v⟩ = -⟨(u·∇)u,v⟩` when `div u = 0`.  The boundary term is the
integral of the divergence of the explicit Schwartz flux `⟨u,v⟩u`. -/
theorem schwartzL2Inner_convection_skew (u v : SchwartzVelocity)
    (hu : DivergenceFreeInitial u) :
    schwartzL2Inner u (convectionSchwartzBilin u v) =
      -schwartzL2Inner (convectionSchwartz u) v := by
  let flux := transportPairingFluxSchwartz u v
  have hflux : ∀ i : Fin 3, Integrable (fun x => flux x i) := by
    intro i
    refine (componentSchwartz flux i).integrable.congr ?_
    filter_upwards with x
    simp [flux]
  have hfluxDeriv : ∀ i : Fin 3,
      Integrable (fun x => fderiv ℝ (fun y => flux y i) x (basisVector i)) := by
    intro i
    have hint : Integrable
        (fun x : Space => (∂_{basisVector i} (componentSchwartz flux i)) x)
        (volume : Measure Space) :=
      (∂_{basisVector i} (componentSchwartz flux i)).integrable
    refine hint.congr ?_
    filter_upwards with x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    congr 2
  have hzero :=
    Navier.Analysis.EnergyPressureIntegral.integral_staticDivergence_eq_zero
      flux flux.differentiable hflux hfluxDeriv
  have hrewrite : (fun x => staticDivergence flux x) = fun x =>
      officialInner (convectionSchwartz u x) (v x) +
        officialInner (u x) (convectionSchwartzBilin u v x) := by
    funext x
    exact staticDivergence_transportPairingFluxSchwartz u v hu x
  rw [hrewrite] at hzero
  have hconv : Integrable (fun x =>
      officialInner (convectionSchwartz u x) (v x)) := by
    refine (velocityPairingSchwartz (convectionSchwartz u) v).integrable.congr ?_
    filter_upwards with x
    simp
  have htest : Integrable (fun x =>
      officialInner (u x) (convectionSchwartzBilin u v x)) := by
    refine (velocityPairingSchwartz u (convectionSchwartzBilin u v)).integrable.congr ?_
    filter_upwards with x
    simp
  rw [MeasureTheory.integral_add hconv htest] at hzero
  unfold schwartzL2Inner
  linarith

/-- The kinetic-energy density of a Schwartz velocity, retained as a scalar
Schwartz map. -/
noncomputable def kineticEnergyDensitySchwartz (u : SchwartzVelocity) :
    SchwartzMap Space ℝ :=
  (1 / 2 : ℝ) • ∑ i : Fin 3,
    SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
      (componentSchwartz u i) (componentSchwartz u i)

@[simp] theorem kineticEnergyDensitySchwartz_apply (u : SchwartzVelocity) (x : Space) :
    kineticEnergyDensitySchwartz u x = kineticEnergyDensity u x := by
  simp [kineticEnergyDensitySchwartz, kineticEnergyDensity]

/-- One coordinate of the Schwartz kinetic-energy flux. -/
noncomputable def kineticEnergyFluxComponentSchwartz (u : SchwartzVelocity) (i : Fin 3) :
    SchwartzMap Space ℝ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
    (kineticEnergyDensitySchwartz u) (componentSchwartz u i)

@[simp] theorem kineticEnergyFluxComponentSchwartz_apply
    (u : SchwartzVelocity) (i : Fin 3) (x : Space) :
    kineticEnergyFluxComponentSchwartz u i x = kineticEnergyFlux u x i := by
  simp [kineticEnergyFluxComponentSchwartz, kineticEnergyFlux]

/-- The whole-space convection work of a divergence-free Schwartz field
vanishes.  The flux hypotheses of the repository's divergence theorem are
discharged by the explicit Schwartz flux components above. -/
theorem schwartzL2Inner_convection_self_eq_zero (u : SchwartzVelocity)
    (hu : DivergenceFreeInitial u) :
    schwartzL2Inner (convectionSchwartz u) u = 0 := by
  let ue : VelocityEvolution := fun _ => u
  have hinc : Incompressible ue := by
    intro t _ x
    simpa [ue, divergence, spatialDerivative, staticDivergence] using hu x
  have hflux : ∀ i : Fin 3,
      Integrable (fun x => kineticEnergyFlux u x i) := by
    intro i
    refine (kineticEnergyFluxComponentSchwartz u i).integrable.congr ?_
    filter_upwards with x
    simp
  have hfluxDeriv : ∀ i : Fin 3,
      Integrable (fun x =>
        fderiv ℝ (fun y => kineticEnergyFlux u y i) x (basisVector i)) := by
    intro i
    have hint : Integrable
        (fun x : Space => (∂_{basisVector i}
          (kineticEnergyFluxComponentSchwartz u i)) x) (volume : Measure Space) :=
      (∂_{basisVector i} (kineticEnergyFluxComponentSchwartz u i)).integrable
    refine hint.congr ?_
    filter_upwards with x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have hfun : (fun y : Space => kineticEnergyFlux u y i) =
        (kineticEnergyFluxComponentSchwartz u i : Space → ℝ) := by
      funext y
      simp
    rw [hfun]
  have hzero :=
    Navier.Analysis.EnergyConvectionIntegral.integral_convection_work_eq_zero
      ue 0 le_rfl hinc u.differentiable hflux hfluxDeriv
  unfold schwartzL2Inner
  calc
    (∫ x : Space, officialInner (convectionSchwartz u x) (u x)) =
        ∫ x : Space, ∑ i : Fin 3, convection ue 0 x i * ue 0 x i := by
      apply integral_congr_ae
      filter_upwards with x
      rw [officialInner_eq_sum, convectionSchwartz_apply]
    _ = 0 := hzero

/-- The concrete projected convection field on finite coefficients.  The sign
matches `u' = -νAu + B(u)`: `B` is minus the Galerkin projection of
`(u·∇)u`. -/
noncomputable def GalerkinBasisFamily.convectionOperator (W : GalerkinBasisFamily)
    (m : ℕ) (a : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i =>
    -schwartzL2Inner (W.w i) (convectionSchwartz (W.coefficientField a))

@[simp] theorem convectionOperator_apply (W : GalerkinBasisFamily) (m : ℕ)
    (a : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    W.convectionOperator m a i =
      -schwartzL2Inner (W.w i) (convectionSchwartz (W.coefficientField a)) := by
  simp [GalerkinBasisFamily.convectionOperator]

/-- Each coordinate of the projected convection field is a finite quadratic
polynomial in the modal coefficients. -/
theorem convectionOperator_apply_eq_sum (W : GalerkinBasisFamily) (m : ℕ)
    (a : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    W.convectionOperator m a i =
      -∑ j : Fin m, ∑ k : Fin m, (a j * a k) *
        schwartzL2Inner (W.w i) (convectionSchwartzBilin (W.w j) (W.w k)) := by
  rw [convectionOperator_apply, convectionSchwartz_coefficientField,
    schwartzL2Inner_finset_sum_right]
  simp_rw [schwartzL2Inner_finset_sum_right, schwartzL2Inner_smul_right]

/-- The concrete finite-mode convection field is `C¹` (indeed polynomial). -/
theorem convectionOperator_contDiff (W : GalerkinBasisFamily) (m : ℕ) :
    ContDiff ℝ 1 (W.convectionOperator m) := by
  rw [contDiff_piLp]
  intro i
  simp_rw [convectionOperator_apply_eq_sum]
  fun_prop

/-- Energy skewness of the concrete projected convection field. -/
theorem convectionOperator_inner_self (W : GalerkinBasisFamily) (m : ℕ)
    (a : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (W.convectionOperator m a) a = 0 := by
  rw [PiLp.inner_apply]
  simp only [convectionOperator_apply, RCLike.inner_apply, conj_trivial]
  have hfield : W.coefficientField a = ∑ i : Fin m, a i • W.w i := rfl
  calc
    (∑ i : Fin m,
        a i * -schwartzL2Inner (W.w i) (convectionSchwartz (W.coefficientField a))) =
        -schwartzL2Inner (∑ i : Fin m, a i • W.w i)
          (convectionSchwartz (W.coefficientField a)) := by
      rw [schwartzL2Inner_finset_sum_left]
      simp only [schwartzL2Inner_smul_left]
      simp only [mul_neg, Finset.sum_neg_distrib]
    _ = -schwartzL2Inner (W.coefficientField a)
        (convectionSchwartz (W.coefficientField a)) := by rw [← hfield]
    _ = -schwartzL2Inner (convectionSchwartz (W.coefficientField a))
        (W.coefficientField a) := by rw [schwartzL2Inner_comm]
    _ = 0 := by
      rw [schwartzL2Inner_convection_self_eq_zero
        (W.coefficientField a) (divergenceFreeInitial_sum_smul Finset.univ
          (fun i : Fin m => a i) (fun i : Fin m => W.w i)
          (fun i => W.divergence_free i))]
      simp

/-- The concrete coefficient convection pairing is exactly the physical weak
transport term against another retained modal field. -/
theorem convectionOperator_pairing (W : GalerkinBasisFamily) (m : ℕ)
    (a b : EuclideanSpace ℝ (Fin m)) :
    schwartzL2Inner (W.coefficientField (W.convectionOperator m a))
        (W.coefficientField b) =
      schwartzL2Inner (W.coefficientField a)
        (convectionSchwartzBilin (W.coefficientField a) (W.coefficientField b)) := by
  rw [coefficientField_l2_inner, PiLp.inner_apply]
  simp only [convectionOperator_apply, RCLike.inner_apply, conj_trivial]
  have hbfield : W.coefficientField b = ∑ i : Fin m, b i • W.w i := rfl
  calc
    (∑ i : Fin m,
        b i * -schwartzL2Inner (W.w i) (convectionSchwartz (W.coefficientField a))) =
        -schwartzL2Inner (W.coefficientField b)
          (convectionSchwartz (W.coefficientField a)) := by
      rw [hbfield, schwartzL2Inner_finset_sum_left]
      simp only [schwartzL2Inner_smul_left, mul_neg, Finset.sum_neg_distrib]
    _ = -schwartzL2Inner (convectionSchwartz (W.coefficientField a))
        (W.coefficientField b) := by rw [schwartzL2Inner_comm]
    _ = schwartzL2Inner (W.coefficientField a)
        (convectionSchwartzBilin (W.coefficientField a) (W.coefficientField b)) := by
      rw [schwartzL2Inner_convection_skew (W.coefficientField a)
        (W.coefficientField b) (divergenceFreeInitial_sum_smul Finset.univ
          (fun i : Fin m => a i) (fun i : Fin m => W.w i)
          (fun i => W.divergence_free i))]

/-- The physical enstrophy of a field realized from one finite coefficient
vector.  A projected Stokes operator represents exactly this quadratic form. -/
noncomputable def GalerkinBasisFamily.coefficientEnstrophy (W : GalerkinBasisFamily)
    {m : ℕ} (a : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ x : Space, officialEuclideanNorm (staticCurl (W.coefficientField a) x) ^ 2

/-- Coefficient enstrophy is the Schwartz `L²` pairing of the concrete curl
field with itself. -/
theorem coefficientEnstrophy_eq_curlSchwartz (W : GalerkinBasisFamily)
    {m : ℕ} (a : EuclideanSpace ℝ (Fin m)) :
    W.coefficientEnstrophy a =
      schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
        (curlSchwartzCLM (W.coefficientField a)) := by
  unfold GalerkinBasisFamily.coefficientEnstrophy schwartzL2Inner
  apply integral_congr_ae
  filter_upwards with x
  rw [curlSchwartzCLM_apply, officialInner_self]

/-- The concrete finite-mode Stokes operator: its `i`th coordinate is the
curl-`L²` pairing of mode `i` with the realized coefficient field. -/
noncomputable def GalerkinBasisFamily.stokesOperator (W : GalerkinBasisFamily)
    (m : ℕ) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => WithLp.toLp 2 fun i =>
        schwartzL2Inner (curlSchwartzCLM (W.w i))
          (curlSchwartzCLM (W.coefficientField a))
      map_add' := by
        intro a b
        ext i
        simp [coefficientField_add, schwartzL2Inner_add_right]
      map_smul' := by
        intro r a
        ext i
        simp [coefficientField_smul, schwartzL2Inner_smul_right] }

@[simp] theorem stokesOperator_apply (W : GalerkinBasisFamily) (m : ℕ)
    (a : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    W.stokesOperator m a i =
      schwartzL2Inner (curlSchwartzCLM (W.w i))
        (curlSchwartzCLM (W.coefficientField a)) := by
  simp [GalerkinBasisFamily.stokesOperator]

/-- Pairing the concrete finite-mode Stokes operator against retained
coefficients is exactly the physical weak Laplacian term. -/
theorem stokesOperator_pairing (W : GalerkinBasisFamily) (m : ℕ)
    (a b : EuclideanSpace ℝ (Fin m)) :
    schwartzL2Inner (W.coefficientField (W.stokesOperator m a))
        (W.coefficientField b) =
      -schwartzL2Inner (W.coefficientField a)
        (laplacianSchwartz (W.coefficientField b)) := by
  rw [coefficientField_l2_inner, PiLp.inner_apply]
  simp only [stokesOperator_apply, RCLike.inner_apply, conj_trivial]
  have hbfield : curlSchwartzCLM (W.coefficientField b) =
      ∑ i : Fin m, b i • curlSchwartzCLM (W.w i) := by
    rw [show W.coefficientField b = ∑ i : Fin m, b i • W.w i from rfl,
      map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  calc
    (∑ i : Fin m, b i *
        schwartzL2Inner (curlSchwartzCLM (W.w i))
          (curlSchwartzCLM (W.coefficientField a))) =
        schwartzL2Inner
          (∑ i : Fin m, b i • curlSchwartzCLM (W.w i))
          (curlSchwartzCLM (W.coefficientField a)) := by
      rw [schwartzL2Inner_finset_sum_left]
      exact Finset.sum_congr rfl
        (fun i _ => (schwartzL2Inner_smul_left _ _ _).symm)
    _ = schwartzL2Inner (curlSchwartzCLM (W.coefficientField b))
        (curlSchwartzCLM (W.coefficientField a)) := by rw [← hbfield]
    _ = schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
        (curlSchwartzCLM (W.coefficientField b)) :=
      schwartzL2Inner_comm _ _
    _ = -schwartzL2Inner (W.coefficientField a)
        (laplacianSchwartz (W.coefficientField b)) :=
      schwartzL2Inner_curl_eq_neg_laplacian _ _
        (divergenceFreeInitial_sum_smul Finset.univ
          (fun i : Fin m => b i) (fun i : Fin m => W.w i)
          (fun i => W.divergence_free i))

/-- The concrete projected vector field paired with a retained mode is the
physical viscous-plus-convective weak spatial term. -/
theorem projectedVectorField_pairing (W : GalerkinBasisFamily) (ν : ℝ)
    (m : ℕ) (a b : EuclideanSpace ℝ (Fin m)) :
    schwartzL2Inner
        (W.coefficientField
          (-(ν • W.stokesOperator m a) + W.convectionOperator m a))
        (W.coefficientField b) =
      schwartzL2Inner (W.coefficientField a)
        (ν • laplacianSchwartz (W.coefficientField b) +
          convectionSchwartzBilin (W.coefficientField a)
            (W.coefficientField b)) := by
  rw [coefficientField_add,
    show -(ν • W.stokesOperator m a) =
      (-ν) • W.stokesOperator m a by simp,
    coefficientField_smul, schwartzL2Inner_add_left,
    schwartzL2Inner_smul_left, stokesOperator_pairing,
    convectionOperator_pairing, schwartzL2Inner_add_right,
    schwartzL2Inner_smul_right]
  ring

/-- The Stokes quadratic form is exactly physical modal enstrophy. -/
theorem stokesOperator_inner_eq_enstrophy (W : GalerkinBasisFamily) (m : ℕ)
    (a : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (W.stokesOperator m a) a = W.coefficientEnstrophy a := by
  rw [PiLp.inner_apply, coefficientEnstrophy_eq_curlSchwartz]
  have hfield : curlSchwartzCLM (W.coefficientField a) =
      ∑ i : Fin m, a i • curlSchwartzCLM (W.w i) := by
    rw [show W.coefficientField a = ∑ i : Fin m, a i • W.w i from rfl,
      map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  simp only [stokesOperator_apply, RCLike.inner_apply, conj_trivial]
  change (∑ i : Fin m, a i *
      schwartzL2Inner (curlSchwartzCLM (W.w i))
        (curlSchwartzCLM (W.coefficientField a))) = _
  calc
    (∑ i : Fin m, a i * schwartzL2Inner (curlSchwartzCLM (W.w i))
        (curlSchwartzCLM (W.coefficientField a))) =
      schwartzL2Inner (∑ i : Fin m, a i • curlSchwartzCLM (W.w i))
        (curlSchwartzCLM (W.coefficientField a)) := by
      rw [schwartzL2Inner_finset_sum_left]
      exact Finset.sum_congr rfl (fun i _ => (schwartzL2Inner_smul_left _ _ _).symm)
    _ = schwartzL2Inner (curlSchwartzCLM (W.coefficientField a))
        (curlSchwartzCLM (W.coefficientField a)) := by rw [← hfield]

/-- Positivity of the concrete finite-mode Stokes operator. -/
theorem stokesOperator_nonneg (W : GalerkinBasisFamily) (m : ℕ)
    (a : EuclideanSpace ℝ (Fin m)) :
    0 ≤ inner ℝ (W.stokesOperator m a) a := by
  rw [stokesOperator_inner_eq_enstrophy]
  exact integral_nonneg fun x => by positivity

/-- At every time, the modal flow is the Schwartz field represented by the
forward-extended coefficient vector. -/
theorem modalApprox_eq_coefficientField_forwardExtend (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (t : ℝ) :
    W.modalApprox c m t = fun x => W.coefficientField (forwardExtend (c m) t) x := by
  funext x
  simp [GalerkinBasisFamily.modalApprox, galerkinModalApprox,
    GalerkinBasisFamily.coefficientField, GalerkinBasisFamily.finiteModes]

/-- At nonnegative time, the forward-extended modal flow is exactly the
Schwartz field represented by its current coefficient vector. -/
theorem modalApprox_eq_coefficientField (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    W.modalApprox c m t = fun x => W.coefficientField (c m t) x := by
  rw [modalApprox_eq_coefficientField_forwardExtend W c m t,
    forwardExtend_eq_of_nonneg (c m) ht]

/-- Physical time displacement is bounded by Euclidean coefficient
displacement at the same constant.  This is the exact modal isometry followed
by the valid pointwise comparison `‖v‖∞² ≤ ∑ᵢ vᵢ²`; no converse norm
conversion is used. -/
theorem modalApprox_timeDisplacement_le (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (s t : ℝ) :
    (∫ x : Space, ‖W.modalApprox c m s x - W.modalApprox c m t x‖ ^ 2) ≤
      ‖forwardExtend (c m) s - forwardExtend (c m) t‖ ^ 2 := by
  let a := forwardExtend (c m) s
  let b := forwardExtend (c m) t
  have hfield : ∀ x : Space,
      W.modalApprox c m s x - W.modalApprox c m t x =
        W.coefficientField (a - b) x := by
    intro x
    rw [congrFun (modalApprox_eq_coefficientField_forwardExtend W c m s) x,
      congrFun (modalApprox_eq_coefficientField_forwardExtend W c m t) x]
    exact (congrArg (fun f : SchwartzVelocity => f x) (coefficientField_sub W a b)).symm
  calc
    (∫ x : Space, ‖W.modalApprox c m s x - W.modalApprox c m t x‖ ^ 2) =
        ∫ x : Space, ‖W.coefficientField (a - b) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hfield x]
    _ ≤ schwartzL2Inner (W.coefficientField (a - b))
        (W.coefficientField (a - b)) :=
      integral_norm_sq_le_integral_officialInner_self (W.coefficientField (a - b))
    _ = ‖a - b‖ ^ 2 := coefficientField_l2_isometry W (a - b)
    _ = ‖forwardExtend (c m) s - forwardExtend (c m) t‖ ^ 2 := rfl

/-- Exact transfer of physical enstrophy to the coefficient representation at
nonnegative time. -/
theorem modalApprox_enstrophy_eq (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    enstrophy (W.modalApprox c m) t = W.coefficientEnstrophy (c m t) := by
  unfold enstrophy vorticity GalerkinBasisFamily.coefficientEnstrophy
  rw [modalApprox_eq_coefficientField W c m ht]

/-- Exact energy transfer from the Euclidean coefficient ODE to the physical
modal field.  The project `kineticEnergy` is the official Euclidean spatial
energy, so orthonormality loses no dimension factor. -/
theorem modalApprox_kineticEnergy_eq (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (t : ℝ) :
    kineticEnergy (W.modalApprox c m) t = ‖forwardExtend (c m) t‖ ^ 2 := by
  rw [← coefficientField_l2_isometry W]
  unfold GalerkinBasisFamily.modalApprox galerkinModalApprox
    GalerkinBasisFamily.coefficientField GalerkinBasisFamily.finiteModes
    kineticEnergy schwartzL2Inner
  apply integral_congr_ae
  filter_upwards with x
  rw [officialInner_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [pow_two]

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

/-- Pairing the Galerkin projection error against any fixed Schwartz field
tends to zero.  This is Bessel convergence plus Hilbert-space Cauchy--Schwarz,
and is the datum-correction term in weak consistency. -/
theorem proj_error_pairing_tendsto_zero (W : GalerkinBasisFamily)
    (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀)
    (v : SchwartzVelocity) :
    Filter.Tendsto
      (fun m => schwartzL2Inner (u₀ - W.proj m u₀) v)
      Filter.atTop (nhds 0) := by
  have hsq : Filter.Tendsto
      (fun m => ‖toL2 (u₀ - W.proj m u₀)‖ ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [norm_toL2_sq] using proj_tendsto_self W u₀ hu₀
  have hnorm : Filter.Tendsto
      (fun m => ‖toL2 (u₀ - W.proj m u₀)‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := hsq.sqrt
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  apply squeeze_zero_norm
  · intro m
    simpa only [Real.norm_eq_abs] using
      abs_schwartzL2Inner_le (u₀ - W.proj m u₀) v
  · simpa using hnorm.mul_const ‖toL2 v‖

/-- A retained modal field pairs identically with a Schwartz field and with
its projection onto the same retained span. -/
theorem coefficientField_pairing_proj (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (v : SchwartzVelocity) :
    schwartzL2Inner (W.coefficientField a) (W.proj m v) =
      schwartzL2Inner (W.coefficientField a) v := by
  rw [← coefficientField_initialCoefficients_eq_proj,
    coefficientField_l2_inner, PiLp.inner_apply]
  change (∑ i : Fin m, (W.initialCoefficients v m i) * a i) = _
  rw [show W.coefficientField a = ∑ i : Fin m, a i • W.w i from rfl,
    schwartzL2Inner_finset_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  change schwartzL2Inner v (W.w i) * a i =
    schwartzL2Inner (a i • W.w i) v
  rw [schwartzL2Inner_smul_left, schwartzL2Inner_comm v (W.w i)]
  ring

/-- Modal coefficients of a time-dependent Schwartz test slice. -/
noncomputable def GalerkinBasisFamily.modalTestCoefficients
    (W : GalerkinBasisFamily) (φ : ℝ → SchwartzVelocity) (m : ℕ) :
    ℝ → EuclideanSpace ℝ (Fin m) :=
  fun t => W.initialCoefficients (φ t) m

theorem coefficientField_modalTestCoefficients
    (W : GalerkinBasisFamily) (φ : ℝ → SchwartzVelocity) (m : ℕ) (t : ℝ) :
    W.coefficientField (W.modalTestCoefficients φ m t) = W.proj m (φ t) := by
  exact coefficientField_initialCoefficients_eq_proj W (φ t) m

/-- Pairing a retained solution slice with the modal test projection is
exactly pairing it with the original test slice. -/
theorem coefficientField_pairing_modalTestCoefficients
    (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (φ : ℝ → SchwartzVelocity) (t : ℝ) :
    schwartzL2Inner (W.coefficientField a)
        (W.coefficientField (W.modalTestCoefficients φ m t)) =
      schwartzL2Inner (W.coefficientField a) (φ t) := by
  rw [coefficientField_modalTestCoefficients,
    coefficientField_pairing_proj]

/-- Projection convergence tested against a fixed Schwartz field. -/
theorem proj_pairing_tendsto (W : GalerkinBasisFamily)
    (u : SchwartzVelocity) (hu : DivergenceFreeInitial u)
    (v : SchwartzVelocity) :
    Filter.Tendsto (fun m => schwartzL2Inner (W.proj m u) v)
      Filter.atTop (nhds (schwartzL2Inner u v)) := by
  have h := proj_error_pairing_tendsto_zero W u hu v
  have hconst : Filter.Tendsto (fun _ : ℕ => schwartzL2Inner u v)
      Filter.atTop (nhds (schwartzL2Inner u v)) := tendsto_const_nhds
  have hsub := hconst.sub h
  have heq : (fun m => schwartzL2Inner (W.proj m u) v) =
      fun m => schwartzL2Inner u v -
        schwartzL2Inner (u - W.proj m u) v := by
    funext m
    rw [schwartzL2Inner_sub_left]
    ring
  rw [heq]
  simpa using hsub

/-- Projection convergence in the second argument, by symmetry. -/
theorem pairing_proj_tendsto (W : GalerkinBasisFamily)
    (u v : SchwartzVelocity) (hv : DivergenceFreeInitial v) :
    Filter.Tendsto (fun m => schwartzL2Inner u (W.proj m v))
      Filter.atTop (nhds (schwartzL2Inner u v)) := by
  simpa only [schwartzL2Inner_comm u, schwartzL2Inner_comm u v] using
    proj_pairing_tendsto W v hv u

/-- Fixed linear pairings against modal test projections converge by basis
completeness. -/
theorem modalTestProjection_pairing_tendsto (W : GalerkinBasisFamily)
    (u : SchwartzVelocity) (φ : ℝ → SchwartzVelocity) (t : ℝ)
    (hφ : DivergenceFreeInitial (φ t)) :
    Filter.Tendsto
      (fun m => schwartzL2Inner u
        (W.coefficientField (W.modalTestCoefficients φ m t)))
      Filter.atTop (nhds (schwartzL2Inner u (φ t))) := by
  simpa only [coefficientField_modalTestCoefficients] using
    pairing_proj_tendsto W u (φ t) hφ

/-- The commutator measuring the exact gap between projecting a test before
and after applying the Schwartz Laplacian.  Plain `L²` completeness controls
`Pₘ(Δφ)`, but does not make this commutator vanish. -/
noncomputable def GalerkinBasisFamily.laplacianProjectionCommutator
    (W : GalerkinBasisFamily) (m : ℕ) (φ : SchwartzVelocity) : SchwartzVelocity :=
  laplacianSchwartz (W.proj m φ) - W.proj m (laplacianSchwartz φ)

theorem laplacian_proj_eq_proj_laplacian_add_commutator
    (W : GalerkinBasisFamily) (m : ℕ) (φ : SchwartzVelocity) :
    laplacianSchwartz (W.proj m φ) =
      W.proj m (laplacianSchwartz φ) +
        W.laplacianProjectionCommutator m φ := by
  unfold GalerkinBasisFamily.laplacianProjectionCommutator
  abel

/-- Against a retained modal field, the projected-test Laplacian splits into
the fixed physical Laplacian plus exactly one commutator pairing. -/
theorem coefficientField_laplacianProjection_pairing
    (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (φ : SchwartzVelocity) :
    schwartzL2Inner (W.coefficientField a)
        (laplacianSchwartz (W.proj m φ)) =
      schwartzL2Inner (W.coefficientField a) (laplacianSchwartz φ) +
        schwartzL2Inner (W.coefficientField a)
          (W.laplacianProjectionCommutator m φ) := by
  rw [laplacian_proj_eq_proj_laplacian_add_commutator,
    schwartzL2Inner_add_right, coefficientField_pairing_proj]

/-- Linear Laplacian limit passage for retained fields.  The fixed-test term
is separated from the sole graph-norm obstruction, the Laplacian/projection
commutator. -/
theorem coefficientField_laplacianProjection_pairing_tendsto
    (W : GalerkinBasisFamily)
    (a : ∀ m : ℕ, EuclideanSpace ℝ (Fin m)) (φ : SchwartzVelocity) (L : ℝ)
    (hlinear : Filter.Tendsto
      (fun m => schwartzL2Inner (W.coefficientField (a m))
        (laplacianSchwartz φ)) Filter.atTop (nhds L))
    (hcomm : Filter.Tendsto
      (fun m => schwartzL2Inner (W.coefficientField (a m))
        (W.laplacianProjectionCommutator m φ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => schwartzL2Inner (W.coefficientField (a m))
        (laplacianSchwartz (W.proj m φ))) Filter.atTop (nhds L) := by
  have hadd := hlinear.add hcomm
  have heq : (fun m => schwartzL2Inner (W.coefficientField (a m))
      (laplacianSchwartz (W.proj m φ))) = fun m =>
      schwartzL2Inner (W.coefficientField (a m)) (laplacianSchwartz φ) +
        schwartzL2Inner (W.coefficientField (a m))
          (W.laplacianProjectionCommutator m φ) := by
    funext m
    exact coefficientField_laplacianProjection_pairing W (a m) φ
  rw [heq]
  simpa using hadd

/-- Unconditional linear convergence with the Laplacian projected *after* it
is taken.  This is the part supplied by ordinary `L²` basis completeness. -/
theorem proj_projectedLaplacian_pairing_tendsto
    (W : GalerkinBasisFamily) (u : SchwartzVelocity)
    (hu : DivergenceFreeInitial u) (φ : SchwartzVelocity) :
    Filter.Tendsto
      (fun m => schwartzL2Inner (W.proj m u)
        (W.proj m (laplacianSchwartz φ)))
      Filter.atTop (nhds (schwartzL2Inner u (laplacianSchwartz φ))) := by
  have h := proj_pairing_tendsto W u hu (laplacianSchwartz φ)
  have heq : (fun m => schwartzL2Inner (W.proj m u)
      (W.proj m (laplacianSchwartz φ))) =
      fun m => schwartzL2Inner (W.proj m u) (laplacianSchwartz φ) := by
    funext m
    rw [← coefficientField_initialCoefficients_eq_proj W u m,
      coefficientField_pairing_proj]
  rw [heq]
  exact h

/-- Specialization of the linear Laplacian limit to projected fixed data.
Basis completeness proves the fixed-Laplacian term; only the displayed
commutator limit remains as an assumption. -/
theorem proj_laplacianProjection_pairing_tendsto_of_commutator
    (W : GalerkinBasisFamily) (u : SchwartzVelocity)
    (hu : DivergenceFreeInitial u) (φ : SchwartzVelocity)
    (hcomm : Filter.Tendsto
      (fun m => schwartzL2Inner (W.proj m u)
        (W.laplacianProjectionCommutator m φ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => schwartzL2Inner (W.proj m u)
        (laplacianSchwartz (W.proj m φ)))
      Filter.atTop (nhds (schwartzL2Inner u (laplacianSchwartz φ))) := by
  have hlinear : Filter.Tendsto
      (fun m => schwartzL2Inner
        (W.coefficientField (W.initialCoefficients u m)) (laplacianSchwartz φ))
      Filter.atTop (nhds (schwartzL2Inner u (laplacianSchwartz φ))) := by
    simpa only [coefficientField_initialCoefficients_eq_proj] using
      proj_pairing_tendsto W u hu (laplacianSchwartz φ)
  have h := coefficientField_laplacianProjection_pairing_tendsto W
    (fun m => W.initialCoefficients u m) φ
    (schwartzL2Inner u (laplacianSchwartz φ))
    hlinear
    (by simpa only [coefficientField_initialCoefficients_eq_proj] using hcomm)
  simpa only [coefficientField_initialCoefficients_eq_proj] using h

/-- Projecting both the datum and the fixed test has the same initial-pairing
limit as the unprojected pair. -/
theorem initialProjection_pairing_tendsto (W : GalerkinBasisFamily)
    (u : SchwartzVelocity) (hu : DivergenceFreeInitial u)
    (v : SchwartzVelocity) :
    Filter.Tendsto
      (fun m => schwartzL2Inner
        (W.coefficientField (W.initialCoefficients u m))
        (W.coefficientField (W.initialCoefficients v m)))
      Filter.atTop (nhds (schwartzL2Inner u v)) := by
  have h := proj_pairing_tendsto W u hu v
  have heq : (fun m => schwartzL2Inner
      (W.coefficientField (W.initialCoefficients u m))
      (W.coefficientField (W.initialCoefficients v m))) =
      fun m => schwartzL2Inner (W.proj m u) v := by
    funext m
    rw [coefficientField_initialCoefficients_eq_proj W v m,
      coefficientField_pairing_proj,
      coefficientField_initialCoefficients_eq_proj W u m]
  rw [heq]
  exact h

/-- The initial linear pairing of a coefficient flow initialized by modal
projection converges to the datum pairing. -/
theorem modalInitial_pairing_tendsto (W : GalerkinBasisFamily)
    (u : SchwartzVelocity) (hu : DivergenceFreeInitial u)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc0 : ∀ m : ℕ, c m 0 = W.initialCoefficients u m)
    (v : SchwartzVelocity) :
    Filter.Tendsto
      (fun m => schwartzL2Inner (W.coefficientField (c m 0)) v)
      Filter.atTop (nhds (schwartzL2Inner u v)) := by
  have h := proj_pairing_tendsto W u hu v
  simpa only [hc0, coefficientField_initialCoefficients_eq_proj] using h

/-!
## Certified-basis modal constructor

This constructor exposes only the genuinely downstream analytic estimates.
The basis realization itself, its initial projection, exact official energy,
joint measurability, slice integrability, and initial convergence are all
discharged here from the concrete coefficient curves and certified basis.
-/

/-- A coefficient curve initialized by the Galerkin coefficients realizes the
genuine projected datum at `t = 0`. -/
theorem modalApprox_initial_eq_proj (W : GalerkinBasisFamily)
    (u₀ : SchwartzVelocity)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc0 : ∀ m : ℕ, c m 0 = W.initialCoefficients u₀ m) :
    ∀ m : ℕ, W.modalApprox c m 0 = fun x => W.proj m u₀ x := by
  intro m
  rw [show W.modalApprox c m =
      galerkinModalApprox (fun n => n) c (fun n => W.finiteModes n) m from rfl,
    galerkinModalApprox_initial_eq]
  funext x
  change W.coefficientField (c m 0) x = W.proj m u₀ x
  rw [hc0 m, coefficientField_initialCoefficients_eq_proj]

/-- A projected coefficient ODE whose Stokes quadratic form is the physical
modal enstrophy supplies the uniform enstrophy field.  This is the exact
finite-dimensional energy-dissipation identity: skew convection contributes
zero, while the Stokes term integrates to at most the initial coefficient
energy divided by `2ν`. -/
theorem modalApprox_uniformEnstrophyBound (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν)
    (A : ∀ m : ℕ, EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (B : ∀ m : ℕ, EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m) (-(ν • A m (c m t)) + B m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (hB_skew : ∀ (m : ℕ) (a : EuclideanSpace ℝ (Fin m)),
      inner ℝ (B m a) a = 0)
    (hA_enstrophy : ∀ (m : ℕ) (a : EuclideanSpace ℝ (Fin m)),
      inner ℝ (A m a) a = W.coefficientEnstrophy a)
    (C : ℝ) (hbudget : ∀ m : ℕ, ‖c m 0‖ ^ 2 / (2 * ν) ≤ C) :
    UniformEnstrophyBound (W.modalApprox c) C := by
  intro m T hT
  have hc_cont : ContinuousOn (c m) (Set.Ici (0 : ℝ)) :=
    fun t ht => (hc m t ht).continuousWithinAt
  have hA_cont : ContinuousOn (fun t => A m (c m t)) (Set.Ici (0 : ℝ)) :=
    (A m).continuous.comp_continuousOn hc_cont
  have hinner_cont : ContinuousOn
      (fun t => (inner ℝ (A m (c m t)) (c m t) : ℝ)) (Set.Ici (0 : ℝ)) :=
    hA_cont.inner hc_cont
  have hdiss :=
    Navier.Analysis.EnergyDissipation.dissipation_integral_le_forward
      (ν := ν) hν (A m) (B m) (c m)
        (fun t => -(ν • A m (c m t)) + B m (c m t))
        (hc m) (fun _ _ => rfl) (fun t _ => hB_skew m (c m t)) hinner_cont hT
  have henstrophy :
      (∫ t in Set.Ioc (0 : ℝ) T, enstrophy (W.modalApprox c m) t) =
        ∫ t in Set.Ioc (0 : ℝ) T, (inner ℝ (A m (c m t)) (c m t) : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    rw [modalApprox_enstrophy_eq W c m (le_of_lt ht.1), ← hA_enstrophy]
  rw [henstrophy]
  exact hdiss.trans (hbudget m)

/-- A uniform bound on the actual projected ODE vector field makes the modal
flows uniformly time-translation equicontinuous.  The proof uses the mean
value theorem on `[0,∞)` for the coefficient curve, the nonexpansive cutoff
`t ↦ max t 0`, and `modalApprox_timeDisplacement_le` to transport the resulting
coefficient Lipschitz estimate to physical `L²`. -/
theorem modalApprox_timeEquicontinuous_of_uniformDerivative
    (W : GalerkinBasisFamily) {ν : ℝ}
    (A : ∀ m : ℕ, EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (B : ∀ m : ℕ, EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m) (-(ν • A m (c m t)) + B m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (K : ℝ) (hK : 0 ≤ K)
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      ‖-(ν • A m (c m t)) + B m (c m t)‖ ≤ K)
    (C : ℝ) (hkin : UniformKineticBound (W.modalApprox c) C) :
    TimeEquicontinuous (W.modalApprox c) := by
  have hjoint : JointlyMeasurable (W.modalApprox c) := by
    simpa [GalerkinBasisFamily.modalApprox] using
      galerkinModalApprox_jointlyMeasurable (fun m => m) c
        (fun m t => -(ν • A m (c m t)) + B m (c m t)) hc
        (fun m => W.finiteModes m)
  have hsq : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      Integrable (fun x : Space => ‖W.modalApprox c m t x‖ ^ 2) := by
    simpa [GalerkinBasisFamily.modalApprox] using
      galerkinModalApprox_sq_integrable (fun m => m) c
        (fun m => W.finiteModes m)
  have hfwd : ∀ m : ℕ, fwd (W.modalApprox c) m = W.modalApprox c m := by
    intro m
    funext t x
    simp [fwd, GalerkinBasisFamily.modalApprox, galerkinModalApprox, forwardExtend]
  intro T ε hε
  rcases lt_or_ge T 0 with hT | hT
  · refine ⟨1, one_pos, fun _ _ _ => ?_⟩
    rw [show Set.Ioc (0 : ℝ) T = ∅ from Set.Ioc_eq_empty (by linarith)]
    simpa using hε.le
  let D : ℝ := (T + 1) * (K + 1) ^ 2
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨min 1 (ε / D), lt_min one_pos (div_pos hε hDpos), ?_⟩
  intro m h hh
  have hh_one : |h| < 1 := hh.trans_le (min_le_left _ _)
  have hh_D : |h| < ε / D := hh.trans_le (min_le_right _ _)
  have hcoeff : ∀ t : ℝ,
      ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ≤ K * |h| := by
    intro t
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := c m)
      (f' := fun r => -(ν • A m (c m r)) + B m (c m r))
      (fun r hr => hc m r hr) (fun r hr => hderiv m r hr)
      (convex_Ici (0 : ℝ))
      (Set.mem_Ici.mpr (le_max_right t 0))
      (Set.mem_Ici.mpr (le_max_right (t + h) 0))
    have hmax : ‖max (t + h) 0 - max t 0‖ ≤ |h| := by
      simpa [Real.norm_eq_abs] using abs_max_sub_max_le_abs (t + h) t 0
    unfold forwardExtend
    exact hmv.trans (mul_le_mul_of_nonneg_left hmax hK)
  have hpoint : ∀ t : ℝ,
      (∫ x : Space,
        ‖W.modalApprox c m (t + h) x - W.modalApprox c m t x‖ ^ 2) ≤
        K ^ 2 * |h| ^ 2 := by
    intro t
    refine (modalApprox_timeDisplacement_le W c m (t + h) t).trans ?_
    have hc_le := hcoeff t
    nlinarith [norm_nonneg (forwardExtend (c m) (t + h) - forwardExtend (c m) t),
      abs_nonneg h]
  have houter : IntegrableOn (fun t : ℝ => ∫ x : Space,
      ‖W.modalApprox c m (t + h) x - W.modalApprox c m t x‖ ^ 2)
      (Set.Ioc (0 : ℝ) T) := by
    simpa only [hfwd m] using
      fwd_tdisp_outer (W.modalApprox c) C hkin hsq hjoint m h 0 T
  have hvol : volume.real (Set.Ioc (0 : ℝ) T) = T := by
    rw [Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ T - 0), sub_zero]
  have habs_sq : |h| ^ 2 ≤ |h| := by
    nlinarith [abs_nonneg h]
  have hTD : T * K ^ 2 ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg K]
  have hDbound : T * (K ^ 2 * |h| ^ 2) ≤ D * |h| := by
    calc
      T * (K ^ 2 * |h| ^ 2) = (T * K ^ 2) * |h| ^ 2 := by ring
      _ ≤ D * |h| ^ 2 := mul_le_mul_of_nonneg_right hTD (sq_nonneg |h|)
      _ ≤ D * |h| := mul_le_mul_of_nonneg_left habs_sq hDpos.le
  have hDsmall : D * |h| < ε := by
    have hm := mul_lt_mul_of_pos_left hh_D hDpos
    calc
      D * |h| < D * (ε / D) := hm
      _ = ε := by field_simp
  calc
    (∫ t in Set.Ioc (0 : ℝ) T, ∫ x : Space,
        ‖W.modalApprox c m (t + h) x - W.modalApprox c m t x‖ ^ 2) ≤
        ∫ _t in Set.Ioc (0 : ℝ) T, K ^ 2 * |h| ^ 2 :=
      setIntegral_mono_on houter
        (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc
        (fun t _ => hpoint t)
    _ = T * (K ^ 2 * |h| ^ 2) := by rw [setIntegral_const, hvol]; simp
    _ ≤ D * |h| := hDbound
    _ ≤ ε := hDsmall.le

/-- Replacing the datum in the weak residual by its Galerkin projection changes
only the initial-time pairing, exactly by the projection error. -/
theorem weakFormResidual_eq_projectedDatum_add (W : GalerkinBasisFamily)
    (ν : ℝ) (u₀ : SchwartzVelocity) (u : VelocityEvolution)
    (φ : DivergenceFreeTestFunction) (m : ℕ) :
    weakFormResidual ν u₀ u φ =
      weakFormResidual ν (W.proj m u₀) u φ +
        schwartzL2Inner (u₀ - W.proj m u₀) (φ.field 0) := by
  have hdatum : schwartzL2Inner u₀ (φ.field 0) =
      schwartzL2Inner (W.proj m u₀) (φ.field 0) +
        schwartzL2Inner (u₀ - W.proj m u₀) (φ.field 0) := by
    rw [schwartzL2Inner_sub_left]
    ring
  unfold weakFormResidual
  change _ + schwartzL2Inner u₀ (φ.field 0) =
    (_ + schwartzL2Inner (W.proj m u₀) (φ.field 0)) +
      schwartzL2Inner (u₀ - W.proj m u₀) (φ.field 0)
  rw [hdatum]
  ring

/-- Weak consistency for the actual datum follows from consistency for the
projected datum used to initialize each finite ODE.  The only correction is a
fixed-test pairing with `u₀ - Pₘu₀`, which vanishes by Bessel convergence. -/
theorem modalApprox_weakConsistent_of_projectedDatum (W : GalerkinBasisFamily)
    (ν : ℝ) (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hprojected : ∀ φ : DivergenceFreeTestFunction,
      Filter.Tendsto
        (fun m => weakFormResidual ν (W.proj m u₀) (W.modalApprox c m) φ)
        Filter.atTop (nhds 0)) :
    ∀ φ : DivergenceFreeTestFunction,
      Filter.Tendsto
        (fun m => weakFormResidual ν u₀ (W.modalApprox c m) φ)
        Filter.atTop (nhds 0) := by
  intro φ
  have heq : (fun m => weakFormResidual ν u₀ (W.modalApprox c m) φ) =
      fun m => weakFormResidual ν (W.proj m u₀) (W.modalApprox c m) φ +
        schwartzL2Inner (u₀ - W.proj m u₀) (φ.field 0) := by
    funext m
    exact weakFormResidual_eq_projectedDatum_add W ν u₀ (W.modalApprox c m) φ m
  rw [heq]
  simpa using
    (hprojected φ).add (proj_error_pairing_tendsto_zero W u₀ hu₀ (φ.field 0))

/-- Bessel's inequality for the actual initial coefficient vector: the energy
of the retained modes is at most the full Euclidean `L²` energy of the datum. -/
theorem initialCoefficients_norm_sq_le (W : GalerkinBasisFamily)
    (u : SchwartzVelocity) (m : ℕ) :
    ‖W.initialCoefficients u m‖ ^ 2 ≤ schwartzL2Inner u u := by
  rw [← coefficientField_l2_isometry W,
    coefficientField_initialCoefficients_eq_proj]
  have horth : schwartzL2Inner (u - W.proj m u) (W.proj m u) = 0 := by
    exact residual_inner_span W m u (W.coeff u)
  have hsplit : u = (u - W.proj m u) + W.proj m u := by abel
  calc
    schwartzL2Inner (W.proj m u) (W.proj m u) ≤
        schwartzL2Inner (u - W.proj m u) (u - W.proj m u) +
          schwartzL2Inner (W.proj m u) (W.proj m u) :=
      le_add_of_nonneg_left (schwartzL2Inner_self_nonneg _)
    _ = schwartzL2Inner ((u - W.proj m u) + W.proj m u)
        ((u - W.proj m u) + W.proj m u) :=
      (schwartzL2Inner_self_add_of_orthogonal _ _ horth).symm
    _ = schwartzL2Inner u u := by rw [← hsplit]

/-- The concrete projected ODE automatically supplies the official modal
energy bound.  Stokes positivity and convection skewness make the coefficient
energy nonincreasing; Bessel's inequality controls its initial value by the
datum's Euclidean `L²` energy. -/
theorem coefficientFlow_energy_le_data (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν) (u₀ : SchwartzVelocity)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (hc0 : ∀ m : ℕ, c m 0 = W.initialCoefficients u₀ m)
    (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖c m t‖ ^ 2 ≤ ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
  have hdiss : ∀ s : ℝ, 0 ≤ s →
      inner ℝ
        (-(ν • W.stokesOperator m (c m s)) + W.convectionOperator m (c m s))
        (c m s) ≤ 0 := by
    intro s _
    rw [inner_add_left, inner_neg_left, inner_smul_left,
      convectionOperator_inner_self]
    simp only [conj_trivial, add_zero]
    exact neg_nonpos.mpr (mul_nonneg hν.le (stokesOperator_nonneg W m (c m s)))
  calc
    ‖c m t‖ ^ 2 ≤ ‖c m 0‖ ^ 2 :=
      norm_sq_le_initial_forward (c m)
        (fun s => -(ν • W.stokesOperator m (c m s)) + W.convectionOperator m (c m s))
        (hc m) hdiss ht
    _ = ‖W.initialCoefficients u₀ m‖ ^ 2 := by rw [hc0 m]
    _ ≤ schwartzL2Inner u₀ u₀ := initialCoefficients_norm_sq_le W u₀ m
    _ = ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
      unfold schwartzL2Inner
      apply integral_congr_ae
      filter_upwards with x
      rw [officialInner_eq_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [pow_two])

/-- **Exact retained-span weak equation.**  Let `b(t)` be a differentiable
finite coefficient test, with continuous derivative and vanishing at a finite
horizon `T`.  Pairing the concrete Galerkin ODE with `b`, integrating the
temporal term by parts on `[0,T]`, and transporting the coefficient inner
product through the modal `L²` isometry gives the physical retained-mode
identity below.  This is the finite-span core of projected weak consistency;
no density claim for arbitrary Schwartz tests is made here. -/
theorem modalFlow_retainedSpan_weakEquation (W : GalerkinBasisFamily)
    (ν : ℝ) (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) (b b' : ℝ → EuclideanSpace ℝ (Fin m))
    (hb : ∀ t : ℝ, HasDerivAt b (b' t) t) (hb'_cont : Continuous b')
    (T : ℝ) (hT : 0 ≤ T) (hb_zero : ∀ t : ℝ, T ≤ t → b t = 0) :
    (∫ t in (0 : ℝ)..T,
        schwartzL2Inner (W.coefficientField (c m t))
          (W.coefficientField (b' t)) +
        schwartzL2Inner
          (W.coefficientField
            (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t)))
          (W.coefficientField (b t))) +
      schwartzL2Inner (W.coefficientField (c m 0))
        (W.coefficientField (b 0)) = 0 := by
  let F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun a => -(ν • W.stokesOperator m a) + W.convectionOperator m a
  have hF_cont : Continuous F := by
    exact ((W.stokesOperator m).contDiff.const_smul ν).neg.add
      (convectionOperator_contDiff W m) |>.continuous
  have hc_cont : ContinuousOn (c m) (Set.Icc (0 : ℝ) T) := by
    intro t ht
    exact (hc m t ht.1).continuousWithinAt.mono Set.Icc_subset_Ici_self
  have hb_cont : Continuous b := continuous_iff_continuousAt.mpr fun t =>
    (hb t).continuousAt
  have hprod_cont : ContinuousOn (fun t => inner ℝ (c m t) (b t))
      (Set.Icc (0 : ℝ) T) := hc_cont.inner hb_cont.continuousOn
  have hF_comp : ContinuousOn (fun t => F (c m t)) (Set.Icc (0 : ℝ) T) :=
    hF_cont.comp_continuousOn hc_cont
  have hdensity_cont : ContinuousOn
      (fun t => inner ℝ (c m t) (b' t) + inner ℝ (F (c m t)) (b t))
      (Set.Icc (0 : ℝ) T) :=
    (hc_cont.inner hb'_cont.continuousOn).add (hF_comp.inner hb_cont.continuousOn)
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => inner ℝ (c m s) (b s))
        (inner ℝ (c m t) (b' t) + inner ℝ (F (c m t)) (b t))
        (Set.Ioi t) t := by
    intro t ht
    have hc_right := (hc m t ht.1.le).mono
      (show Set.Ioi t ⊆ Set.Ici (0 : ℝ) by
        intro s hs
        exact le_trans ht.1.le hs.le)
    simpa only [F] using hc_right.inner ℝ (hb t).hasDerivWithinAt
  have hint : IntervalIntegrable
      (fun t => inner ℝ (c m t) (b' t) + inner ℝ (F (c m t)) (b t))
      volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact hdensity_cont
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hT hprod_cont hderiv hint
  have hcoeff :
      (∫ t in (0 : ℝ)..T,
          inner ℝ (c m t) (b' t) + inner ℝ (F (c m t)) (b t)) +
        inner ℝ (c m 0) (b 0) = 0 := by
    rw [hb_zero T le_rfl, inner_zero_right, zero_sub] at hftc
    linarith
  simpa only [coefficientField_l2_inner, F] using hcoeff

/-- The retained-span coefficient equation rewritten entirely as the physical
weak-form integrand.  The test still lies in the first `m` basis modes; this
statement makes no density or all-Schwartz-test assertion. -/
theorem modalFlow_retainedSpan_physicalWeakEquation (W : GalerkinBasisFamily)
    (ν : ℝ) (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) (b b' : ℝ → EuclideanSpace ℝ (Fin m))
    (hb : ∀ t : ℝ, HasDerivAt b (b' t) t) (hb'_cont : Continuous b')
    (T : ℝ) (hT : 0 ≤ T) (hb_zero : ∀ t : ℝ, T ≤ t → b t = 0) :
    (∫ t in (0 : ℝ)..T,
        schwartzL2Inner (W.coefficientField (c m t))
          (W.coefficientField (b' t)) +
        schwartzL2Inner (W.coefficientField (c m t))
          (ν • laplacianSchwartz (W.coefficientField (b t)) +
            convectionSchwartzBilin (W.coefficientField (c m t))
              (W.coefficientField (b t)))) +
      schwartzL2Inner (W.coefficientField (c m 0))
        (W.coefficientField (b 0)) = 0 := by
  simpa only [projectedVectorField_pairing] using
    modalFlow_retainedSpan_weakEquation W ν c hc m b b' hb hb'_cont T hT hb_zero

/-- Apply the retained-span physical equation to the actual first-`m` modal
projection of a compactly time-supported Schwartz test.  The hypothesis
`hmodal_deriv` is the explicit differentiation-under-the-spatial-integral
seam: it identifies the coefficient derivative with the supplied Schwartz
slice `φ'`. -/
theorem modalFlow_projectedTest_physicalWeakEquation
    (W : GalerkinBasisFamily) (ν : ℝ)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (φ : DivergenceFreeTestFunction) (φ' : ℝ → SchwartzVelocity) (m : ℕ)
    (hmodal_deriv : ∀ t : ℝ,
      HasDerivAt (W.modalTestCoefficients φ.field m)
        (W.modalTestCoefficients φ' m t) t)
    (hmodal_deriv_cont : Continuous (W.modalTestCoefficients φ' m)) :
    ∃ T : ℝ, 0 < T ∧
      (∫ t in (0 : ℝ)..T,
          schwartzL2Inner (W.coefficientField (c m t)) (φ' t) +
          schwartzL2Inner (W.coefficientField (c m t))
            (ν • laplacianSchwartz (W.proj m (φ.field t)) +
              convectionSchwartzBilin (W.coefficientField (c m t))
                (W.proj m (φ.field t)))) +
        schwartzL2Inner (W.coefficientField (c m 0))
          (φ.field 0) = 0 := by
  obtain ⟨T, hT, hφzero⟩ := φ.compact_time
  refine ⟨T, hT, ?_⟩
  have hbzero : ∀ t : ℝ, T ≤ t → W.modalTestCoefficients φ.field m t = 0 := by
    intro t ht
    ext i
    simp [GalerkinBasisFamily.modalTestCoefficients, hφzero t ht,
      GalerkinBasisFamily.initialCoefficients, GalerkinBasisFamily.coeff,
      schwartzL2Inner_zero_left]
  have h := modalFlow_retainedSpan_physicalWeakEquation W ν c hc m
      (W.modalTestCoefficients φ.field m) (W.modalTestCoefficients φ' m)
      hmodal_deriv hmodal_deriv_cont T hT.le hbzero
  simp_rw [coefficientField_pairing_modalTestCoefficients] at h
  simpa only [coefficientField_modalTestCoefficients] using h

/-- The projected-test equation with its linear viscous term split into the
unprojected physical Laplacian and the exact Laplacian/projection commutator.
The convection test remains projected, so nonlinear convergence is not
claimed here. -/
theorem modalFlow_projectedTest_splitLaplacianWeakEquation
    (W : GalerkinBasisFamily) (ν : ℝ)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (φ : DivergenceFreeTestFunction) (φ' : ℝ → SchwartzVelocity) (m : ℕ)
    (hmodal_deriv : ∀ t : ℝ,
      HasDerivAt (W.modalTestCoefficients φ.field m)
        (W.modalTestCoefficients φ' m t) t)
    (hmodal_deriv_cont : Continuous (W.modalTestCoefficients φ' m)) :
    ∃ T : ℝ, 0 < T ∧
      (∫ t in (0 : ℝ)..T,
          schwartzL2Inner (W.coefficientField (c m t)) (φ' t) +
          schwartzL2Inner (W.coefficientField (c m t))
            (ν • laplacianSchwartz (φ.field t) +
              convectionSchwartzBilin (W.coefficientField (c m t))
                (W.proj m (φ.field t))) +
          ν * schwartzL2Inner (W.coefficientField (c m t))
            (W.laplacianProjectionCommutator m (φ.field t))) +
        schwartzL2Inner (W.coefficientField (c m 0)) (φ.field 0) = 0 := by
  obtain ⟨T, hT, heq⟩ :=
    modalFlow_projectedTest_physicalWeakEquation W ν c hc φ φ' m
      hmodal_deriv hmodal_deriv_cont
  refine ⟨T, hT, ?_⟩
  have hintegral :
      (∫ t in (0 : ℝ)..T,
          schwartzL2Inner (W.coefficientField (c m t)) (φ' t) +
          schwartzL2Inner (W.coefficientField (c m t))
            (ν • laplacianSchwartz (W.proj m (φ.field t)) +
              convectionSchwartzBilin (W.coefficientField (c m t))
                (W.proj m (φ.field t)))) =
        ∫ t in (0 : ℝ)..T,
          schwartzL2Inner (W.coefficientField (c m t)) (φ' t) +
          schwartzL2Inner (W.coefficientField (c m t))
            (ν • laplacianSchwartz (φ.field t) +
              convectionSchwartzBilin (W.coefficientField (c m t))
                (W.proj m (φ.field t))) +
          ν * schwartzL2Inner (W.coefficientField (c m t))
            (W.laplacianProjectionCommutator m (φ.field t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [schwartzL2Inner_add_right, schwartzL2Inner_smul_right,
      coefficientField_laplacianProjection_pairing,
      schwartzL2Inner_add_right, schwartzL2Inner_smul_right]
    ring
  rw [hintegral] at heq
  exact heq

/-- Build finite-mode Galerkin data from a certified divergence-free basis and
actual Euclidean coefficient flows.  The constructor itself supplies the
modal realization, projected initial slice, exact official-energy transfer,
joint measurability, square-integrability, and Bessel convergence.  The
remaining hypotheses are precisely the PDE estimates not implied by basis
orthonormality or projected energy dissipation: the inherited-sup kinetic
bound, a uniform projected-vector-field bound, spatial translations, and weak
consistency. -/
theorem galerkinModeData_of_basis_modalFlow (W : GalerkinBasisFamily)
    (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (hc0 : ∀ m : ℕ, c m 0 = W.initialCoefficients u₀ m)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hbound_le : bound ≤ ∫ x : Space, ‖u₀ x‖ ^ 2)
    (hkin : UniformKineticBound (W.modalApprox c) bound)
    (henstrophy_budget : ∀ m : ℕ, ‖c m 0‖ ^ 2 / (2 * ν) ≤ bound)
    (derivativeBound : ℝ) (hderivativeBound : 0 ≤ derivativeBound)
    (hderivative : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      ‖-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t)‖
        ≤ derivativeBound)
    (hspace : SpaceEquicontinuous (W.modalApprox c))
    (hprojectedWeak : ∀ φ : DivergenceFreeTestFunction,
      Filter.Tendsto
        (fun m => weakFormResidual ν (W.proj m u₀) (W.modalApprox c m) φ)
        Filter.atTop (nhds 0)) :
    Nonempty (GalerkinModeData ν u₀) := by
  refine ⟨{
    approx := W.modalApprox c
    initialMode := fun m => W.proj m u₀
    initial_eq := modalApprox_initial_eq_proj W u₀ c hc0
    bound := bound
    bound_nonneg := hbound
    bound_le := hbound_le
    kinetic_bounded := hkin
    official_kinetic_bounded := ?_
    enstrophy_bounded := modalApprox_uniformEnstrophyBound W hν
      (fun m => W.stokesOperator m) (fun m => W.convectionOperator m) c hc
      (convectionOperator_inner_self W)
      (stokesOperator_inner_eq_enstrophy W) bound henstrophy_budget
    time_equicontinuous := modalApprox_timeEquicontinuous_of_uniformDerivative
      W (fun m => W.stokesOperator m) (fun m => W.convectionOperator m) c hc derivativeBound
      hderivativeBound hderivative bound hkin
    space_equicontinuous := hspace
    jointly_measurable := ?_
    sq_integrable := ?_
    initial_converges_L2 := proj_initial_converges_L2 W u₀ hu₀
    weak_consistent := modalApprox_weakConsistent_of_projectedDatum
      W ν u₀ hu₀ c hprojectedWeak }⟩
  · intro m t ht
    rw [modalApprox_kineticEnergy_eq W c m t,
      forwardExtend_eq_of_nonneg (c m) ht]
    exact coefficientFlow_energy_le_data W hν u₀ c hc hc0 m ht
  · simpa [GalerkinBasisFamily.modalApprox] using
      galerkinModalApprox_jointlyMeasurable (fun m => m) c
        (fun m t =>
          -(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t)) hc
        (fun m => W.finiteModes m)
  · simpa [GalerkinBasisFamily.modalApprox] using
      galerkinModalApprox_sq_integrable (fun m => m) c
        (fun m => W.finiteModes m)

end Navier.Analysis.GalerkinBasis
