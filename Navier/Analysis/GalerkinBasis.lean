import Navier.Analysis.GalerkinRawFamily
import Navier.Analysis.EnergyNormBridge
import Navier.Analysis.EnergyDissipation
import Navier.Analysis.EnergyConvectionIntegral
import Navier.Analysis.CurlIdentities
import Navier.Analysis.GalerkinSpaceEquicontinuity

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

## The Stokes bilinear form (certified, no sorry)

* `stokesOperator_inner_eq_curlPairing` — the **polarized** Stokes form
  `⟨A a, b⟩ = ⟨curl u_a, curl u_b⟩_{L²}`, strictly generalizing
  `stokesOperator_inner_eq_enstrophy` (its `b = a` diagonal) off the diagonal.
* `stokesOperator_symm` — self-adjointness, an immediate corollary.
* `abs_stokesOperator_inner_le` — **Cauchy–Schwarz for the Stokes form**,
  `|⟨A a, b⟩| ≤ √(enstrophy a)·√(enstrophy b)`, sharp (equality at `b = a`).
  This is the estimate that converts the *time-integrated* enstrophy bound into
  control of the viscous term in the Galerkin time-displacement identity.

## Time equicontinuity: spatial half certified, coefficient half named

* `timeEquicontinuous_of_coefficientDisplacement` (certified, no sorry) —
  `TimeEquicontinuous (W.modalApprox c)` follows from the *coefficient-level*
  translation bound alone.  The route is `modalApprox_timeDisplacement_le` (the
  modal `L²` isometry composed with `‖·‖∞² ≤ ‖·‖₂²`, constant `1`) plus
  continuity of the forward-extended coefficient curve, and it transports the
  `δ` verbatim, so uniformity in the mode count `m` is preserved.
* `galerkinCoefficientFlow_timeEquicontinuous_of_convectionEstimate` (certified,
  no sorry) — the coefficient half, with the convective estimate carried as an
  explicit hypothesis.  Its conclusion mentions only `ℝ^m`-valued curves: no
  Schwartz field, no spatial integral, no basis property.  The `∃ δ` stands
  outside `∀ m` (the strong, compactness-bearing form; the `∀ m, ∃ δ` weakening
  is content-free and is what would re-falsify
  `aubin_lions_l2loc_compactness`), and the constants are chosen in the order
  `G`, then `θ` against `E` and `T` alone, then `δ` — which is exactly why no
  constant depends on `m`.  Supporting chain, all certified here:
  `coefficientFlow_norm_sq_le_of_enstrophyBound` (the uniform coefficient
  energy, extracted from the *global-in-`T`* enstrophy budget alone via
  positive definiteness of `Ω` and the exact energy identity),
  `coefficientFlow_displacement_identity`, `abs_projectedVectorField_inner_le`,
  `coefficientFlow_displacement_sq_le`,
  `coefficientFlow_shifted_displacement_integral_le`.
* `galerkinCoefficientFlow_timeEquicontinuous` itself now lives in
  `Navier.Analysis.GalerkinModeData`, together with its only consumer
  `exists_galerkinModeData`.  It cannot live here: discharging the convective
  hypothesis needs
  `ConvectionLadyzhenskaya.abs_convectionOperator_inner_pow_four_le_enstrophy`,
  and `ConvectionTrilinear` imports *this* file for `convectionOperator`, so
  the estimate is strictly downstream.  The relocation is a routing move only;
  the statement is byte-identical.

With this layer, `galerkin_approximation_exists`'s remaining inputs are: the
projected Stokes/nonlinearity operators on `span{w_0, …, w_{m−1}}` (feeding
`finiteDim_dissipative_ode_global` + `galerkin_apriori_bound` +
`EnergyDissipation.dissipation_integral_le_forward`, all BANKED), the
coefficient-level time-regularity leaf above, and the weak-consistency
bookkeeping.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped LineDeriv

namespace Navier.Analysis.GalerkinBasis

open Navier
open Navier.Analysis.EnergyNormBridge
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

/-- **The polarized Stokes form is the curl `L²` pairing (certified, no
`sorry`).**  The strict generalization of `stokesOperator_inner_eq_enstrophy`
off the diagonal: pairing `A a` with an arbitrary second coefficient vector `b`
is the physical `⟨∇u_a, ∇u_b⟩_{L²}` term, realized here as the curl pairing
(the two agree on divergence-free fields, which every basis mode is).

Restricting to `b = a` recovers `stokesOperator_inner_eq_enstrophy` exactly, so
this is not a weakening; it is the bilinear form of which the enstrophy is the
quadratic diagonal.  It is what turns Stokes positivity into a genuine
Cauchy–Schwarz estimate (`abs_stokesOperator_inner_le` below), which is the
form the Aubin–Lions time-regularity argument consumes. -/
theorem stokesOperator_inner_eq_curlPairing (W : GalerkinBasisFamily) (m : ℕ)
    (a b : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (W.stokesOperator m a) b =
      schwartzL2Inner (curlSchwartzCLM (W.coefficientField b))
        (curlSchwartzCLM (W.coefficientField a)) := by
  rw [PiLp.inner_apply]
  have hfield : curlSchwartzCLM (W.coefficientField b) =
      ∑ i : Fin m, b i • curlSchwartzCLM (W.w i) := by
    rw [show W.coefficientField b = ∑ i : Fin m, b i • W.w i from rfl, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  simp only [stokesOperator_apply, RCLike.inner_apply, conj_trivial]
  change (∑ i : Fin m, b i *
      schwartzL2Inner (curlSchwartzCLM (W.w i))
        (curlSchwartzCLM (W.coefficientField a))) = _
  rw [hfield, schwartzL2Inner_finset_sum_left]
  exact Finset.sum_congr rfl (fun i _ => (schwartzL2Inner_smul_left _ _ _).symm)

/-- **Self-adjointness of the finite-mode Stokes operator (certified, no
`sorry`).**  Immediate from `stokesOperator_inner_eq_curlPairing` and symmetry
of the `L²` pairing: both sides are the same curl pairing read in the two
orders. -/
theorem stokesOperator_symm (W : GalerkinBasisFamily) (m : ℕ)
    (a b : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (W.stokesOperator m a) b = inner ℝ (W.stokesOperator m b) a := by
  rw [stokesOperator_inner_eq_curlPairing, stokesOperator_inner_eq_curlPairing,
    schwartzL2Inner_comm]

/-- **Cauchy–Schwarz for the Stokes form (certified, no `sorry`).**

`|⟨A a, b⟩| ≤ √(enstrophy a) · √(enstrophy b)`.

The Stokes form is positive semidefinite (`stokesOperator_nonneg`) with
quadratic diagonal `coefficientEnstrophy` (`stokesOperator_inner_eq_enstrophy`),
so it obeys Cauchy–Schwarz; the proof routes through the certified pairing
Cauchy–Schwarz `abs_schwartzL2Inner_le` on the curl fields rather than
re-deriving it.  Equality holds at `b = a`, so the constant `1` is not inflated
and the bound is sharp.

This is the estimate that converts the *time-integrated* enstrophy bound
`UniformEnstrophyBound` into control of the viscous term `⟨A c(s), c(t+h) −
c(t)⟩` in the Galerkin time-displacement identity — the linear half of the
Aubin–Lions time-regularity obligation
`galerkinCoefficientFlow_timeEquicontinuous`. -/
theorem abs_stokesOperator_inner_le (W : GalerkinBasisFamily) (m : ℕ)
    (a b : EuclideanSpace ℝ (Fin m)) :
    |inner ℝ (W.stokesOperator m a) b| ≤
      Real.sqrt (W.coefficientEnstrophy a) * Real.sqrt (W.coefficientEnstrophy b) := by
  rw [stokesOperator_inner_eq_curlPairing]
  have hcs := abs_schwartzL2Inner_le (curlSchwartzCLM (W.coefficientField b))
    (curlSchwartzCLM (W.coefficientField a))
  have ha : ‖toL2 (curlSchwartzCLM (W.coefficientField a))‖ =
      Real.sqrt (W.coefficientEnstrophy a) := by
    rw [coefficientEnstrophy_eq_curlSchwartz, ← norm_toL2_sq]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hb : ‖toL2 (curlSchwartzCLM (W.coefficientField b))‖ =
      Real.sqrt (W.coefficientEnstrophy b) := by
    rw [coefficientEnstrophy_eq_curlSchwartz, ← norm_toL2_sq]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [ha, hb] at hcs
  rw [mul_comm]
  exact hcs

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

/-- **Time equicontinuity descends from the coefficient flow (certified, no
`sorry`).**  The whole spatial half of `TimeEquicontinuous` for a modal
Galerkin family is discharged here: `modalApprox_timeDisplacement_le` (the
modal `L²` isometry followed by `‖·‖∞² ≤ ‖·‖₂²`) bounds the physical
space–time translation error by the finite-dimensional Euclidean coefficient
translation error at the *same* constant `1`, and continuity of the
forward-extended coefficient curve makes the majorant integrable on
`Ioc 0 T`, so `integral_mono_of_nonneg` applies.

The `δ` produced is the `δ` of `hcoef` verbatim, so the uniformity in `m` — the
load-bearing part of `TimeEquicontinuous`, and the whole reason the
`u_m = sin(m t)·w` family is excluded — is transported without loss.  No
Schwartz field, no spatial integral and no basis property survives into
`hcoef`: it is a statement about `ℝ^m`-valued curves alone. -/
theorem timeEquicontinuous_of_coefficientDisplacement (W : GalerkinBasisFamily)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hcont : ∀ m : ℕ, Continuous (fun t : ℝ => forwardExtend (c m) t))
    (hcoef : ∀ T ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ) (h : ℝ), |h| < δ →
      (∫ t in Set.Ioc (0:ℝ) T,
        ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2) ≤ ε) :
    TimeEquicontinuous (W.modalApprox c) := by
  intro T ε hε
  obtain ⟨δ, hδ0, hδ⟩ := hcoef T ε hε
  refine ⟨δ, hδ0, fun m h hh => ?_⟩
  have hgcont : Continuous
      (fun t : ℝ => ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2) :=
    (((hcont m).comp (continuous_id.add continuous_const)).sub (hcont m)).norm.pow 2
  have hgint : IntegrableOn
      (fun t : ℝ => ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2)
      (Set.Ioc (0:ℝ) T) := hgcont.integrableOn_Ioc
  calc
    (∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space,
        ‖W.modalApprox c m (t + h) x - W.modalApprox c m t x‖ ^ 2)
        ≤ ∫ t in Set.Ioc (0:ℝ) T,
            ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2 := by
      refine integral_mono_of_nonneg ?_ hgint ?_
      · filter_upwards with t
        exact integral_nonneg fun x => by positivity
      · filter_upwards with t
        exact modalApprox_timeDisplacement_le W c m (t + h) t
    _ ≤ ε := hδ m h hh

/-- A Schwartz field that is constant is zero: the `k = 1` decay estimate
`‖x‖ · ‖u x‖ ≤ C` forces the constant value to vanish. -/
theorem schwartz_eq_zero_of_const (u : SchwartzVelocity) (hc : ∀ x : Space, u x = u 0) :
    u = 0 := by
  obtain ⟨C, hC0, hC⟩ := u.decay 1 0
  simp only [norm_iteratedFDeriv_zero, pow_one] at hC
  have hv : ‖u 0‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖u 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ Space (C / ‖u 0‖)
    have h1 : ‖x‖ * ‖u x‖ ≤ C := hC x
    rw [hc x] at h1
    have h2 : C / ‖u 0‖ * ‖u 0‖ < ‖x‖ * ‖u 0‖ := mul_lt_mul_of_pos_right hx hpos
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h2
    linarith
  have hzero : u 0 = 0 := norm_eq_zero.mp hv
  ext y i
  rw [hc y, hzero]
  simp

/-- The `L²` pairing of the zero field with itself vanishes. -/
theorem schwartzL2Inner_zero_zero :
    schwartzL2Inner (0 : SchwartzVelocity) (0 : SchwartzVelocity) = 0 := by
  unfold schwartzL2Inner
  have : (fun x : Space =>
      officialInner ((0 : SchwartzVelocity) x) ((0 : SchwartzVelocity) x)) =
      fun _ : Space => (0 : ℝ) := by
    funext x
    simp [officialInner, officialEuclideanPoint]
  rw [this]
  simp

/-- The realized field of a coefficient vector is divergence free. -/
theorem coefficientField_divergenceFree (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) : DivergenceFreeInitial (W.coefficientField a) :=
  divergenceFreeInitial_sum_smul Finset.univ (fun i : Fin m => a i)
    (fun i : Fin m => W.w i) (fun i => W.divergence_free i)

/-- **The coefficient enstrophy form is positive definite.**  If the modal
enstrophy of a coefficient vector vanishes then the vector is zero.

Route: the Dirichlet bridge
`integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree` turns a vanishing
curl energy into a vanishing Dirichlet energy; the Dirichlet integrand is
continuous, nonnegative and integrable (the derivative of a Schwartz field is
Schwartz), so it vanishes identically; a field with vanishing derivative is
constant, and a constant Schwartz field is zero; finally the modal `L²`
isometry `coefficientField_l2_isometry` transports `u = 0` back to `a = 0`. -/
theorem coefficientEnstrophy_eq_zero_iff (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) :
    W.coefficientEnstrophy a = 0 ↔ a = 0 := by
  constructor
  · intro h
    set u : SchwartzVelocity := W.coefficientField a with hu
    -- the Dirichlet energy is dominated by three times the (vanishing) curl energy
    have hcurl : (∫ x : Space, officialEuclideanNorm (staticCurl (⇑u) x) ^ 2) = 0 := h
    have hle := _root_.Navier.Analysis.DivFreeGradientEnstrophy.integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree u (coefficientField_divergenceFree W a)
    rw [hcurl, mul_zero] at hle
    -- the Dirichlet integrand is the squared norm of a Schwartz map
    have hfd : (fun x : Space => fderiv ℝ (⇑u) x) =
        ⇑(SchwartzMap.fderivCLM ℝ Space Space u) := by
      funext x
      rw [SchwartzMap.fderivCLM_apply]
    have hint : Integrable (fun x : Space => ‖fderiv ℝ (⇑u) x‖ ^ 2) := by
      rw [show (fun x : Space => ‖fderiv ℝ (⇑u) x‖ ^ 2) =
          (fun x : Space => ‖(SchwartzMap.fderivCLM ℝ Space Space u) x‖ ^ 2) by
        funext x; rw [SchwartzMap.fderivCLM_apply]]
      exact Navier.Analysis.GalerkinSpaceEquicontinuity.schwartz_integrable_norm_sq (SchwartzMap.fderivCLM ℝ Space Space u)
    have hnonneg : 0 ≤ (fun x : Space => ‖fderiv ℝ (⇑u) x‖ ^ 2) := fun x => by positivity
    have hzeroint : (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) = 0 :=
      le_antisymm hle (integral_nonneg hnonneg)
    have hae : (fun x : Space => ‖fderiv ℝ (⇑u) x‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg hnonneg hint).mp hzeroint
    -- continuity upgrades a.e. vanishing to identical vanishing
    have hcont : Continuous (fun x : Space => ‖fderiv ℝ (⇑u) x‖ ^ 2) := by
      rw [show (fun x : Space => ‖fderiv ℝ (⇑u) x‖ ^ 2) =
          (fun x : Space => ‖(SchwartzMap.fderivCLM ℝ Space Space u) x‖ ^ 2) by
        funext x; rw [SchwartzMap.fderivCLM_apply]]
      exact (SchwartzMap.fderivCLM ℝ Space Space u).continuous.norm.pow 2
    have heq : (fun x : Space => ‖fderiv ℝ (⇑u) x‖ ^ 2) = 0 :=
      (hcont.ae_eq_iff_eq volume continuous_const).mp hae
    have hfderiv : ∀ x : Space, fderiv ℝ (⇑u) x = 0 := by
      intro x
      have := congrFun heq x
      simp only [Pi.zero_apply] at this
      have h2 : ‖fderiv ℝ (⇑u) x‖ = 0 := by
        nlinarith [norm_nonneg (fderiv ℝ (⇑u) x)]
      exact norm_eq_zero.mp h2
    -- constant, hence zero
    have hconst : ∀ x : Space, u x = u 0 :=
      fun x => is_const_of_fderiv_eq_zero u.differentiable hfderiv x 0
    have huz : u = 0 := schwartz_eq_zero_of_const u hconst
    -- transport through the modal isometry
    have hiso := coefficientField_l2_isometry W a
    rw [← hu, huz] at hiso
    have : ‖a‖ ^ 2 = 0 := by
      rw [← hiso, schwartzL2Inner_zero_zero]
    have : ‖a‖ = 0 := by nlinarith [norm_nonneg a]
    exact norm_eq_zero.mp this
  · rintro rfl
    have : W.coefficientField (0 : EuclideanSpace ℝ (Fin m)) = 0 := by
      simp [GalerkinBasisFamily.coefficientField]
    rw [coefficientEnstrophy_eq_curlSchwartz, this, map_zero,
      schwartzL2Inner_zero_zero]

/-- **Positive definiteness of the modal enstrophy form, in positive form.**
A nonzero coefficient vector has strictly positive modal enstrophy.  This is
`coefficientEnstrophy_eq_zero_iff` combined with nonnegativity of the density.
[Temam III §3; the underlying fact is that a divergence-free Schwartz field on
`ℝ³` with vanishing curl vanishes.] -/
theorem coefficientEnstrophy_pos_of_ne_zero (W : GalerkinBasisFamily) {m : ℕ}
    {a : EuclideanSpace ℝ (Fin m)} (ha : a ≠ 0) :
    0 < W.coefficientEnstrophy a := by
  have hnn : 0 ≤ W.coefficientEnstrophy a := integral_nonneg fun x => by positivity
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exact absurd ((coefficientEnstrophy_eq_zero_iff W a).mp h.symm) ha

/-- **The enstrophy density along a coefficient flow is continuous.**  The
Stokes quadratic form is continuous and equals the modal enstrophy
(`stokesOperator_inner_eq_enstrophy`), and the trajectory is continuous on
`[0,∞)` because it is differentiable there. -/
theorem coefficientFlow_enstrophy_continuousOn (W : GalerkinBasisFamily)
    {ν : ℝ} (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) :
    ContinuousOn (fun s => W.coefficientEnstrophy (c m s)) (Set.Ici (0 : ℝ)) := by
  have hc_cont : ContinuousOn (c m) (Set.Ici (0 : ℝ)) :=
    fun s hs => (hc m s hs).continuousWithinAt
  have hA_cont : ContinuousOn (fun s => W.stokesOperator m (c m s)) (Set.Ici (0 : ℝ)) :=
    (W.stokesOperator m).continuous.comp_continuousOn hc_cont
  refine (hA_cont.inner hc_cont).congr ?_
  intro s _
  exact (stokesOperator_inner_eq_enstrophy W m (c m s)).symm

/-- **The exact finite-dimensional energy identity for the concrete projected
flow.**  `‖c(T)‖² + 2ν∫₀ᵀ Ω(c(s)) ds = ‖c(0)‖²`: pairing the ODE with the
solution kills the skew convection term (`convectionOperator_inner_self`) and
leaves the Stokes quadratic form, which is exactly the modal enstrophy
(`stokesOperator_inner_eq_enstrophy`).  This is
`EnergyDissipation.energy_dissipation_identity_forward` specialized to the
concrete operators and rewritten into the `Set.Ioc` integral that the enstrophy
budget uses. [Leray 1934 §§18–20; Temam III §3 eq. (3.29).] -/
theorem coefficientFlow_energy_identity (W : GalerkinBasisFamily)
    {ν : ℝ} (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖c m T‖ ^ 2 + 2 * ν * (∫ s in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m s))
      = ‖c m 0‖ ^ 2 := by
  have hc_cont : ContinuousOn (c m) (Set.Ici (0 : ℝ)) :=
    fun s hs => (hc m s hs).continuousWithinAt
  have hA_cont : ContinuousOn (fun s => W.stokesOperator m (c m s)) (Set.Ici (0 : ℝ)) :=
    (W.stokesOperator m).continuous.comp_continuousOn hc_cont
  have hinner_cont : ContinuousOn
      (fun s => (inner ℝ (W.stokesOperator m (c m s)) (c m s) : ℝ)) (Set.Ici (0 : ℝ)) :=
    hA_cont.inner hc_cont
  have h := Navier.Analysis.EnergyDissipation.energy_dissipation_identity_forward
    ν (W.stokesOperator m) (W.convectionOperator m) (c m)
    (fun s => -(ν • W.stokesOperator m (c m s)) + W.convectionOperator m (c m s))
    (hc m) (fun _ _ => rfl)
    (fun s _ => convectionOperator_inner_self W m (c m s)) hinner_cont hT
  rw [intervalIntegral.integral_of_le hT] at h
  have hcongr : (∫ s in Set.Ioc (0:ℝ) T,
      (inner ℝ (W.stokesOperator m (c m s)) (c m s) : ℝ)) =
      ∫ s in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m s) := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro s _
    exact stokesOperator_inner_eq_enstrophy W m (c m s)
  rwa [hcongr] at h

/-- **A compact spherical shell carries a uniform positive enstrophy floor.**
On `{a : L ≤ ‖a‖ ≤ R}` with `L > 0` the continuous form `Ω` attains its minimum
(the shell is closed and bounded in a finite-dimensional space, hence compact),
and the minimizer is nonzero, so the minimum is strictly positive by
`coefficientEnstrophy_pos_of_ne_zero`.  When the shell is empty — which happens
exactly when `m = 0` — any positive constant works. -/
theorem exists_pos_enstrophy_floor_on_shell (W : GalerkinBasisFamily) (m : ℕ)
    {L R : ℝ} (hL : 0 < L) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ a : EuclideanSpace ℝ (Fin m),
      L ≤ ‖a‖ → ‖a‖ ≤ R → eta ≤ W.coefficientEnstrophy a := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin m)) := {a | L ≤ ‖a‖ ∧ ‖a‖ ≤ R} with hSdef
  have hOm_cont :
      Continuous (fun a : EuclideanSpace ℝ (Fin m) => W.coefficientEnstrophy a) := by
    have hbase : Continuous
        (fun a : EuclideanSpace ℝ (Fin m) => (inner ℝ (W.stokesOperator m a) a : ℝ)) :=
      (W.stokesOperator m).continuous.inner continuous_id
    refine hbase.congr ?_
    intro a
    exact stokesOperator_inner_eq_enstrophy W m a
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, ?_⟩
    intro a h1 h2
    have : a ∈ S := ⟨h1, h2⟩
    rw [hSe] at this
    exact absurd this (by simp)
  · have hSclosed : IsClosed S :=
      (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    have hSbdd : Bornology.IsBounded S := by
      refine (Metric.isBounded_closedBall
        (x := (0 : EuclideanSpace ℝ (Fin m))) (r := R)).subset ?_
      intro a ha
      simpa [Metric.mem_closedBall, dist_zero_right] using ha.2
    have hScompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
    obtain ⟨a0, ha0S, ha0min⟩ := hScompact.exists_isMinOn hSne hOm_cont.continuousOn
    have ha0ne : a0 ≠ 0 := by
      intro hz
      have h1 : L ≤ ‖a0‖ := ha0S.1
      rw [hz, norm_zero] at h1
      linarith
    exact ⟨W.coefficientEnstrophy a0, coefficientEnstrophy_pos_of_ne_zero W ha0ne,
      fun a h1 h2 => ha0min ⟨h1, h2⟩⟩

/-- **The initial coefficient energy is controlled by the enstrophy budget.**
`‖c_m(0)‖² ≤ 2νE`, uniformly in `m`.

If not, the energy identity `‖c(T)‖² = ‖c(0)‖² − 2ν∫₀ᵀ Ω` together with
`∫₀ᵀ Ω ≤ E` confines the trajectory for *all* time to the compact shell
`L ≤ ‖a‖ ≤ ‖c(0)‖` with `L² = ‖c(0)‖² − 2νE > 0`.  On that shell
`exists_pos_enstrophy_floor_on_shell` gives `Ω ≥ η > 0`, so `∫₀ᵀ Ω ≥ ηT`,
which exceeds `E` at `T = (E+1)/η` — contradicting the budget.

The *global-in-`T`* form of the hypothesis is load-bearing here: a
finite-horizon enstrophy budget genuinely does not bound the initial energy. -/
theorem coefficientFlow_initial_norm_sq_le_of_enstrophyBound (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (enstrophyBound : ℝ)
    (henst : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound)
    (m : ℕ) :
    ‖c m 0‖ ^ 2 ≤ 2 * ν * enstrophyBound := by
  classical
  have hOmega_cont := coefficientFlow_enstrophy_continuousOn W c hc m
  have hE0 : 0 ≤ enstrophyBound := by simpa using henst m 0 le_rfl
  have hid := fun (T : ℝ) (hT : 0 ≤ T) => coefficientFlow_energy_identity W c hc m hT
  by_contra hcon
  push_neg at hcon
  set R : ℝ := ‖c m 0‖ with hR
  set Lsq : ℝ := ‖c m 0‖ ^ 2 - 2 * ν * enstrophyBound with hLsq
  have hLsq_pos : 0 < Lsq := by simp only [hLsq]; linarith
  set L : ℝ := Real.sqrt Lsq with hL
  have hL_pos : 0 < L := Real.sqrt_pos.mpr hLsq_pos
  -- the trajectory is trapped in the shell `L ≤ ‖a‖ ≤ R` for all time
  have hlow : ∀ T : ℝ, 0 ≤ T → L ≤ ‖c m T‖ := by
    intro T hT
    have h3 : Lsq ≤ ‖c m T‖ ^ 2 := by nlinarith [hid T hT, henst m T hT]
    calc L = Real.sqrt Lsq := hL
      _ ≤ Real.sqrt (‖c m T‖ ^ 2) := Real.sqrt_le_sqrt h3
      _ = ‖c m T‖ := Real.sqrt_sq (norm_nonneg _)
  have hhigh : ∀ T : ℝ, 0 ≤ T → ‖c m T‖ ≤ R := by
    intro T hT
    have h2 : (0:ℝ) ≤ ∫ s in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m s) :=
      setIntegral_nonneg measurableSet_Ioc
        (fun s _ => integral_nonneg fun x => by positivity)
    have h3 : ‖c m T‖ ^ 2 ≤ R ^ 2 := by nlinarith [hid T hT]
    calc ‖c m T‖ = Real.sqrt (‖c m T‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt h3
      _ = R := Real.sqrt_sq (norm_nonneg _)
  -- a uniform positive enstrophy floor along the whole trajectory
  obtain ⟨eta, heta_pos, hfloor⟩ := exists_pos_enstrophy_floor_on_shell W m (R := R) hL_pos
  have hbig : ∀ T : ℝ, 0 ≤ T →
      eta * T ≤ ∫ s in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m s) := by
    intro T hT
    have hIntOn : IntegrableOn (fun s => W.coefficientEnstrophy (c m s))
        (Set.Ioc (0:ℝ) T) :=
      (((hOmega_cont.mono Set.Icc_subset_Ici_self).integrableOn_Icc)).mono_set
        Set.Ioc_subset_Icc_self
    have hconst : (∫ _s in Set.Ioc (0:ℝ) T, eta) = eta * T := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc,
        sub_zero, ENNReal.toReal_ofReal hT]
      ring
    calc eta * T = ∫ _s in Set.Ioc (0:ℝ) T, eta := hconst.symm
      _ ≤ ∫ s in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m s) :=
          setIntegral_mono_on
            (((continuousOn_const (s := Set.Icc (0:ℝ) T)
                (c := eta)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
            hIntOn measurableSet_Ioc
            (fun s hs => hfloor _ (hlow s hs.1.le) (hhigh s hs.1.le))
  have hTchoice : (0:ℝ) ≤ (enstrophyBound + 1) / eta := by positivity
  have h1 := hbig _ hTchoice
  have h2 := henst m _ hTchoice
  rw [mul_div_cancel₀ _ (ne_of_gt heta_pos)] at h1
  linarith

/-- **The uniform coefficient-energy bound extracted from the enstrophy budget
alone.**

The hypotheses of the Aubin–Lions leaf budget only the *time-integrated
enstrophy* `∫₀ᵀ Ω(c(t)) dt ≤ E`, uniformly in `m` and in `T`.  The convective
estimate that leaf must consume,
`|⟨B(a), b⟩|⁴ ≤ C‖a‖²Ω(a)³Ω(b)²`, additionally needs the coefficient *energy*
`‖a‖`, which is not among those hypotheses.  This theorem supplies it, with a
constant depending only on `ν` and `E` — in particular uniform in `m`:

  `‖c_m(t)‖² ≤ 2 ν E`  for every `m` and every `t ≥ 0`.

The energy is nonincreasing along the flow (`norm_sq_le_initial_forward`, using
Stokes positivity and convection skewness), so the claim reduces to
`coefficientFlow_initial_norm_sq_le_of_enstrophyBound` at `t = 0`.

Dimensional check: on `ℝ³` the Dirichlet form controls `L⁶` but not `L⁴`, so no
estimate of the convective shape above can drop the `L²` factor; the energy
really is a needed ingredient rather than a rearrangement of `henst`. -/
theorem coefficientFlow_norm_sq_le_of_enstrophyBound (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (enstrophyBound : ℝ)
    (henst : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound)
    (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖c m t‖ ^ 2 ≤ 2 * ν * enstrophyBound := by
  calc ‖c m t‖ ^ 2 ≤ ‖c m 0‖ ^ 2 := by
        refine norm_sq_le_initial_forward (c m)
          (fun s => -(ν • W.stokesOperator m (c m s)) + W.convectionOperator m (c m s))
          (hc m) ?_ ht
        intro s _
        rw [inner_add_left, inner_neg_left, inner_smul_left,
          convectionOperator_inner_self]
        simp only [conj_trivial, add_zero]
        exact neg_nonpos.mpr (mul_nonneg hν.le (stokesOperator_nonneg W m (c m s)))
    _ ≤ 2 * ν * enstrophyBound :=
        coefficientFlow_initial_norm_sq_le_of_enstrophyBound W hν c hc enstrophyBound henst m

/-- **Young's inequality at exponent `2`.**  `√y ≤ θ y + 1/(4θ)` for `y ≥ 0`
and `θ > 0`; the slack is `(1/(4θ))(2θ√y − 1)² ≥ 0`.  Equality at
`y = 1/(4θ²)`, so the constant is sharp. -/
theorem sqrt_le_mul_add_inv (θ y : ℝ) (hθ : 0 < θ) (hy : 0 ≤ y) :
    Real.sqrt y ≤ θ * y + 1 / (4 * θ) := by
  obtain ⟨e, hnn, he⟩ : ∃ e : ℝ, 0 ≤ e ∧ e ^ 2 = y :=
    ⟨Real.sqrt y, Real.sqrt_nonneg y, Real.sq_sqrt hy⟩
  have hs : Real.sqrt y = e := by rw [← he, Real.sqrt_sq hnn]
  rw [hs, ← he]
  have hid : θ * e ^ 2 + 1 / (4 * θ) - e = (2 * θ * e - 1) ^ 2 / (4 * θ) := by
    field_simp
    ring
  have hpos : (0:ℝ) ≤ (2 * θ * e - 1) ^ 2 / (4 * θ) := by positivity
  linarith

/-- **Young's inequality at exponent `4`.**  If `d ≥ 0`, `y ≥ 0` and
`d⁴ ≤ K y³` with `K ≥ 0`, then `d ≤ θ y + K/(4θ³)` for every `θ > 0`.

This is the device that keeps the Aubin–Lions assembly free of fractional
powers: the convective estimate is available only in its fourth-power form, and
this converts it into a bound that is *linear* in the enstrophy density, which
is exactly the quantity the budget `henst` controls.  Sending `θ → 0` recovers
the sharp `d ≤ K^{1/4} y^{3/4}` in the limit. -/
theorem quartic_root_le_mul_add {K θ d y : ℝ} (hK : 0 ≤ K) (hθ : 0 < θ)
    (hy : 0 ≤ y) (hd : 0 ≤ d) (hd4 : d ^ 4 ≤ K * y ^ 3) :
    d ≤ θ * y + K / (4 * θ ^ 3) := by
  have hC0 : 0 ≤ K / (4 * θ ^ 3) := by positivity
  have hb : 0 ≤ θ * y := by positivity
  -- `(a + C)⁴ ≥ 4a³C` for `a, C ≥ 0`, and `4(θy)³C = K y³`
  have hexp : 4 * (θ * y) ^ 3 * (K / (4 * θ ^ 3)) = K * y ^ 3 := by
    field_simp
  have hpow : d ^ 4 ≤ (θ * y + K / (4 * θ ^ 3)) ^ 4 := by
    nlinarith [hd4, hexp, sq_nonneg (θ * y), sq_nonneg (K / (4 * θ ^ 3)),
      mul_nonneg hb hC0, sq_nonneg (θ * y + K / (4 * θ ^ 3)),
      mul_nonneg (mul_nonneg hb hb) hC0,
      mul_nonneg (mul_nonneg hb hC0) hC0, mul_nonneg (mul_nonneg hC0 hC0) hC0]
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow

/-- **`√Ω` obeys the triangle inequality.**  The modal enstrophy is the
quadratic form of the positive semidefinite Stokes operator, so its square root
is a seminorm; the polarization uses `stokesOperator_symm` and the certified
Cauchy–Schwarz `abs_stokesOperator_inner_le`. -/
theorem sqrt_coefficientEnstrophy_sub_le (W : GalerkinBasisFamily) (m : ℕ)
    (a b : EuclideanSpace ℝ (Fin m)) :
    Real.sqrt (W.coefficientEnstrophy (a - b)) ≤
      Real.sqrt (W.coefficientEnstrophy a) + Real.sqrt (W.coefficientEnstrophy b) := by
  have hna : 0 ≤ W.coefficientEnstrophy a := integral_nonneg fun x => by positivity
  have hnb : 0 ≤ W.coefficientEnstrophy b := integral_nonneg fun x => by positivity
  have hpolar : W.coefficientEnstrophy (a - b) =
      W.coefficientEnstrophy a - 2 * (inner ℝ (W.stokesOperator m a) b : ℝ)
        + W.coefficientEnstrophy b := by
    have h1 : (inner ℝ (W.stokesOperator m (a - b)) (a - b) : ℝ) =
        W.coefficientEnstrophy (a - b) := stokesOperator_inner_eq_enstrophy W m (a - b)
    have h2 : (inner ℝ (W.stokesOperator m a) a : ℝ) = W.coefficientEnstrophy a :=
      stokesOperator_inner_eq_enstrophy W m a
    have h3 : (inner ℝ (W.stokesOperator m b) b : ℝ) = W.coefficientEnstrophy b :=
      stokesOperator_inner_eq_enstrophy W m b
    have h4 : (inner ℝ (W.stokesOperator m b) a : ℝ) =
        (inner ℝ (W.stokesOperator m a) b : ℝ) := stokesOperator_symm W m b a
    rw [← h1, ← h2, ← h3, map_sub, inner_sub_left, inner_sub_right, inner_sub_right, h4]
    ring
  have hcs : |(inner ℝ (W.stokesOperator m a) b : ℝ)| ≤
      Real.sqrt (W.coefficientEnstrophy a) * Real.sqrt (W.coefficientEnstrophy b) :=
    abs_stokesOperator_inner_le W m a b
  have hkey : W.coefficientEnstrophy (a - b) ≤
      (Real.sqrt (W.coefficientEnstrophy a) + Real.sqrt (W.coefficientEnstrophy b)) ^ 2 := by
    have hsa : Real.sqrt (W.coefficientEnstrophy a) ^ 2 = W.coefficientEnstrophy a :=
      Real.sq_sqrt hna
    have hsb : Real.sqrt (W.coefficientEnstrophy b) ^ 2 = W.coefficientEnstrophy b :=
      Real.sq_sqrt hnb
    have := abs_le.mp hcs
    rw [hpolar]
    nlinarith [this.1, this.2, hsa, hsb]
  calc Real.sqrt (W.coefficientEnstrophy (a - b))
      ≤ Real.sqrt ((Real.sqrt (W.coefficientEnstrophy a)
          + Real.sqrt (W.coefficientEnstrophy b)) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt (W.coefficientEnstrophy a) + Real.sqrt (W.coefficientEnstrophy b) :=
        Real.sqrt_sq (by positivity)

/-- **The displacement identity for the projected flow.**  Pairing the Galerkin
ODE with the fixed vector `c(p) − c(q)` and integrating on the interval between
`q` and `p` gives

  `‖c(p) − c(q)‖² = ∫_q^p ⟨c'(s), c(p) − c(q)⟩ ds`.

This is the identity that starts every Aubin–Lions time-regularity argument
[Simon, Ann. Mat. Pura Appl. 146 (1987) 65–96; Temam III §3].  The right
derivative on `Ioo` suffices, which is what the forward-in-time
`HasDerivWithinAt … (Set.Ici 0)` hypothesis supplies. -/
theorem coefficientFlow_displacement_identity (W : GalerkinBasisFamily) {ν : ℝ}
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ‖c m p - c m q‖ ^ 2 =
      ∫ s in q..p, (inner ℝ
        (-(ν • W.stokesOperator m (c m s)) + W.convectionOperator m (c m s))
        (c m p - c m q) : ℝ) := by
  set w : EuclideanSpace ℝ (Fin m) := c m p - c m q with hw
  set F : ℝ → EuclideanSpace ℝ (Fin m) := fun s =>
    -(ν • W.stokesOperator m (c m s)) + W.convectionOperator m (c m s) with hF
  -- the ordered case, proved once and used in both orders
  have hordered : ∀ x y : ℝ, 0 ≤ x → x ≤ y →
      (∫ s in x..y, (inner ℝ (F s) w : ℝ)) =
        (inner ℝ (c m y) w : ℝ) - (inner ℝ (c m x) w : ℝ) := by
    intro x y hx hxy
    have hy : 0 ≤ y := le_trans hx hxy
    have hderiv : ∀ z ∈ Set.Ioo x y,
        HasDerivWithinAt (fun s => (inner ℝ (c m s) w : ℝ))
          ((inner ℝ (F z) w : ℝ)) (Set.Ioi z) z := by
      intro z hz
      have hz0 : 0 ≤ z := le_trans hx hz.1.le
      have hd : HasDerivWithinAt (c m) (F z) (Set.Ioi z) z :=
        (hc m z hz0).mono (fun r hr => le_trans hz0 (le_of_lt hr))
      have hconstd : HasDerivWithinAt (fun _ : ℝ => w) (0 : EuclideanSpace ℝ (Fin m))
        (Set.Ioi z) z := hasDerivWithinAt_const _ _ _
      have h := hd.inner ℝ hconstd
      simpa using h
    have hcontOn : ContinuousOn (fun s => (inner ℝ (c m s) w : ℝ)) (Set.Icc x y) := by
      intro s hs
      have hs0 : 0 ≤ s := le_trans hx hs.1
      exact (((hc m s hs0).continuousWithinAt).mono
        (fun r hr => le_trans hx hr.1)).inner continuousWithinAt_const
    have hcontF : ContinuousOn (fun s => (inner ℝ (F s) w : ℝ)) (Set.Icc x y) := by
      intro s hs
      have hs0 : 0 ≤ s := le_trans hx hs.1
      have hcm : ContinuousWithinAt (c m) (Set.Icc x y) s :=
        ((hc m s hs0).continuousWithinAt).mono (fun r hr => le_trans hx hr.1)
      have hA : ContinuousWithinAt (fun r => W.stokesOperator m (c m r)) (Set.Icc x y) s :=
        (W.stokesOperator m).continuous.continuousAt.comp_continuousWithinAt hcm
      have hB : ContinuousWithinAt (fun r => W.convectionOperator m (c m r))
          (Set.Icc x y) s :=
        ((convectionOperator_contDiff W m).continuous).continuousAt.comp_continuousWithinAt hcm
      exact ((hA.const_smul ν).neg.add hB).inner continuousWithinAt_const
    have hint : IntervalIntegrable (fun s => (inner ℝ (F s) w : ℝ)) volume x y := by
      apply ContinuousOn.intervalIntegrable
      rwa [Set.uIcc_of_le hxy]
    exact (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hxy hcontOn hderiv hint)
  rcases le_total q p with hqp | hpq
  · rw [hordered q p hq hqp]
    rw [← real_inner_self_eq_norm_sq]
    rw [hw, inner_sub_left]
  · rw [intervalIntegral.integral_symm, hordered p q hp hpq]
    rw [← real_inner_self_eq_norm_sq]
    rw [hw, inner_sub_left]
    ring

/-- **The pointwise convective bound in enstrophy-linear form.**  Combining the
fourth-power convective estimate with the uniform energy bound and Young at
exponent `4`, the convection pairing against a fixed vector `b` is bounded by a
quantity *linear* in the enstrophy density of `a` — which is exactly what the
time-integrated enstrophy budget controls. -/
theorem abs_convectionOperator_inner_le_linear (W : GalerkinBasisFamily) {m : ℕ}
    {K θ : ℝ} (hK : 0 ≤ K) (hθ : 0 < θ)
    (a b : EuclideanSpace ℝ (Fin m))
    (hbound : |(inner ℝ (W.convectionOperator m a) b : ℝ)| ^ 4 ≤
      K * W.coefficientEnstrophy a ^ 3 * W.coefficientEnstrophy b ^ 2) :
    |(inner ℝ (W.convectionOperator m a) b : ℝ)| ≤
      (θ * W.coefficientEnstrophy a + K / (4 * θ ^ 3)) *
        Real.sqrt (W.coefficientEnstrophy b) := by
  set Y : ℝ := W.coefficientEnstrophy a with hY
  set Z : ℝ := W.coefficientEnstrophy b with hZ
  have hYn : 0 ≤ Y := integral_nonneg fun x => by positivity
  have hZn : 0 ≤ Z := integral_nonneg fun x => by positivity
  set X : ℝ := |(inner ℝ (W.convectionOperator m a) b : ℝ)| with hX
  have hXn : 0 ≤ X := abs_nonneg _
  set D : ℝ := Real.sqrt (Real.sqrt (K * Y ^ 3)) with hD
  have hDn : 0 ≤ D := Real.sqrt_nonneg _
  have hu : 0 ≤ K * Y ^ 3 := by positivity
  have hD4 : D ^ 4 = K * Y ^ 3 := by
    have h1 : Real.sqrt (K * Y ^ 3) ^ 2 = K * Y ^ 3 := Real.sq_sqrt hu
    have h2 : D ^ 2 = Real.sqrt (K * Y ^ 3) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc D ^ 4 = (D ^ 2) ^ 2 := by ring
      _ = Real.sqrt (K * Y ^ 3) ^ 2 := by rw [h2]
      _ = K * Y ^ 3 := h1
  have hsq4 : Real.sqrt Z ^ 4 = Z ^ 2 := by
    have h1 : Real.sqrt Z ^ 2 = Z := Real.sq_sqrt hZn
    calc Real.sqrt Z ^ 4 = (Real.sqrt Z ^ 2) ^ 2 := by ring
      _ = Z ^ 2 := by rw [h1]
  -- `X ≤ D · √Z` from the fourth powers
  have hXD : X ≤ D * Real.sqrt Z := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
    calc X ^ 4 ≤ K * Y ^ 3 * Z ^ 2 := hbound
      _ = (D * Real.sqrt Z) ^ 4 := by rw [mul_pow, hD4, hsq4]
  -- Young at exponent `4` linearizes `D`
  have hDY : D ≤ θ * Y + K / (4 * θ ^ 3) :=
    quartic_root_le_mul_add hK hθ hYn hDn (le_of_eq hD4)
  calc X ≤ D * Real.sqrt Z := hXD
    _ ≤ (θ * Y + K / (4 * θ ^ 3)) * Real.sqrt Z :=
        mul_le_mul_of_nonneg_right hDY (Real.sqrt_nonneg _)

/-- **The projected ODE vector field, paired against a fixed vector, is
bounded linearly in the enstrophy density.**

`|⟨c'(s), b⟩| ≤ ((ν+1)θ·Ω(c(s)) + ν/(4θ) + K/(4θ³))·√Ω(b)`, with
`K = C·2νE`.

Both halves are linearized by Young so that the `s`-dependence enters only
through `Ω(c(s))` — the one quantity the time-integrated budget `henst`
controls.  The viscous half uses the Stokes Cauchy–Schwarz
`abs_stokesOperator_inner_le` and `sqrt_le_mul_add_inv`; the convective half
uses `abs_convectionOperator_inner_le_linear`, whose energy factor is supplied
uniformly in `m` by `coefficientFlow_norm_sq_le_of_enstrophyBound`. -/
theorem abs_projectedVectorField_inner_le (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (enstrophyBound : ℝ)
    (henst : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound)
    {Cconv : ℝ} (hCconv : 0 ≤ Cconv)
    (hconv : ∀ (m : ℕ) (a b : EuclideanSpace ℝ (Fin m)),
      |(inner ℝ (W.convectionOperator m a) b : ℝ)| ^ 4 ≤
        Cconv * ‖a‖ ^ 2 * W.coefficientEnstrophy a ^ 3 * W.coefficientEnstrophy b ^ 2)
    {θ : ℝ} (hθ : 0 < θ) (m : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (b : EuclideanSpace ℝ (Fin m)) :
    |(inner ℝ (-(ν • W.stokesOperator m (c m s)) + W.convectionOperator m (c m s)) b : ℝ)|
      ≤ ((ν + 1) * θ * W.coefficientEnstrophy (c m s)
          + (ν / (4 * θ) + Cconv * (2 * ν * enstrophyBound) / (4 * θ ^ 3)))
        * Real.sqrt (W.coefficientEnstrophy b) := by
  have hE0 : 0 ≤ enstrophyBound := by simpa using henst m 0 le_rfl
  set K : ℝ := Cconv * (2 * ν * enstrophyBound) with hK
  have hKn : 0 ≤ K := by positivity
  set sqZ : ℝ := Real.sqrt (W.coefficientEnstrophy b) with hsqZ
  have hsqZn : 0 ≤ sqZ := Real.sqrt_nonneg _
  have hYn : 0 ≤ W.coefficientEnstrophy (c m s) := integral_nonneg fun x => by positivity
  -- viscous half
  have hvisc : |(inner ℝ (-(ν • W.stokesOperator m (c m s))) b : ℝ)|
      ≤ ν * (θ * W.coefficientEnstrophy (c m s) + 1 / (4 * θ)) * sqZ := by
    have h1 : |(inner ℝ (-(ν • W.stokesOperator m (c m s))) b : ℝ)|
        = ν * |(inner ℝ (W.stokesOperator m (c m s)) b : ℝ)| := by
      rw [inner_neg_left, inner_smul_left]
      simp [abs_mul, abs_of_pos hν]
    have h2 := abs_stokesOperator_inner_le W m (c m s) b
    have h3 : Real.sqrt (W.coefficientEnstrophy (c m s))
        ≤ θ * W.coefficientEnstrophy (c m s) + 1 / (4 * θ) :=
      sqrt_le_mul_add_inv θ _ hθ hYn
    rw [h1]
    refine (mul_le_mul_of_nonneg_left h2 hν.le).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hsqZn) hν.le
  -- convective half
  have hconvpt : |(inner ℝ (W.convectionOperator m (c m s)) b : ℝ)|
      ≤ (θ * W.coefficientEnstrophy (c m s) + K / (4 * θ ^ 3)) * sqZ := by
    refine abs_convectionOperator_inner_le_linear W hKn hθ (c m s) b ?_
    have hen : ‖c m s‖ ^ 2 ≤ 2 * ν * enstrophyBound :=
      coefficientFlow_norm_sq_le_of_enstrophyBound W hν c hc enstrophyBound henst m hs
    have h0 := hconv m (c m s) b
    have hZ2 : 0 ≤ W.coefficientEnstrophy b ^ 2 := by positivity
    have hY3 : 0 ≤ W.coefficientEnstrophy (c m s) ^ 3 := by positivity
    calc |(inner ℝ (W.convectionOperator m (c m s)) b : ℝ)| ^ 4
        ≤ Cconv * ‖c m s‖ ^ 2 * W.coefficientEnstrophy (c m s) ^ 3
            * W.coefficientEnstrophy b ^ 2 := h0
      _ ≤ K * W.coefficientEnstrophy (c m s) ^ 3 * W.coefficientEnstrophy b ^ 2 := by
          rw [hK]
          have : Cconv * ‖c m s‖ ^ 2 ≤ Cconv * (2 * ν * enstrophyBound) :=
            mul_le_mul_of_nonneg_left hen hCconv
          nlinarith [this, hY3, hZ2, mul_nonneg hY3 hZ2]
  have hsplit : (inner ℝ
      (-(ν • W.stokesOperator m (c m s)) + W.convectionOperator m (c m s)) b : ℝ) =
      (inner ℝ (-(ν • W.stokesOperator m (c m s))) b : ℝ)
        + (inner ℝ (W.convectionOperator m (c m s)) b : ℝ) := inner_add_left _ _ _
  calc |(inner ℝ
        (-(ν • W.stokesOperator m (c m s)) + W.convectionOperator m (c m s)) b : ℝ)|
      ≤ |(inner ℝ (-(ν • W.stokesOperator m (c m s))) b : ℝ)|
          + |(inner ℝ (W.convectionOperator m (c m s)) b : ℝ)| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ ν * (θ * W.coefficientEnstrophy (c m s) + 1 / (4 * θ)) * sqZ
          + (θ * W.coefficientEnstrophy (c m s) + K / (4 * θ ^ 3)) * sqZ :=
        add_le_add hvisc hconvpt
    _ = ((ν + 1) * θ * W.coefficientEnstrophy (c m s)
          + (ν / (4 * θ) + K / (4 * θ ^ 3))) * sqZ := by ring

/-- **The Aubin–Lions pointwise displacement estimate.**

For any two nonnegative times `p, q`,

  `‖c(p) − c(q)‖² ≤ Φ(θ, |p−q|) · (√Ω(c(p)) + √Ω(c(q)))`,
  `Φ(θ, ℓ) = (ν+1)θE + (ν/(4θ) + K/(4θ³))·ℓ`,  `K = C·2νE`,

with every constant uniform in `m` and in `W`.  Pair the ODE with the
displacement (`coefficientFlow_displacement_identity`), bound the viscous half
by the Stokes Cauchy–Schwarz and the convective half by
`abs_convectionOperator_inner_le_linear`, both linearized in the enstrophy
density by Young, and integrate: the enstrophy budget `henst` absorbs the
linear part uniformly and the remainder carries the factor `|p−q|`.

The two-parameter shape is what makes the *uniform in `m`* conclusion
possible: `θ` is chosen first, against `E` alone, and only then is `|p−q|`
made small. -/
theorem coefficientFlow_displacement_sq_le (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (enstrophyBound : ℝ)
    (henst : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound)
    {Cconv : ℝ} (hCconv : 0 ≤ Cconv)
    (hconv : ∀ (m : ℕ) (a b : EuclideanSpace ℝ (Fin m)),
      |(inner ℝ (W.convectionOperator m a) b : ℝ)| ^ 4 ≤
        Cconv * ‖a‖ ^ 2 * W.coefficientEnstrophy a ^ 3 * W.coefficientEnstrophy b ^ 2)
    {θ : ℝ} (hθ : 0 < θ) (m : ℕ) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ‖c m p - c m q‖ ^ 2 ≤
      ((ν + 1) * θ * enstrophyBound
        + (ν / (4 * θ)
            + Cconv * (2 * ν * enstrophyBound) / (4 * θ ^ 3)) * |p - q|)
      * (Real.sqrt (W.coefficientEnstrophy (c m p))
          + Real.sqrt (W.coefficientEnstrophy (c m q))) := by
  classical
  have hE0 : 0 ≤ enstrophyBound := by simpa using henst m 0 le_rfl
  set w : EuclideanSpace ℝ (Fin m) := c m p - c m q with hw
  set F : ℝ → EuclideanSpace ℝ (Fin m) := fun s =>
    -(ν • W.stokesOperator m (c m s)) + W.convectionOperator m (c m s) with hF
  set K : ℝ := Cconv * (2 * ν * enstrophyBound) with hK
  have hKn : 0 ≤ K := by positivity
  set A : ℝ := (ν + 1) * θ with hA
  set B : ℝ := ν / (4 * θ) + K / (4 * θ ^ 3) with hB
  have hAn : 0 ≤ A := by positivity
  have hBn : 0 ≤ B := by positivity
  set Z : ℝ := W.coefficientEnstrophy w with hZ
  have hZn : 0 ≤ Z := integral_nonneg fun x => by positivity
  set sqZ : ℝ := Real.sqrt Z with hsqZ
  have hsqZn : 0 ≤ sqZ := Real.sqrt_nonneg _
  -- (1) the pointwise integrand bound, linear in the enstrophy density
  have hpt : ∀ s : ℝ, 0 ≤ s →
      |(inner ℝ (F s) w : ℝ)| ≤ (A * W.coefficientEnstrophy (c m s) + B) * sqZ := by
    intro s hs
    have h := abs_projectedVectorField_inner_le W hν c hc enstrophyBound henst
      hCconv hconv hθ m hs w
    rw [hF, hA, hB, hK, hsqZ, hZ]
    exact h
  -- (2) integrate over the interval between `q` and `p`
  have hmin : (0:ℝ) ≤ min q p := le_min hq hp
  have huIoc : Set.uIoc q p = Set.Ioc (min q p) (max q p) := rfl
  have hsubIci : Set.Icc (min q p) (max q p) ⊆ Set.Ici (0:ℝ) :=
    fun s hs => le_trans hmin hs.1
  have hOmcontOn : ContinuousOn (fun s => W.coefficientEnstrophy (c m s))
      (Set.Icc (min q p) (max q p)) :=
    (coefficientFlow_enstrophy_continuousOn W c hc m).mono hsubIci
  have hFwcont : ContinuousOn (fun s => (inner ℝ (F s) w : ℝ))
      (Set.Icc (min q p) (max q p)) := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hmin hs.1
    have hcm : ContinuousWithinAt (c m) (Set.Icc (min q p) (max q p)) s :=
      ((hc m s hs0).continuousWithinAt).mono hsubIci
    have hA' : ContinuousWithinAt (fun r => W.stokesOperator m (c m r))
        (Set.Icc (min q p) (max q p)) s :=
      (W.stokesOperator m).continuous.continuousAt.comp_continuousWithinAt hcm
    have hB' : ContinuousWithinAt (fun r => W.convectionOperator m (c m r))
        (Set.Icc (min q p) (max q p)) s :=
      ((convectionOperator_contDiff W m).continuous).continuousAt.comp_continuousWithinAt hcm
    exact ((hA'.const_smul ν).neg.add hB').inner continuousWithinAt_const
  have hIntFw : IntegrableOn (fun s => |(inner ℝ (F s) w : ℝ)|) (Set.uIoc q p) := by
    rw [huIoc]
    exact ((hFwcont.abs).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hIntOm : IntegrableOn (fun s => W.coefficientEnstrophy (c m s)) (Set.uIoc q p) := by
    rw [huIoc]
    exact (hOmcontOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hIntMaj : IntegrableOn
      (fun s => (A * W.coefficientEnstrophy (c m s) + B) * sqZ) (Set.uIoc q p) := by
    have : (fun s => (A * W.coefficientEnstrophy (c m s) + B) * sqZ)
        = fun s => (A * sqZ) * W.coefficientEnstrophy (c m s) + B * sqZ := by
      funext s; ring
    rw [this]
    refine (hIntOm.const_mul _).add ?_
    rw [huIoc]
    exact ((continuousOn_const (s := Set.Icc (min q p) (max q p))
      (c := B * sqZ)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hvol : (volume (Set.uIoc q p)).toReal = |p - q| := by
    rw [Real.volume_uIoc, ENNReal.toReal_ofReal (abs_nonneg _)]
  -- the displacement identity, then absolute values, then the majorant
  have hid := coefficientFlow_displacement_identity W c hc m hp hq
  have habs : ‖w‖ ^ 2 ≤ ∫ s in Set.uIoc q p, |(inner ℝ (F s) w : ℝ)| := by
    have h0 : ‖w‖ ^ 2 = ∫ s in q..p, (inner ℝ (F s) w : ℝ) := hid
    have h1 := intervalIntegral.norm_integral_le_integral_norm_uIoc
      (f := fun s => (inner ℝ (F s) w : ℝ)) (a := q) (b := p) (μ := volume)
    simp only [Real.norm_eq_abs] at h1
    calc ‖w‖ ^ 2 = |‖w‖ ^ 2| := (abs_of_nonneg (by positivity)).symm
      _ = |∫ s in q..p, (inner ℝ (F s) w : ℝ)| := by rw [h0]
      _ ≤ ∫ s in Set.uIoc q p, |(inner ℝ (F s) w : ℝ)| := h1
  have hmaj : (∫ s in Set.uIoc q p, |(inner ℝ (F s) w : ℝ)|)
      ≤ ∫ s in Set.uIoc q p, (A * W.coefficientEnstrophy (c m s) + B) * sqZ :=
    setIntegral_mono_on hIntFw hIntMaj measurableSet_uIoc
      (fun s hs => hpt s (by rw [huIoc] at hs; exact le_trans hmin hs.1.le))
  have hcomp : (∫ s in Set.uIoc q p, (A * W.coefficientEnstrophy (c m s) + B) * sqZ)
      = (A * (∫ s in Set.uIoc q p, W.coefficientEnstrophy (c m s)) + B * |p - q|) * sqZ := by
    have hrw : (fun s => (A * W.coefficientEnstrophy (c m s) + B) * sqZ)
        = fun s => (A * sqZ) * W.coefficientEnstrophy (c m s) + B * sqZ := by
      funext s; ring
    have hIntC : IntegrableOn (fun _ : ℝ => B * sqZ) (Set.uIoc q p) := by
      rw [huIoc]
      exact ((continuousOn_const (s := Set.Icc (min q p) (max q p))
        (c := B * sqZ)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    rw [hrw, integral_add (hIntOm.const_mul _) hIntC,
      integral_const_mul, setIntegral_const, smul_eq_mul, measureReal_def, hvol]
    ring
  have hbudget : (∫ s in Set.uIoc q p, W.coefficientEnstrophy (c m s)) ≤ enstrophyBound := by
    have hmax : (0:ℝ) ≤ max q p := le_trans hmin (min_le_max)
    have hIntBig : IntegrableOn (fun s => W.coefficientEnstrophy (c m s))
        (Set.Ioc (0:ℝ) (max q p)) :=
      (((coefficientFlow_enstrophy_continuousOn W c hc m).mono
        (Set.Icc_subset_Ici_self)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hsub : Set.uIoc q p ⊆ Set.Ioc (0:ℝ) (max q p) := by
      rw [huIoc]
      exact Set.Ioc_subset_Ioc_left hmin
    calc (∫ s in Set.uIoc q p, W.coefficientEnstrophy (c m s))
        ≤ ∫ s in Set.Ioc (0:ℝ) (max q p), W.coefficientEnstrophy (c m s) :=
          setIntegral_mono_set hIntBig
            (Filter.Eventually.of_forall fun s => integral_nonneg fun x => by positivity)
            (HasSubset.Subset.eventuallyLE hsub)
      _ ≤ enstrophyBound := henst m _ hmax
  -- (3) assemble
  have hPhi : (0:ℝ) ≤ A * enstrophyBound + B * |p - q| := by positivity
  have hchain : ‖w‖ ^ 2 ≤ (A * enstrophyBound + B * |p - q|) * sqZ := by
    refine le_trans (le_trans habs hmaj) ?_
    rw [hcomp]
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [hbudget, hAn]) hsqZn
  have htri : sqZ ≤ Real.sqrt (W.coefficientEnstrophy (c m p))
      + Real.sqrt (W.coefficientEnstrophy (c m q)) := by
    rw [hsqZ, hZ, hw]
    exact sqrt_coefficientEnstrophy_sub_le W m (c m p) (c m q)
  calc ‖c m p - c m q‖ ^ 2 = ‖w‖ ^ 2 := by rw [hw]
    _ ≤ (A * enstrophyBound + B * |p - q|) * sqZ := hchain
    _ ≤ (A * enstrophyBound + B * |p - q|) *
        (Real.sqrt (W.coefficientEnstrophy (c m p))
          + Real.sqrt (W.coefficientEnstrophy (c m q))) :=
        mul_le_mul_of_nonneg_left htri hPhi
    _ = ((ν + 1) * θ * enstrophyBound
          + (ν / (4 * θ) + Cconv * (2 * ν * enstrophyBound) / (4 * θ ^ 3)) * |p - q|)
        * (Real.sqrt (W.coefficientEnstrophy (c m p))
            + Real.sqrt (W.coefficientEnstrophy (c m q))) := by rw [hA, hB, hK]

/-- `√x ≤ x + 1` for `x ≥ 0`; the slack is `(√x − 1)² ≥ 0` plus `√x ≥ 0`. -/
theorem sqrt_le_add_one (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ≤ x + 1 := by
  have he : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith [sq_nonneg (Real.sqrt x - 1), he, hnn]

/-- **The time-integrated displacement bound on a forward window.**

On any window `[a, T]` with `0 ≤ a` and `0 ≤ a + h` — so that both `t` and
`t + h` stay in the forward half-line — the displacement integral obeys

  `∫_a^T ‖c(t+h) − c(t)‖² dt ≤ Φ(θ, |h|) · (2E + 2T)`,

with `Φ(θ, ℓ) = (ν+1)θE + (ν/(4θ) + K/(4θ³))ℓ` and every constant uniform in
`m` and `W`.  The outer factor is bounded by `√Ω ≤ Ω + 1` together with the
budget, once on the window and once on its translate by `h`. -/
theorem coefficientFlow_shifted_displacement_integral_le (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (enstrophyBound : ℝ)
    (henst : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound)
    {Cconv : ℝ} (hCconv : 0 ≤ Cconv)
    (hconv : ∀ (m : ℕ) (a b : EuclideanSpace ℝ (Fin m)),
      |(inner ℝ (W.convectionOperator m a) b : ℝ)| ^ 4 ≤
        Cconv * ‖a‖ ^ 2 * W.coefficientEnstrophy a ^ 3 * W.coefficientEnstrophy b ^ 2)
    {θ : ℝ} (hθ : 0 < θ) (m : ℕ)
    {a T h : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (hah : 0 ≤ a + h) :
    (∫ t in a..T, ‖c m (t + h) - c m t‖ ^ 2) ≤
      ((ν + 1) * θ * enstrophyBound
        + (ν / (4 * θ)
            + Cconv * (2 * ν * enstrophyBound) / (4 * θ ^ 3)) * |h|)
      * (2 * enstrophyBound + 2 * T) := by
  classical
  have hE0 : 0 ≤ enstrophyBound := by simpa using henst m 0 le_rfl
  have hT0 : 0 ≤ T := le_trans ha haT
  have hTh : 0 ≤ T + h := by linarith
  set Φ : ℝ := (ν + 1) * θ * enstrophyBound
      + (ν / (4 * θ) + Cconv * (2 * ν * enstrophyBound) / (4 * θ ^ 3)) * |h| with hΦ
  have hΦn : 0 ≤ Φ := by rw [hΦ]; positivity
  have hOm : ∀ s : ℝ, 0 ≤ W.coefficientEnstrophy (c m s) :=
    fun s => integral_nonneg fun x => by positivity
  have hOmcont := coefficientFlow_enstrophy_continuousOn W c hc m
  -- continuity of the pieces on `[a, T]` and on its translate
  have hcOn : ContinuousOn (c m) (Set.Ici (0:ℝ)) := fun s hs => (hc m s hs).continuousWithinAt
  have hsubIci : Set.Icc a T ⊆ Set.Ici (0:ℝ) := fun r hr => le_trans ha hr.1
  have hmaps : Set.MapsTo (fun r : ℝ => r + h) (Set.Icc a T) (Set.Ici (0:ℝ)) := by
    intro r hr
    simp only [Set.mem_Ici]
    have h1 := hr.1
    linarith
  have hshiftC : ContinuousOn (fun r : ℝ => c m (r + h)) (Set.Icc a T) :=
    hcOn.comp (continuous_id.add continuous_const).continuousOn hmaps
  have hbaseC : ContinuousOn (c m) (Set.Icc a T) := hcOn.mono hsubIci
  have hdispCont : ContinuousOn (fun t => ‖c m (t + h) - c m t‖ ^ 2) (Set.Icc a T) :=
    ((hshiftC.sub hbaseC).norm).pow 2
  have hOmShiftC : ContinuousOn (fun r : ℝ => W.coefficientEnstrophy (c m (r + h)))
      (Set.Icc a T) :=
    hOmcont.comp (continuous_id.add continuous_const).continuousOn hmaps
  have hOmBaseC : ContinuousOn (fun r => W.coefficientEnstrophy (c m r)) (Set.Icc a T) :=
    hOmcont.mono hsubIci
  have hsqrtShiftCont : ContinuousOn
      (fun t => Real.sqrt (W.coefficientEnstrophy (c m (t + h)))
        + Real.sqrt (W.coefficientEnstrophy (c m t))) (Set.Icc a T) :=
    (Real.continuous_sqrt.comp_continuousOn hOmShiftC).add
      (Real.continuous_sqrt.comp_continuousOn hOmBaseC)
  have hint1 : IntervalIntegrable (fun t => ‖c m (t + h) - c m t‖ ^ 2) volume a T := by
    apply ContinuousOn.intervalIntegrable; rwa [Set.uIcc_of_le haT]
  have hint2 : IntervalIntegrable
      (fun t => Φ * (Real.sqrt (W.coefficientEnstrophy (c m (t + h)))
        + Real.sqrt (W.coefficientEnstrophy (c m t)))) volume a T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le haT]
    exact continuousOn_const.mul hsqrtShiftCont
  -- (1) the pointwise displacement estimate on the window
  have hstep1 : (∫ t in a..T, ‖c m (t + h) - c m t‖ ^ 2)
      ≤ ∫ t in a..T, Φ * (Real.sqrt (W.coefficientEnstrophy (c m (t + h)))
          + Real.sqrt (W.coefficientEnstrophy (c m t))) := by
    refine intervalIntegral.integral_mono_on haT hint1 hint2 ?_
    intro t ht
    have ht0 : (0:ℝ) ≤ t := le_trans ha ht.1
    have hth : (0:ℝ) ≤ t + h := by
      have : a + h ≤ t + h := by linarith [ht.1]
      linarith
    have hbase := coefficientFlow_displacement_sq_le W hν c hc enstrophyBound henst
      hCconv hconv hθ m hth ht0
    have habs : |t + h - t| = |h| := by ring_nf
    rw [habs] at hbase
    exact hbase
  -- (2) the outer factor: `√Ω ≤ Ω + 1`, twice, against the budget
  have hbudgetBase : (∫ t in a..T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound := by
    rw [intervalIntegral.integral_of_le haT]
    calc (∫ t in Set.Ioc a T, W.coefficientEnstrophy (c m t))
        ≤ ∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m t) := by
          refine setIntegral_mono_set ?_ (Filter.Eventually.of_forall fun s => hOm s)
            (HasSubset.Subset.eventuallyLE (Set.Ioc_subset_Ioc_left ha))
          exact (((hOmcont.mono Set.Icc_subset_Ici_self).integrableOn_Icc).mono_set
            Set.Ioc_subset_Icc_self)
      _ ≤ enstrophyBound := henst m T hT0
  have hbudgetShift : (∫ t in a..T, W.coefficientEnstrophy (c m (t + h))) ≤ enstrophyBound := by
    rw [intervalIntegral.integral_comp_add_right
      (f := fun s => W.coefficientEnstrophy (c m s)) h,
      intervalIntegral.integral_of_le (by linarith : a + h ≤ T + h)]
    calc (∫ t in Set.Ioc (a + h) (T + h), W.coefficientEnstrophy (c m t))
        ≤ ∫ t in Set.Ioc (0:ℝ) (T + h), W.coefficientEnstrophy (c m t) := by
          refine setIntegral_mono_set ?_ (Filter.Eventually.of_forall fun s => hOm s)
            (HasSubset.Subset.eventuallyLE (Set.Ioc_subset_Ioc_left hah))
          exact (((hOmcont.mono Set.Icc_subset_Ici_self).integrableOn_Icc).mono_set
            Set.Ioc_subset_Icc_self)
      _ ≤ enstrophyBound := henst m (T + h) hTh
  -- (3) `√x ≤ x + 1`, then linearity
  have hiA : IntervalIntegrable (fun t => W.coefficientEnstrophy (c m (t + h))) volume a T := by
    apply ContinuousOn.intervalIntegrable; rwa [Set.uIcc_of_le haT]
  have hiB : IntervalIntegrable (fun t => W.coefficientEnstrophy (c m t)) volume a T := by
    apply ContinuousOn.intervalIntegrable; rwa [Set.uIcc_of_le haT]
  have hint3 : IntervalIntegrable
      (fun t => Φ * ((W.coefficientEnstrophy (c m (t + h)) + 1)
        + (W.coefficientEnstrophy (c m t) + 1))) volume a T :=
    (((hiA.add (intervalIntegrable_const (c := (1:ℝ)))).add
      (hiB.add (intervalIntegrable_const (c := (1:ℝ)))))).const_mul Φ
  have hstep2 : (∫ t in a..T, Φ * (Real.sqrt (W.coefficientEnstrophy (c m (t + h)))
          + Real.sqrt (W.coefficientEnstrophy (c m t))))
      ≤ ∫ t in a..T, Φ * ((W.coefficientEnstrophy (c m (t + h)) + 1)
          + (W.coefficientEnstrophy (c m t) + 1)) := by
    refine intervalIntegral.integral_mono_on haT hint2 hint3 ?_
    intro t _
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hΦn
    · exact sqrt_le_add_one _ (hOm _)
    · exact sqrt_le_add_one _ (hOm _)
  have hval : (∫ t in a..T, Φ * ((W.coefficientEnstrophy (c m (t + h)) + 1)
        + (W.coefficientEnstrophy (c m t) + 1)))
      = Φ * (∫ t in a..T, W.coefficientEnstrophy (c m (t + h)))
        + Φ * (∫ t in a..T, W.coefficientEnstrophy (c m t)) + 2 * Φ * (T - a) := by
    rw [show (fun t => Φ * ((W.coefficientEnstrophy (c m (t + h)) + 1)
          + (W.coefficientEnstrophy (c m t) + 1)))
        = fun t => (Φ * W.coefficientEnstrophy (c m (t + h))
            + Φ * W.coefficientEnstrophy (c m t)) + 2 * Φ from by funext t; ring]
    rw [intervalIntegral.integral_add ((hiA.const_mul Φ).add (hiB.const_mul Φ))
        (intervalIntegrable_const),
      intervalIntegral.integral_add (hiA.const_mul Φ) (hiB.const_mul Φ),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hfinal : Φ * (∫ t in a..T, W.coefficientEnstrophy (c m (t + h)))
      + Φ * (∫ t in a..T, W.coefficientEnstrophy (c m t)) + 2 * Φ * (T - a)
      ≤ Φ * (2 * enstrophyBound + 2 * T) := by
    have h1 : Φ * (∫ t in a..T, W.coefficientEnstrophy (c m (t + h)))
        ≤ Φ * enstrophyBound := mul_le_mul_of_nonneg_left hbudgetShift hΦn
    have h2 : Φ * (∫ t in a..T, W.coefficientEnstrophy (c m t))
        ≤ Φ * enstrophyBound := mul_le_mul_of_nonneg_left hbudgetBase hΦn
    have h3 : 2 * Φ * (T - a) ≤ 2 * Φ * T := by nlinarith [hΦn, ha]
    nlinarith [h1, h2, h3]
  calc (∫ t in a..T, ‖c m (t + h) - c m t‖ ^ 2)
      ≤ ∫ t in a..T, Φ * (Real.sqrt (W.coefficientEnstrophy (c m (t + h)))
          + Real.sqrt (W.coefficientEnstrophy (c m t))) := hstep1
    _ ≤ ∫ t in a..T, Φ * ((W.coefficientEnstrophy (c m (t + h)) + 1)
          + (W.coefficientEnstrophy (c m t) + 1)) := hstep2
    _ = Φ * (∫ t in a..T, W.coefficientEnstrophy (c m (t + h)))
        + Φ * (∫ t in a..T, W.coefficientEnstrophy (c m t)) + 2 * Φ * (T - a) := hval
    _ ≤ Φ * (2 * enstrophyBound + 2 * T) := hfinal

/-- **Aubin–Lions time equicontinuity for the Galerkin coefficient flow, given
the convective estimate.**

This is `galerkinCoefficientFlow_timeEquicontinuous` with the convective
estimate carried as an explicit hypothesis, because
`ConvectionLadyzhenskaya` — where that estimate is certified — is strictly
downstream of this file.

`∃ δ` stands *outside* `∀ m`, which is the whole content: `θ` is chosen first
against the enstrophy budget `E` and the horizon `T` alone, and only then is
`δ` chosen, so no constant anywhere in the argument depends on the mode count.

Negative `h` is genuinely different and is handled by a split: on
`t ≤ |h|` the clamp `forwardExtend` pins `t + h` to `0`, the enstrophy at time
`0` is *not* uniformly bounded in `m`, and the fine estimate is unavailable —
so that sliver is absorbed by the crude bound `‖c(p) − c(q)‖² ≤ 4·2νE`, which
costs `O(|h|)` and is uniform in `m` precisely because of
`coefficientFlow_norm_sq_le_of_enstrophyBound`. -/
theorem galerkinCoefficientFlow_timeEquicontinuous_of_convectionEstimate
    (W : GalerkinBasisFamily) {ν : ℝ} (hν : 0 < ν)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (enstrophyBound : ℝ)
    (henst : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      (∫ t in Set.Ioc (0:ℝ) T, W.coefficientEnstrophy (c m t)) ≤ enstrophyBound)
    {Cconv : ℝ} (hCconv : 0 ≤ Cconv)
    (hconv : ∀ (m : ℕ) (a b : EuclideanSpace ℝ (Fin m)),
      |(inner ℝ (W.convectionOperator m a) b : ℝ)| ^ 4 ≤
        Cconv * ‖a‖ ^ 2 * W.coefficientEnstrophy a ^ 3 * W.coefficientEnstrophy b ^ 2) :
    ∀ T ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ) (h : ℝ), |h| < δ →
      (∫ t in Set.Ioc (0:ℝ) T,
        ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2) ≤ ε := by
  classical
  intro T ε hε
  have hE0 : 0 ≤ enstrophyBound := by simpa using henst 0 0 le_rfl
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨1, one_pos, fun m h _ => ?_⟩
    rw [show Set.Ioc (0:ℝ) T = ∅ from Set.Ioc_eq_empty (by linarith)]
    simpa using hε.le
  -- the constants, chosen in the order that makes them independent of `m`
  set M2 : ℝ := 2 * ν * enstrophyBound with hM2
  have hM2n : 0 ≤ M2 := by rw [hM2]; positivity
  set G : ℝ := 2 * enstrophyBound + 2 * T with hG
  have hGpos : 0 < G := by rw [hG]; linarith
  set θ : ℝ := ε / (2 * G * ((ν + 1) * enstrophyBound + 1)) with hθdef
  have hden : 0 < 2 * G * ((ν + 1) * enstrophyBound + 1) := by positivity
  have hθ : 0 < θ := by rw [hθdef]; positivity
  set Bc : ℝ := ν / (4 * θ) + Cconv * M2 / (4 * θ ^ 3) with hBc
  have hBcn : 0 ≤ Bc := by rw [hBc]; positivity
  set δ : ℝ := min 1 (ε / (2 * (Bc * G + 4 * M2 + 1))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min one_pos (by positivity)
  -- the `θ`-half of the budget
  have hθhalf : (ν + 1) * θ * enstrophyBound * G ≤ ε / 2 := by
    have hθD : θ * (2 * G * ((ν + 1) * enstrophyBound + 1)) = ε := by
      rw [hθdef]; field_simp
    nlinarith [hθD, mul_nonneg hGpos.le hθ.le]
  refine ⟨δ, hδpos, fun m h hh => ?_⟩
  have hhabs : (0:ℝ) ≤ |h| := abs_nonneg h
  have hh1 : |h| < 1 := lt_of_lt_of_le hh (by rw [hδdef]; exact min_le_left _ _)
  have hT0 : (0:ℝ) ≤ T := hT.le
  -- the uniform energy ceiling, and the crude displacement bound it yields
  have hnormsq : ∀ s : ℝ, ‖forwardExtend (c m) s‖ ^ 2 ≤ M2 := by
    intro s
    have := coefficientFlow_norm_sq_le_of_enstrophyBound W hν c hc enstrophyBound henst m
      (t := max s 0) (le_max_right s 0)
    simpa [forwardExtend, hM2] using this
  have hcrude : ∀ s r : ℝ,
      ‖forwardExtend (c m) s - forwardExtend (c m) r‖ ^ 2 ≤ 4 * M2 := by
    intro s r
    have h1 := hnormsq s
    have h2 := hnormsq r
    have htri := norm_sub_le (forwardExtend (c m) s) (forwardExtend (c m) r)
    have hsq : ‖forwardExtend (c m) s - forwardExtend (c m) r‖ ^ 2
        ≤ (‖forwardExtend (c m) s‖ + ‖forwardExtend (c m) r‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsq, h1, h2,
      sq_nonneg (‖forwardExtend (c m) s‖ - ‖forwardExtend (c m) r‖)]
  -- continuity of the forward extension
  have hcOn : ContinuousOn (c m) (Set.Ici (0:ℝ)) := fun s hs => (hc m s hs).continuousWithinAt
  have hfe : Continuous (fun t : ℝ => forwardExtend (c m) t) := by
    have : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
    exact hcOn.comp_continuous this (fun t => le_max_right t 0)
  have hdisp : Continuous
      (fun t : ℝ => ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2) :=
    (((hfe.comp (continuous_id.add continuous_const)).sub hfe).norm).pow 2
  -- the split point
  set a : ℝ := max 0 (min T (-h)) with hadef
  have ha0 : (0:ℝ) ≤ a := le_max_left _ _
  have haT : a ≤ T := max_le hT0 (min_le_left _ _)
  have hah : a ≤ |h| := max_le hhabs (le_trans (min_le_right _ _) (neg_le_abs h))
  have hint0a : IntervalIntegrable
      (fun t : ℝ => ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2)
      volume 0 a := hdisp.intervalIntegrable _ _
  have hintaT : IntervalIntegrable
      (fun t : ℝ => ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2)
      volume a T := hdisp.intervalIntegrable _ _
  -- region 1: the clamped sliver, absorbed crudely
  have hreg1 : (∫ t in (0:ℝ)..a,
      ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2) ≤ 4 * M2 * |h| := by
    calc (∫ t in (0:ℝ)..a, ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2)
        ≤ ∫ _t in (0:ℝ)..a, 4 * M2 :=
          intervalIntegral.integral_mono_on ha0 hint0a intervalIntegrable_const
            (fun t _ => hcrude _ _)
      _ = 4 * M2 * a := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ 4 * M2 * |h| := by nlinarith [hM2n, hah]
  -- region 2: the fine estimate, where the clamp is inactive
  have hreg2 : (∫ t in a..T,
      ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2)
      ≤ ((ν + 1) * θ * enstrophyBound + Bc * |h|) * G := by
    have hnn : 0 ≤ ((ν + 1) * θ * enstrophyBound + Bc * |h|) * G := by positivity
    rcases eq_or_lt_of_le haT with heq | hlt
    · rw [← heq, intervalIntegral.integral_same]; exact hnn
    · -- on `a < T` the clamp is inactive: `0 ≤ a + h`
      have hahn : (0:ℝ) ≤ a + h := by
        rcases le_or_gt (-h) 0 with hh0 | hh0
        · have hmin : min T (-h) ≤ 0 := le_trans (min_le_right _ _) hh0
          have : a = 0 := by rw [hadef, max_eq_left hmin]
          rw [this]; linarith
        · rcases le_or_gt T (-h) with hTh | hTh
          · exfalso
            have : a = T := by rw [hadef, min_eq_left hTh, max_eq_right hT0]
            linarith
          · have : a = -h := by
              rw [hadef, min_eq_right hTh.le, max_eq_right hh0.le]
            rw [this]; linarith
      have hcongr : (∫ t in a..T,
          ‖forwardExtend (c m) (t + h) - forwardExtend (c m) t‖ ^ 2)
          = ∫ t in a..T, ‖c m (t + h) - c m t‖ ^ 2 := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        rw [Set.uIcc_of_le haT] at ht
        have ht0 : (0:ℝ) ≤ t := le_trans ha0 ht.1
        have hth : (0:ℝ) ≤ t + h := by linarith [ht.1]
        simp only [forwardExtend, max_eq_left ht0, max_eq_left hth]
      rw [hcongr]
      have := coefficientFlow_shifted_displacement_integral_le W hν c hc enstrophyBound
        henst hCconv hconv hθ m ha0 haT hahn
      calc (∫ t in a..T, ‖c m (t + h) - c m t‖ ^ 2)
          ≤ ((ν + 1) * θ * enstrophyBound
              + (ν / (4 * θ) + Cconv * (2 * ν * enstrophyBound) / (4 * θ ^ 3)) * |h|)
            * (2 * enstrophyBound + 2 * T) := this
        _ = ((ν + 1) * θ * enstrophyBound + Bc * |h|) * G := by rw [hBc, hG, hM2]
  -- the `δ`-half of the budget
  have hδhalf : 4 * M2 * |h| + Bc * |h| * G ≤ ε / 2 := by
    set q : ℝ := ε / (2 * (Bc * G + 4 * M2 + 1)) with hq
    have hqn : 0 ≤ q := by rw [hq]; positivity
    have hqD : q * (2 * (Bc * G + 4 * M2 + 1)) = ε := by
      rw [hq]; field_simp
    have hd2 : |h| ≤ q :=
      le_of_lt (lt_of_lt_of_le hh (by rw [hδdef]; exact min_le_right _ _))
    have hSn : 0 ≤ 4 * M2 + Bc * G := by positivity
    have hkey : (4 * M2 + Bc * G) * |h| ≤ (4 * M2 + Bc * G) * q :=
      mul_le_mul_of_nonneg_left hd2 hSn
    nlinarith [hkey, hqD, hqn]
  -- assemble
  rw [← intervalIntegral.integral_of_le hT0,
    ← intervalIntegral.integral_add_adjacent_intervals hint0a hintaT]
  nlinarith [hreg1, hreg2, hθhalf, hδhalf, hGpos.le, hBcn, hhabs]

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

/-- The concrete nonlinear residual caused only by replacing a test `φ` by
its modal projection.  It is linear in the test error, while retaining the
actual (possibly varying) velocity in the two nonlinear slots. -/
noncomputable def GalerkinBasisFamily.convectionTestProjectionCommutator
    (W : GalerkinBasisFamily) (m : ℕ)
    (u φ : SchwartzVelocity) : SchwartzVelocity :=
  convectionSchwartzBilin u (W.proj m φ - φ)

/-- Exact splitting of projected-test convection into the fixed-test term and
the nonlinear test-projection commutator. -/
theorem convectionTestProjection_pairing
    (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (φ : SchwartzVelocity) :
    schwartzL2Inner (W.coefficientField a)
        (convectionSchwartzBilin (W.coefficientField a) (W.proj m φ)) =
      schwartzL2Inner (W.coefficientField a)
          (convectionSchwartzBilin (W.coefficientField a) φ) +
        schwartzL2Inner (W.coefficientField a)
          (W.convectionTestProjectionCommutator m
            (W.coefficientField a) φ) := by
  rw [show W.proj m φ = φ + (W.proj m φ - φ) by abel,
    convectionSchwartzBilin_add_right, schwartzL2Inner_add_right]
  rfl

/-- An `L²`-small convection commutator gives a small scalar residual against
uniformly `L²`-bounded modal fields. -/
theorem convectionTestProjection_pairing_tendsto_zero_of_L2
    (W : GalerkinBasisFamily)
    (a : ∀ m : ℕ, EuclideanSpace ℝ (Fin m)) (φ : SchwartzVelocity)
    (C : ℝ)
    (hbound : ∀ m, ‖toL2 (W.coefficientField (a m))‖ ≤ C)
    (hcommL2 : Filter.Tendsto
      (fun m => ‖toL2 (W.convectionTestProjectionCommutator m
        (W.coefficientField (a m)) φ)‖) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => schwartzL2Inner (W.coefficientField (a m))
        (W.convectionTestProjectionCommutator m
          (W.coefficientField (a m)) φ))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm
  · intro m
    calc
      ‖schwartzL2Inner (W.coefficientField (a m))
          (W.convectionTestProjectionCommutator m
            (W.coefficientField (a m)) φ)‖ =
          |schwartzL2Inner (W.coefficientField (a m))
            (W.convectionTestProjectionCommutator m
              (W.coefficientField (a m)) φ)| := Real.norm_eq_abs _
      _ ≤ ‖toL2 (W.coefficientField (a m))‖ *
          ‖toL2 (W.convectionTestProjectionCommutator m
            (W.coefficientField (a m)) φ)‖ :=
        abs_schwartzL2Inner_le _ _
      _ ≤ C * ‖toL2 (W.convectionTestProjectionCommutator m
          (W.coefficientField (a m)) φ)‖ :=
        mul_le_mul_of_nonneg_right (hbound m) (norm_nonneg _)
  · simpa using (tendsto_const_nhds.mul hcommL2 :
      Filter.Tendsto
        (fun m => C * ‖toL2 (W.convectionTestProjectionCommutator m
          (W.coefficientField (a m)) φ)‖) Filter.atTop (nhds (C * 0)))

/-- Conditional nonlinear limit passage consumed by the weak equation.  It
requires only convergence of the fixed-test scalar pairing and vanishing of
the one explicit test-projection residual, not the all-test weak-form crown. -/
theorem coefficientField_convectionTestProjection_pairing_tendsto
    (W : GalerkinBasisFamily)
    (a : ∀ m : ℕ, EuclideanSpace ℝ (Fin m)) (φ : SchwartzVelocity) (L : ℝ)
    (hfixed : Filter.Tendsto
      (fun m => schwartzL2Inner (W.coefficientField (a m))
        (convectionSchwartzBilin (W.coefficientField (a m)) φ))
      Filter.atTop (nhds L))
    (hcomm : Filter.Tendsto
      (fun m => schwartzL2Inner (W.coefficientField (a m))
        (W.convectionTestProjectionCommutator m
          (W.coefficientField (a m)) φ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => schwartzL2Inner (W.coefficientField (a m))
        (convectionSchwartzBilin (W.coefficientField (a m)) (W.proj m φ)))
      Filter.atTop (nhds L) := by
  have hadd := hfixed.add hcomm
  have heq : (fun m => schwartzL2Inner (W.coefficientField (a m))
      (convectionSchwartzBilin (W.coefficientField (a m)) (W.proj m φ))) =
      fun m => schwartzL2Inner (W.coefficientField (a m))
          (convectionSchwartzBilin (W.coefficientField (a m)) φ) +
        schwartzL2Inner (W.coefficientField (a m))
          (W.convectionTestProjectionCommutator m
            (W.coefficientField (a m)) φ) := by
    funext m
    exact convectionTestProjection_pairing W (a m) φ
  rw [heq]
  simpa using hadd

/-- Stability estimate for the quadratic convection pairing against one fixed
Schwartz test.  It is the polarization identity followed by two Hilbert-space
Cauchy--Schwarz bounds. -/
theorem fixedTestConvection_pairing_sub_bound
    (u v φ : SchwartzVelocity) :
    |schwartzL2Inner u (convectionSchwartzBilin u φ) -
        schwartzL2Inner v (convectionSchwartzBilin v φ)| ≤
      ‖toL2 (u - v)‖ * ‖toL2 (convectionSchwartzBilin u φ)‖ +
        ‖toL2 v‖ * ‖toL2 (convectionSchwartzBilin (u - v) φ)‖ := by
  have hconv : convectionSchwartzBilin (u - v) φ =
      convectionSchwartzBilin u φ - convectionSchwartzBilin v φ := by
    rw [sub_eq_add_neg, convectionSchwartzBilin_add_left]
    have hneg : convectionSchwartzBilin (-v) φ =
        -convectionSchwartzBilin v φ := by
      rw [show -v = (-1 : ℝ) • v by simp,
        convectionSchwartzBilin_smul_left]
      simp
    rw [hneg]
    rfl
  have hsub_right (f g h : SchwartzVelocity) :
      schwartzL2Inner f (g - h) =
        schwartzL2Inner f g - schwartzL2Inner f h := by
    rw [schwartzL2Inner_comm, schwartzL2Inner_sub_left,
      schwartzL2Inner_comm g f, schwartzL2Inner_comm h f]
  have hsplit : schwartzL2Inner u (convectionSchwartzBilin u φ) -
        schwartzL2Inner v (convectionSchwartzBilin v φ) =
      schwartzL2Inner (u - v) (convectionSchwartzBilin u φ) +
        schwartzL2Inner v (convectionSchwartzBilin (u - v) φ) := by
    rw [hconv, schwartzL2Inner_sub_left, hsub_right]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_schwartzL2Inner_le (u - v) (convectionSchwartzBilin u φ))
    (abs_schwartzL2Inner_le v (convectionSchwartzBilin (u - v) φ)))

/-- Strong-`L²` convergence and strong convergence after the fixed-test
transport operator imply convergence of the quadratic convection pairing.
The uniform bound is only on the transformed approximants and is exactly what
the stability estimate consumes. -/
theorem fixedTestConvection_pairing_tendsto_of_strongL2
    (u : ℕ → SchwartzVelocity) (v φ : SchwartzVelocity) (C : ℝ)
    (hbound : ∀ n, ‖toL2 (convectionSchwartzBilin (u n) φ)‖ ≤ C)
    (hu : Filter.Tendsto (fun n => ‖toL2 (u n - v)‖)
      Filter.atTop (nhds 0))
    (htransport : Filter.Tendsto
      (fun n => ‖toL2 (convectionSchwartzBilin (u n - v) φ)‖)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => schwartzL2Inner (u n) (convectionSchwartzBilin (u n) φ))
      Filter.atTop (nhds (schwartzL2Inner v (convectionSchwartzBilin v φ))) := by
  have herr : Filter.Tendsto
      (fun n => schwartzL2Inner (u n) (convectionSchwartzBilin (u n) φ) -
        schwartzL2Inner v (convectionSchwartzBilin v φ))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (a := fun n =>
      ‖toL2 (u n - v)‖ * C +
        ‖toL2 v‖ * ‖toL2 (convectionSchwartzBilin (u n - v) φ)‖) ?_ ?_
    · intro n
      rw [Real.norm_eq_abs]
      refine (fixedTestConvection_pairing_sub_bound (u n) v φ).trans ?_
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _)) le_rfl
    · have hfirst := hu.mul_const C
      have hsecond : Filter.Tendsto
          (fun n => ‖toL2 v‖ *
            ‖toL2 (convectionSchwartzBilin (u n - v) φ)‖)
          Filter.atTop (nhds 0) := by
        simpa using (tendsto_const_nhds.mul htransport :
          Filter.Tendsto
            (fun n => ‖toL2 v‖ *
              ‖toL2 (convectionSchwartzBilin (u n - v) φ)‖)
            Filter.atTop (nhds (‖toL2 v‖ * 0)))
      simpa using hfirst.add hsecond
  have hadd := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => schwartzL2Inner v (convectionSchwartzBilin v φ))
      Filter.atTop (nhds (schwartzL2Inner v (convectionSchwartzBilin v φ)))).add herr
  have heq : (fun n => schwartzL2Inner (u n)
      (convectionSchwartzBilin (u n) φ)) = fun n =>
      schwartzL2Inner v (convectionSchwartzBilin v φ) +
        (schwartzL2Inner (u n) (convectionSchwartzBilin (u n) φ) -
          schwartzL2Inner v (convectionSchwartzBilin v φ)) := by
    funext n
    ring
  rw [heq]
  simpa using hadd

/-- Strong-`L²` fixed-test stability wired to the projected-test residual
split.  The final hypothesis is only the one scalar projection residual from
`convectionTestProjection_pairing`, not weak consistency for all tests. -/
theorem coefficientField_convectionTestProjection_pairing_tendsto_of_strongL2
    (W : GalerkinBasisFamily)
    (a : ∀ m : ℕ, EuclideanSpace ℝ (Fin m))
    (v φ : SchwartzVelocity) (C : ℝ)
    (hbound : ∀ m, ‖toL2
      (convectionSchwartzBilin (W.coefficientField (a m)) φ)‖ ≤ C)
    (hu : Filter.Tendsto
      (fun m => ‖toL2 (W.coefficientField (a m) - v)‖)
      Filter.atTop (nhds 0))
    (htransport : Filter.Tendsto
      (fun m => ‖toL2
        (convectionSchwartzBilin (W.coefficientField (a m) - v) φ)‖)
      Filter.atTop (nhds 0))
    (hcomm : Filter.Tendsto
      (fun m => schwartzL2Inner (W.coefficientField (a m))
        (W.convectionTestProjectionCommutator m
          (W.coefficientField (a m)) φ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => schwartzL2Inner (W.coefficientField (a m))
        (convectionSchwartzBilin (W.coefficientField (a m)) (W.proj m φ)))
      Filter.atTop
        (nhds (schwartzL2Inner v (convectionSchwartzBilin v φ))) := by
  apply coefficientField_convectionTestProjection_pairing_tendsto W a φ
    (schwartzL2Inner v (convectionSchwartzBilin v φ))
  · exact fixedTestConvection_pairing_tendsto_of_strongL2
      (fun m => W.coefficientField (a m)) v φ C hbound hu htransport
  · exact hcomm

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

/-- The projected-test equation with both projection effects isolated.  Its
main integrand uses the unprojected physical test; the only remaining terms
are the explicit Laplacian and convection projection commutators. -/
theorem modalFlow_projectedTest_splitResidualWeakEquation
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
                (φ.field t)) +
          ν * schwartzL2Inner (W.coefficientField (c m t))
            (W.laplacianProjectionCommutator m (φ.field t)) +
          schwartzL2Inner (W.coefficientField (c m t))
            (W.convectionTestProjectionCommutator m
              (W.coefficientField (c m t)) (φ.field t))) +
        schwartzL2Inner (W.coefficientField (c m 0)) (φ.field 0) = 0 := by
  obtain ⟨T, hT, heq⟩ :=
    modalFlow_projectedTest_splitLaplacianWeakEquation W ν c hc φ φ' m
      hmodal_deriv hmodal_deriv_cont
  refine ⟨T, hT, ?_⟩
  have hintegral :
      (∫ t in (0 : ℝ)..T,
          schwartzL2Inner (W.coefficientField (c m t)) (φ' t) +
          schwartzL2Inner (W.coefficientField (c m t))
            (ν • laplacianSchwartz (φ.field t) +
              convectionSchwartzBilin (W.coefficientField (c m t))
                (W.proj m (φ.field t))) +
          ν * schwartzL2Inner (W.coefficientField (c m t))
            (W.laplacianProjectionCommutator m (φ.field t))) =
        ∫ t in (0 : ℝ)..T,
          schwartzL2Inner (W.coefficientField (c m t)) (φ' t) +
          schwartzL2Inner (W.coefficientField (c m t))
            (ν • laplacianSchwartz (φ.field t) +
              convectionSchwartzBilin (W.coefficientField (c m t))
                (φ.field t)) +
          ν * schwartzL2Inner (W.coefficientField (c m t))
            (W.laplacianProjectionCommutator m (φ.field t)) +
          schwartzL2Inner (W.coefficientField (c m t))
            (W.convectionTestProjectionCommutator m
              (W.coefficientField (c m t)) (φ.field t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [schwartzL2Inner_add_right,
      convectionTestProjection_pairing,
      schwartzL2Inner_add_right]
    ring
  rw [hintegral] at heq
  exact heq

/-- Fixed-horizon version of the fully split projected-test equation.  This is
the form consumed by the scalar commutator limit theorem below. -/
theorem modalFlow_projectedTest_splitResidualWeakEquation_at
    (W : GalerkinBasisFamily) (ν : ℝ)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (φ : DivergenceFreeTestFunction) (φ' : ℝ → SchwartzVelocity)
    (T : ℝ) (hT : 0 ≤ T) (hφzero : ∀ t, T ≤ t → φ.field t = 0)
    (m : ℕ)
    (hmodal_deriv : ∀ t : ℝ,
      HasDerivAt (W.modalTestCoefficients φ.field m)
        (W.modalTestCoefficients φ' m t) t)
    (hmodal_deriv_cont : Continuous (W.modalTestCoefficients φ' m)) :
    (∫ t in (0 : ℝ)..T,
        schwartzL2Inner (W.coefficientField (c m t)) (φ' t) +
        schwartzL2Inner (W.coefficientField (c m t))
          (ν • laplacianSchwartz (φ.field t) +
            convectionSchwartzBilin (W.coefficientField (c m t)) (φ.field t)) +
        ν * schwartzL2Inner (W.coefficientField (c m t))
          (W.laplacianProjectionCommutator m (φ.field t)) +
        schwartzL2Inner (W.coefficientField (c m t))
          (W.convectionTestProjectionCommutator m
            (W.coefficientField (c m t)) (φ.field t))) +
      schwartzL2Inner (W.coefficientField (c m 0)) (φ.field 0) = 0 := by
  have hbzero : ∀ t : ℝ, T ≤ t → W.modalTestCoefficients φ.field m t = 0 := by
    intro t ht
    ext i
    simp [GalerkinBasisFamily.modalTestCoefficients, hφzero t ht,
      GalerkinBasisFamily.initialCoefficients, GalerkinBasisFamily.coeff,
      schwartzL2Inner_zero_left]
  have h := modalFlow_retainedSpan_physicalWeakEquation W ν c hc m
    (W.modalTestCoefficients φ.field m) (W.modalTestCoefficients φ' m)
    hmodal_deriv hmodal_deriv_cont T hT hbzero
  simp_rw [coefficientField_pairing_modalTestCoefficients] at h
  simp only [coefficientField_modalTestCoefficients] at h
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
              convectionSchwartzBilin (W.coefficientField (c m t)) (φ.field t)) +
          ν * schwartzL2Inner (W.coefficientField (c m t))
            (W.laplacianProjectionCommutator m (φ.field t)) +
          schwartzL2Inner (W.coefficientField (c m t))
            (W.convectionTestProjectionCommutator m
              (W.coefficientField (c m t)) (φ.field t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [schwartzL2Inner_add_right, schwartzL2Inner_smul_right,
      coefficientField_laplacianProjection_pairing,
      convectionTestProjection_pairing,
      schwartzL2Inner_add_right, schwartzL2Inner_smul_right]
    ring
  rw [hintegral] at h
  exact h

/-- The finite-interval density in the retained modal equation is exactly the
half-line density used by `weakFormResidual` once both certified test slices
have vanished.  The endpoint `t = 0` is handled by the null singleton, not by
discarding the repo's right-within derivative convention. -/
theorem weakFormResidual_modalApprox_eq_interval
    (W : GalerkinBasisFamily) (ν : ℝ) (u₀ : SchwartzVelocity)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (φ : DivergenceFreeTestFunction) (m : ℕ)
    (T : ℝ) (hT : 0 ≤ T)
    (hφzero : ∀ t, T ≤ t → φ.field t = 0)
    (hφ'zero : ∀ t, T ≤ t → φ.timeDerivSchwartz t = 0) :
    weakFormResidual ν u₀ (W.modalApprox c m) φ =
      (∫ t in (0 : ℝ)..T,
        schwartzL2Inner (W.coefficientField (c m t))
          (φ.timeDerivSchwartz t) +
        schwartzL2Inner (W.coefficientField (c m t))
          (ν • laplacianSchwartz (φ.field t) +
            convectionSchwartzBilin (W.coefficientField (c m t)) (φ.field t))) +
      schwartzL2Inner u₀ (φ.field 0) := by
  let F : ℝ → ℝ := fun t => ∫ x : Space,
    officialInner (W.modalApprox c m t x)
      (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
        spatialDerivative (fun s => (φ.field s : Space → Space)) t x
          (W.modalApprox c m t x) +
        ν • laplacian (fun s => (φ.field s : Space → Space)) t x)
  let G : ℝ → ℝ := fun t =>
    schwartzL2Inner (W.coefficientField (c m t)) (φ.timeDerivSchwartz t) +
    schwartzL2Inner (W.coefficientField (c m t))
      (ν • laplacianSchwartz (φ.field t) +
        convectionSchwartzBilin (W.coefficientField (c m t)) (φ.field t))
  have hFG : ∀ t : ℝ, 0 ≤ t → F t = G t := by
    intro t ht
    have hu := modalApprox_eq_coefficientField W c m ht
    change (∫ x : Space,
      officialInner (W.modalApprox c m t x)
        (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
          spatialDerivative (fun s => (φ.field s : Space → Space)) t x
            (W.modalApprox c m t x) +
          ν • laplacian (fun s => (φ.field s : Space → Space)) t x)) = _
    rw [hu]
    have hphysical : (∫ x : Space,
        officialInner (W.coefficientField (c m t) x)
          (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
            spatialDerivative (fun s => (φ.field s : Space → Space)) t x
              (W.coefficientField (c m t) x) +
            ν • laplacian (fun s => (φ.field s : Space → Space)) t x)) =
        schwartzL2Inner (W.coefficientField (c m t))
          (φ.timeDerivSchwartz t +
            convectionSchwartzBilin (W.coefficientField (c m t)) (φ.field t) +
            ν • laplacianSchwartz (φ.field t)) := by
      unfold schwartzL2Inner
      apply integral_congr_ae
      filter_upwards with x
      rw [φ.timeDeriv_eq t ht x]
      change officialInner (W.coefficientField (c m t) x)
          (φ.timeDerivSchwartz t x +
            fderiv ℝ (φ.field t) x (W.coefficientField (c m t) x) +
            ν • laplacian (fun _ => φ.field t) 0 x) = _
      change officialInner (W.coefficientField (c m t) x)
          (φ.timeDerivSchwartz t x +
            fderiv ℝ (φ.field t) x (W.coefficientField (c m t) x) +
            ν • laplacian (fun _ => φ.field t) 0 x) =
        officialInner (W.coefficientField (c m t) x)
          (φ.timeDerivSchwartz t x +
            convectionSchwartzBilin (W.coefficientField (c m t)) (φ.field t) x +
            ν • laplacianSchwartz (φ.field t) x)
      rw [convectionSchwartzBilin_apply, laplacianSchwartz_apply]
      rfl
    rw [hphysical, schwartzL2Inner_add_right, schwartzL2Inner_add_right]
    change _ = schwartzL2Inner (W.coefficientField (c m t))
        (φ.timeDerivSchwartz t) +
      schwartzL2Inner (W.coefficientField (c m t))
        (ν • laplacianSchwartz (φ.field t) +
          convectionSchwartzBilin (W.coefficientField (c m t)) (φ.field t))
    rw [schwartzL2Inner_add_right, schwartzL2Inner_smul_right]
    ring
  have hFtail : ∀ t ∈ Set.Ici (0 : ℝ) \ Set.Icc 0 T, F t = 0 := by
    intro t ht
    have hnot : ¬ t ≤ T := fun htt => ht.2 ⟨ht.1, htt⟩
    have hTt : T ≤ t := (lt_of_not_ge hnot).le
    have hfield : φ.field t = 0 := hφzero t hTt
    have hderiv : φ.timeDerivSchwartz t = 0 := hφ'zero t hTt
    have ht0 : 0 ≤ t := ht.1
    change (∫ x : Space,
      officialInner (W.modalApprox c m t x)
        (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
          spatialDerivative (fun s => (φ.field s : Space → Space)) t x
            (W.modalApprox c m t x) +
          ν • laplacian (fun s => (φ.field s : Space → Space)) t x)) = 0
    apply integral_eq_zero_of_ae
    filter_upwards with x
    rw [φ.timeDeriv_eq t ht0 x, hderiv]
    change officialInner (W.modalApprox c m t x)
      (0 + fderiv ℝ (φ.field t) x (W.modalApprox c m t x) +
        ν • laplacian (fun _ => φ.field t) 0 x) = 0
    rw [hfield]
    have hz : ((0 : SchwartzVelocity) : Space → Space) =
        fun _ : Space => (0 : Space) := by
      funext y
      simp
    rw [hz]
    simp only [laplacian, fderiv_const_apply, zero_apply,
      Finset.sum_const_zero, add_zero, smul_zero]
    unfold officialInner
    rw [show officialEuclideanPoint (0 : Space) = 0 by
      ext i
      simp [officialEuclideanPoint], inner_zero_right]
  have hrestrict : (∫ t in Set.Ici (0 : ℝ), F t) =
      ∫ t in Set.Icc (0 : ℝ) T, F t :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
      (fun _ ht => ht.1) hFtail
  have hinterval : (∫ t in Set.Ici (0 : ℝ), F t) = ∫ t in (0 : ℝ)..T, G t := by
    rw [hrestrict, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hT]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact hFG t ht.1.le
  unfold weakFormResidual
  change (∫ t in Set.Ici (0 : ℝ), F t) +
    (∫ x : Space, officialInner (u₀ x) (φ.field 0 x)) = _
  rw [hinterval]
  rfl

/-- Direct fixed-test weak-residual limit.  The retained ODE supplies the
split equation; after the finite-interval/`weakFormResidual` identification,
only the two scalar projection-commutator integrals must vanish. -/
theorem modalFlow_fixedTest_projectedResidual_tendsto_of_commutators
    (W : GalerkinBasisFamily) (ν : ℝ) (u₀ : SchwartzVelocity)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (hc0 : ∀ m, c m 0 = W.initialCoefficients u₀ m)
    (φ : DivergenceFreeTestFunction)
    (T : ℝ) (hT : 0 ≤ T) (hφzero : ∀ t, T ≤ t → φ.field t = 0)
    (hφ'zero : ∀ t, T ≤ t → φ.timeDerivSchwartz t = 0)
    (hmodal_deriv : ∀ (m : ℕ) (t : ℝ),
      HasDerivAt (W.modalTestCoefficients φ.field m)
        (W.modalTestCoefficients φ.timeDerivSchwartz m t) t)
    (hmodal_deriv_cont : ∀ m,
      Continuous (W.modalTestCoefficients φ.timeDerivSchwartz m))
    (hmainInt : ∀ m, IntervalIntegrable (fun t =>
      schwartzL2Inner (W.coefficientField (c m t)) (φ.timeDerivSchwartz t) +
      schwartzL2Inner (W.coefficientField (c m t))
        (ν • laplacianSchwartz (φ.field t) +
          convectionSchwartzBilin (W.coefficientField (c m t)) (φ.field t)))
      volume 0 T)
    (hlapInt : ∀ m, IntervalIntegrable (fun t =>
      ν * schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (φ.field t))) volume 0 T)
    (hconvInt : ∀ m, IntervalIntegrable (fun t =>
      schwartzL2Inner (W.coefficientField (c m t))
        (W.convectionTestProjectionCommutator m
          (W.coefficientField (c m t)) (φ.field t))) volume 0 T)
    (hlap : Filter.Tendsto (fun m =>
      ∫ t in (0 : ℝ)..T, ν * schwartzL2Inner (W.coefficientField (c m t))
        (W.laplacianProjectionCommutator m (φ.field t)))
      Filter.atTop (nhds 0))
    (hconv : Filter.Tendsto (fun m =>
      ∫ t in (0 : ℝ)..T, schwartzL2Inner (W.coefficientField (c m t))
        (W.convectionTestProjectionCommutator m
          (W.coefficientField (c m t)) (φ.field t)))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => weakFormResidual ν (W.proj m u₀) (W.modalApprox c m) φ)
      Filter.atTop (nhds 0) := by
  have heq (m : ℕ) := modalFlow_projectedTest_splitResidualWeakEquation_at
    W ν c hc φ φ.timeDerivSchwartz T hT hφzero m
      (hmodal_deriv m) (hmodal_deriv_cont m)
  have hidentify (m : ℕ) := weakFormResidual_modalApprox_eq_interval
    W ν (W.proj m u₀) c φ m T hT hφzero hφ'zero
  have hresidual : (fun m =>
      weakFormResidual ν (W.proj m u₀) (W.modalApprox c m) φ) = fun m =>
      -(∫ t in (0 : ℝ)..T, ν * schwartzL2Inner (W.coefficientField (c m t))
          (W.laplacianProjectionCommutator m (φ.field t))) -
      (∫ t in (0 : ℝ)..T, schwartzL2Inner (W.coefficientField (c m t))
          (W.convectionTestProjectionCommutator m
            (W.coefficientField (c m t)) (φ.field t))) := by
    funext m
    have heq' := heq m
    rw [intervalIntegral.integral_add ((hmainInt m).add (hlapInt m)) (hconvInt m),
      intervalIntegral.integral_add (hmainInt m) (hlapInt m)] at heq'
    rw [hidentify m, ← coefficientField_initialCoefficients_eq_proj W u₀ m,
      ← hc0 m]
    linarith [heq']
  rw [hresidual]
  simpa using hlap.neg.sub hconv

/-- Fixed-test form of the projected-datum correction.  Together with
`modalFlow_fixedTest_projectedResidual_tendsto_of_commutators`, this supplies
the exact fixed-test input consumed by Galerkin weak consistency. -/
theorem modalApprox_fixedTest_weakConsistent_of_projectedDatum
    (W : GalerkinBasisFamily) (ν : ℝ)
    (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (φ : DivergenceFreeTestFunction)
    (hprojected : Filter.Tendsto
      (fun m => weakFormResidual ν (W.proj m u₀) (W.modalApprox c m) φ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => weakFormResidual ν u₀ (W.modalApprox c m) φ)
      Filter.atTop (nhds 0) := by
  have heq : (fun m => weakFormResidual ν u₀ (W.modalApprox c m) φ) =
      fun m => weakFormResidual ν (W.proj m u₀) (W.modalApprox c m) φ +
        schwartzL2Inner (u₀ - W.proj m u₀) (φ.field 0) := by
    funext m
    exact weakFormResidual_eq_projectedDatum_add W ν u₀ (W.modalApprox c m) φ m
  rw [heq]
  simpa using hprojected.add
    (proj_error_pairing_tendsto_zero W u₀ hu₀ (φ.field 0))

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
    (hbound_le : bound ≤ ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2)
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
    enstrophyBound := bound
    enstrophyBound_nonneg := hbound
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
