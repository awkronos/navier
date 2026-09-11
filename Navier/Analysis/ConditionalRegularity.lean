import Navier.Analysis.BealeKatoMajda
import Navier.Analysis.EnergyNormBridge
import Navier.Analysis.ParabolicCaccioppoli
import Navier.Scaling
import Navier.Analysis.ESSInputs
import Navier.Analysis.EnergyNormBridge
import Navier.Analysis.HeatSemigroupSmoothing
import Navier.Analysis.WholeSpaceCutoffLimit
import Navier.EnergyObstruction

/-!
# Conditional regularity estimates and counterexamples

This module proves compact-region bounds, reductions to spatial tails,
Gaussian cutoff and convolution estimates under explicit integrability
hypotheses, and vorticity-direction geometry. The Duhamel representation is
proved here for zero velocity; the general representation and source bounds
needed for full Prodi–Serrin and Constantin–Fefferman criteria require further
analytic proofs.

The explicit strain-flow counterexamples and integral vacuity witnesses show
why smoothness, default-valued integrals, and unconditional cross-product
bounds cannot supply the omitted analytic hypotheses. No admitted criterion
is exported from this module.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace Navier.Analysis.ConditionalRegularity

open scoped Matrix
open scoped ContDiff

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.EnergyNormBridge
open Navier.Analysis.ParabolicCaccioppoli
open Navier.Breakdown
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.WholeSpaceDuhamel
open Navier.Analysis.WholeSpaceCutoffLimit
open Navier.Analysis.ScaledCutoff

/-! ### Shared established leaves -/

/-- Split a uniform bound on `[0,T)` into an initial layer `[0,δ]` and an
interior `(δ,T)`, recombined by `max`.  Purely order-theoretic; this is the
shared assembly step for both conditional-regularity bridges below. -/
theorem uniformBound_of_split {α : Type*} {T δ : ℝ} (g : ℝ → α → ℝ) (R₁ R₂ : ℝ)
    (hlayer : ∀ t : ℝ, 0 ≤ t → t < T → t ≤ δ → ∀ a : α, g t a ≤ R₁)
    (hinterior : ∀ t : ℝ, δ < t → t < T → ∀ a : α, g t a ≤ R₂) :
    ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → ∀ a : α, g t a ≤ R := by
  refine ⟨max R₁ R₂, fun t ht0 htT a => ?_⟩
  by_cases h : t ≤ δ
  · exact (hlayer t ht0 htT h a).trans (le_max_left _ _)
  · exact (hinterior t (lt_of_not_ge h) htT a).trans (le_max_right _ _)

/-- On the Ladyzhenskaya–Prodi–Serrin critical line `2/q + 3/p = 1`, the
spatial constraint `p > 3` forces the temporal exponent `q > 2`.

The critical-line equation itself excludes the degenerate temporal exponents.
If `q = 0` then `2/q = 0` in Lean's division convention, so the equation reads
`3/p = 1`, contradicting `3 < p`; if `q < 0` then `2/q < 0`, so `3/p > 1`,
again contradicting `3 < p`.  Hence `0 < q`, and `2/q = 1 - 3/p < 1` gives
`2 < q`.  Sample points: `p = 6 ⟹ q = 4`, `p = 9 ⟹ q = 3`, `p = 4 ⟹ q = 8`;
`q ↓ 2` only in the limit `p ↑ ∞`, and `q ↑ ∞` as `p ↓ 3`. -/
theorem serrin_exponent_gt_two {p q : ℝ} (hp : 3 < p)
    (hcrit : Navier.Scaling.CriticalLine p q) : 2 < q := by
  have hp0 : (0 : ℝ) < p := lt_trans (by norm_num) hp
  have h3p_lt_one : 3 / p < 1 := (div_lt_one hp0).2 hp
  have h3p_pos : 0 < 3 / p := div_pos (by norm_num) hp0
  have hcrit' : 2 / q = 1 - 3 / p := by
    simp only [Navier.Scaling.CriticalLine] at hcrit
    linarith
  have h2q_pos : 0 < 2 / q := by rw [hcrit']; linarith
  have hq0 : 0 < q := by
    rcases div_pos_iff.1 h2q_pos with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · linarith
  have h2q_lt_one : 2 / q < 1 := by rw [hcrit']; linarith
  exact (div_lt_one hq0).1 h2q_lt_one

/-- **Necessity of the bounded-initial-datum hypothesis.**  A partial classical
solution has positive terminal time and time-zero slice `u₀`, so a uniform
velocity bound on `[0,T)` *entails* that `u₀` is bounded.

This certifies that the hypothesis `hu₀` carried by both bridges below is
minimal rather than an over-assumption: the ambient hypotheses do not supply
it (`SmoothVelocityBefore` is `ContDiffOn` on `Set.Ico 0 T ×ˢ univ`, a purely
local condition, and per-slice `L^p` integrability does not imply spatial
boundedness), while the stated conclusion demands it. -/
theorem initialDatum_bounded_of_uniformBound
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (h : ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Space,
      ‖sol.velocity t x‖ ≤ R) :
    ∃ B₀ : ℝ, ∀ x : Space, ‖u₀ x‖ ≤ B₀ := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun x => ?_⟩
  have hx := hR 0 le_rfl sol.terminalTime_pos x
  rwa [sol.initial_condition] at hx

/-- The uniform-in-time `L²` mass bracket carried by a hypothesis-carried
energy bound: for every time in `[0,T)` the kinetic-energy integral lies in
`[0, E]`.  The lower endpoint is new content — it does not appear among the
hypotheses — and it is what makes `energyBound_nonneg` available downstream.

**Pattern-A repair (this wave): the bracket was FALSE as previously
stated.**  `kineticEnergy` is the *official* Euclidean sum-of-squares energy
(`Navier.Problem.kineticEnergy`), whereas `Space`'s inherited norm is the
finite-product sup norm — the two densities are neither equal nor `defeq`.
Recovering the sup-norm mass bracket from a sum-of-squares bound needs the
componentwise measurability of the slice (it is not implied by mere
integrability of the sup-norm-squared density); `hmeas` is the added
hypothesis, discharged at every call site by
`PartialClassicalSolution.velocity_slice_aestronglyMeasurable`. -/
theorem uniformL2Mass_of_energyBound {u : VelocityEvolution} {T E : ℝ}
    (henergy : ∀ t : ℝ, 0 ≤ t → t < T →
      AEStronglyMeasurable (u t) volume ∧
      Integrable (fun x : Space => ‖u t x‖ ^ 2) ∧ kineticEnergy u t ≤ E) :
    ∀ t : ℝ, 0 ≤ t → t < T →
      (∫ x : Space, ‖u t x‖ ^ 2) ∈ Set.Icc (0 : ℝ) E := by
  intro t ht0 htT
  obtain ⟨hmeas, hint, hk⟩ := henergy t ht0 htT
  refine ⟨integral_nonneg fun x => by positivity, ?_⟩
  exact intNormSq_le_of_kineticEnergy_le u t E hmeas hint hk

/-- A hypothesis-carried energy bound over a nonempty time interval is
nonnegative.  Not assumed anywhere: it is forced by the nonnegativity of the
kinetic-energy integrand at the admissible time `t = 0`. -/
theorem energyBound_nonneg {u : VelocityEvolution} {T E : ℝ} (hT : 0 < T)
    (henergy : ∀ t : ℝ, 0 ≤ t → t < T →
      AEStronglyMeasurable (u t) volume ∧
      Integrable (fun x : Space => ‖u t x‖ ^ 2) ∧ kineticEnergy u t ≤ E) :
    0 ≤ E := by
  have hnn : (0 : ℝ) ≤ kineticEnergy u 0 := by
    unfold kineticEnergy
    exact integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  exact hnn.trans (henergy 0 le_rfl hT).2.2

/-- The integrability half of a hypothesis-carried energy bound.  Companion to
`uniformL2Mass_of_energyBound`, which retains only the numeric bracket and
discards this conjunct.  Discarding it is exactly what made the two
Constantin–Fefferman leaves false as previously stated; see
`massBracket_vacuous_of_infiniteMass`. -/
theorem uniformL2Integrable_of_energyBound {u : VelocityEvolution} {T E : ℝ}
    (henergy : ∀ t : ℝ, 0 ≤ t → t < T →
      AEStronglyMeasurable (u t) volume ∧
      Integrable (fun x : Space => ‖u t x‖ ^ 2) ∧ kineticEnergy u t ≤ E) :
    ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖u t x‖ ^ 2) :=
  fun t ht0 htT => (henergy t ht0 htT).2.1

/-! ### Falsification of the bare integral brackets -/

/-- Without integrability, the bare energy bracket is vacuous: the Bochner
integral of a nonintegrable integrand is zero, so every nonnegative budget
satisfies the bracket. -/
theorem massBracket_vacuous_of_infiniteMass
    {u : VelocityEvolution} {T E : ℝ} (hE : 0 ≤ E)
    (hbad : ∀ t : ℝ, 0 ≤ t → t < T →
      ¬ Integrable (fun x : Space => ‖u t x‖ ^ 2)) :
    ∀ t : ℝ, 0 ≤ t → t < T →
      (∫ x : Space, ‖u t x‖ ^ 2) ∈ Set.Icc (0 : ℝ) E := by
  intro t ht0 htT
  rw [integral_undef (hbad t ht0 htT)]
  exact ⟨le_rfl, hE⟩

/-- **The bare Serrin mixed-norm bracket is vacuous off the time-integrable
class.**  The Ladyzhenskaya–Prodi–Serrin hypothesis is `u ∈ L^q(0,T; L^p(ℝ³))`,
whose definition includes integrability of `s ↦ ‖u(s,·)‖_{L^p}^q` on `(0,T')`.
The numeric encoding

`∀ T' ∈ [0,T), ∫₀^{T'} (∫ |u(s,x)|^p dx)^{q/p} ds ≤ M`

drops that conjunct, and Lean's interval integral returns the junk value `0`
on a non-interval-integrable integrand, so the bracket is satisfied by *every*
velocity evolution whose slice-norm profile fails to be interval-integrable on
`(0,T')` for every admissible `T'` — for instance one blowing up like `s⁻¹` at
the initial time — for every `M ≥ 0`.

This is the same defect class as `massBracket_vacuous_of_infiniteMass`, in the
temporal slot rather than the spatial one, and it is repaired the same way
(Pattern A): the Prodi–Serrin leaf, its assembly and the bridge now carry the
explicit conjunct `hMint`, which is part of the classical hypothesis
`u ∈ L^q_t L^p_x` and is therefore not an additional assumption but the
restoration of a dropped one. -/
theorem serrinMixedNorm_vacuous_of_nonIntegrableTime
    {u : VelocityEvolution} {T p q M : ℝ} (hM : 0 ≤ M)
    (hbad : ∀ T' : ℝ, 0 ≤ T' → T' < T →
      ¬ IntervalIntegrable
          (fun s : ℝ => (∫ x : Space, ‖u s x‖ ^ p) ^ (q / p)) volume 0 T') :
    ∀ T' : ℝ, 0 ≤ T' → T' < T →
      (∫ s in (0 : ℝ)..T', (∫ x : Space, ‖u s x‖ ^ p) ^ (q / p)) ≤ M := by
  intro T' h0 hT
  rw [intervalIntegral.integral_undef (hbad T' h0 hT)]
  exact hM

/-! ### Compact space-time control (established) -/

/-- Continuity of the velocity norm on the classical space-time region
`[0,T) × ℝ³`, extracted from joint smoothness. -/
theorem norm_continuousOn_spacetimeBefore
    {u : VelocityEvolution} {T : ℝ} (hu : SmoothVelocityBefore T u) :
    ContinuousOn (fun z : ℝ × Space => ‖u z.1 z.2‖) (spacetimeBefore T) :=
  hu.continuousOn.norm

/-- **Compact space-time bound.**  On a closed time window `[a,b]` with
`0 ≤ a` and `b < T`, and any compact spatial set `K`, a classical velocity
field is uniformly bounded on `[a,b] × K`.

This is the compact-set strengthening of
`Navier.Breakdown.bounded_pointEvaluation_of_smooth`, which bounds a classical
velocity along a single fixed spatial point.  It is exactly the portion of both
conditional-regularity bridges that needs no analytic machinery: `[a,b] ×ˢ K`
is compact and contained in `spacetimeBefore T`, so the continuous norm attains
a finite supremum there.  What it does **not** supply — and what the residual
leaves below now isolate — is uniformity as `‖x‖ → ∞` or as `t ↑ T`, because
neither `ℝ³` nor `[0,T)` is compact. -/
theorem compactSpaceTime_bounded
    {u : VelocityEvolution} {T a b : ℝ} (hu : SmoothVelocityBefore T u)
    (ha : 0 ≤ a) (hb : b < T) {K : Set Space} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, a ≤ t → t ≤ b → ∀ x ∈ K, ‖u t x‖ ≤ R := by
  have hsub : Set.Icc a b ×ˢ K ⊆ spacetimeBefore T := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨ha.trans ht.1, lt_of_le_of_lt ht.2 hb⟩, Set.mem_univ x⟩
  have hcont : ContinuousOn (fun z : ℝ × Space => ‖u z.1 z.2‖) (Set.Icc a b ×ˢ K) :=
    (norm_continuousOn_spacetimeBefore hu).mono hsub
  have hcpt : IsCompact (Set.Icc a b ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨R, hR⟩ := hcpt.bddAbove_image hcont
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro t hat htb x hx
  have hmem : ((t, x) : ℝ × Space) ∈ Set.Icc a b ×ˢ K := ⟨⟨hat, htb⟩, hx⟩
  exact le_trans (hR (Set.mem_image_of_mem _ hmem)) (le_max_left _ _)

/-- **Far-field reduction on a closed time window.**  On `[a,b]` with `b < T`, a
bound outside a single closed ball upgrades to a uniform bound on all of
`ℝ³`: the complementary ball is compact, so `compactSpaceTime_bounded` handles
it and the two bounds recombine by `max`.

This is what makes the initial-layer residuals strictly smaller than the
statements they support — the compact core is discharged here, and only decay
at spatial infinity remains. -/
theorem uniformBound_of_farField_window
    {u : VelocityEvolution} {T a b : ℝ} (hu : SmoothVelocityBefore T u)
    (ha : 0 ≤ a) (hb : b < T) {ϱ R₂ : ℝ}
    (htail : ∀ t : ℝ, a ≤ t → t ≤ b → ∀ x : Space, ϱ ≤ ‖x‖ → ‖u t x‖ ≤ R₂) :
    ∃ R : ℝ, ∀ t : ℝ, a ≤ t → t ≤ b → ∀ x : Space, ‖u t x‖ ≤ R := by
  obtain ⟨R₁, _, hcpt⟩ :=
    compactSpaceTime_bounded hu ha hb (isCompact_closedBall (0 : Space) ϱ)
  refine ⟨max R₁ R₂, fun t hat htb x => ?_⟩
  by_cases hx : ϱ ≤ ‖x‖
  · exact (htail t hat htb x hx).trans (le_max_right _ _)
  · refine le_trans (hcpt t hat htb x ?_) (le_max_left _ _)
    simpa [mem_closedBall_zero_iff] using (not_le.1 hx).le

/-- **Outer-region reduction on the half-open interior window.**  On `(δ,T)` a
bound on the outer region — far field `ϱ ≤ ‖x‖`, or late times `m < t` for one
interior split point `m < T` — upgrades to a uniform bound, because the
complementary set `[δ,m] × closedBall 0 ϱ` is compact.

This is the interior analogue of `uniformBound_of_farField_window`; the two
remaining obstructions it isolates are exactly decay at spatial infinity and
uniformity as `t ↑ T`. -/
theorem interiorBound_of_outerRegion
    {u : VelocityEvolution} {T δ m : ℝ} (hu : SmoothVelocityBefore T u)
    (hδ : 0 ≤ δ) (hm : m < T) {ϱ R₂ : ℝ}
    (htail : ∀ t : ℝ, δ < t → t < T → ∀ x : Space,
      (ϱ ≤ ‖x‖ ∨ m < t) → ‖u t x‖ ≤ R₂) :
    ∃ R : ℝ, ∀ t : ℝ, δ < t → t < T → ∀ x : Space, ‖u t x‖ ≤ R := by
  obtain ⟨R₁, _, hcpt⟩ :=
    compactSpaceTime_bounded hu hδ hm (isCompact_closedBall (0 : Space) ϱ)
  refine ⟨max R₁ R₂, fun t htδ htT x => ?_⟩
  by_cases hx : ϱ ≤ ‖x‖
  · exact (htail t htδ htT x (Or.inl hx)).trans (le_max_right _ _)
  · by_cases htm : m < t
    · exact (htail t htδ htT x (Or.inr htm)).trans (le_max_right _ _)
    · refine le_trans (hcpt t htδ.le (not_lt.1 htm) x ?_) (le_max_left _ _)
      simpa [mem_closedBall_zero_iff] using (not_le.1 hx).le

/-- **Vorticity-direction depletion at scale `ε`.**  Constantin–Fefferman
`ρ`-coherence bounds the vorticity cross product by `(|x−y|/ρ)·|ω(x)||ω(y)|`.
Restricting to pairs separated by at most `ε·ρ` therefore gains the explicit
depletion factor `ε`:

`|ω(x) ⨯ ω(y)| ≤ ε · |ω(x)| · |ω(y)|`.

This is the form the enstrophy stretching estimate consumes.  It is
informative exactly for `ε < 1`: at `ε = 1` it degenerates to the
unconditional Lagrange bound `officialEuclideanNorm_crossProduct_le`, which
`depletedCrossProduct_vacuous` certifies is a tautology and
`crossProductBound_saturated` certifies is attained. -/
theorem coherentVorticity_crossProduct_le_scaled
    {u : VelocityEvolution} {T ρ Ω₀ : ℝ} (hρ : 0 < ρ)
    (hcoh : ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity u t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity u t y) →
      officialEuclideanNorm (vorticity u t x ⨯₃ vorticity u t y) ≤
        (officialEuclideanNorm (fun i => x i - y i) / ρ) *
          (officialEuclideanNorm (vorticity u t x) *
            officialEuclideanNorm (vorticity u t y)))
    (ε : ℝ) :
    ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity u t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity u t y) →
      officialEuclideanNorm (fun i => x i - y i) ≤ ε * ρ →
      officialEuclideanNorm (vorticity u t x ⨯₃ vorticity u t y) ≤
        ε * (officialEuclideanNorm (vorticity u t x) *
          officialEuclideanNorm (vorticity u t y)) := by
  intro t ht0 htT x y hx hy hd
  refine (hcoh t ht0 htT x y hx hy).trans ?_
  exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hρ).2 hd)
    (mul_nonneg (officialEuclideanNorm_nonneg _) (officialEuclideanNorm_nonneg _))

/-! ### Euclidean cross-product geometry -/

/-- Coordinate formula for the square of the official Euclidean point norm. -/
theorem euclideanNormSq_eq_sum (x : Space) :
    officialEuclideanNorm x ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
  rw [officialEuclideanNorm_eq_sqrt_sum_sq,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [sq_abs]

/-- The official Euclidean point norm vanishes at the origin. -/
theorem officialEuclideanNorm_zero : officialEuclideanNorm (0 : Space) = 0 :=
  (officialEuclideanNorm_eq_zero_iff 0).2 rfl

/-- Bilinearity of the cross product in the two scalar factors. -/
theorem crossProduct_smul_smul (c d : ℝ) (a b : Space) :
    (c • a) ⨯₃ (d • b) = (c * d) • (a ⨯₃ b) := by
  simp only [cross_apply]
  ext i
  fin_cases i <;> simp [Pi.smul_apply] <;> ring

/-- **Lagrange's identity bound.**  `|a ⨯ b|² = |a|²|b|² − ⟨a,b⟩² ≤ |a|²|b|²`,
so the Euclidean norm of a cross product never exceeds the product of the two
norms.

This holds for *every* pair of vectors, with no hypothesis whatsoever.  It is
the reason `depletedCrossProduct_vacuous` below is a tautology, and hence the
kernel-checked source of the second Pattern-A repair recorded in the module
header. -/
theorem officialEuclideanNorm_crossProduct_le (a b : Space) :
    officialEuclideanNorm (a ⨯₃ b) ≤
      officialEuclideanNorm a * officialEuclideanNorm b := by
  have hb : 0 ≤ officialEuclideanNorm a * officialEuclideanNorm b :=
    mul_nonneg (officialEuclideanNorm_nonneg _) (officialEuclideanNorm_nonneg _)
  have h1 : officialEuclideanNorm (a ⨯₃ b) ^ 2
      ≤ (officialEuclideanNorm a * officialEuclideanNorm b) ^ 2 := by
    rw [mul_pow, euclideanNormSq_eq_sum, euclideanNormSq_eq_sum, euclideanNormSq_eq_sum]
    simp only [cross_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    nlinarith [sq_nonneg (a 0 * b 0 + a 1 * b 1 + a 2 * b 2)]
  nlinarith [officialEuclideanNorm_nonneg (a ⨯₃ b), h1, hb]

/-- **The universal cross-product bound is saturated.**  At the orthogonal unit
pair `e₁, e₂` the inequality of `officialEuclideanNorm_crossProduct_le` is an
equality (ratio exactly `1`), so the coefficient in the unconditional bound
cannot be decreased. -/
theorem crossProductBound_saturated :
    officialEuclideanNorm ((![1, 0, 0] : Space) ⨯₃ (![0, 1, 0] : Space)) =
      officialEuclideanNorm (![1, 0, 0] : Space) *
        officialEuclideanNorm (![0, 1, 0] : Space) := by
  have hcross : ((![1, 0, 0] : Space) ⨯₃ (![0, 1, 0] : Space)) = ![0, 0, 1] := by
    simp only [cross_apply]
    ext i
    fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
  rw [hcross, officialEuclideanNorm_eq_sqrt_sum_sq, officialEuclideanNorm_eq_sqrt_sum_sq,
    officialEuclideanNorm_eq_sqrt_sum_sq]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- **Unit-vector direction bound.**  For Euclidean unit vectors,
`|a ⨯ b| ≤ |a − b|`.

In the angle variable this is `|sin θ| = 2 sin(θ/2) cos(θ/2) ≤ 2 sin(θ/2) =
|a − b|`; algebraically, writing `c = ⟨a,b⟩`, it is `1 − c² ≤ 2 − 2c`, i.e.
`0 ≤ (1 − c)²`.  This is the geometric step that converts Lipschitz continuity
of the vorticity *direction* into the Constantin–Fefferman sine bound
[Constantin–Fefferman, Indiana Univ. Math. J. 42 (1993) 775–789, §2]. -/
theorem officialEuclideanNorm_crossProduct_le_sub_of_unit {a b : Space}
    (ha : officialEuclideanNorm a = 1) (hb : officialEuclideanNorm b = 1) :
    officialEuclideanNorm (a ⨯₃ b) ≤ officialEuclideanNorm (a - b) := by
  have ha2 : ∑ i : Fin 3, (a i) ^ 2 = 1 := by
    rw [← euclideanNormSq_eq_sum, ha]; norm_num
  have hb2 : ∑ i : Fin 3, (b i) ^ 2 = 1 := by
    rw [← euclideanNormSq_eq_sum, hb]; norm_num
  have h1 : officialEuclideanNorm (a ⨯₃ b) ^ 2 ≤ officialEuclideanNorm (a - b) ^ 2 := by
    rw [euclideanNormSq_eq_sum, euclideanNormSq_eq_sum]
    simp only [cross_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Pi.sub_apply] at *
    nlinarith [sq_nonneg (1 - (a 0 * b 0 + a 1 * b 1 + a 2 * b 2)), ha2, hb2]
  nlinarith [officialEuclideanNorm_nonneg (a ⨯₃ b), officialEuclideanNorm_nonneg (a - b), h1]

/-- **Cross product controlled by direction distance.**  For arbitrary vectors,

`|a ⨯ b| ≤ |a/|a| − b/|b|| · (|a| · |b|)`,

both sides vanishing when either factor does.  This is the division-free form
of `|sin θ(a,b)| ≤ |ξ(a) − ξ(b)|`, and unlike
`officialEuclideanNorm_crossProduct_le` it is *not* vacuous: its right-hand
factor is the distance between the two directions, which is small exactly when
the two vectors are nearly aligned. -/
theorem officialEuclideanNorm_crossProduct_le_directionDist (a b : Space) :
    officialEuclideanNorm (a ⨯₃ b) ≤
      officialEuclideanNorm
          ((officialEuclideanNorm a)⁻¹ • a - (officialEuclideanNorm b)⁻¹ • b) *
        (officialEuclideanNorm a * officialEuclideanNorm b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [officialEuclideanNorm_zero]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [officialEuclideanNorm_zero]
  have hna : officialEuclideanNorm a ≠ 0 := fun h =>
    ha ((officialEuclideanNorm_eq_zero_iff a).1 h)
  have hnb : officialEuclideanNorm b ≠ 0 := fun h =>
    hb ((officialEuclideanNorm_eq_zero_iff b).1 h)
  set α := officialEuclideanNorm a with hα
  set β := officialEuclideanNorm b with hβ
  have hαpos : 0 < α := lt_of_le_of_ne (officialEuclideanNorm_nonneg a) (Ne.symm hna)
  have hβpos : 0 < β := lt_of_le_of_ne (officialEuclideanNorm_nonneg b) (Ne.symm hnb)
  have hu : officialEuclideanNorm (α⁻¹ • a) = 1 := by
    rw [officialEuclideanNorm_smul, abs_of_nonneg (inv_nonneg.2 hαpos.le), ← hα,
      inv_mul_cancel₀ hna]
  have hv : officialEuclideanNorm (β⁻¹ • b) = 1 := by
    rw [officialEuclideanNorm_smul, abs_of_nonneg (inv_nonneg.2 hβpos.le), ← hβ,
      inv_mul_cancel₀ hnb]
  have key := officialEuclideanNorm_crossProduct_le_sub_of_unit hu hv
  have hdecomp : a ⨯₃ b = (α * β) • ((α⁻¹ • a) ⨯₃ (β⁻¹ • b)) := by
    rw [crossProduct_smul_smul, smul_smul,
      show α * β * (α⁻¹ * β⁻¹) = 1 by field_simp, one_smul]
  rw [hdecomp, officialEuclideanNorm_smul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α * β)]
  calc α * β * officialEuclideanNorm ((α⁻¹ • a) ⨯₃ (β⁻¹ • b))
      ≤ α * β * officialEuclideanNorm (α⁻¹ • a - β⁻¹ • b) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = officialEuclideanNorm (α⁻¹ • a - β⁻¹ • b) * (α * β) := by ring

/-! ### Falsification of the `ε = 1` depletion hypothesis -/

/-- The unconditional cross-product bound holds regardless of distance or
vorticity thresholds, and therefore supplies no direction-coherence control.
`crossProductCoherent_of_directionLipschitz` gives a distance-dependent bound
from an actual regularity hypothesis on the direction field. -/
theorem depletedCrossProduct_vacuous (u : VelocityEvolution) (T ρ Ω₀ : ℝ) :
    ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity u t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity u t y) →
      officialEuclideanNorm (fun i => x i - y i) ≤ ρ →
      officialEuclideanNorm (vorticity u t x ⨯₃ vorticity u t y) ≤
        officialEuclideanNorm (vorticity u t x) *
          officialEuclideanNorm (vorticity u t y) :=
  fun _ _ _ _ _ _ _ _ => officialEuclideanNorm_crossProduct_le _ _

/-! ### The genuine Constantin–Fefferman direction hypothesis -/

/-- **Lipschitz vorticity direction implies Constantin–Fefferman coherence.**
If the unit vorticity direction `ξ = ω/|ω|` is `ρ⁻¹`-Lipschitz on the
high-vorticity region `{|ω| ≥ Ω₀}` — the hypothesis actually used in
[Constantin–Fefferman, Indiana Univ. Math. J. 42 (1993) 775–789] — then the
division-free coherence bound

`|ω(x) ⨯ ω(y)| ≤ (|x−y|/ρ) · |ω(x)| · |ω(y)|`

holds on that region.  Geometrically: `|sin θ| ≤ |ξ(x) − ξ(y)| ≤ |x−y|/ρ`, the
first step being `officialEuclideanNorm_crossProduct_le_sub_of_unit`.

Unlike `depletedCrossProduct_vacuous`, the conclusion here is genuinely
constraining: it degenerates to `0` as `y → x`, which is exactly the depletion
that makes the enstrophy stretching term subordinate to viscous dissipation. -/
theorem crossProductCoherent_of_directionLipschitz
    {u : VelocityEvolution} {T ρ Ω₀ : ℝ}
    (hdir : ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity u t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity u t y) →
      officialEuclideanNorm
          ((officialEuclideanNorm (vorticity u t x))⁻¹ • vorticity u t x -
            (officialEuclideanNorm (vorticity u t y))⁻¹ • vorticity u t y) ≤
        officialEuclideanNorm (fun i => x i - y i) / ρ) :
    ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity u t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity u t y) →
      officialEuclideanNorm (vorticity u t x ⨯₃ vorticity u t y) ≤
        (officialEuclideanNorm (fun i => x i - y i) / ρ) *
          (officialEuclideanNorm (vorticity u t x) *
            officialEuclideanNorm (vorticity u t y)) := by
  intro t ht0 htT x y hx hy
  refine (officialEuclideanNorm_crossProduct_le_directionDist _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (hdir t ht0 htT x y hx hy)
    (mul_nonneg (officialEuclideanNorm_nonneg _) (officialEuclideanNorm_nonneg _))

/-! ### Shared linear ingredient: the heat flow of the initial datum -/

/-- **The initial datum of a partial classical solution is continuous.**  It is
the time-zero slice of a velocity field that is `C^∞` on `[0,T) × ℝ³`, and
`0 ∈ [0,T)` because `terminalTime_pos` gives `0 < T`.

Extracted from the far-field leaves, which both need measurability of `u₀` to
integrate it against the heat kernel; it holds for an arbitrary force field, so
it is stated for a general `PartialClassicalSolution`. -/
theorem initialDatum_continuous
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) : Continuous u₀ := by
  have hcontOn : ContinuousOn (fun z : ℝ × Space => sol.velocity z.1 z.2)
      (spacetimeBefore T) := sol.velocity_smooth.continuousOn
  have hcontOn_u₀ : ContinuousOn (fun x : Space => sol.velocity 0 x) Set.univ :=
    hcontOn.comp (Continuous.prodMk continuous_const continuous_id).continuousOn (by
      intro x _
      exact ⟨⟨le_rfl, by simpa using sol.terminalTime_pos⟩, Set.mem_univ x⟩)
  have hcont_u₀ : Continuous (fun x : Space => sol.velocity 0 x) :=
    continuousOn_univ.1 hcontOn_u₀
  rw [← sol.initial_condition]
  exact hcont_u₀

/-- **The heat flow of bounded data is bounded by the same constant.**  For
every viscosity `ν > 0`, every positive time `t` and every measurable field `g`
with `‖g‖ ≤ B` pointwise,

`‖∫ G^ν_t(x − y) • g(y) dy‖ ≤ B`   for every `x`,

because the Gaussian kernel is nonnegative and integrates to `1`
(`integral_heatKernel`).  No decay of `g` is used, and the constant is not
inflated: at `g ≡ b` constant the bound is attained.

This bounds the linear term `e^{tνΔ}u₀` in a Duhamel representation by
`‖u₀‖_∞`. -/
theorem heatFlow_bounded_of_bounded {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    {g : VelocityField} (hg : Measurable g) {B : ℝ} (hB : ∀ x : Space, ‖g x‖ ≤ B)
    (x : Space) :
    ‖∫ y : Space, heatKernel ν t (x - y) • g y‖ ≤ B := by
  have hintK : Integrable (fun y : Space => heatKernel ν t (y - x)) := by
    have hK : Integrable (fun y : Space => heatKernel ν t y) := by
      have := integrable_heatKernel_rpow hν ht one_pos
      simpa [Real.rpow_one] using this
    exact hK.comp_sub_right x
  have hintKx : Integrable (fun y : Space => heatKernel ν t (x - y)) :=
    hintK.congr (Filter.Eventually.of_forall (fun y => by
      simpa using (heatKernel_comm ν t x y).symm))
  have hintKxB : Integrable (fun y : Space => heatKernel ν t (x - y) * B) := by
    have h' := hintKx.const_mul B
    refine h'.congr (Filter.Eventually.of_forall (fun y => ?_))
    ring
  have hprod_int : Integrable (fun y : Space => heatKernel ν t (x - y) * ‖g y‖) := by
    have hmeas : AEStronglyMeasurable
        (fun y : Space => heatKernel ν t (x - y) * ‖g y‖) volume :=
      (((heatKernel_continuous ν t).measurable.comp
        (measurable_const.sub measurable_id)).mul
          (measurable_norm.comp hg)).aestronglyMeasurable
    have h_nonneg : ∀ᵐ y ∂ volume, 0 ≤ heatKernel ν t (x - y) * ‖g y‖ :=
      Filter.Eventually.of_forall
        (fun y => mul_nonneg (heatKernel_nonneg hν ht (x - y)) (norm_nonneg _))
    have h_bound : ∀ᵐ y ∂ volume,
        heatKernel ν t (x - y) * ‖g y‖ ≤ heatKernel ν t (x - y) * B :=
      Filter.Eventually.of_forall
        (fun y => mul_le_mul_of_nonneg_left (hB y) (heatKernel_nonneg hν ht (x - y)))
    exact hintKxB.mono_nonneg hmeas h_nonneg h_bound
  calc
    ‖∫ y : Space, heatKernel ν t (x - y) • g y‖
        ≤ ∫ y : Space, ‖heatKernel ν t (x - y) • g y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : Space, heatKernel ν t (x - y) * ‖g y‖ := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      simp [norm_smul, abs_of_nonneg (heatKernel_nonneg hν ht (x - y))]
    _ ≤ ∫ y : Space, heatKernel ν t (x - y) * B :=
      integral_mono hprod_int hintKxB (fun y =>
        mul_le_mul_of_nonneg_left (hB y) (heatKernel_nonneg hν ht (x - y)))
    _ = (∫ y : Space, heatKernel ν t (x - y)) * B := by rw [integral_mul_const]
    _ = B * ∫ y : Space, heatKernel ν t (x - y) := by rw [mul_comm]
    _ = B * 1 := by
      rw [show (∫ y : Space, heatKernel ν t (x - y)) = 1 by
        calc
          ∫ y : Space, heatKernel ν t (x - y) = ∫ y : Space, heatKernel ν t (y - x) := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
            simpa using heatKernel_comm ν t x y
          _ = ∫ y : Space, heatKernel ν t y := by rw [integral_sub_right_eq_self _ x]
          _ = 1 := integral_heatKernel hν ht]
    _ = B := by ring

/-- **The heat flow of a partial classical solution's initial datum is bounded
by `B₀`.**  The composite of `initialDatum_continuous` and
`heatFlow_bounded_of_bounded`, in exactly the form the two far-field leaves
consume: it discharges the linear term `e^{tνΔ}u₀` of the Duhamel formula on
the whole initial layer, uniformly in `x`, from the hypothesis `hu₀` alone. -/
theorem heatFlow_initialDatum_bounded
    {ν : ℝ} (hν : 0 < ν) {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) {B₀ : ℝ}
    (hu₀ : ∀ x : Space, ‖u₀ x‖ ≤ B₀) :
    ∀ t : ℝ, 0 < t → ∀ x : Space,
      ‖∫ y : Space, heatKernel ν t (x - y) • u₀ y‖ ≤ B₀ :=
  fun _ ht x =>
    heatFlow_bounded_of_bounded hν ht (initialDatum_continuous sol).measurable hu₀ x

/-! ### Named residual leaves -/

/-- The Prodi--Serrin per-slice `L^p` hypothesis supplies the endpoint
domination required by
`WholeSpaceCutoffLimit.gaussianCutoffMomentumRhs_tendsto`.  Thus the complete
finite-cutoff tested PDE right-hand side has a genuine Gaussian limit on every
positive interior time interval.  What remains for Duhamel is termwise
identification and time-tail control, not existence of the combined cutoff
limit. -/
theorem prodiSerrin_gaussianCutoffMomentumRhs_tendsto
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {p : ℝ} (hp : 3 < p)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hbT : b < T)
    {τ : ℝ} (hτ : 0 < τ) (x₀ : Space) (j : Fin 3) :
    Filter.Tendsto (fun R : ℝ => cutoffMomentumCoordinateTimeRhs sol
        (fun y : Space => scaledCutoff R y * heatKernel ν τ (x₀ - y)) a b j)
      Filter.atTop (nhds
        ((∫ y : Space, heatKernel ν τ (x₀ - y) * sol.velocity b y j) -
          ∫ y : Space, heatKernel ν τ (x₀ - y) * sol.velocity a y j)) := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hcoord_pow : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun y : Space => |sol.velocity t y j| ^ p) := by
    intro t ht0 htT
    have hcomp : Continuous (fun y : Space => sol.velocity t y j) :=
      (continuous_apply j).comp
        (velocity_slice_contDiff sol ht0 htT).continuous
    apply (hint t ht0 htT).mono'
      (hcomp.abs.rpow_const (fun _ => Or.inr hp0.le)).aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _)
      (by simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (sol.velocity t y) j) hp0.le
  have hcoord_meas : ∀ t : ℝ, 0 ≤ t → t < T →
      Measurable (fun y : Space => sol.velocity t y j) := by
    intro t ht0 htT
    exact ((continuous_apply j).comp
      (velocity_slice_contDiff sol ht0 htT).continuous).measurable
  have hinta : Integrable (fun y : Space =>
      heatKernel ν τ (x₀ - y) * sol.velocity a y j) :=
    integrable_heatKernel_mul_of_integrable_rpow hν hτ
      (by linarith : 1 < p) (hcoord_pow a ha0.le (hab.trans_lt hbT))
      (hcoord_meas a ha0.le (hab.trans_lt hbT)) x₀
  have hintb : Integrable (fun y : Space =>
      heatKernel ν τ (x₀ - y) * sol.velocity b y j) :=
    integrable_heatKernel_mul_of_integrable_rpow hν hτ
      (by linarith : 1 < p) (hcoord_pow b (ha0.le.trans hab) hbT)
      (hcoord_meas b (ha0.le.trans hab) hbT) x₀
  exact gaussianCutoffMomentumRhs_tendsto sol ha0 hab hbT j ν τ x₀
    hinta hintb

/-- The Prodi--Serrin slice hypothesis makes the velocity square integrable
against every positive-time Gaussian translate.  This is the common majorant
for both pieces of the Gaussian-tested convection term. -/
theorem prodiSerrin_gaussianVelocitySq_integrable
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {p : ℝ} (hp : 3 < p)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    {τ : ℝ} (hτ : 0 < τ) (x₀ : Space) :
    Integrable (fun y : Space =>
      heatKernel ν τ (x₀ - y) * ‖sol.velocity t y‖ ^ 2) := by
  have hsqMeas : Measurable (fun y : Space => ‖sol.velocity t y‖ ^ 2) :=
    ((velocity_slice_contDiff sol ht0 htT).continuous.norm.pow 2).measurable
  have hsqPow : Integrable (fun y : Space =>
      |‖sol.velocity t y‖ ^ 2| ^ (p / 2)) := by
    apply (hint t ht0 htT).congr
    filter_upwards with y
    symm
    rw [abs_of_nonneg (sq_nonneg _), ← Real.rpow_natCast]
    rw [← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  exact integrable_heatKernel_mul_of_integrable_rpow hν hτ
    (by linarith : 1 < p / 2) hsqPow hsqMeas x₀

/-- The surviving Gaussian-gradient convection integrand is genuinely
integrable under the Prodi--Serrin slice hypothesis.  Its majorant is a
doubled-time Gaussian times `‖u(t,y)‖²`; no derivative decay of the solution is
assumed. -/
theorem prodiSerrin_gaussianGradientConvection_integrable
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {p : ℝ} (hp : 3 < p)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    {τ : ℝ} (hτ : 0 < τ) (x₀ : Space) (j : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ (fun z : Space => heatKernel ν τ (x₀ - z)) y
          (sol.velocity t y) * sol.velocity t y j) := by
  obtain ⟨C, hCpos, hgrad⟩ :=
    exists_abs_fderiv_heatKernel_translate_le_doubled hν hτ
  have hGaussianSq := prodiSerrin_gaussianVelocitySq_integrable hν sol hp hint
    ht0 htT (τ := 2 * τ) (by positivity) x₀
  have hmajor : Integrable (fun y : Space =>
      C * (heatKernel ν (2 * τ) (x₀ - y) * ‖sol.velocity t y‖ ^ 2)) :=
    hGaussianSq.const_mul C
  have huC : ContDiff ℝ ∞ (sol.velocity t) := velocity_slice_contDiff sol ht0 htT
  have hKC : ContDiff ℝ ∞ (fun y : Space => heatKernel ν τ (x₀ - y)) :=
    heatKernel_translate_contDiff ν τ x₀
  have hgradC : ContDiff ℝ ∞ (fun y : Space =>
      fderiv ℝ (fun z : Space => heatKernel ν τ (x₀ - z)) y
        (sol.velocity t y)) :=
    (hKC.fderiv_right (m := ∞) (by norm_num)).clm_apply huC
  have hujC : Continuous (fun y : Space => sol.velocity t y j) :=
    (continuous_apply j).comp huC.continuous
  apply hmajor.mono' (hgradC.continuous.mul hujC).aestronglyMeasurable
  filter_upwards with y
  have hG2 : 0 ≤ heatKernel ν (2 * τ) (x₀ - y) :=
    heatKernel_nonneg hν (by positivity) _
  have hj : |sol.velocity t y j| ≤ ‖sol.velocity t y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (sol.velocity t y) j
  calc
    ‖fderiv ℝ (fun z : Space => heatKernel ν τ (x₀ - z)) y
          (sol.velocity t y) * sol.velocity t y j‖ =
        |fderiv ℝ (fun z : Space => heatKernel ν τ (x₀ - z)) y
          (sol.velocity t y)| * |sol.velocity t y j| := by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (C * heatKernel ν (2 * τ) (x₀ - y) * ‖sol.velocity t y‖) *
          ‖sol.velocity t y‖ :=
      mul_le_mul (hgrad x₀ y (sol.velocity t y)) hj (abs_nonneg _)
        (mul_nonneg (mul_nonneg hCpos.le hG2) (norm_nonneg _))
    _ = C * (heatKernel ν (2 * τ) (x₀ - y) * ‖sol.velocity t y‖ ^ 2) := by
      ring

/-- Removing the scaled cutoff from the surviving Gaussian-gradient
convection term.  This is the second term in the product-rule expansion of
`D(χ_R G)(u) u_j`; the first term tends to zero in
`prodiSerrin_gaussianCutoffConvectionTail_tendsto_zero`. -/
theorem prodiSerrin_gaussianGradientConvection_tendsto
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {p : ℝ} (hp : 3 < p)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    {τ : ℝ} (hτ : 0 < τ) (x₀ : Space) (j : Fin 3) :
    Filter.Tendsto (fun R : ℝ => ∫ y : Space,
        scaledCutoff R y *
          (fderiv ℝ (fun z : Space => heatKernel ν τ (x₀ - z)) y
            (sol.velocity t y) * sol.velocity t y j))
      Filter.atTop (nhds (∫ y : Space,
        fderiv ℝ (fun z : Space => heatKernel ν τ (x₀ - z)) y
          (sol.velocity t y) * sol.velocity t y j)) :=
  scaledCutoff_integral_tendsto _
    (prodiSerrin_gaussianGradientConvection_integrable hν sol hp hint
      ht0 htT hτ x₀ j)

/-- The Prodi--Serrin spatial hypothesis closes the convective
first-derivative cutoff tail in the Gaussian-tested momentum balance:

`∫ Dχ_R(u(t)) G^ν_τ(x₀-·) u_j(t) → 0`.

Indeed `p > 3` makes the Gaussian-weighted velocity square integrable, and
the concrete scaled cutoff contributes the sharp `R⁻¹` derivative decay.
This removes the `Dχ_R` part of the convection limit; the theorem below
composes it with the surviving `χ_R DG(u)u_j` limit. -/
theorem prodiSerrin_gaussianCutoffConvectionTail_tendsto_zero
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {p : ℝ} (hp : 3 < p)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    {τ : ℝ} (hτ : 0 < τ) (x₀ : Space) (j : Fin 3) :
    Filter.Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ (scaledCutoff R) y (sol.velocity t y) *
          (heatKernel ν τ (x₀ - y) * sol.velocity t y j))
      Filter.atTop (nhds 0) := by
  have hGaussianSq : Integrable (fun y : Space =>
      heatKernel ν τ (x₀ - y) * ‖sol.velocity t y‖ ^ 2) :=
    prodiSerrin_gaussianVelocitySq_integrable hν sol hp hint ht0 htT hτ x₀
  apply scaledCutoff_fderiv_remainder_tendsto_zero
    (v := sol.velocity t)
    (f := fun y : Space =>
      heatKernel ν τ (x₀ - y) * sol.velocity t y j)
    (h := fun y : Space =>
      heatKernel ν τ (x₀ - y) * ‖sol.velocity t y‖ ^ 2)
    hGaussianSq
  intro y
  have hG : 0 ≤ heatKernel ν τ (x₀ - y) := heatKernel_nonneg hν hτ _
  have hj : |sol.velocity t y j| ≤ ‖sol.velocity t y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (sol.velocity t y) j
  calc
    ‖sol.velocity t y‖ *
        |heatKernel ν τ (x₀ - y) * sol.velocity t y j|
        = ‖sol.velocity t y‖ *
            (heatKernel ν τ (x₀ - y) * |sol.velocity t y j|) := by
              rw [abs_mul, abs_of_nonneg hG]
    _ ≤ ‖sol.velocity t y‖ *
          (heatKernel ν τ (x₀ - y) * ‖sol.velocity t y‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hj hG) (norm_nonneg _)
    _ = heatKernel ν τ (x₀ - y) * ‖sol.velocity t y‖ ^ 2 := by ring

/-- Exact product-rule decomposition of the Gaussian cutoff convection
integrand.  This is the pointwise identity connecting the two termwise limits
below to the convection slot in the finite-cutoff momentum balance. -/
theorem gaussianCutoff_convection_product_rule
    (R ν τ : ℝ) (x₀ y v : Space) (a : ℝ) :
    fderiv ℝ (fun z : Space =>
      scaledCutoff R z * heatKernel ν τ (x₀ - z)) y v * a =
      fderiv ℝ (scaledCutoff R) y v * (heatKernel ν τ (x₀ - y) * a) +
      scaledCutoff R y *
        (fderiv ℝ (fun z : Space => heatKernel ν τ (x₀ - z)) y v * a) := by
  change fderiv ℝ (scaledCutoff R *
    (fun z : Space => heatKernel ν τ (x₀ - z))) y v * a = _
  rw [fderiv_mul
    ((scaledCutoff_contDiff R).differentiable (by norm_num) y)
    ((heatKernel_translate_contDiff ν τ x₀).differentiable (by norm_num) y)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The complete product-rule split of the finite-cutoff convection term has
the Gaussian-gradient limit.  The first integral is the `Dχ_R` remainder and
vanishes; the second is the `χ_R DG` term and converges by its doubled-Gaussian
`‖u‖²` majorant.  Thus this theorem consumes both analytic leaves and exposes
the actual termwise convection limit used by the Gaussian momentum balance. -/
theorem prodiSerrin_gaussianConvectionSplit_tendsto
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {p : ℝ} (hp : 3 < p)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    {τ : ℝ} (hτ : 0 < τ) (x₀ : Space) (j : Fin 3) :
    Filter.Tendsto (fun R : ℝ =>
        (∫ y : Space,
          fderiv ℝ (scaledCutoff R) y (sol.velocity t y) *
            (heatKernel ν τ (x₀ - y) * sol.velocity t y j)) +
        ∫ y : Space, scaledCutoff R y *
          (fderiv ℝ (fun z : Space => heatKernel ν τ (x₀ - z)) y
            (sol.velocity t y) * sol.velocity t y j))
      Filter.atTop (nhds (∫ y : Space,
        fderiv ℝ (fun z : Space => heatKernel ν τ (x₀ - z)) y
          (sol.velocity t y) * sol.velocity t y j)) := by
  have htail := prodiSerrin_gaussianCutoffConvectionTail_tendsto_zero
    hν sol hp hint ht0 htT hτ x₀ j
  have hgradient := prodiSerrin_gaussianGradientConvection_tendsto
    hν sol hp hint ht0 htT hτ x₀ j
  simpa only [zero_add] using htail.add hgradient

/-! ### The Duhamel correction

The source `duhamelSource` and correction `duhamelNonlinear` below are explicit
integrals of the convection, pressure gradient and heat kernel.
`layerBound_of_duhamelNonlinear_bounded` combines a representation using this
specific correction with a uniform bound on it. Proving the representation
for an arbitrary solution still requires the analytic cutoff-limit argument.
-/

/-- **The Navier–Stokes Duhamel source** `−((u·∇)u + ∇p)`.  This is the
momentum equation read as a forced heat equation `∂ₜu − νΔu = duhamelSource`;
every ingredient is estate-defined (`Navier.convection`,
`Navier.pressureGradient`), so no Leray projector and no opaque carrier
appears. -/
def duhamelSource {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) (s : ℝ) (y : Space) : Space :=
  f s y - (convection sol.velocity s y + pressureGradient sol.pressure s y)

/-- **The Duhamel nonlinear correction**

  `N(t,x) = ∫₀ᵗ ∫_{ℝ³} G^ν_{t−s}(x−y) · duhamelSource(s,y) dy ds`,

the variation-of-constants term of the mild formulation.  Concretely defined,
hence a real carrier: the residual leaves below are estimates *about this
integral*, not restatements of the conclusion they support. -/
def duhamelNonlinear {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) (t : ℝ) (x : Space) : Space :=
  ∫ s in (0 : ℝ)..t,
    (∫ y : Space, heatKernel ν (t - s) (x - y) • duhamelSource sol s y)

/-- **The layer bound reduces to a bound on the Duhamel correction alone.**

Given the variation-of-constants representation on `(0,δ]` and a uniform bound
`C` on the nonlinear correction there, the solution is bounded by `B₀ + C` on
the *whole* closed layer `[0,δ]` and on *all* of space — strictly stronger than
the far-field conclusion the two layer leaves need, which is why they can both
consume it with `ϱ = 0`.

The linear half is `heatFlow_initialDatum_bounded` (kernel-clean, already in
this file): the heat flow of a `B₀`-bounded datum is `B₀`-bounded because the
kernel is nonnegative with unit mass.  The `t = 0` endpoint is
`sol.initial_condition`.  Nothing here is conditional on `L^p` or `L²` data —
those enter only in the estimate on `duhamelNonlinear`. -/
theorem layerBound_of_duhamelNonlinear_bounded
    {ν : ℝ} (hν : 0 < ν) {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) {B₀ : ℝ}
    (hu₀ : ∀ x : Space, ‖u₀ x‖ ≤ B₀)
    {δ : ℝ} (hδ0 : 0 < δ)
    (hrep : ∀ t : ℝ, 0 < t → t ≤ δ → ∀ x : Space,
      sol.velocity t x
        = (∫ y : Space, heatKernel ν t (x - y) • u₀ y) + duhamelNonlinear sol t x)
    {C : ℝ} (hC : ∀ t : ℝ, 0 < t → t ≤ δ → ∀ x : Space,
      ‖duhamelNonlinear sol t x‖ ≤ C) :
    ∃ ϱ R : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ δ → ∀ x : Space,
      ϱ ≤ ‖x‖ → ‖sol.velocity t x‖ ≤ R := by
  have hheat0 : ∀ t : ℝ, 0 < t → ∀ x : Space,
      ‖∫ y : Space, heatKernel ν t (x - y) • u₀ y‖ ≤ B₀ :=
    heatFlow_initialDatum_bounded hν sol hu₀
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hC (δ / 2) (by linarith) (by linarith) 0)
  have hB0 : 0 ≤ B₀ := le_trans (norm_nonneg _) (hu₀ 0)
  refine ⟨0, B₀ + C, fun t ht0 htδ x _ => ?_⟩
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · have : sol.velocity t x = u₀ x := by
      rw [← h0, sol.initial_condition]
    rw [this]
    exact le_trans (hu₀ x) (by linarith)
  · rw [hrep t hpos htδ x]
    exact le_trans (norm_add_le _ _)
      (add_le_add (hheat0 t hpos x) (hC t hpos htδ x))

/-- If a partial solution's velocity vanishes identically, its momentum
equation forces the exact Duhamel source to vanish throughout the solution
interval.  Pressure and forcing may be nonzero separately, but cancel in the
source as the equation requires. -/
theorem duhamelSource_eq_zero_of_velocity_eq_zero
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (hvelocity : sol.velocity = (0 : VelocityEvolution))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) (x : Space) :
    duhamelSource sol t x = 0 := by
  have heq := sol.equation t ht0 htT x
  rw [hvelocity] at heq
  unfold duhamelSource
  rw [hvelocity]
  simp [timeDerivative, convection, spatialDerivative, laplacian] at heq ⊢
  simpa [sub_eq_add_neg, add_comm] using heq.symm

/-- The variation-of-constants identity is explicit in the homogeneous zero
velocity case.  The initial datum and Duhamel source are both forced to vanish
by fields already present in `PartialClassicalSolution`; no semigroup theorem
or added representation hypothesis is used. -/
theorem duhamelRepresentation_layer_of_velocity_eq_zero
    {ν : ℝ} (_hν : 0 < ν) {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (hvelocity : sol.velocity = (0 : VelocityEvolution))
    {δ : ℝ} (_hδ0 : 0 < δ) (hδT : δ < T) :
    ∀ t : ℝ, 0 < t → t ≤ δ → ∀ x : Space,
      sol.velocity t x
        = (∫ y : Space, heatKernel ν t (x - y) • u₀ y)
          + duhamelNonlinear sol t x := by
  have hu₀ : u₀ = (0 : VelocityField) := by
    rw [← sol.initial_condition, hvelocity]
    rfl
  intro t ht0 htδ x
  rw [hvelocity]
  change 0 = (∫ y : Space, heatKernel ν t (x - y) • u₀ y) +
    duhamelNonlinear sol t x
  have hheat : (∫ y : Space, heatKernel ν t (x - y) • u₀ y) = 0 := by
    rw [hu₀]
    simp
  rw [hheat, zero_add]
  symm
  unfold duhamelNonlinear
  apply intervalIntegral.integral_zero_ae
  exact Filter.Eventually.of_forall fun s hs ↦ by
    rw [Set.uIoc_of_le ht0.le] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hsT : s < T := lt_of_le_of_lt (le_trans hs.2 htδ) hδT
    simp_rw [duhamelSource_eq_zero_of_velocity_eq_zero sol hvelocity hs0 hsT]
    simp


/-- Every zero-force Duhamel source slice strictly before the terminal time is
spatially `C∞`.  Thus the measurability premise of the general `L^r` Duhamel
estimate is automatic for a partial classical solution; only integrability and
the quantitative source bound remain analytic inputs. -/
theorem duhamelSource_slice_contDiff
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    ContDiff ℝ ∞ (duhamelSource sol t) := by
  have hu : ContDiff ℝ ∞ (sol.velocity t) :=
    velocity_slice_contDiff sol ht0 htT
  have hp : ContDiff ℝ ∞ (sol.pressure t) :=
    pressure_slice_contDiff sol ht0 htT
  have hconvection : ContDiff ℝ ∞ (convection sol.velocity t) := by
    change ContDiff ℝ ∞
      (fun x ↦ fderiv ℝ (sol.velocity t) x (sol.velocity t x))
    exact (hu.fderiv_right (by simp)).clm_apply hu
  have hpressure : ContDiff ℝ ∞ (pressureGradient sol.pressure t) := by
    change ContDiff ℝ ∞
      (fun x ↦ fun i ↦ fderiv ℝ (sol.pressure t) x (basisVector i))
    refine contDiff_pi.2 fun i ↦ ?_
    exact (hp.fderiv_right (by simp)).clm_apply contDiff_const
  change ContDiff ℝ ∞ (fun x ↦
    zeroForce t x - (convection sol.velocity t x + pressureGradient sol.pressure t x))
  simpa only [zeroForce] using contDiff_const.sub (hconvection.add hpressure)

/-- Spatial measurability of the zero-force Duhamel source, obtained from the
actual solution smoothness rather than carried as an extra hypothesis. -/
theorem duhamelSource_slice_measurable
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    Measurable (duhamelSource sol t) :=
  (duhamelSource_slice_contDiff sol ht0 htT).continuous.measurable

/-- The spatial `L²` mass of convection has scaling weight `+3` under the
Navier--Stokes parabolic dilation.  This is the quantitative obstruction behind
the missing source bound: velocity energy has weight `-1`, while convection
grows at weight `+3`. -/
theorem convectionL2Mass_parabolicScaled
    (c : ℝ) (hc : 0 < c) (u : VelocityEvolution) (t : ℝ) :
    (∫ x : Space, ‖convection
        (Navier.Analysis.Covariance.parabolicScaledVelocity c u) t x‖ ^ 2) =
      c ^ 3 * ∫ x : Space, ‖convection u (c ^ 2 * t) x‖ ^ 2 := by
  simp_rw [Navier.Analysis.Covariance.convection_scaled]
  let g : Space → Space := fun x ↦ convection u (c ^ 2 * t) x
  change (∫ x : Space, ‖c ^ 3 • g (c • x)‖ ^ 2) =
    c ^ 3 * ∫ x : Space, ‖g x‖ ^ 2
  have hnorm : ∀ y : Space, ‖c ^ 3 • g y‖ ^ 2 =
      c ^ 6 • ‖g y‖ ^ 2 := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hc 3)]
    simp only [smul_eq_mul]
    ring
  have hscale : 0 < (c ^ 3)⁻¹ := by positivity
  simp_rw [hnorm]
  rw [integral_smul]
  rw [MeasureTheory.Measure.integral_comp_smul volume
    (fun x ↦ ‖g x‖ ^ 2) c]
  simp only [Module.finrank_fin_fun, abs_of_pos hscale, smul_eq_mul]
  field_simp

/-- **Energy-only convection control is scale-impossible.**  Starting from
any slice with positive convection `L²` mass, parabolic dilation can keep the
velocity `L²` mass below its original value while making the convection mass
exceed any prescribed number. A uniform source estimate therefore requires
more information than the velocity energy bracket alone. -/
theorem energyBound_cannot_control_convectionL2
    (u : VelocityEvolution)
    (hconv : 0 < ∫ x : Space, ‖convection u 0 x‖ ^ 2) :
    ∀ K : ℝ, ∃ c : ℝ, 0 < c ∧
      (∫ x : Space,
          ‖Navier.Analysis.Covariance.parabolicScaledVelocity c u 0 x‖ ^ 2) ≤
        ∫ x : Space, ‖u 0 x‖ ^ 2 ∧
      K < ∫ x : Space, ‖convection
        (Navier.Analysis.Covariance.parabolicScaledVelocity c u) 0 x‖ ^ 2 := by
  intro K
  let A : ℝ := ∫ x : Space, ‖convection u 0 x‖ ^ 2
  let c : ℝ := max 1 (K / A + 1)
  have hA : 0 < A := hconv
  have hc1 : 1 ≤ c := le_max_left _ _
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  refine ⟨c, hc, ?_, ?_⟩
  · change (∫ x : Space, ‖c • u (c ^ 2 * 0) (c • x)‖ ^ 2) ≤
      ∫ x : Space, ‖u 0 x‖ ^ 2
    simp only [mul_zero]
    rw [Navier.EnergyObstruction.l2_energy_dilation c hc (u 0)]
    simp only [smul_eq_mul]
    rw [← div_eq_inv_mul]
    apply (div_le_iff₀ hc).2
    have hmass : 0 ≤ ∫ x : Space, ‖u 0 x‖ ^ 2 :=
      integral_nonneg fun x ↦ sq_nonneg ‖u 0 x‖
    nlinarith
  · rw [convectionL2Mass_parabolicScaled c hc u 0]
    simp only [mul_zero]
    have hKc : K < c * A := by
      apply (div_lt_iff₀ hA).1
      exact lt_of_lt_of_le (lt_add_one (K / A)) (le_max_right _ _)
    have hcubic : c ≤ c ^ 3 := by
      have hfac : 0 ≤ (c - 1) * (c ^ 2 + c) :=
        mul_nonneg (by linarith) (by nlinarith [sq_nonneg c])
      nlinarith
    change K < c ^ 3 * A
    exact hKc.trans_le (mul_le_mul_of_nonneg_right hcubic hA.le)

/-! ### The heat-smoothing half of the Duhamel estimate, discharged

The two `duhamelNonlinear_bounded_of_*` leaves below were each described as a
`~250 LOC` estimate whose route is "`L^r → L^∞` heat smoothing, integrated in
`s` against the slice norm".  That whole route is now a *theorem*
(`duhamelNonlinear_bounded_of_source_Lr`), kernel-clean, with the two
supporting facts it needs also proved here:

* `intervalIntegral_sub_rpow_neg` — the time integral
  `∫₀ᵗ (t−s)^{−a} ds = t^{1−a}/(1−a)` for `a < 1`.  The docstrings previously
  asserted in prose that "the exponent condition is exactly what makes
  `∫₀ᵗ (t−s)^{−3/(2r)}‖F(s)‖_r ds` converge"; this is that sentence, checked.
* `heatKernel_convolution_norm_vec_le_uniform` — the vector-valued `L^r → L^∞`
  smoothing bound with the constant hoisted ABOVE the field.  The existing
  `HeatSemigroupSmoothing.heatKernel_convolution_norm_vec_le` puts `∃ C` *after*
  fixing `f`, so it cannot be applied to the family `s ↦ duhamelSource sol s`
  and produce one constant; hoisting is what makes the time integration
  possible at all, and the constant really is field-independent because it
  comes from `heatKernel_Lr_scaling`.

What is left of the two leaves after this is exactly an `L^r` bound on the
*source* `duhamelSource sol s = f − ((u·∇)u + ∇p)` uniformly on the layer,
i.e. `L^r` control of `(u·∇)u` and of `∇p` — plus two side conditions
(slice measurability, and interval-integrability in `s` of the inner
convolution's norm).  No heat-semigroup, Young, or time-integrability
mathematics remains in them. -/

/-- **The Duhamel time integral (certified, no `sorry`).**  For `a < 1`,

  `∫₀ᵗ (t − s)^{−a} ds = t^{1−a} / (1 − a)`.

This is the convergence the Prodi–Serrin exponent condition buys: with
`a = 3/(2r)` the integral is finite exactly when `r > 3/2`. -/
theorem intervalIntegral_sub_rpow_neg {t a : ℝ} (ha1 : a < 1) :
    (∫ s in (0 : ℝ)..t, (t - s) ^ (-a)) = t ^ (1 - a) / (1 - a) := by
  have h1 : (∫ s in (0 : ℝ)..t, (t - s) ^ (-a)) = ∫ u in (t - t)..(t - 0), u ^ (-a) := by
    rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-a)) t]
  rw [h1]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith))]
  have h0 : (0 : ℝ) ^ (-a + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0]
  have h2 : -a + 1 = 1 - a := by ring
  rw [h2]
  ring

/-- **Interval integrability of the Duhamel time weight (certified, no
`sorry`).**  `s ↦ (t − s)^{−a}` is interval integrable on `[0,t]` whenever
`−1 < −a`. -/
theorem intervalIntegrable_sub_rpow_neg {t a : ℝ} (ha : -1 < -a) :
    IntervalIntegrable (fun s : ℝ => (t - s) ^ (-a)) volume 0 t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := t) (b := 0) ha).comp_sub_left t
  simpa using h

/-- **`L^r → L^∞` heat smoothing, vector valued, with the constant hoisted
above the field (certified, no `sorry`).**  For `r > 1` there is one
`C = C(r,ν) > 0` such that for *every* measurable `g` with `‖g‖^r` integrable,
every `t > 0` and every `x`,

  `‖∫ G^ν_t(x−y) • g(y) dy‖ ≤ C · t^{−3/(2r)} · ‖g‖_{L^r}`.

The quantifier order is the whole point (`epistemic-rigor.md` §"Quantifier
order is a satisfiability question").  `HeatSemigroupSmoothing.
heatKernel_convolution_norm_vec_le` states the same bound with `∃ C` *inside*
the scope of `f`, which cannot be integrated in time against a moving slice.
The constant is genuinely field-independent: it is the one produced by
`heatKernel_Lr_scaling`, a statement about the kernel alone. -/
theorem heatKernel_convolution_norm_vec_le_uniform {ν : ℝ} (hν : 0 < ν) {r : ℝ}
    (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Space → Space, Measurable g →
      Integrable (fun y : Space => ‖g y‖ ^ r) →
      ∀ t : ℝ, 0 < t → ∀ x : Space,
        ‖∫ y : Space, heatKernel ν t (x - y) • g y‖
          ≤ C * t ^ (-(3 : ℝ) / (2 * r)) * (∫ y : Space, ‖g y‖ ^ r) ^ (1 / r) := by
  obtain ⟨C, hC0, hC⟩ := heatKernel_Lr_scaling hν hr
  refine ⟨C, hC0, fun g hgm hgr t ht x => ?_⟩
  have hgnorm : Measurable (fun y : Space => ‖g y‖) := hgm.norm
  have hgnorm_int : Integrable (fun y : Space => |‖g y‖| ^ r) :=
    hgr.congr (Filter.Eventually.of_forall (fun y => by simp))
  have h_nonneg_int : 0 ≤ ∫ y : Space, heatKernel ν t (x - y) * ‖g y‖ :=
    integral_nonneg (fun y => mul_nonneg (heatKernel_nonneg hν ht (x - y)) (norm_nonneg _))
  calc
    ‖∫ y : Space, heatKernel ν t (x - y) • g y‖
        ≤ ∫ y : Space, ‖heatKernel ν t (x - y) • g y‖ := norm_integral_le_integral_norm _
    _ = ∫ y : Space, heatKernel ν t (x - y) * ‖g y‖ := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hν ht (x - y))]
    _ = |∫ y : Space, heatKernel ν t (x - y) * ‖g y‖| := by rw [abs_of_nonneg h_nonneg_int]
    _ ≤ (∫ y : Space, heatKernel ν t y ^ (r / (r - 1))) ^ ((r - 1) / r) *
          (∫ y : Space, |‖g y‖| ^ r) ^ (1 / r) :=
        heatKernel_convolution_abs_le hν ht hr hgnorm_int hgnorm x
    _ = C * t ^ (-(3 : ℝ) / (2 * r)) * (∫ y : Space, ‖g y‖ ^ r) ^ (1 / r) := by
        rw [hC t ht]; simp

/-- **[THEOREM — the Duhamel correction is bounded on the layer as soon as the
SOURCE is bounded in `L^r`, `r > 3/2`.]**  No `sorry`, no axiom beyond the
Mathlib triple.

  `‖N(t,x)‖ ≤ C₀(r,ν) · S · δ^{1−3/(2r)} / (1 − 3/(2r))`   for `0 < t ≤ δ`,

where `S` bounds the `L^r` norms of `duhamelSource sol s` on the layer.

This is an `L^r → L^∞` smoothing and time-integration estimate. The threshold
`r > 3/2` is exactly
`3/(2r) < 1`, the condition under which `intervalIntegral_sub_rpow_neg`
converges, and the Prodi–Serrin exponent `p > 3` sits strictly above it.

Statement hygiene.  `S` bounds the norm of `duhamelSource`, which is a
*definition* (`f − ((u·∇)u + ∇p)`), not a parameter — so this is not the
conclusion in disguise: nothing here says anything about `sol.velocity`, and a
bound on the source is a genuinely different (and strictly lower) object than a
bound on the Duhamel integral of the source.  `hNint` is a measurability-class
side condition on one explicitly written function, not an estimate.

Reference for the classical statement: Kato, Math. Z. 187 (1984) 471–480, §2;
Giga–Miyakawa, Arch. Ration. Mech. Anal. 89 (1985) 267–281. -/
theorem duhamelNonlinear_bounded_of_source_Lr {ν : ℝ} (hν : 0 < ν) {f : ForceField}
    {u₀ : VelocityField} {T : ℝ} (sol : PartialClassicalSolution ν f u₀ T)
    {δ : ℝ} (hδ0 : 0 < δ)
    {r : ℝ} (hr : 3 / 2 < r)
    (hsm : ∀ s : ℝ, 0 ≤ s → s ≤ δ → Measurable (duhamelSource sol s))
    (hsi : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      Integrable (fun y : Space => ‖duhamelSource sol s y‖ ^ r))
    (S : ℝ) (hS : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      (∫ y : Space, ‖duhamelSource sol s y‖ ^ r) ^ (1 / r) ≤ S)
    (hNint : ∀ t : ℝ, 0 < t → t ≤ δ → ∀ x : Space,
      IntervalIntegrable
        (fun s : ℝ => ‖∫ y : Space, heatKernel ν (t - s) (x - y) • duhamelSource sol s y‖)
        volume 0 t) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ δ → ∀ x : Space,
      ‖duhamelNonlinear sol t x‖ ≤ C := by
  have hr1 : (1 : ℝ) < r := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 3 / (2 * r) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have ha1 : a < 1 := by
    rw [ha_def, div_lt_one (by positivity)]
    linarith
  have hna : -(3 : ℝ) / (2 * r) = -a := by rw [ha_def]; ring
  obtain ⟨C₀, hC₀0, hC₀⟩ := heatKernel_convolution_norm_vec_le_uniform (ν := ν) hν hr1
  have hS0 : 0 ≤ S := by
    refine le_trans ?_ (hS 0 le_rfl hδ0.le)
    exact Real.rpow_nonneg (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _) _
  refine ⟨C₀ * S * (δ ^ (1 - a) / (1 - a)), fun t ht0 htδ x => ?_⟩
  have hIIrhs : IntervalIntegrable (fun s : ℝ => C₀ * S * (t - s) ^ (-a)) volume 0 t :=
    (intervalIntegrable_sub_rpow_neg (t := t) (a := a) (by linarith)).const_mul _
  have hunfold : duhamelNonlinear sol t x
      = ∫ s in (0 : ℝ)..t,
          (∫ y : Space, heatKernel ν (t - s) (x - y) • duhamelSource sol s y) := rfl
  have hkey : ‖duhamelNonlinear sol t x‖
      ≤ ∫ s in (0 : ℝ)..t, C₀ * S * (t - s) ^ (-a) := by
    rw [hunfold]
    calc ‖∫ s in (0 : ℝ)..t,
            (∫ y : Space, heatKernel ν (t - s) (x - y) • duhamelSource sol s y)‖
        ≤ ∫ s in (0 : ℝ)..t,
            ‖∫ y : Space, heatKernel ν (t - s) (x - y) • duhamelSource sol s y‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht0.le
      _ ≤ ∫ s in (0 : ℝ)..t, C₀ * S * (t - s) ^ (-a) := by
          refine intervalIntegral.integral_mono_on_of_le_Ioo ht0.le
            (hNint t ht0 htδ x) hIIrhs ?_
          intro s hs
          have hs0 : 0 ≤ s := le_of_lt hs.1
          have hsδ : s ≤ δ := le_trans hs.2.le htδ
          have hts : 0 < t - s := by linarith [hs.2]
          have hb := hC₀ (duhamelSource sol s) (hsm s hs0 hsδ) (hsi s hs0 hsδ) (t - s) hts x
          rw [hna] at hb
          refine hb.trans ?_
          have hpow : (0 : ℝ) ≤ (t - s) ^ (-a) := Real.rpow_nonneg hts.le _
          have hSs := hS s hs0 hsδ
          calc C₀ * (t - s) ^ (-a) *
                (∫ y : Space, ‖duhamelSource sol s y‖ ^ r) ^ (1 / r)
              ≤ C₀ * (t - s) ^ (-a) * S :=
                mul_le_mul_of_nonneg_left hSs (by positivity)
            _ = C₀ * S * (t - s) ^ (-a) := by ring
  refine hkey.trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral_sub_rpow_neg ha1]
  have hmono : t ^ (1 - a) ≤ δ ^ (1 - a) :=
    Real.rpow_le_rpow ht0.le htδ (by linarith)
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hCS : (0 : ℝ) ≤ C₀ * S := by positivity
  gcongr

/-- Joint interior continuity of the actual zero-force momentum source.
Spatial derivatives depend continuously on time because the velocity and
pressure are smooth in space-time. -/
theorem duhamelSource_continuousAt_interior
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {z : ℝ × Space} (hz : z.1 ∈ Ioo 0 T) :
    ContinuousAt (fun z : ℝ × Space => duhamelSource sol z.1 z.2) z := by
  have hnhds : spacetimeBefore T ∈ nhds z := by
    have hsub : Ioo 0 T ×ˢ (univ : Set Space) ⊆ spacetimeBefore T := by
      intro p hp
      exact ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩
    exact Filter.mem_of_superset
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩) hsub
  have hu : ContDiffAt ℝ ∞ (fun z : ℝ × Space => sol.velocity z.1 z.2) z :=
    sol.velocity_smooth.contDiffAt hnhds
  have hp : ContDiffAt ℝ ∞ (fun z : ℝ × Space => sol.pressure z.1 z.2) z :=
    sol.pressure_smooth.contDiffAt hnhds
  have hdu : ContDiffAt ℝ 0
      (fun z : ℝ × Space => fderiv ℝ (sol.velocity z.1) z.2) z := by
    apply ContDiffAt.fderiv (n := ∞) (g := fun z : ℝ × Space => z.2)
    · exact hu.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    · exact contDiffAt_snd
    · simp
  have hdp : ContDiffAt ℝ 0
      (fun z : ℝ × Space => fderiv ℝ (sol.pressure z.1) z.2) z := by
    apply ContDiffAt.fderiv (n := ∞) (g := fun z : ℝ × Space => z.2)
    · exact hp.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    · exact contDiffAt_snd
    · simp
  have hcon : ContinuousAt
      (fun z : ℝ × Space => convection sol.velocity z.1 z.2) z :=
    hdu.continuousAt.clm_apply hu.continuousAt
  have hgrad : ContinuousAt
      (fun z : ℝ × Space => pressureGradient sol.pressure z.1 z.2) z := by
    apply continuousAt_pi.2
    intro i
    exact hdp.continuousAt.clm_apply continuousAt_const
  exact continuousAt_const.sub (hcon.add hgrad)

/-- The vector heat convolution exists as a Bochner integral whenever its
source lies in `L^r`, for `r > 1`. Scalar Hölder integrability dominates the
actual vector integrand. -/
theorem heatKernel_smul_integrable_of_integrable_rpow
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) {r : ℝ} (hr : 1 < r)
    {g : Space → Space} (hgm : Measurable g)
    (hgr : Integrable (fun y : Space => ‖g y‖ ^ r)) (x : Space) :
    Integrable (fun y : Space => heatKernel ν t (x - y) • g y) := by
  have hK : Continuous (fun y : Space => heatKernel ν t (x - y)) := by
    unfold heatKernel
    fun_prop
  have hint := integrable_heatKernel_mul_of_integrable_rpow hν ht hr
    (by simpa only [abs_norm] using hgr) hgm.norm x
  apply hint.mono' (hK.aestronglyMeasurable.smul hgm.aestronglyMeasurable)
  filter_upwards [] with y
  rw [Pi.smul_apply', norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (heatKernel_nonneg hν ht _)]

/-- Both integrals defining the Duhamel convolution exist under a uniform
source `L^r` bound, for `r > 3/2`. Joint source continuity supplies parameter
measurability; the heat estimate is dominated by `(t-s)^(-3/(2r))`. The
spatial integral exists at every interior time, and the resulting vector
function is integrable in time.

Reference: Kato, Math. Z. 187 (1984), Section 2. -/
theorem duhamelConvolution_integrable_of_source_Lr
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {δ : ℝ} (hδT : δ < T) {r : ℝ} (hr : 3 / 2 < r)
    (hsi : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      Integrable (fun y : Space => ‖duhamelSource sol s y‖ ^ r))
    (S : ℝ) (hS : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      (∫ y : Space, ‖duhamelSource sol s y‖ ^ r) ^ (1 / r) ≤ S)
    {t : ℝ} (ht0 : 0 < t) (htδ : t ≤ δ) (x : Space) :
    (∀ s ∈ Ioo 0 t, Integrable (fun y : Space =>
      heatKernel ν (t - s) (x - y) • duhamelSource sol s y)) ∧
      IntervalIntegrable
        (fun s : ℝ => ∫ y : Space,
          heatKernel ν (t - s) (x - y) • duhamelSource sol s y) volume 0 t := by
  have hspace : ∀ s ∈ Ioo 0 t, Integrable (fun y : Space =>
      heatKernel ν (t - s) (x - y) • duhamelSource sol s y) := by
    intro s hs
    have hsδ : s ≤ δ := hs.2.le.trans htδ
    exact heatKernel_smul_integrable_of_integrable_rpow hν
      (sub_pos.mpr hs.2) (by linarith : 1 < r)
      (duhamelSource_slice_measurable sol hs.1.le (hsδ.trans_lt hδT))
      (hsi s hs.1.le hsδ) x
  refine ⟨hspace, ?_⟩
  have hF : ContinuousOn
      (fun z : ℝ × Space =>
        heatKernel ν (t - z.1) (x - z.2) • duhamelSource sol z.1 z.2)
      (Ioo 0 t ×ˢ univ) := by
    intro z hz
    have hts : 0 < t - z.1 := sub_pos.mpr hz.1.2
    have hK : ContinuousAt
        (fun z : ℝ × Space => heatKernel ν (t - z.1) (x - z.2)) z := by
      unfold heatKernel
      have htime : ContinuousAt (fun z : ℝ × Space => t - z.1) z :=
        continuousAt_const.sub continuousAt_fst
      have hbase : ContinuousAt
          (fun z : ℝ × Space => 4 * Real.pi * ν * (t - z.1)) z :=
        continuousAt_const.mul htime
      have hpow := hbase.rpow_const (p := -(3 : ℝ) / 2)
        (Or.inl (by positivity : 4 * Real.pi * ν * (t - z.1) ≠ 0))
      have hinv := (continuousAt_const.mul htime).inv₀
        (by positivity : 4 * ν * (t - z.1) ≠ 0)
      have hsum : Continuous
          (fun z : ℝ × Space => ∑ i : Fin 3, (x i - z.2 i) ^ 2) := by
        fun_prop
      exact hpow.mul (Real.continuous_exp.continuousAt.comp
        (hinv.neg.mul hsum.continuousAt))
    exact (hK.smul (duhamelSource_continuousAt_interior sol
      ⟨hz.1.1, (hz.1.2.trans_le htδ).trans hδT⟩)).continuousWithinAt
  have hmeas := hF.aestronglyMeasurable (μ := volume.prod volume)
    (measurableSet_Ioo.prod MeasurableSet.univ)
  rw [← Measure.restrict_prod_eq_prod_univ] at hmeas
  have him := hmeas.integral_prod_right'
  obtain ⟨C, hCpos, hC⟩ := heatKernel_convolution_norm_vec_le_uniform hν
    (show 1 < r by linarith)
  have ha : -1 < -(3 : ℝ) / (2 * r) := by
    have hrpos : 0 < r := by linarith
    apply (lt_div_iff₀ (by positivity : 0 < 2 * r)).2
    linarith
  have hw : IntervalIntegrable
      (fun s : ℝ => C * S * (t - s) ^ (-(3 : ℝ) / (2 * r))) volume 0 t := by
    simpa only [neg_div] using
      (intervalIntegrable_sub_rpow_neg (t := t) (a := 3 / (2 * r))
        (by simpa only [neg_div] using ha)).const_mul (C * S)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht0.le] at hw ⊢
  refine hw.mono' him ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsδ : s ≤ δ := hs.2.le.trans htδ
  have hts : 0 < t - s := sub_pos.mpr hs.2
  have hbound := hC (duhamelSource sol s)
    (duhamelSource_slice_measurable sol hs.1.le (hsδ.trans_lt hδT))
    (hsi s hs.1.le hsδ) (t - s) (sub_pos.mpr hs.2) x
  calc
    _ ≤ C * (t - s) ^ (-(3 : ℝ) / (2 * r)) *
        (∫ y : Space, ‖duhamelSource sol s y‖ ^ r) ^ (1 / r) := hbound
    _ ≤ C * (t - s) ^ (-(3 : ℝ) / (2 * r)) * S :=
      mul_le_mul_of_nonneg_left (hS s hs.1.le hsδ) (by positivity)
    _ = C * S * (t - s) ^ (-(3 : ℝ) / (2 * r)) := by ring

/-- The time-integrable vector convolution supplies the norm-integrability
input of the original Duhamel bound. -/
theorem duhamelConvolution_intervalIntegrable_of_source_Lr
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {δ : ℝ} (hδT : δ < T) {r : ℝ} (hr : 3 / 2 < r)
    (hsi : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      Integrable (fun y : Space => ‖duhamelSource sol s y‖ ^ r))
    (S : ℝ) (hS : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      (∫ y : Space, ‖duhamelSource sol s y‖ ^ r) ^ (1 / r) ≤ S)
    {t : ℝ} (ht0 : 0 < t) (htδ : t ≤ δ) (x : Space) :
    IntervalIntegrable
      (fun s : ℝ => ‖∫ y : Space,
        heatKernel ν (t - s) (x - y) • duhamelSource sol s y‖) volume 0 t :=
  (duhamelConvolution_integrable_of_source_Lr hν sol hδT hr hsi S hS ht0 htδ x).2.norm



/-! ### Sharpness: an explicit strain flow -/

/-- Diagonal strain coefficients `(1, -1, 0)`.  They sum to zero, which is
exactly incompressibility of `strainVelocity` below. -/
def strainCoeff : Fin 3 → ℝ := ![1, -1, 0]

lemma sum_strainCoeff : ∑ i : Fin 3, strainCoeff i = 0 := by
  simp [strainCoeff, Fin.sum_univ_three]

/-- The time-`t` strain, as a continuous linear map on `ℝ³`. -/
def strainMap (t : ℝ) : Space →L[ℝ] Space :=
  ContinuousLinearMap.pi fun i => (strainCoeff i * t) • ContinuousLinearMap.proj i

@[simp] lemma strainMap_apply (t : ℝ) (x : Space) (i : Fin 3) :
    strainMap t x i = strainCoeff i * t * x i := rfl

/-- The diagonal strain flow `u(t,x) = (t x₁, −t x₂, 0)`. -/
def strainVelocity : VelocityEvolution := fun t x => strainMap t x

@[simp] lemma strainVelocity_apply (t : ℝ) (x : Space) (i : Fin 3) :
    strainVelocity t x i = strainCoeff i * t * x i := rfl

/-- The pressure `p(t,x) = −½ ∑ᵢ (cᵢ + cᵢ²t²) xᵢ²` that closes the strain
flow into an exact zero-force Navier–Stokes solution. -/
def strainPressure : PressureEvolution := fun t x =>
  -(2⁻¹ : ℝ) * ∑ i : Fin 3, (strainCoeff i + (strainCoeff i * t) ^ 2) * (x i) ^ 2

lemma strainVelocity_fderiv (t : ℝ) (y : Space) :
    fderiv ℝ (strainVelocity t) y = strainMap t :=
  (strainMap t).hasFDerivAt.fderiv

lemma strainVelocity_contDiff :
    ContDiff ℝ ∞ (fun z : ℝ × Space => strainVelocity z.1 z.2) := by
  refine contDiff_pi.2 fun i => ?_
  simpa using (contDiff_const.mul contDiff_fst).mul (contDiff_pi.1 contDiff_snd i)

lemma strainPressure_contDiff :
    ContDiff ℝ ∞ (fun z : ℝ × Space => strainPressure z.1 z.2) := by
  refine contDiff_const.mul (ContDiff.sum fun i _ => ?_)
  exact ((contDiff_const.add ((contDiff_const.mul contDiff_fst).pow 2)).mul
    ((contDiff_pi.1 contDiff_snd i).pow 2))

lemma strainVelocity_divergence (t : ℝ) (x : Space) :
    divergence strainVelocity t x = 0 := by
  simp [divergence, spatialDerivative, strainVelocity_fderiv, basisVector,
    strainCoeff, Fin.sum_univ_three]

lemma strainVelocity_laplacian (t : ℝ) (x : Space) :
    laplacian strainVelocity t x = 0 := by
  have hconst : ∀ i : Fin 3,
      (fun y : Space => fderiv ℝ (strainVelocity t) y (basisVector i))
        = fun _ : Space => strainMap t (basisVector i) := by
    intro i
    funext y
    rw [strainVelocity_fderiv]
  simp [laplacian, hconst]

lemma strainVelocity_convection (t : ℝ) (x : Space) (i : Fin 3) :
    convection strainVelocity t x i = (strainCoeff i * t) ^ 2 * x i := by
  simp [convection, spatialDerivative, strainVelocity_fderiv]
  ring

lemma strainVelocity_timeDerivative {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    timeDerivative strainVelocity t x = fun i => strainCoeff i * x i := by
  have hfun : (fun s : ℝ => strainVelocity s x)
      = fun s : ℝ => s • (fun j => strainCoeff j * x j : Space) := by
    funext s
    funext j
    simp [strainVelocity]
    ring
  have hd : HasDerivAt (fun s : ℝ => strainVelocity s x)
      (fun j => strainCoeff j * x j : Space) t := by
    rw [hfun]
    simpa using (hasDerivAt_id t).smul_const (fun j => strainCoeff j * x j : Space)
  have := hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)
  simpa [timeDerivative, derivWithin] using this

lemma strainPressure_hasFDerivAt (t : ℝ) (x : Space) :
    HasFDerivAt (strainPressure t)
      ((-(2⁻¹ : ℝ)) • ∑ i : Fin 3,
        (strainCoeff i + (strainCoeff i * t) ^ 2) •
          ((2 * x i) • (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ))) x := by
  have hterm : ∀ i : Fin 3,
      HasFDerivAt
        (fun y : Space => (strainCoeff i + (strainCoeff i * t) ^ 2) * (y i) ^ 2)
        ((strainCoeff i + (strainCoeff i * t) ^ 2) •
          ((2 * x i) • (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ))) x := by
    intro i
    refine HasFDerivAt.const_mul ?_ _
    simpa using ((ContinuousLinearMap.proj i :
      Space →L[ℝ] ℝ).hasFDerivAt).pow 2
  have hfun :
      (∑ i : Fin 3, fun y : Space =>
        (strainCoeff i + (strainCoeff i * t) ^ 2) * (y i) ^ 2)
        = fun y : Space =>
          ∑ i : Fin 3, (strainCoeff i + (strainCoeff i * t) ^ 2) * (y i) ^ 2 := by
    funext y
    simp
  have hsum := HasFDerivAt.sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hterm i)
  rw [hfun] at hsum
  have hp : strainPressure t = fun y : Space =>
      -(2⁻¹ : ℝ) * ∑ i : Fin 3,
        (strainCoeff i + (strainCoeff i * t) ^ 2) * (y i) ^ 2 := rfl
  rw [hp]
  exact hsum.const_mul _

lemma strainPressure_gradient (t : ℝ) (x : Space) (j : Fin 3) :
    pressureGradient strainPressure t x j
      = -((strainCoeff j + (strainCoeff j * t) ^ 2) * x j) := by
  rw [pressureGradient, (strainPressure_hasFDerivAt t x).fderiv]
  fin_cases j <;>
    simp [basisVector, Fin.sum_univ_three, strainCoeff, Fin.ext_iff] <;>
    ring

lemma strainFlow_equation (ν T : ℝ) :
    SatisfiesNavierStokesBefore ν zeroForce T strainVelocity strainPressure := by
  intro t ht0 _ x
  funext i
  simp [strainVelocity_timeDerivative ht0, strainVelocity_convection,
    strainVelocity_laplacian, strainPressure_gradient, zeroForce]
  ring

/-- **The diagonal strain flow is an exact zero-force classical solution with
zero initial datum.**  For every viscosity `ν` and every horizon `T > 0`,

`u(t,x) = (t x₁, −t x₂, 0)`,  `p(t,x) = −½[(1+t²)x₁² + (t²−1)x₂²]`

is smooth on `[0,T) × ℝ³`, divergence-free, solves the Navier–Stokes system
with zero body force, and starts from `u(0,·) = 0`.  (The Laplacian vanishes
identically, which is why the construction is viscosity-independent.) -/
def strainSolution (ν T : ℝ) (hT : 0 < T) :
    PartialClassicalSolution ν zeroForce (fun _ : Space => (0 : Space)) T where
  terminalTime_pos := hT
  velocity := strainVelocity
  pressure := strainPressure
  velocity_smooth := strainVelocity_contDiff.contDiffOn
  pressure_smooth := strainPressure_contDiff.contDiffOn
  initial_condition := by
    funext x
    funext i
    simp
  incompressible := fun t _ _ x => strainVelocity_divergence t x
  equation := strainFlow_equation ν T

/-- At any positive time the strain velocity exceeds every level `R` somewhere
outside every ball: this is the exact negation shape of the far-field
conclusions of the four residual leaves. -/
lemma strainVelocity_farField_exceeds {t : ℝ} (ht : 0 < t) (ϱ R : ℝ) :
    ∃ x : Space, ϱ ≤ ‖x‖ ∧ R < ‖strainVelocity t x‖ := by
  set c : ℝ := max (max ϱ 0) ((|R| + 1) / t) with hc
  have hc0 : (0 : ℝ) ≤ c := le_trans (le_max_right ϱ 0) (le_max_left _ _)
  have hcϱ : ϱ ≤ c := le_trans (le_max_left ϱ 0) (le_max_left _ _)
  have hcR : (|R| + 1) / t ≤ c := le_max_right _ _
  refine ⟨Pi.single 0 c, hcϱ.trans ?_, ?_⟩
  · have h := norm_le_pi_norm (Pi.single (0 : Fin 3) c : Space) 0
    rwa [Pi.single_eq_same, Real.norm_eq_abs, abs_of_nonneg hc0] at h
  · have hval : strainVelocity t (Pi.single 0 c) 0 = t * c := by simp [strainCoeff]
    have h := norm_le_pi_norm (strainVelocity t (Pi.single (0 : Fin 3) c : Space)) 0
    rw [hval, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.le hc0)] at h
    have hgt : |R| + 1 ≤ t * c := by
      have := (div_le_iff₀ ht).mp hcR
      linarith
    have hR' : R ≤ |R| := le_abs_self R
    linarith

/-- An explicit smooth, divergence-free, zero-force strain solution with
zero initial datum has unbounded velocity outside every spatial ball at
positive times. Thus those hypotheses alone do not give a far-field bound. -/
theorem strainFlow_farField_unbounded (ν : ℝ) {T δ : ℝ} (hT : 0 < T)
    (hδ0 : 0 < δ) (_hδT : δ < T) :
    (∃ B₀ : ℝ, ∀ x : Space, ‖(fun _ : Space => (0 : Space)) x‖ ≤ B₀) ∧
      ¬ ∃ ϱ R : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ δ → ∀ x : Space,
          ϱ ≤ ‖x‖ → ‖(strainSolution ν T hT).velocity t x‖ ≤ R := by
  refine ⟨⟨0, fun x => by simp⟩, ?_⟩
  rintro ⟨ϱ, R, h⟩
  obtain ⟨x, hx, hR⟩ := strainVelocity_farField_exceeds hδ0 ϱ R
  have hv : (strainSolution ν T hT).velocity = strainVelocity := rfl
  have := h δ hδ0.le le_rfl x hx
  rw [hv] at this
  linarith

/-! #### The strain flow satisfies every non-integrability hypothesis -/

/-- The strain flow is irrotational: its velocity gradient is a diagonal
matrix, so the curl vanishes identically.  Consequently *every*
direction-coherence hypothesis — in particular the `ρ`-scaled
Constantin–Fefferman bound `hcoh` — holds vacuously for it whenever
`Ω₀ > 0`. -/
lemma crossProduct_self_smul (c : ℝ) (a : Space) : a ⨯₃ (c • a) = 0 := by
  funext j
  fin_cases j <;> simp

lemma strainMap_basisVector (t : ℝ) (i : Fin 3) :
    strainMap t (basisVector i) = (strainCoeff i * t) • basisVector i := by
  funext j
  by_cases h : j = i
  · subst h; simp [basisVector]
  · simp [basisVector, Pi.single_eq_of_ne h]

lemma strainVelocity_vorticity (t : ℝ) (x : Space) :
    vorticity strainVelocity t x = 0 := by
  have h : ∀ i : Fin 3,
      basisVector i ⨯₃ (fderiv ℝ (strainVelocity t) x (basisVector i)) = 0 := by
    intro i
    rw [strainVelocity_fderiv, strainMap_basisVector]
    exact crossProduct_self_smul _ _
  simp only [vorticity, staticCurl, h, Finset.sum_const_zero]

/-- Any half-space slab `{x | a ≤ x₀}` has infinite Lebesgue measure in `ℝ³`,
so a function bounded below by `1` on such a slab is not integrable. -/
lemma not_integrable_of_slab {g : Space → ℝ} {a : ℝ}
    (h : ∀ x : Space, a ≤ x 0 → (1 : ℝ) ≤ g x) : ¬ Integrable g := by
  intro hI
  have hlt := hI.measure_ge_lt_top (ε := (1 : ℝ)) one_pos
  have hsub : (Set.univ.pi fun _ : Fin 3 => Set.Ici a)
      ⊆ {y : Space | (1 : ℝ) ≤ g y} := fun x hx => h x (hx 0 (Set.mem_univ 0))
  have hvol : volume (Set.univ.pi fun _ : Fin 3 => Set.Ici a) = ⊤ := by
    rw [volume_pi_pi]
    simp
  have hle := measure_mono (μ := (volume : Measure Space)) hsub
  rw [hvol] at hle
  exact absurd (hle.trans_lt hlt) (lt_irrefl _)

lemma strainVelocity_one_le_norm {t : ℝ} (ht : t ≠ 0) {x : Space}
    (hx : |t|⁻¹ ≤ x 0) : (1 : ℝ) ≤ ‖strainVelocity t x‖ := by
  have ht0 : 0 < |t| := abs_pos.mpr ht
  have hx0 : 0 < x 0 := lt_of_lt_of_le (by positivity) hx
  have hone : (1 : ℝ) ≤ |t| * x 0 := by
    have := mul_le_mul_of_nonneg_left hx ht0.le
    rwa [mul_inv_cancel₀ ht0.ne'] at this
  have hval : strainVelocity t x 0 = t * x 0 := by simp [strainCoeff]
  have h := norm_le_pi_norm (strainVelocity t x) 0
  rw [hval, Real.norm_eq_abs, abs_mul, abs_of_pos hx0] at h
  linarith

/-- **The strain flow fails the `L^p` integrability hypothesis.**  For `t ≠ 0`
the velocity is a nonzero linear field, so `‖u(t,·)‖^p` is bounded below by `1`
on a half-space and is therefore not integrable, for every exponent `p > 0`.
This is precisely the hypothesis `hint` of the Prodi–Serrin leaves. -/
lemma strainVelocity_not_integrable_rpow {t : ℝ} (ht : t ≠ 0) {p : ℝ} (hp : 0 < p) :
    ¬ Integrable (fun x : Space => ‖strainVelocity t x‖ ^ p) := by
  refine not_integrable_of_slab (a := |t|⁻¹) fun x hx => ?_
  calc (1 : ℝ) = (1 : ℝ) ^ p := (Real.one_rpow p).symm
    _ ≤ ‖strainVelocity t x‖ ^ p :=
        Real.rpow_le_rpow zero_le_one (strainVelocity_one_le_norm ht hx) hp.le

/-- **The strain flow fails the `L²` integrability hypothesis** `hL2` of the
Constantin–Fefferman leaves, for the same reason. -/
lemma strainVelocity_not_integrable_sq {t : ℝ} (ht : t ≠ 0) :
    ¬ Integrable (fun x : Space => ‖strainVelocity t x‖ ^ 2) := by
  refine not_integrable_of_slab (a := |t|⁻¹) fun x hx => ?_
  exact one_le_pow₀ (strainVelocity_one_le_norm ht hx)

lemma strainVelocity_zero_time : strainVelocity 0 = fun _ : Space => (0 : Space) := by
  funext x
  funext i
  simp

/-- Lean's Bochner integral returns its junk value `0` off the integrable
class, so the strain flow's `L^p` slice integrals all vanish. -/
lemma strainVelocity_integral_rpow (t : ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ x : Space, ‖strainVelocity t x‖ ^ p) = 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [strainVelocity_zero_time, Real.zero_rpow hp.ne']
  · exact integral_undef (strainVelocity_not_integrable_rpow ht hp)

lemma strainVelocity_integral_sq (t : ℝ) :
    (∫ x : Space, ‖strainVelocity t x‖ ^ 2) = 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [strainVelocity_zero_time]
  · exact integral_undef (strainVelocity_not_integrable_sq ht)

/-- The uniform `L²` mass bracket `hmass` holds for the strain flow, for every
energy budget `E ≥ 0`. -/
lemma strainVelocity_massBracket {E : ℝ} (hE : 0 ≤ E) (t : ℝ) :
    (∫ x : Space, ‖strainVelocity t x‖ ^ 2) ∈ Set.Icc (0 : ℝ) E := by
  rw [strainVelocity_integral_sq]
  exact ⟨le_rfl, hE⟩

/-- The Serrin mixed norm `hM` holds for the strain flow, for every budget
`M ≥ 0`. -/
lemma strainVelocity_mixedNorm {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (T' : ℝ) :
    (∫ s in (0 : ℝ)..T',
      (∫ x : Space, ‖strainVelocity s x‖ ^ p) ^ (q / p)) = 0 := by
  have h : ∀ s : ℝ,
      (∫ x : Space, ‖strainVelocity s x‖ ^ p) ^ (q / p) = 0 := fun s => by
    rw [strainVelocity_integral_rpow s hp, Real.zero_rpow (by positivity)]
  simp [h]

lemma strainVelocity_mixedNorm_intervalIntegrable
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (T' : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => (∫ x : Space, ‖strainVelocity s x‖ ^ p) ^ (q / p))
      volume 0 T' := by
  have h : (fun s : ℝ => (∫ x : Space, ‖strainVelocity s x‖ ^ p) ^ (q / p))
      = fun _ : ℝ => (0 : ℝ) := by
    funext s
    rw [strainVelocity_integral_rpow s hp, Real.zero_rpow (by positivity)]
  rw [h]
  exact intervalIntegrable_const

/-- The strain solution has zero vorticity and satisfies every nonnegative
bare energy bracket through default-valued integrals, while the interior
outer-region velocity bound fails. -/
theorem strainFlow_interior_outerRegion_unbounded (ν : ℝ) {T δ : ℝ} (hT : 0 < T)
    (hδ0 : 0 < δ) (hδT : δ < T) :
    (∀ {E : ℝ}, 0 ≤ E → ∀ t : ℝ,
        (∫ x : Space, ‖(strainSolution ν T hT).velocity t x‖ ^ 2)
          ∈ Set.Icc (0 : ℝ) E) ∧
      (∀ t : ℝ, ∀ x : Space,
        vorticity (strainSolution ν T hT).velocity t x = 0) ∧
      ¬ ∃ ϱ R : ℝ, ∀ t : ℝ, δ < t → t < T → ∀ x : Space,
          (ϱ ≤ ‖x‖ ∨ (δ + T) / 2 < t) →
            ‖(strainSolution ν T hT).velocity t x‖ ≤ R := by
  have hv : (strainSolution ν T hT).velocity = strainVelocity := rfl
  refine ⟨fun hE t => ?_, fun t x => ?_, ?_⟩
  · rw [hv]; exact strainVelocity_massBracket hE t
  · rw [hv]; exact strainVelocity_vorticity t x

  · rintro ⟨ϱ, R, h⟩
    have ht0 : 0 < (δ + T) / 2 := by linarith
    have htδ : δ < (δ + T) / 2 := by linarith
    have htT : (δ + T) / 2 < T := by linarith
    obtain ⟨x, hx, hR⟩ := strainVelocity_farField_exceeds ht0 ϱ R
    have := h ((δ + T) / 2) htδ htT x (Or.inl hx)
    rw [hv] at this
    linarith

end Navier.Analysis.ConditionalRegularity
