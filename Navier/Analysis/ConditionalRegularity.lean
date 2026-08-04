import Navier.Analysis.BealeKatoMajda
import Navier.Scaling

/-!
# Conditional regularity bridges: Prodi–Serrin and Constantin–Fefferman

Two classical conditional-regularity criteria for the repository's partial
classical solutions, stated as skeletons with hypothesis-carried norms
(Step-0e: explicit integrability keeps the Bochner integrals honest; the
conclusion is the same continuation surrogate as the BKM layer — a uniform
velocity bound on `[0,T)`, which `PointEvaluationBreakdownWitness` machinery
turns into "no pointwise blow-up").

Per the ladder (rung 5, R3 class, ≤1 conditional bridge per headline), these
do not advance the headline; they delimit the conditional-regularity surface
honestly.

## Established leaves

* `uniformBound_of_split` — order-theoretic assembly: an initial-layer bound on
  `[0,δ]` and an interior bound on `(δ,T)` combine by `max` into the uniform
  bound on `[0,T)`.  Shared by both bridges.
* `serrin_exponent_gt_two` — on the critical line, `p > 3` forces `q > 2`.
* `initialDatum_bounded_of_uniformBound` — the conclusion of either bridge
  *entails* boundedness of `u₀`, which is why both now carry `hu₀`.
* `uniformL2Mass_of_energyBound`, `energyBound_nonneg` — the uniform-in-time
  `L²` mass bracket extracted from the hypothesis-carried energy bound.
* `coherentVorticity_crossProduct_le_scaled` — the depletion factor `ε` that
  direction coherence hands to the enstrophy stretching estimate at separations
  `|x−y| ≤ ε·ρ`.  Informative exactly for `ε < 1`; see
  `depletedCrossProduct_vacuous` for why the `ε = 1` instance is not.
* `euclideanNormSq_eq_sum`, `crossProduct_smul_smul`,
  `officialEuclideanNorm_crossProduct_le`, `crossProductBound_saturated`,
  `officialEuclideanNorm_crossProduct_le_sub_of_unit`,
  `officialEuclideanNorm_crossProduct_le_directionDist` — the Euclidean
  cross-product geometry underlying Constantin–Fefferman: Lagrange's bound,
  its saturation at an orthogonal pair, and the sharp comparison
  `|ξ ⨯ η| ≤ |ξ − η|` for unit vectors.
* `crossProductCoherent_of_directionLipschitz` — Lipschitz continuity of the
  vorticity direction `ξ = ω/|ω|` on `{|ω| ≥ Ω₀}` implies the division-free
  Constantin–Fefferman coherence bound.
* `massBracket_vacuous_of_infiniteMass`,
  `serrinMixedNorm_vacuous_of_nonIntegrableTime`, `depletedCrossProduct_vacuous`
  — the three kernel-checked vacuity witnesses driving the Pattern-A repairs
  recorded below.
* `uniformL2Integrable_of_energyBound` — the integrability conjunct of a
  hypothesis-carried energy bound, which `uniformL2Mass_of_energyBound`
  discards.
* `norm_continuousOn_spacetimeBefore`, `compactSpaceTime_bounded` — the
  compact-set uniform bound on `[a,b] × K` for `0 ≤ a`, `b < T`, `K` compact.
  This strengthens `Navier.Breakdown.bounded_pointEvaluation_of_smooth` from a
  single spatial point to an arbitrary compact set, and it is the whole part of
  both bridges that needs no analytic machinery.
* `uniformBound_of_farField_window`, `interiorBound_of_outerRegion` — the two
  reductions that discharge that compact core, leaving only decay at spatial
  infinity (both windows) and uniformity as `t ↑ T` (interior window).

## Falsification and repair (Pattern A)

`massBracket_vacuous_of_infiniteMass` is a kernel-checked witness that the bare
`L²` mass bracket

`∀ t ∈ [0,T), (∫ x, ‖u t x‖ ^ 2) ∈ Set.Icc 0 E`

is satisfied by *every* velocity field of infinite `L²` mass, for every
`E ≥ 0`, because Lean's Bochner integral returns the junk value `0` off the
integrable class.  Both Constantin–Fefferman leaves previously carried only
that bracket, and were therefore **false as stated**: the shear flow
`u(t,x) = (φ(t,x₃),0,0)`, `p ≡ 0`, built from a nonzero Tychonov solution `φ`
of the one-dimensional heat equation with `φ(0,·) = 0`
[Tychonov, Mat. Sb. 42 (1935) 199–216], is an exact zero-force classical
solution with bounded (zero) initial datum whose vorticity is everywhere
parallel to `e₂` — so every direction-coherence hypothesis holds for every
`ρ`, `Ω₀` — while `φ` is unbounded
on every strip by Tychonov uniqueness.  The repair adds the integrability
hypothesis `hL2` to both leaves; `constantinFefferman_velocity_bounded` already
holds it inside `henergy` and now forwards it via
`uniformL2Integrable_of_energyBound`, so no caller pays for the repair.  The
Prodi–Serrin leaves were unaffected: their `hint` is a genuine `Integrable`
hypothesis and already excludes this class.

### Second falsification and repair (Pattern A): the tautologous `hdep`

`constantinFefferman_interior_outerRegion_bounded` additionally carried

`|ω(x) ⨯ ω(y)| ≤ |ω(x)| · |ω(y)|` on `{|ω| ≥ Ω₀} × {|ω| ≥ Ω₀}`, `|x−y| ≤ ρ`

as its supposed direction-coherence hypothesis `hdep`, obtained by
specialising `coherentVorticity_crossProduct_le_scaled` to `ε = 1`.
`depletedCrossProduct_vacuous` is the kernel-checked witness that this formula
is a **tautology**: it is an instance of the unconditional Lagrange bound
`officialEuclideanNorm_crossProduct_le`, its proof term discards every
antecedent and never mentions `u`, `ρ` or `Ω₀`, and by
`crossProductBound_saturated` it is attained with ratio `1` at an orthogonal
pair.  So the leaf constrained the vorticity geometry not at all, whereas the
Constantin–Fefferman mechanism *is* the depletion of the stretching term
`α = (ξ·∇)u·ξ` caused by continuity of the direction field `ξ = ω/|ω|`; a
cross-product magnitude bound expresses none of it.

The repair is Pattern A — strengthening a hypothesis that was vacuous, hence
a repair and not a weakening.  The leaf and
`constantinFefferman_interior_bounded` now carry the genuine `ρ`-scaled
coherence hypothesis `hcoh`, verbatim the one
`constantinFefferman_velocity_bounded` already holds, so again no caller pays;
the collapsing lemma `coherentVorticity_crossProduct_le` is deleted.  For
callers holding the geometric form,
`crossProductCoherent_of_directionLipschitz` derives `hcoh` from
`|ξ(x) − ξ(y)| ≤ |x−y|/ρ` on the high-vorticity region.

### Third falsification and repair (Pattern A): the untimed Serrin bracket

The same junk-value defect recurs in the *temporal* slot.  `hM` encodes the
Ladyzhenskaya–Prodi–Serrin hypothesis as
`∀ T' < T, ∫₀^{T'} (∫|u|^p)^{q/p} ds ≤ M` with no conjunct asserting that the
slice-norm profile is interval-integrable, and Lean's interval integral
returns `0` off that class.  `serrinMixedNorm_vacuous_of_nonIntegrableTime` is
the kernel-checked witness.  Repair: `prodiSerrin_interior_outerRegion_bounded`,
`prodiSerrin_interior_bounded` and `prodiSerrin_velocity_bounded` now carry
`hMint`.  This restores a conjunct the encoding dropped — `u ∈ L^q(0,T;L^p)`
already asserts it — rather than adding a new assumption.

## Bridges (assembled from named residual leaves)

* `prodiSerrin_velocity_bounded` — the Ladyzhenskaya–Prodi–Serrin continuation
  criterion: a critical mixed-norm bound `u ∈ L^q_t L^p_x`, `2/q + 3/p = 1`,
  `p > 3`, forces a uniform velocity bound
  [Prodi, Ann. Mat. Pura Appl. 48 (1959); Serrin, ARMA 9 (1962);
  Escauriaza–Serëgin–Šverák (2003) for the `p = 3` endpoint].
  Residuals: `prodiSerrin_layer_farField_bounded`,
  `prodiSerrin_interior_outerRegion_bounded` — each the corresponding uniform
  bound restricted to the outer region left over by `compactSpaceTime_bounded`.
* `constantinFefferman_velocity_bounded` — the vorticity-direction coherence
  criterion: if the direction of the vorticity is `ρ`-coherent (division-free
  form: `|ω(x) ⨯ ω(y)| ≤ (|x−y|/ρ)·|ω(x)||ω(y)|`) wherever the vorticity is
  large, a finite-energy classical solution stays bounded
  [Constantin–Fefferman, Indiana Univ. Math. J. 42 (1993) 775–789].
  Residuals: `constantinFefferman_layer_farField_bounded`,
  `constantinFefferman_interior_outerRegion_bounded` — likewise restricted to
  the outer region, the latter carrying `hcoh` itself after the tautology
  repair recorded above.

## Statement repair (bounded initial datum)

Both bridges previously concluded a uniform bound on `[0,T)` from hypotheses
that do not constrain `u₀` in `L^∞`.  Since `0 < T` (`terminalTime_pos`) and
`velocity 0 = u₀`, the conclusion *includes* `∀ x, ‖u₀ x‖ ≤ R`, whereas
`SmoothVelocityBefore` is `ContDiffOn` on `Set.Ico 0 T ×ˢ univ` — a purely
local condition carrying no uniform spatial bound — and per-slice `L^p`
integrability likewise does not imply boundedness.  Both statements therefore
carry the explicit hypothesis `hu₀ : ∃ B₀, ∀ x, ‖u₀ x‖ ≤ B₀`, which the formal problem
formulation supplies (Schwartz initial data).  `initialDatum_bounded_of_uniformBound`
certifies that this hypothesis is *necessary*, hence minimal rather than an
over-assumption.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace Navier.Analysis.ConditionalRegularity

open scoped Matrix

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Breakdown

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
hypotheses — and it is what makes `energyBound_nonneg` available downstream. -/
theorem uniformL2Mass_of_energyBound {u : VelocityEvolution} {T E : ℝ}
    (henergy : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖u t x‖ ^ 2) ∧ kineticEnergy u t ≤ E) :
    ∀ t : ℝ, 0 ≤ t → t < T →
      (∫ x : Space, ‖u t x‖ ^ 2) ∈ Set.Icc (0 : ℝ) E := by
  intro t ht0 htT
  refine ⟨integral_nonneg fun x => by positivity, ?_⟩
  simpa [kineticEnergy] using (henergy t ht0 htT).2

/-- A hypothesis-carried energy bound over a nonempty time interval is
nonnegative.  Not assumed anywhere: it is forced by the nonnegativity of the
kinetic-energy integrand at the admissible time `t = 0`. -/
theorem energyBound_nonneg {u : VelocityEvolution} {T E : ℝ} (hT : 0 < T)
    (henergy : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖u t x‖ ^ 2) ∧ kineticEnergy u t ≤ E) :
    0 ≤ E := by
  obtain ⟨h0, hE⟩ := uniformL2Mass_of_energyBound henergy 0 le_rfl hT
  exact h0.trans hE

/-- The integrability half of a hypothesis-carried energy bound.  Companion to
`uniformL2Mass_of_energyBound`, which retains only the numeric bracket and
discards this conjunct.  Discarding it is exactly what made the two
Constantin–Fefferman leaves false as previously stated; see
`massBracket_vacuous_of_infiniteMass`. -/
theorem uniformL2Integrable_of_energyBound {u : VelocityEvolution} {T E : ℝ}
    (henergy : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖u t x‖ ^ 2) ∧ kineticEnergy u t ≤ E) :
    ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖u t x‖ ^ 2) :=
  fun t ht0 htT => (henergy t ht0 htT).1

/-! ### Falsification of the bare integral brackets -/

/-- **The bare `L²` mass bracket is vacuous off the integrable class.**  Lean's
Bochner integral returns the junk value `0` on a non-integrable integrand, so
the hypothesis

`∀ t ∈ [0,T), (∫ x, ‖u t x‖ ^ 2) ∈ Set.Icc 0 E`

is satisfied by *every* velocity field of infinite `L²` mass, however large,
for every `E ≥ 0`.  It therefore carries no information whatsoever outside the
integrable class.

This is the kernel-checked falsification witness for the previous statements of
`constantinFefferman_initialLayer_bounded` and
`constantinFefferman_interior_bounded`, which carried only that bracket and no
integrability hypothesis.  A concrete inhabitant of the vacuous class: let `φ`
be a nonzero Tychonov solution of the one-dimensional heat equation
`∂ₜφ = ν ∂_z² φ` with `φ(0,·) = 0` [Tychonov, Mat. Sb. 42 (1935) 199–216], and
put `u(t,x) = (φ(t,x₃), 0, 0)` with `p ≡ 0`.  Then

* `u` is a genuine `PartialClassicalSolution ν zeroForce 0 T`: it is smooth,
  `div u = ∂₁φ = 0`, the convection term `(u·∇)u = u₁ ∂₁ u` vanishes because
  `φ` is independent of `x₁`, and the equation collapses to the heat equation;
* its initial datum is `0`, so `hu₀` holds with `B₀ = 0`;
* its vorticity `ω = (0, ∂₃φ, 0)` is everywhere parallel to `e₂`, so
  `ω(x) ⨯ ω(y) = 0` and every direction-coherence hypothesis — the
  tautologous `hdep` and the genuine `hcoh` alike — holds for every `ρ` and
  `Ω₀`;
* `x ↦ ‖u t x‖ ^ 2` is independent of `(x₁,x₂)` and not a.e. zero once
  `φ(t,·) ≠ 0`, hence is not integrable on `ℝ³`, so this lemma supplies the
  mass bracket for every `E ≥ 0`;
* yet `φ` is unbounded on every strip `[0,δ] × ℝ`, since a heat solution that
  is bounded on a strip and vanishes initially is identically zero by Tychonov
  uniqueness.  Translating the activation time of `φ` from `0` to `δ` gives the
  same refutation on the interior window `(δ,T)`.

So both conclusions `∃ R, ∀ t, ∀ x, ‖u t x‖ ≤ R` fail while every hypothesis
holds.  The repair is Pattern A: both Constantin–Fefferman leaves now carry the
integrability hypothesis `hL2`, which the bridge's own `henergy` already
supplies through `uniformL2Integrable_of_energyBound`, and which excludes this
class outright at no cost to any caller. -/
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
equality (ratio exactly `1`), so it cannot be sharpened by any constant and it
separates no pair of vectors from any other.  Together with
`officialEuclideanNorm_crossProduct_le` this is the falsification witness for
the `hdep` hypothesis previously carried by
`constantinFefferman_interior_outerRegion_bounded`. -/
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

/-- **The `ε = 1` depletion bound is a tautology.**  The statement

`|ω(x) ⨯ ω(y)| ≤ |ω(x)| · |ω(y)|` whenever `|ω(x)|, |ω(y)| ≥ Ω₀` and `|x−y| ≤ ρ`

holds for *every* velocity evolution `u`, every `T`, every `ρ` and every `Ω₀`,
because it is an instance of the unconditional Lagrange bound
`officialEuclideanNorm_crossProduct_le`.  Note the proof term below discards
all three antecedents and never mentions `u`, `ρ` or `Ω₀`.

This is the kernel-checked falsification witness for the previous statement of
`constantinFefferman_interior_outerRegion_bounded`, which carried exactly this
formula as its hypothesis `hdep` and therefore carried *no* geometric
constraint on the vorticity direction at all — while the Constantin–Fefferman
mechanism is precisely the depletion of the stretching term
`α = (ξ·∇)u·ξ` produced by continuity of `ξ = ω/|ω|`.  By
`crossProductBound_saturated` the bound is attained with ratio `1`, so it is
not even a quantitatively useful universal estimate: it is the sharp form of
"no information".

The repair is Pattern A: the leaf now carries the genuine `ρ`-scaled
Constantin–Fefferman coherence hypothesis `hcoh`, which its only caller
`constantinFefferman_velocity_bounded` already holds verbatim, so no caller
pays for the repair; and `crossProductCoherent_of_directionLipschitz` derives
`hcoh` from Lipschitz continuity of the vorticity direction. -/
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

/-! ### Named residual leaves -/

/-- **[LEAF — Prodi–Serrin far-field layer tail; est ~300 LOC.]**  Outside one
closed ball, a partial classical solution with bounded initial datum and
per-slice `L^p` integrability (`p > 3`) is uniformly bounded on the closed
initial layer `[0,δ]`.

This is the residual of `prodiSerrin_initialLayer_bounded` *after*
`compactSpaceTime_bounded` discharges the compact core.  It is the original
conclusion restricted to `ϱ ≤ ‖x‖`, hence strictly weaker, and it is not
circular: establishing it nowhere uses the uniform bound it supports.

Classical route: Kato's mild-solution theory in `L^∞ ∩ L^p` — the Duhamel
formulation `u(t) = e^{tνΔ}u₀ − ∫₀^t e^{(t−s)νΔ} P ∇·(u ⊗ u) ds` gives a
short-time `L^∞` bound from `‖u₀‖_∞`, and the `L^p → L^∞` smoothing of the heat
semigroup turns the per-slice `L^p` control into decay at spatial infinity
[Kato, Math. Z. 187 (1984) 471–480;
Giga–Miyakawa, Arch. Ration. Mech. Anal. 89 (1985) 267–281].
Depends on: the heat semigroup on `ℝ³` with its `L^p → L^∞` smoothing
estimates, the Leray projector, and Duhamel/Gronwall — none currently in
Mathlib.

Frontier status: `HeatSemigroupSmoothing` now lands the Gaussian kernel and
its `L^s` norms (`integral_heatKernel_rpow`, `heatKernel_Lr_scaling`), the
scaling behind the smoothing estimate.  Still missing: a convolution (Young)
layer turning those norms into pointwise kernel-convolution bounds on
`Space`; a Duhamel representation of an arbitrary `PartialClassicalSolution`
— integration by parts against the kernel, with the boundary terms at
spatial infinity controlled by the per-slice integrability — noting that the
in-repo Duhamel developments `FrequencyDuhamel`/`CriticalMild*` act on
one-frequency or lattice encodings, not on pointwise classical solutions;
and the Leray projector as a pointwise bounded kernel. -/
theorem prodiSerrin_layer_farField_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (hu₀ : ∃ B₀ : ℝ, ∀ x : Space, ‖u₀ x‖ ≤ B₀)
    (p : ℝ) (hp : 3 < p)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    (δ : ℝ) (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ ϱ R : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ δ → ∀ x : Space,
      ϱ ≤ ‖x‖ → ‖sol.velocity t x‖ ≤ R := by
  sorry

/-- **Prodi–Serrin initial layer.**  With a bounded initial datum, a partial
classical solution carrying per-slice `L^p` integrability (`p > 3`) is
uniformly bounded on any closed initial layer `[0,δ]` with `δ < T`.

Assembled from the established compact core `compactSpaceTime_bounded`, routed
through `uniformBound_of_farField_window`, and the named far-field residual
`prodiSerrin_layer_farField_bounded`
[Prodi, Ann. Mat. Pura Appl. 48 (1959) 173–182;
Serrin, Arch. Rational Mech. Anal. 9 (1962) 187–195]. -/
theorem prodiSerrin_initialLayer_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (hu₀ : ∃ B₀ : ℝ, ∀ x : Space, ‖u₀ x‖ ≤ B₀)
    (p : ℝ) (hp : 3 < p)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    (δ : ℝ) (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ R₁ : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → t ≤ δ → ∀ x : Space,
      ‖sol.velocity t x‖ ≤ R₁ := by
  obtain ⟨ϱ, R₂, htail⟩ :=
    prodiSerrin_layer_farField_bounded hν sol hu₀ p hp hint δ hδ0 hδT
  obtain ⟨R, hR⟩ :=
    uniformBound_of_farField_window (a := 0) (b := δ) sol.velocity_smooth
      le_rfl hδT htail
  exact ⟨R, fun t ht0 _ htδ x => hR t ht0 htδ x⟩

/-- **[LEAF — Prodi–Serrin interior outer region; est ~450 LOC.]**  Away from
the initial time, the critical mixed-norm bound controls the velocity on the
*outer* region of the interior window: far field `ϱ ≤ ‖x‖`, or late times
`(δ+T)/2 < t`.  The temporal exponent hypothesis `2 < q` is exactly what
`serrin_exponent_gt_two` supplies from `p > 3` on the critical line, and it is
what makes the time integration in the Moser iteration converge.

This is the residual of `prodiSerrin_interior_bounded` *after*
`compactSpaceTime_bounded` discharges the compact core
`[δ,(δ+T)/2] × closedBall 0 ϱ`.  It is the original conclusion restricted to
the outer region, hence strictly weaker, and it is not circular.

Classical route: Serrin's local regularity criterion — on every parabolic
cylinder `Q_r(z)` with `r ≤ √δ` contained in `ℝ³ × (0,T)`, the critical norm
controls `‖u‖_{L^∞(Q_{r/2})}`; the global bound `M` makes the resulting
estimate uniform in the cylinder centre [Serrin, Arch. Ration. Mech. Anal. 9
(1962) 187–195; Struwe, Comm. Pure Appl. Math. 41 (1988) 437–458].
Depends on: parabolic Moser/De Giorgi iteration, the Caccioppoli inequality
for the local energy, and the Biot–Savart representation of the pressure —
none currently in Mathlib.

Frontier status: no parabolic Caccioppoli or Moser/De Giorgi layer exists
in-repo or in Mathlib.  `BiotSavartKernel` lands the kernel's elementary
algebra and its pointwise far-field `L²` tail bound, with the
Calderón–Zygmund near-field cancellation named as an honest residual in
`SingularIntegralPrelims`, so the pressure representation is not yet
available either. -/
theorem prodiSerrin_interior_outerRegion_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (p q : ℝ) (hp : 3 < p) (hq : 2 < q)
    (hcrit : Navier.Scaling.CriticalLine p q)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    (M : ℝ)
    (hM : ∀ T' : ℝ, 0 ≤ T' → T' < T →
      (∫ s in (0 : ℝ)..T',
        (∫ x : Space, ‖sol.velocity s x‖ ^ p) ^ (q / p)) ≤ M)
    (hMint : ∀ T' : ℝ, 0 ≤ T' → T' < T →
      IntervalIntegrable
        (fun s : ℝ => (∫ x : Space, ‖sol.velocity s x‖ ^ p) ^ (q / p)) volume 0 T')
    (δ : ℝ) (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ ϱ R : ℝ, ∀ t : ℝ, δ < t → t < T → ∀ x : Space,
      (ϱ ≤ ‖x‖ ∨ (δ + T) / 2 < t) → ‖sol.velocity t x‖ ≤ R := by
  sorry

/-- **Prodi–Serrin interior bound.**  Away from the initial time, the critical
mixed-norm bound gives a uniform velocity bound on `(δ,T)`.

Assembled from the established compact core `compactSpaceTime_bounded`, routed
through `interiorBound_of_outerRegion` at the split time `(δ+T)/2`, and the
named outer-region residual `prodiSerrin_interior_outerRegion_bounded`
[Serrin, Arch. Rational Mech. Anal. 9 (1962) 187–195]. -/
theorem prodiSerrin_interior_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (p q : ℝ) (hp : 3 < p) (hq : 2 < q)
    (hcrit : Navier.Scaling.CriticalLine p q)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    (M : ℝ)
    (hM : ∀ T' : ℝ, 0 ≤ T' → T' < T →
      (∫ s in (0 : ℝ)..T',
        (∫ x : Space, ‖sol.velocity s x‖ ^ p) ^ (q / p)) ≤ M)
    (hMint : ∀ T' : ℝ, 0 ≤ T' → T' < T →
      IntervalIntegrable
        (fun s : ℝ => (∫ x : Space, ‖sol.velocity s x‖ ^ p) ^ (q / p)) volume 0 T')
    (δ : ℝ) (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ R₂ : ℝ, ∀ t : ℝ, δ < t → t < T → ∀ x : Space,
      ‖sol.velocity t x‖ ≤ R₂ := by
  obtain ⟨ϱ, R, htail⟩ :=
    prodiSerrin_interior_outerRegion_bounded hν sol p q hp hq hcrit hint M hM
      hMint δ hδ0 hδT
  exact interiorBound_of_outerRegion (m := (δ + T) / 2) sol.velocity_smooth
    hδ0.le (by linarith) htail

/-- **[LEAF — Constantin–Fefferman far-field layer tail; est ~220 LOC.]**
Outside one closed ball, a finite-energy partial classical solution with
bounded initial datum is uniformly bounded on the closed initial layer `[0,δ]`.

Carries the integrability hypothesis `hL2` alongside the numeric bracket
`hmass`.  Both are needed: by `massBracket_vacuous_of_infiniteMass` the bracket
alone is satisfied by every field of infinite `L²` mass, which is what made the
previous statement of `constantinFefferman_initialLayer_bounded` false.  The
bridge supplies `hL2` for free through `uniformL2Integrable_of_energyBound`.

This is the residual after `compactSpaceTime_bounded` discharges the compact
core, so it is the original conclusion restricted to `ϱ ≤ ‖x‖`.

Classical route: the same Kato mild-solution short-time `L^∞` bound as in
`prodiSerrin_layer_farField_bounded`, with the `L²` mass replacing the `L^p`
slice control in the Duhamel estimate [Kato, Math. Z. 187 (1984) 471–480].
Depends on: the heat semigroup `L² → L^∞` smoothing estimate, the Leray
projector, and Gronwall — none currently in Mathlib.

Frontier status: identical to `prodiSerrin_layer_farField_bounded` with the
uniform `L²` mass bracket replacing the per-slice `L^p` control — the
kernel's `L^s` norms exist (`HeatSemigroupSmoothing`); the convolution
layer, the Duhamel representation for an arbitrary
`PartialClassicalSolution`, and the pointwise Leray projector do not. -/
theorem constantinFefferman_layer_farField_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (hu₀ : ∃ B₀ : ℝ, ∀ x : Space, ‖u₀ x‖ ≤ B₀)
    (E : ℝ) (hE : 0 ≤ E)
    (hL2 : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2))
    (hmass : ∀ t : ℝ, 0 ≤ t → t < T →
      (∫ x : Space, ‖sol.velocity t x‖ ^ 2) ∈ Set.Icc (0 : ℝ) E)
    (δ : ℝ) (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ ϱ R : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ δ → ∀ x : Space,
      ϱ ≤ ‖x‖ → ‖sol.velocity t x‖ ≤ R := by
  sorry

/-- **Constantin–Fefferman initial layer.**  With a bounded initial datum, the
uniform `L²` mass bracket and its integrability hypothesis, a finite-energy
partial classical solution is uniformly bounded on any closed initial layer
`[0,δ]` with `δ < T`.

Assembled from `compactSpaceTime_bounded` via `uniformBound_of_farField_window`
and the named residual `constantinFefferman_layer_farField_bounded`
[Constantin–Fefferman, Indiana Univ. Math. J. 42 (1993) 775–789]. -/
theorem constantinFefferman_initialLayer_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (hu₀ : ∃ B₀ : ℝ, ∀ x : Space, ‖u₀ x‖ ≤ B₀)
    (E : ℝ) (hE : 0 ≤ E)
    (hL2 : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2))
    (hmass : ∀ t : ℝ, 0 ≤ t → t < T →
      (∫ x : Space, ‖sol.velocity t x‖ ^ 2) ∈ Set.Icc (0 : ℝ) E)
    (δ : ℝ) (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ R₁ : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → t ≤ δ → ∀ x : Space,
      ‖sol.velocity t x‖ ≤ R₁ := by
  obtain ⟨ϱ, R₂, htail⟩ :=
    constantinFefferman_layer_farField_bounded hν sol hu₀ E hE hL2 hmass δ hδ0 hδT
  obtain ⟨R, hR⟩ :=
    uniformBound_of_farField_window (a := 0) (b := δ) sol.velocity_smooth
      le_rfl hδT htail
  exact ⟨R, fun t ht0 _ htδ x => hR t ht0 htδ x⟩

/-- **[LEAF — Constantin–Fefferman interior outer region; est ~400 LOC.]**
Away from the initial time, the uniform `L²` mass bracket with its
integrability hypothesis, together with the `ρ`-scaled Constantin–Fefferman
direction-coherence bound `hcoh`, controls the velocity on the *outer* region
of the interior window: far field `ϱ ≤ ‖x‖`, or late times `(δ+T)/2 < t`.

Carries `hL2` alongside `hmass` for the reason recorded in
`massBracket_vacuous_of_infiniteMass`: the bracket alone is satisfied by every
field of infinite `L²` mass, and the Tychonov shear flow described there has
vorticity everywhere parallel to `e₂`, hence satisfies every direction
hypothesis for every `ρ` and `Ω₀` while violating the conclusion.  That flow is
precisely what the previous statement of this leaf failed to exclude.

Carries `hcoh` rather than the collapsed `ε = 1` bound `hdep` it previously
carried: by `depletedCrossProduct_vacuous` that bound is a tautology, satisfied
by every velocity evolution whatsoever, so the leaf as previously stated
asserted the Constantin–Fefferman conclusion with *no* geometric hypothesis on
the vorticity direction.  `hcoh` is exactly the hypothesis the only caller
`constantinFefferman_velocity_bounded` already holds, and
`crossProductCoherent_of_directionLipschitz` supplies it from Lipschitz
continuity of `ξ = ω/|ω|`.

This is the residual after `compactSpaceTime_bounded` discharges the compact
core `[δ,(δ+T)/2] × closedBall 0 ϱ`.

Classical route: in the enstrophy budget the stretching term
`∫ ω · ∇u · ω` is rewritten through the Biot–Savart singular integral as a
kernel against `ω(x) ⨯ ω(y)`; direction coherence supplies the geometric
depletion factor, so the stretching term is dominated by the viscous term and
the enstrophy stays bounded, whence `L^∞` by Sobolev embedding
[Constantin–Fefferman, Indiana Univ. Math. J. 42 (1993) 775–789;
Constantin, SIAM Rev. 36 (1994) 73–98].
Depends on: the Biot–Savart singular integral and its Calderón–Zygmund
bounds, the enstrophy identity from `Navier.Analysis.Enstrophy`, and the
`H² ↪ L^∞` Sobolev embedding on `ℝ³` — the singular-integral layer is the
same Mathlib gap as in the Beale–Kato–Majda tower.

Frontier status: `Enstrophy` lands the pointwise vortex-stretching identity
(`vorticityTransportEquation`) while the integral enstrophy budget remains
open; `BiotSavartKernel` stops at the elementary kernel algebra and the
far-field `L²` tail, with the near-field cancellation named as an honest
residual in `SingularIntegralPrelims`; and `SobolevEmbedding`'s `H³ ↪ L^∞`
assembly still carries its disclosed Plancherel `sorryAx`, so even the
closing embedding is not yet residual-free. -/
theorem constantinFefferman_interior_outerRegion_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (E : ℝ) (hE : 0 ≤ E)
    (hL2 : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2))
    (hmass : ∀ t : ℝ, 0 ≤ t → t < T →
      (∫ x : Space, ‖sol.velocity t x‖ ^ 2) ∈ Set.Icc (0 : ℝ) E)
    (ρ Ω₀ : ℝ) (hρ : 0 < ρ) (hΩ₀ : 0 < Ω₀)
    (hcoh : ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t y) →
      officialEuclideanNorm
          (vorticity sol.velocity t x ⨯₃ vorticity sol.velocity t y) ≤
        (officialEuclideanNorm (fun i => x i - y i) / ρ) *
          (officialEuclideanNorm (vorticity sol.velocity t x) *
            officialEuclideanNorm (vorticity sol.velocity t y)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ ϱ R : ℝ, ∀ t : ℝ, δ < t → t < T → ∀ x : Space,
      (ϱ ≤ ‖x‖ ∨ (δ + T) / 2 < t) → ‖sol.velocity t x‖ ≤ R := by
  sorry

/-- **Constantin–Fefferman interior bound.**  Away from the initial time, the
uniform `L²` mass bracket with its integrability hypothesis, together with the
depleted cross-product bound, gives a uniform velocity bound on `(δ,T)`.

Assembled from `compactSpaceTime_bounded` via `interiorBound_of_outerRegion` at
the split time `(δ+T)/2` and the named outer-region residual
`constantinFefferman_interior_outerRegion_bounded`
[Constantin–Fefferman, Indiana Univ. Math. J. 42 (1993) 775–789]. -/
theorem constantinFefferman_interior_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (E : ℝ) (hE : 0 ≤ E)
    (hL2 : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2))
    (hmass : ∀ t : ℝ, 0 ≤ t → t < T →
      (∫ x : Space, ‖sol.velocity t x‖ ^ 2) ∈ Set.Icc (0 : ℝ) E)
    (ρ Ω₀ : ℝ) (hρ : 0 < ρ) (hΩ₀ : 0 < Ω₀)
    (hcoh : ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t y) →
      officialEuclideanNorm
          (vorticity sol.velocity t x ⨯₃ vorticity sol.velocity t y) ≤
        (officialEuclideanNorm (fun i => x i - y i) / ρ) *
          (officialEuclideanNorm (vorticity sol.velocity t x) *
            officialEuclideanNorm (vorticity sol.velocity t y)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ R₂ : ℝ, ∀ t : ℝ, δ < t → t < T → ∀ x : Space,
      ‖sol.velocity t x‖ ≤ R₂ := by
  obtain ⟨ϱ, R, htail⟩ :=
    constantinFefferman_interior_outerRegion_bounded hν sol E hE hL2 hmass
      ρ Ω₀ hρ hΩ₀ hcoh δ hδ0 hδT
  exact interiorBound_of_outerRegion (m := (δ + T) / 2) sol.velocity_smooth
    hδ0.le (by linarith) htail

/-! ### The two conditional-regularity bridges -/

/-- **[Ladyzhenskaya–Prodi–Serrin; Prodi 1959, Serrin 1962, ESŠ 2003.]**  A
partial classical solution on `[0,T)` with bounded initial datum whose
velocity carries a finite critical mixed norm — `∫₀^{T'} (∫ |u|^p)^{q/p} ≤ M`
uniformly in `T' < T`, with `(p,q)` on the Serrin critical line `2/q + 3/p = 1`
and `p > 3` — is uniformly bounded on `[0,T)`.  The spatial integrability of
`|u|^p` per time slice is hypothesis-carried so the mixed norm is a genuine
integral, not the Bochner junk value.

Assembled from `prodiSerrin_initialLayer_bounded` and
`prodiSerrin_interior_bounded` at the split time `δ = T/2` via
`uniformBound_of_split`, with the interior leaf's temporal exponent hypothesis
supplied by `serrin_exponent_gt_two`.  The hypothesis `hu₀` is necessary by
`initialDatum_bounded_of_uniformBound`. -/
theorem prodiSerrin_velocity_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (hu₀ : ∃ B₀ : ℝ, ∀ x : Space, ‖u₀ x‖ ≤ B₀)
    (p q : ℝ) (hp : 3 < p) (hcrit : Navier.Scaling.CriticalLine p q)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    (M : ℝ)
    (hM : ∀ T' : ℝ, 0 ≤ T' → T' < T →
      (∫ s in (0:ℝ)..T',
        (∫ x : Space, ‖sol.velocity s x‖ ^ p) ^ (q / p)) ≤ M)
    (hMint : ∀ T' : ℝ, 0 ≤ T' → T' < T →
      IntervalIntegrable
        (fun s : ℝ => (∫ x : Space, ‖sol.velocity s x‖ ^ p) ^ (q / p)) volume 0 T') :
    ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Space,
      ‖sol.velocity t x‖ ≤ R := by
  have hq : 2 < q := serrin_exponent_gt_two hp hcrit
  have hT : 0 < T := sol.terminalTime_pos
  have hδ0 : 0 < T / 2 := by linarith
  have hδT : T / 2 < T := by linarith
  obtain ⟨R₁, hR₁⟩ :=
    prodiSerrin_initialLayer_bounded hν sol hu₀ p hp hint (T / 2) hδ0 hδT
  obtain ⟨R₂, hR₂⟩ :=
    prodiSerrin_interior_bounded hν sol p q hp hq hcrit hint M hM hMint
      (T / 2) hδ0 hδT
  exact uniformBound_of_split (fun t x => ‖sol.velocity t x‖) R₁ R₂ hR₁ hR₂

/-- **[Constantin–Fefferman direction coherence; Indiana Univ. Math. J. 42
(1993) 775–789.]**  A finite-energy partial classical solution with bounded
initial datum whose vorticity direction is `ρ`-coherent in the high-vorticity
region — in the division-free cross-product form
`|ω(x) ⨯ ω(y)| ≤ (|x−y|/ρ)·|ω(x)|·|ω(y)|` whenever both vorticities exceed
`Ω₀` — is uniformly bounded on `[0,T)`.  (`|sin θ(ω(x), ω(y))| ≤ |x−y|/ρ` in
Constantin–Fefferman's notation; the cross product bilinearizes the sine.)

Assembled from `constantinFefferman_initialLayer_bounded` and
`constantinFefferman_interior_bounded` at the split time `δ = T/2` via
`uniformBound_of_split`, with the `L²` mass bracket supplied by
`uniformL2Mass_of_energyBound`/`energyBound_nonneg` and the direction-coherence
hypothesis `hcoh` forwarded verbatim to the interior leaf.  (It was previously
collapsed to the `ε = 1` bound `hdep` en route; `depletedCrossProduct_vacuous`
shows that collapse discarded the entire hypothesis.)  The hypothesis `hu₀` is
necessary by `initialDatum_bounded_of_uniformBound`. -/
theorem constantinFefferman_velocity_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (hu₀ : ∃ B₀ : ℝ, ∀ x : Space, ‖u₀ x‖ ≤ B₀)
    (E : ℝ)
    (henergy : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2) ∧
        kineticEnergy sol.velocity t ≤ E)
    (ρ Ω₀ : ℝ) (hρ : 0 < ρ) (hΩ₀ : 0 < Ω₀)
    (hcoh : ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t y) →
      officialEuclideanNorm
          (vorticity sol.velocity t x ⨯₃ vorticity sol.velocity t y) ≤
        (officialEuclideanNorm (fun i => x i - y i) / ρ) *
          (officialEuclideanNorm (vorticity sol.velocity t x) *
            officialEuclideanNorm (vorticity sol.velocity t y))) :
    ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Space,
      ‖sol.velocity t x‖ ≤ R := by
  have hT : 0 < T := sol.terminalTime_pos
  have hE : 0 ≤ E := energyBound_nonneg hT henergy
  have hL2 := uniformL2Integrable_of_energyBound henergy
  have hmass := uniformL2Mass_of_energyBound henergy
  have hδ0 : 0 < T / 2 := by linarith
  have hδT : T / 2 < T := by linarith
  obtain ⟨R₁, hR₁⟩ :=
    constantinFefferman_initialLayer_bounded hν sol hu₀ E hE hL2 hmass
      (T / 2) hδ0 hδT
  obtain ⟨R₂, hR₂⟩ :=
    constantinFefferman_interior_bounded hν sol E hE hL2 hmass ρ Ω₀ hρ hΩ₀ hcoh
      (T / 2) hδ0 hδT
  exact uniformBound_of_split (fun t x => ‖sol.velocity t x‖) R₁ R₂ hR₁ hR₂

end Navier.Analysis.ConditionalRegularity
