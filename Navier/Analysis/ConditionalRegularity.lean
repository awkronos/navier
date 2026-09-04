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
* `initialDatum_continuous`, `heatFlow_bounded_of_bounded`,
  `heatFlow_initialDatum_bounded` — the linear half of the Duhamel estimate
  shared by both far-field leaves: the initial datum of a partial classical
  solution is continuous (hence measurable), and the Gaussian heat flow of any
  measurable field bounded by `B` is again bounded by `B`, since the kernel is
  nonnegative with unit mass.  Previously trapped inside the `sorry`-carrying
  proof of `prodiSerrin_layer_farField_bounded`; now kernel-clean and reusable,
  so what remains open in both far-field leaves is exactly the nonlinear
  Duhamel correction.
* `WholeSpaceDuhamel.cutoff_testedMomentum_coordinate` — the first honest
  pointwise-solution representation leaf: against every smooth compactly
  supported scalar test, the zero-force momentum equation is integrated by
  parts with convection, viscosity, and pressure derivatives moved onto the
  test.  Its first proof-producing consumer is
  `WholeSpaceCutoffLimit.cutoffMomentumCoordinate_timeIntegrated`: compact
  support and the actual partial-solution smoothness justify differentiation
  under the spatial integral and give the exact time-integrated tested
  momentum balance on `[a,b] ⊂ (0,T)`.  This remains a standalone finite-cutoff
  artifact, not a proof input to either far-field leaf.
  `WholeSpaceDuhamel.heatKernel_translate_not_hasCompactSupport` proves why the
  Gaussian itself still needs a cutoff-limit argument, while
  `WholeSpaceDuhamel.cutoff_pressurePairing_add_const` keeps the pressure slot
  gauge invariant.
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

This is the *linear half* of the Duhamel estimate shared by both far-field
leaves below — `prodiSerrin_layer_farField_bounded` and
`constantinFefferman_layer_farField_bounded` — where it bounds `e^{tνΔ}u₀` by
`‖u₀‖_∞`.  Isolating it here makes it a kernel-clean, reusable theorem instead
of a fragment trapped inside a `sorry`-carrying proof; what remains open in
both leaves is exactly the nonlinear Duhamel correction. -/
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

/-! ### The Duhamel (variation-of-constants) decomposition of the layer leaves

Both far-field layer leaves — `prodiSerrin_layer_farField_bounded` and
`constantinFefferman_layer_farField_bounded` — previously carried the *whole*
Kato mild-solution argument inside one `sorry`, described only in prose ("the
Duhamel formula is the missing piece").  A prose description is not a carrier:
nothing in the file named the object whose bound was missing, so neither leaf
could be attacked below itself.

The decomposition below makes that object real.  Reading the momentum equation
as a forced heat equation `∂ₜu − νΔu = −((u·∇)u + ∇p)` names the source
(`duhamelSource`) and the variation-of-constants correction
(`duhamelNonlinear`) as explicit integrals of estate-defined quantities —
`convection`, `pressureGradient` and `heatKernel` — with no opaque carrier and
no Leray projector.  `layerBound_of_duhamelNonlinear_bounded` then discharges
the layer conclusion from the representation plus a uniform bound on that one
correction, kernel-clean.

Statement hygiene, checked before landing.  The pinning matters and is the
whole point: an interface that merely postulated *some* function `N` with
`u = e^{tνΔ}u₀ + N` and `‖N‖ ≤ C` would be satisfied by `N := u − e^{tνΔ}u₀`
for every solution whatsoever, making the hypothesis bundle an alias of the
conclusion (`epistemic-rigor.md` §"UNDER-SPECIFIED relative to its consumer").
`duhamelNonlinear` is a *definition*, not a parameter, so that route is closed:
`duhamelRepresentation_layer` is a genuine analytic assertion about a specific
integral, and `duhamelNonlinear_bounded_of_*` is a genuine estimate on it.
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

/-- **[LEAF — the variation-of-constants representation; est ~400 LOC.]**  On
the closed layer `(0,δ]` a partial classical solution equals the heat flow of
its initial datum plus the Duhamel correction of the momentum-equation source.

This is the *only* place the mild formulation is asserted, and it is asserted
about explicitly named integrals rather than described in prose.

Classical route: `sol.equation` gives `∂ₜu − νΔu = duhamelSource` pointwise;
Duhamel/variation of constants for the heat semigroup on `ℝ³` then converts the
pointwise ODE-in-`t` statement into the integral identity, which requires
`d/ds ∫ G^ν_{t−s}(x−y) u(s,y) dy = ∫ G^ν_{t−s}(x−y) (duhamelSource)(s,y) dy`
and the boundary behaviour `G^ν_{t−s} → δ` as `s → t`
[Kato, Math. Z. 187 (1984) 471–480, §1; Giga–Miyakawa, Arch. Ration. Mech.
Anal. 89 (1985) 267–281].

Frontier status: the estate has the kernel and its `L^s` norms
(`HeatSemigroupSmoothing.integral_heatKernel_rpow`, `heatKernel_Lr_scaling`),
the Young/convolution layer (`heatKernel_convolution_abs_le`,
`heatKernel_convolution_smoothing_le`), an exact finite-cutoff momentum
representation (`WholeSpaceDuhamel.cutoff_testedMomentum_coordinate`) and its
interior-time FTC composition
(`WholeSpaceCutoffLimit.cutoffMomentumCoordinate_timeIntegrated`).  What is
missing is the removal of the spatial cutoff without a Gaussian test function:
`WholeSpaceDuhamel.heatKernel_translate_not_hasCompactSupport` shows this is a
genuine limit step, and its boundary terms need tail control of `u` and `∇u`
that no per-slice integrability hypothesis supplies.

This leaf is strictly lower than the two layer leaves it replaces: it carries
no conclusion about boundedness at all, only the identity. -/
theorem duhamelRepresentation_layer
    {ν : ℝ} (hν : 0 < ν) {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    {δ : ℝ} (hδ0 : 0 < δ) (hδT : δ < T) :
    ∀ t : ℝ, 0 < t → t ≤ δ → ∀ x : Space,
      sol.velocity t x
        = (∫ y : Space, heatKernel ν t (x - y) • u₀ y)
          + duhamelNonlinear sol t x := by
  by_cases hvelocity : sol.velocity = (0 : VelocityEvolution)
  · exact duhamelRepresentation_layer_of_velocity_eq_zero
      hν sol hvelocity hδ0 hδT
  · sorry

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
exceed any prescribed number.  Therefore the energy bracket in
`duhamelNonlinear_bounded_of_L2` cannot by itself supply the uniform source
bound; a derivative estimate using additional PDE structure is indispensable. -/
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

This is the complete `L^r → L^∞`-smoothing-plus-time-integration route that
`duhamelNonlinear_bounded_of_Lp` and `duhamelNonlinear_bounded_of_L2` were both
described as needing.  The threshold `r > 3/2` is not decoration: it is exactly
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
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hν ht _)]

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


/-- **[LEAF — `L^p` smoothing bound on the Duhamel correction; est ~250 LOC.]**
Under the Prodi–Serrin mixed-norm hypothesis the Duhamel correction is
uniformly bounded on the layer.

Classical route: `‖∫ G^ν_{t−s}(x−·) F(s,·)‖_∞ ≤ C(r,ν)(t−s)^{−3/(2r)}‖F(s)‖_r`
— which the estate already certifies as
`HeatSemigroupSmoothing.heatKernel_convolution_smoothing_le` — integrated in
`s` against the critical mixed norm `∫₀^{T'}‖u(s)‖_p^q ds ≤ M`.  The exponent
condition `2/q + 3/p = 1` with `p > 3` is exactly what makes
`∫₀ᵗ (t−s)^{−3/(2r)} ‖F(s)‖_r ds` converge.
Depends on: `‖duhamelSource(s)‖_r` control, i.e. `L^r` bounds on `(u·∇)u` and
on `∇p`.  The `∇p` half is available with no singular-integral input from
`PressureNormalization.pressureGradient_eq_of_solution` /
`memLp_pressureGradient_of_terms`; the `(u·∇)u` half needs a gradient bound the
`L^p` slice hypothesis alone does not give.

This leaf is strictly lower than `prodiSerrin_layer_farField_bounded`: it is a
bound on one explicitly written integral, and it says nothing about
`sol.velocity`.

**Residual narrowed 2026-09-02, and the estimate itself is no longer part of
it.**  `duhamelNonlinear_bounded_of_source_Lr` (above, kernel-clean, axioms
`[propext, Classical.choice, Quot.sound]`) proves the entire `L^r → L^∞`
smoothing-plus-time-integration route for every `r > 3/2`, with the constant
hoisted above the slice.  The Prodi–Serrin exponent `p > 3` satisfies
`p > 3/2`, so this leaf now needs from that theorem exactly three things and
nothing else:

* a uniform `L^p` bound `S` on the *source* `duhamelSource sol s` over the
  layer — i.e. `L^p` control of `(u·∇)u` and `∇p`, which is where the
  remaining mathematics is;
* slice integrability of `‖duhamelSource sol s‖^p`.

Joint source continuity and time integrability of the convolution norm are
now constructed by `duhamelConvolution_intervalIntegrable_of_source_Lr`
from the same source bound. They impose no independent remaining premise.

The `∇p` half of the first item is already available from
`PressureNormalization.pressureGradient_eq_of_solution` /
`memLp_pressureGradient_of_terms` with no singular-integral input.  What is
genuinely open is the `(u·∇)u` half: the `L^p` slice hypothesis on `u` does
not bound `∇u`.  Nothing about the heat semigroup, Young's inequality, or the
convergence of `∫₀ᵗ (t−s)^{−3/(2p)} ds` remains here — those are theorems now
(`intervalIntegral_sub_rpow_neg`,
`heatKernel_convolution_norm_vec_le_uniform`). -/
theorem duhamelNonlinear_bounded_of_Lp
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
    {δ : ℝ} (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ δ → ∀ x : Space,
      ‖duhamelNonlinear sol t x‖ ≤ C := by
  sorry

/-- **[LEAF — `L²` smoothing bound on the Duhamel correction; est ~250 LOC.]**
The Constantin–Fefferman twin of `duhamelNonlinear_bounded_of_Lp`, with the
uniform `L²` mass bracket replacing the critical mixed norm.

Carries `hL2` alongside `hmass` for the reason recorded in
`massBracket_vacuous_of_infiniteMass`: the bracket alone is satisfied by every
field of infinite `L²` mass.

Classical route: the same `L^r → L^∞` heat smoothing
(`heatKernel_convolution_smoothing_le`) with `r = 2`, integrated against the
energy bound [Kato, Math. Z. 187 (1984) 471–480].
Depends on: `L²` control of `duhamelSource`, i.e. of `(u·∇)u` and `∇p`.

**Residual narrowed 2026-09-02.**  `r = 2 > 3/2`, so
`duhamelNonlinear_bounded_of_source_Lr` (above, kernel-clean, axioms
`[propext, Classical.choice, Quot.sound]`) discharges the whole
`L² → L^∞`-smoothing-and-time-integration argument this leaf was described as
needing.  Spatial measurability of the source is now discharged by
`duhamelSource_slice_measurable`.  What is left is exactly: slice `L²`
integrability and a uniform `L²` bound on the *source* over the layer.
`duhamelConvolution_intervalIntegrable_of_source_Lr` now proves the
time-integrability premise from these same inputs and actual joint source
regularity. The
`∇p` half of the source bound is available without singular integrals
(`memLp_pressureGradient_of_terms`); the open half is `L²` control of
`(u·∇)u`, which the energy bracket `hmass` alone does not supply — it bounds
`u`, not `∇u`.  That gap, and not the heat semigroup, is the mathematics. -/
theorem duhamelNonlinear_bounded_of_L2
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (E : ℝ) (hE : 0 ≤ E)
    (hL2 : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2))
    (hmass : ∀ t : ℝ, 0 ≤ t → t < T →
      (∫ x : Space, ‖sol.velocity t x‖ ^ 2) ∈ Set.Icc (0 : ℝ) E)
    {δ : ℝ} (hδ0 : 0 < δ) (hδT : δ < T) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ δ → ∀ x : Space,
      ‖duhamelNonlinear sol t x‖ ≤ C := by
  have hsm : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      Measurable (duhamelSource sol s) := by
    intro s hs0 hsδ
    exact duhamelSource_slice_measurable sol hs0 (lt_of_le_of_lt hsδ hδT)
  have hsi : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      Integrable (fun y : Space => ‖duhamelSource sol s y‖ ^ (2 : ℝ)) := by
    -- SCIENTIFIC_FRONTIER: `L²` control of convection and pressure gradient.
    sorry
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      (∫ y : Space, ‖duhamelSource sol s y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ S := by
    -- SCIENTIFIC_FRONTIER: uniform source bound; the energy controls `u`,
    -- not the derivative in `(u·∇)u`.
    sorry
  have hNint : ∀ t : ℝ, 0 < t → t ≤ δ → ∀ x : Space,
      IntervalIntegrable
        (fun s : ℝ => ‖∫ y : Space,
          heatKernel ν (t - s) (x - y) • duhamelSource sol s y‖)
        volume 0 t := by
    intro t ht0 htδ x
    exact duhamelConvolution_intervalIntegrable_of_source_Lr hν sol hδT
      (r := 2) (by norm_num) hsi S hS ht0 htδ x
  exact duhamelNonlinear_bounded_of_source_Lr hν sol hδ0
    (r := 2) (by norm_num) hsm hsi S hS hNint

/-- **[ASSEMBLY — Prodi–Serrin far-field layer tail.]**  Outside one
closed ball, a partial classical solution with bounded initial datum and
per-slice `L^p` integrability (`p > 3`) is uniformly bounded on the closed
initial layer `[0,δ]`.

**Decomposed 2026-09-02 (lane NAVIER2).**  This is no longer a leaf: the proof
below is a kernel-clean assembly of `layerBound_of_duhamelNonlinear_bounded`
over two strictly lower named residuals, `duhamelRepresentation_layer` (shared
with the Constantin–Fefferman twin) and `duhamelNonlinear_bounded_of_Lp`.  The
conclusion it actually gets from that reduction is stronger than the one stated
here — `ϱ = 0`, i.e. the bound holds on all of space — and the far-field form is
kept because it is what the caller consumes.  The prose route recorded below is
retained as the reference for the two residuals.

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

Frontier status: `HeatSemigroupSmoothing` now lands the Gaussian kernel, its
`L^s` norms (`integral_heatKernel_rpow`, `heatKernel_Lr_scaling`), and the
convolution (Young) layer — `heatKernel_convolution_abs_le` and
`heatKernel_convolution_smoothing_le` give the pointwise smoothing bound
`|∫ G_t^ν(x−y) f(y)| ≤ C(r,ν) t^{-3/(2r)} ‖f‖_r`.  The finite-cutoff spatial
transport is now certified by
`WholeSpaceDuhamel.cutoff_testedMomentum_coordinate`, and
`WholeSpaceCutoffLimit.cutoffMomentumCoordinate_timeIntegrated` performs its
interior-time FTC composition.  The theorems immediately above now prove
convergence of the complete finite-cutoff right-hand side to the increment of
Gaussian-tested momentum under the present `L^p` hypothesis and identify the
complete product-rule convection limit.  Still missing: convergence of the
viscosity/pressure terms, uniform domination in the Duhamel time variable, and
the Leray projection.
`WholeSpaceDuhamel.heatKernel_translate_not_hasCompactSupport` shows that this
is a genuine limit step; its boundary terms require tail control of the
solution and its first spatial derivatives that the per-slice `L^p` hypothesis
alone does not supply (narrow bump constructions defeat such pointwise
derivative decay).  Raw pressure `L^p` cannot replace that step:
for every solution and finite positive exponent, some pressure gauge shift
preserves the velocity while leaving the raw pressure outside `L^p`.  The
in-repo Duhamel developments
`FrequencyDuhamel`/`CriticalMild*` act on one-frequency or lattice encodings,
not on pointwise classical solutions; and the Leray projector as a pointwise
bounded kernel.

**Statement repair 2026-09-02 (lane NAVIER).**  This leaf previously carried
no Serrin criterion at all: only a bounded initial datum and *per-slice* `L^p`
integrability, with no control of `t ↦ ‖u(t)‖_{L^p}` as a function of time.
That is strictly stronger than Prodi–Serrin and it is not what the leaf's own
stated route consumes — the Duhamel estimate needs
`∫₀^{T'} ‖u(s)‖_{L^p}^q ds ≤ M` on the critical line, which is precisely the
Ladyzhenskaya–Prodi–Serrin hypothesis the theorem is named after.  The
mixed-norm data `(q, hq, hcrit, M, hM, hMint)` is now carried here.  It costs
the consumer nothing: `prodiSerrin_velocity_bounded`, the only caller of the
chain, already holds all six and previously discarded them on the
initial-layer branch while forwarding them on the interior branch.  The leaf
is therefore *strictly lower* than before, and its route is now stated over
the hypotheses that route actually uses. -/
theorem prodiSerrin_layer_farField_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (hu₀ : ∃ B₀ : ℝ, ∀ x : Space, ‖u₀ x‖ ≤ B₀)
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
    ∃ ϱ R : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ δ → ∀ x : Space,
      ϱ ≤ ‖x‖ → ‖sol.velocity t x‖ ≤ R := by
  -- Now an assembly, not a leaf.  `layerBound_of_duhamelNonlinear_bounded`
  -- discharges the conclusion kernel-clean from two strictly lower named
  -- facts: the variation-of-constants representation and a uniform bound on
  -- the Duhamel correction under the critical mixed norm.  The linear half
  -- (`heatFlow_initialDatum_bounded`) is inside that reduction.
  obtain ⟨B₀, hu₀B⟩ := hu₀
  obtain ⟨C, hC⟩ :=
    duhamelNonlinear_bounded_of_Lp hν sol p q hp hq hcrit hint M hM hMint hδ0 hδT
  exact layerBound_of_duhamelNonlinear_bounded hν sol hu₀B hδ0
    (duhamelRepresentation_layer hν sol hδ0 hδT) hC

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
    ∃ R₁ : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → t ≤ δ → ∀ x : Space,
      ‖sol.velocity t x‖ ≤ R₁ := by
  obtain ⟨ϱ, R₂, htail⟩ :=
    prodiSerrin_layer_farField_bounded hν sol hu₀ p q hp hq hcrit hint M hM hMint
      δ hδ0 hδT
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

Frontier status (N3 sweep 2026-08-21): `ParabolicCaccioppoli` lands the
pointwise local energy identity `local_energy_balance` and the De
Giorgi–Moser engine `deGiorgiMoser_tendsto_zero`, and former blocker (a)
is now certified: `CutoffEnergyIbp.cutoffEnergy_ibp_eq` gives the cutoff
IBP balance.  Blocker (b) — "an `L^r` pressure bound for `∫ χ² ⟨∇p, u⟩`;
no `MemLp`/`Integrable` estimate for `sol.pressure` exists in the estate"
— has now been *analysed rather than merely restated*, in
`Navier.Analysis.PressureNormalization`, and it splits in three:

* **The raw-pressure form of (b) is FALSE as stated.**
  `PressureNormalization.not_forall_memLp_pressure` refutes it with an
  explicit witness (that theorem's own axiom audit is in its file):
  `SatisfiesNavierStokesBefore` constrains the pressure only through
  `pressureGradient`, so `PressureNormalization.shiftPressure` produces, from
  any solution, another solution with the same velocity and pressure shifted
  by an arbitrary constant; a nonzero constant lies in no `L^r(ℝ³)` for
  `0 < r < ∞`.  There was never a `MemLp` estimate for `sol.pressure` to find.
* **The `∇p` half of (b) is discharged, with no singular-integral input.**
  `PressureNormalization.pressureGradient_eq_of_solution` solves the momentum
  equation for `∇p = ν Δu + f − ∂ₜu − (u·∇)u`, and
  `memLp_pressureGradient_of_terms` / `integrable_pressureGradient_of_terms`
  transport `MemLp`/`Integrable` from the velocity terms to `∇p`.
* **The remaining residual is well posed after normalization.**  The
  derivative-free slot `2 ∫ p · χ (∇χ·u)` of
  `CutoffEnergyIbp.cutoffEnergy_pressure_ibp` is gauge invariant
  (`PressureNormalization.cutoffPressure_add_const`, via the vanishing cutoff
  flux `integral_cutoff_flux_eq_zero` of a divergence-free field), and the
  `L^r`-normalized pressure is unique
  (`PressureNormalization.pressure_eq_of_memLp`).

`PressureNormalization.abs_cutoffPressure_le_localL2` then bounds that slot by
`√(∫ (χp)²) · √(∫ (∇χ·u)²)`, the second factor unconditionally finite.  So (b)
is now exactly one named leaf: a **local** `L²` bound `∫ (χp)² ≤ …` for the
normalized pressure, which still needs the Calderón–Zygmund representation
`p = Σ RᵢRⱼ(uᵢuⱼ)`.

**Status repair 2026-09-02 (lane NAVIER2).**  The sentence this paragraph used
to end with — "the transform's `L^r` bounds stay a named residual in
`SingularIntegralPrelims`" — is no longer true at `r = 2`, and `r = 2` is the
only exponent this blocker needs.  Plancherel is present in the pinned Mathlib
`v4.31.0` (`Mathlib/Analysis/Fourier/LpSpace.lean`), and the whole `p = 2`
Calderón–Zygmund layer is now certified kernel-clean:
`SingularIntegralPrelims.l2_multiplier_bound` (every bounded Fourier multiplier
is `L²`-bounded with the same constant), `exists_l2_multiplier_apply` (the
operator exists, so the bound is not about an empty hypothesis set),
`doubleRiesz_l2_bound` and `exists_doubleRieszTransform` (`‖RᵢRⱼf‖₂ ≤ ‖f‖₂`,
realised), and — on this estate's own carrier `Space = Fin 3 → ℝ`, transported
along the volume-preserving coordinate identification —
`PressureL2Riesz.pressure_l2_bound_space`:

  `P = Σᵢⱼ RᵢRⱼ(wᵢⱼ)`  ⟹  `‖P‖₂ ≤ Σᵢⱼ ‖wᵢⱼ‖₂`.

So blocker (b) has halved.  What is left of it is *not* an operator bound at
all: it is the **representation** `p = Σᵢⱼ RᵢRⱼ(uᵢuⱼ)` itself — the solution of
the pressure Poisson equation `−Δp = Σᵢⱼ ∂ᵢ∂ⱼ(uᵢuⱼ)` for a partial classical
solution, together with the localisation of the resulting global `L²` bound to
`∫ (χp)²`.  `CZNearField` certifies the pointwise Hörmander core; the `r ≠ 2`
theory (weak-`(1,1)`, Marcinkiewicz) remains genuinely Mathlib-absent but is
not needed here.

The remaining blockers of this leaf are therefore three, and the pressure one
is now the smallest: (i) the integrated Caccioppoli inequality, (ii) the
parabolic Moser/De Giorgi iteration to `L^∞`, and (iii) the pressure
representation above. -/
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
  -- The classical route is Serrin's local regularity criterion: on every parabolic
  -- cylinder Q_r(z) with r ≤ √δ contained in ℝ³ × (0,T), the critical mixed-norm
  -- bound controls ‖u‖_{L^∞(Q_{r/2})}; the global bound M makes the estimate
  -- uniform in the cylinder centre.  This is a parabolic Moser/De Giorgi iteration
  -- argument.
  --
  -- The estate has `ParabolicCaccioppoli` which lands:
  --   * `local_energy_balance` — the pointwise local energy identity
  --   * `deGiorgiMoser_tendsto_zero` — the De Giorgi–Moser engine
  --   * `CutoffEnergyIbp.cutoffEnergy_ibp_eq` — the cutoff IBP balance
  -- The integrated Caccioppoli inequality itself is still missing.  Its
  -- pressure blocker has been analysed in `PressureNormalization`:
  --   * `not_forall_memLp_pressure` — the raw-pressure `MemLp` statement is
  --     FALSE for every `0 < r < ∞`, witness `shiftPressure sol 1`; the
  --     system constrains `p` only through `∇p`, so `p` is free up to an
  --     additive constant and a nonzero constant is in no `L^r(ℝ³)`.
  --   * `pressureGradient_eq_of_solution`, `memLp_pressureGradient_of_terms`
  --     — the `∇p` half is available outright from the momentum equation,
  --     with no singular-integral input.
  --   * `cutoffPressure_add_const`, `pressure_eq_of_memLp` — the
  --     derivative-free Caccioppoli slot is gauge invariant and the
  --     `L^r`-normalized pressure is unique, so the residual is well posed.
  --   * `abs_cutoffPressure_le_localL2` — that slot is bounded by
  --     √(∫ (χp)²)·√(∫ (∇χ·u)²), the second factor unconditionally finite.
  -- What remains is a local `L²` bound on the NORMALIZED pressure, i.e. the
  -- Calderón–Zygmund representation `p = Σ RᵢRⱼ(uᵢuⱼ)`.  `CZNearField`
  -- certifies the pointwise Hörmander core, but the singular integral's L^r
  -- bounds stay a named residual in `SingularIntegralPrelims`.
  --
  -- Without that bound, the De Giorgi–Moser engine cannot produce the
  -- `L^∞_t L^∞_x` bound that the outer-region conclusion requires.
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

/-- **[ASSEMBLY — Constantin–Fefferman far-field layer tail.]**
Outside one closed ball, a finite-energy partial classical solution with
bounded initial datum is uniformly bounded on the closed initial layer `[0,δ]`.

**Decomposed 2026-09-02 (lane NAVIER2).**  No longer a leaf: a kernel-clean
assembly of `layerBound_of_duhamelNonlinear_bounded` over
`duhamelRepresentation_layer` (shared with the Prodi–Serrin twin) and
`duhamelNonlinear_bounded_of_L2`.

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
kernel's `L^s` norms and the convolution (Young) layer exist
(`HeatSemigroupSmoothing`, in particular
`heatKernel_convolution_smoothing_le`); the Duhamel representation for an
arbitrary `PartialClassicalSolution` and the pointwise Leray projector do
not. -/
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
  -- The same assembly as `prodiSerrin_layer_farField_bounded`, with the
  -- uniform `L²` mass bracket replacing the critical mixed norm in the bound
  -- on the Duhamel correction.  The representation leaf is shared.
  obtain ⟨B₀, hu₀B⟩ := hu₀
  obtain ⟨C, hC⟩ :=
    duhamelNonlinear_bounded_of_L2 hν sol E hE hL2 hmass hδ0 hδT
  exact layerBound_of_duhamelNonlinear_bounded hν sol hu₀B hδ0
    (duhamelRepresentation_layer hν sol hδ0 hδT) hC

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
`H² ↪ L^∞` Sobolev embedding on `ℝ³`.

**Status repair 2026-09-02 (lane NAVIER2).**  The `L²` half of the
singular-integral dependency is no longer a gap:
`SingularIntegralPrelims.riesz_l2_bound` / `exists_rieszTransform` certify
`‖Rⱼf‖₂ ≤ ‖f‖₂` kernel-clean via Plancherel, which is present in the pinned
Mathlib.  That is *not* enough for this leaf, and the docstring should not be
read as claiming it is: the Constantin–Fefferman stretching term needs the
Biot–Savart **representation** of `∇u` in the pairwise-vorticity form that
`hcoh` depletes, plus `L^r` control for `r ≠ 2` in the enstrophy budget, and
both remain absent.  What has changed is that the operator-boundedness half of
the dependency is discharged at the exponent where the energy space lives.

Frontier status (N4 sweep 2026-08-18): `Enstrophy` lands the pointwise
identity `vorticityTransportEquation`; the integral enstrophy budget
stays open, and no sound Biot–Savart representation of `∇u`
exists (routes use the open leaf `exists_biotSavartLogTextbook`).  The
closing embedding IS residual-free: `sobolevEmbeddingDomination_H3` is
vetted since `19192df` (N4-verified via `#print axioms`); caveat —
it needs `SchwartzVelocity` slices; slice-Schwartz control stays open. -/
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
  -- The classical Constantin–Fefferman route: in the enstrophy budget the
  -- stretching term ∫ ω·∇u·ω is rewritten through the Biot–Savart singular
  -- integral as a kernel against ω(x) ⨯ ω(y); direction coherence supplies
  -- the geometric depletion factor, so the stretching term is dominated by
  -- the viscous term and the enstrophy stays bounded, whence L^∞ by Sobolev
  -- embedding.
  --
  -- The estate has:
  --   * `Enstrophy.vorticityTransportEquation` — the pointwise vorticity
  --     transport equation
  --   * `sobolevEmbeddingDomination_H3` — kernel-clean H² ↪ L^∞ Sobolev
  --     embedding (for Schwartz slices)
  --   * `hcoh` — the genuine Constantin–Fefferman direction coherence
  -- Still missing:
  --   * The integral enstrophy budget (the pointwise identity exists, but
  --     the integrated identity with boundary terms at infinity is open)
  --   * A kernel-clean Biot–Savart representation of ∇u (routes use the
  --     open leaf `exists_biotSavartLogTextbook`)
  --   * Slice-Schwartz control (the Sobolev embedding needs Schwartz slices)
  -- Without the Biot–Savart representation, the stretching term cannot be
  -- expressed in the pairwise-vorticity form that `hcoh` depletes.
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
    prodiSerrin_initialLayer_bounded hν sol hu₀ p q hp hq hcrit hint M hM hMint
      (T / 2) hδ0 hδT
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
  have henergy' : ∀ t : ℝ, 0 ≤ t → t < T →
      AEStronglyMeasurable (sol.velocity t) volume ∧
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2) ∧ kineticEnergy sol.velocity t ≤ E :=
    fun t ht0 htT =>
      ⟨Navier.Analysis.ESSInputs.PartialClassicalSolution.velocity_slice_aestronglyMeasurable
          sol ht0 htT, henergy t ht0 htT⟩
  have hE : 0 ≤ E := energyBound_nonneg hT henergy'
  have hL2 := uniformL2Integrable_of_energyBound henergy'
  have hmass := uniformL2Mass_of_energyBound henergy'
  have hδ0 : 0 < T / 2 := by linarith
  have hδT : T / 2 < T := by linarith
  obtain ⟨R₁, hR₁⟩ :=
    constantinFefferman_initialLayer_bounded hν sol hu₀ E hE hL2 hmass
      (T / 2) hδ0 hδT
  obtain ⟨R₂, hR₂⟩ :=
    constantinFefferman_interior_bounded hν sol E hE hL2 hmass ρ Ω₀ hρ hΩ₀ hcoh
      (T / 2) hδ0 hδT
  exact uniformBound_of_split (fun t x => ‖sol.velocity t x‖) R₁ R₂ hR₁ hR₂

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

/-- **Sharpness witness: the integrability hypotheses of the far-field leaves
are load-bearing.**  For every viscosity `ν`, every horizon `T > 0` and every
layer thickness `δ ∈ (0,T)`, the strain solution `strainSolution` satisfies
*every* hypothesis of `prodiSerrin_layer_farField_bounded` and of
`constantinFefferman_layer_farField_bounded` except the integrability clauses
(`hint`, respectively `hL2`) — in particular its initial datum is bounded,
being identically zero — and yet its far-field conclusion

`∃ ϱ R, ∀ t ∈ [0,δ], ∀ x with ϱ ≤ ‖x‖, ‖u t x‖ ≤ R`

is false: at any fixed `t > 0` the velocity grows linearly in `x`.

Consequences.  (i) No proof of either far-field leaf can avoid using its
integrability hypothesis; the smoothness, incompressibility, equation and
bounded-initial-datum data are jointly insufficient.  (ii) Since the initial
datum is zero and the flow is not, this is also a kernel-checked instance of
non-uniqueness for `PartialClassicalSolution` in the absence of a decay or
integrability clause — the elementary analogue of the Tychonov shear flow
recorded in the falsification note above, with an explicit closed form in
place of Tychonov's non-analytic series.

Scope.  The witness does *not* refute the two leaves: the strain velocity is a
nonzero linear field, so it fails `hint` and `hL2`.  This file does not
formalize that failure; the statement below claims only what it proves. -/
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

/-- **Sharpness for the two interior outer-region leaves.**  The strain
solution satisfies every hypothesis of `prodiSerrin_interior_outerRegion_bounded`
except `hint` — the mixed-norm budget `hM` and its integrability `hMint` hold
for *every* `M ≥ 0` because the slice integrals take Lean's junk value `0` —
and every hypothesis of `constantinFefferman_interior_outerRegion_bounded`
except `hL2`, since its vorticity vanishes identically
(`strainVelocity_vorticity`) so the direction-coherence hypothesis `hcoh` is
vacuous, and the mass bracket `hmass` again holds for every `E ≥ 0`.  Its
outer-region conclusion nevertheless fails. -/
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
