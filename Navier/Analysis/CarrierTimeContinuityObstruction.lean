import Navier.Analysis.GalerkinRawFamily
import Navier.Analysis.RestartAgreementOpen
import Navier.Breakdown.MaximalNonextension

/-!
# The carrier's missing time continuity, with its witness  (ledger `F-026`)

Three places in this repository justify the same fact **in prose and never prove it**:

* `Analysis.ClassRestartDecomposition`, header bullet 2: "`SolvesBefore` carries no time
  continuity: a jointly smooth evolution with finite-energy slices can fail to be continuous
  into `L²` (a bump translated to infinity as `t ↓ 0`, extended by zero), so the Serrin/Kato
  energy argument for uniqueness has nothing to differentiate";
* `Analysis.RestartAgreementOpen`, "Why the cheap routes fail (**measured**, not assumed)",
  bullet 2: "Needs `E ε → E 0` in `L²`, i.e. right-continuity of the *energy*, which pointwise
  hypotheses cannot give (mass escaping to spatial infinity keeps `‖u ε - v ε‖_{L²}` bounded
  away from `0` while converging pointwise to `0`)";
* `Analysis.EnvelopePropagation` §3, where the residual rung `EnvelopeBudgetContinuousOn` (P1)
  cites the same parenthetical as the reason the envelope map's time-continuity is not a
  structural consequence of `SolvesBefore` + `RegularOnCompacts`.

This file mechanizes the named witness: the certified divergence-free curl-of-bump field
`phifun` (`Analysis.LerayWeak`), translated along the first axis to `1/t` as `t → 0` and
extended by zero at `t = 0`.

## What is proved

* `contDiff_escapingCarrier` — the witness is jointly `C^∞` on the **whole** spacetime
  `ℝ × ℝ³`, strictly more than the carrier clause `SmoothVelocityBefore T` asks (that one only
  needs `ContDiffOn` on `[0,T) × ℝ³`).  The case split costs nothing: near every point of the
  initial hyperplane `{0} × ℝ³` the field is *locally identically* zero, the bump's support
  having already escaped past that point (`escapingCarrier_eq_zero_of_near`).
* `escapingCarrier_incompressible`, `escapingCarrier_incompressibleBefore`,
  `integrable_sumSq_density_escapingCarrier`, `integrable_normSq_density_escapingCarrier`,
  `escapingCarrier_energy_bdd` — every slice is divergence-free, every slice has finite energy
  in both forms the carriers state, and the energy is uniformly bounded.  The failure below is
  not a blow-up.
* `escapingCarrier_rightContinuousAtStart` — the witness even satisfies the repository's own
  named pointwise clause `RestartAgreementOpen.RightContinuousAtStart`, the one obligation
  `OpenRestartDatum` records as missing from ITEM-6's `RestartPiece`.  Pointwise continuity at
  the start is *not* what fails.
* `kineticEnergy_escapingCarrier` — the energy is exactly `0` at the initial time and the fixed
  positive bump energy `bumpEnergy` at every other time: translation moves mass, it does not
  change it (`integral_phifun_shift`).
* `not_tendsto_kineticEnergy_atStart`, `not_tendsto_L2Gap_atStart` — the failure itself: neither
  the energy nor the squared `L²` gap to the initial slice tends to `0`.
* `not_carrier_clauses_give_L2_time_continuity` — the headline negation, over the clauses the
  carriers actually record (closed-slab joint smoothness at every horizon, open-slab smoothness,
  incompressibility before every horizon, both energy-integrability forms, a uniform energy
  bound, pointwise right-continuity at the start): they do not entail `L²` right-continuity.
* `tendsto_kineticEnergy_atStart_of_dominated` — the complementary **positive** fact, and the
  form the missing input has to take: pointwise right-continuity plus *one integrable spatial
  envelope* for the squared slices does give energy right-continuity, by dominated convergence.
* `not_exists_integrable_envelope_escapingCarrier` — and for this witness no such envelope
  exists: no integrable `g` dominates the squared slices on any right neighbourhood of `0`.  At
  `n` well-separated escape times the translated bumps have pairwise disjoint supports, so any
  envelope would carry integral at least `n · bumpEnergy` for *every* `n`, which no integrable
  function can do.  The envelope is therefore not a restatement of what the clauses already
  give: it is content, and it is exactly the content the escape destroys.
* `escapingCarrier_density_disjoint_of_separated` and `card_bumpEnergy_le_integral_of_disjoint_envelope`
  — the two steps that count is made of, each named with its own hypotheses rather than absorbed
  into one long proof: escape centres more than `2 · R0` apart give disjoint slice supports (the
  triangle inequality plus the certified vanishing radius), and an envelope dominating `n`
  pairwise-disjoint slices of energy `bumpEnergy` has integral at least `n · bumpEnergy`.  The
  second is stated for arbitrary times, so the disjointness, not the arithmetic progression, is
  what it uses.

## What is NOT claimed

The witness is **not** a Navier–Stokes evolution: no pressure makes it satisfy the momentum
equation, and nothing here says `L²` time-continuity fails for genuine solutions — interior
parabolic smoothing may well give it.  What is refuted is the *derivation*: obtaining the time
continuity that ledger `F-026` needs for the BKM/Kato energy argument, and that `F-027`'s
general-field carrier is told to "put in the class law", from regularity, incompressibility and
energy bounds alone.  The class law's continuity clause is therefore genuinely extra input, and
`tendsto_kineticEnergy_atStart_of_dominated` says what it costs: an integrable envelope that
excludes escape of mass.

## Placement

Depends on `Analysis.GalerkinRawFamily` (the translate machinery `shiftPhi` and the certified
support radius) and on `Analysis.RestartAgreementOpen` (for the names `RightContinuousAtStart`
and `SmoothVelocityOnOpen`, so the obstruction is stated against the clauses the ITEM-6
obligation actually uses).  No existing declaration is modified; `RegularOnCompacts`,
`SolClass` and `SolvesBefore` are untouched.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

namespace Navier.Analysis.CarrierTimeContinuityObstruction

open Navier
open Navier.Breakdown
open Navier.Analysis.LerayWeak
open Navier.Analysis.GalerkinBasis
open Navier.Analysis.RestartAgreementOpen

/-! ## §1 The witness -/

/-- **The escaping centre.**  At time `t` the bump sits at `1/t` along the first coordinate
axis, so its centre runs to spatial infinity as `t → 0`, from either side. -/
def escapeCentre (t : ℝ) : Space := (t⁻¹ : ℝ) • basisVector (0 : Fin 3)

/-- **The carrier obstruction witness** (ledger `F-026`: "a bump translated to infinity as
`t ↓ 0`, extended by zero").  The initial slice is the zero field. -/
def escapingCarrier : VelocityEvolution :=
  fun t x => if t = 0 then (0 : Space) else phifun (x - escapeCentre t)

/-- The bump's kinetic energy: the value `kineticEnergy escapingCarrier t` takes for every
`t ≠ 0`.  It is strictly positive (`bumpEnergy_pos`). -/
def bumpEnergy : ℝ := ∫ x : Space, ∑ i : Fin 3, (phifun x i) ^ 2

theorem escapingCarrier_apply {t : ℝ} (ht : t ≠ 0) (x : Space) :
    escapingCarrier t x = phifun (x - escapeCentre t) := by
  show (if t = 0 then (0 : Space) else phifun (x - escapeCentre t)) = phifun (x - escapeCentre t)
  exact if_neg ht

theorem escapingCarrier_zero (x : Space) : escapingCarrier 0 x = (0 : Space) := by
  show (if (0 : ℝ) = 0 then (0 : Space) else phifun (x - escapeCentre 0)) = (0 : Space)
  exact if_pos rfl

theorem escapingCarrier_zero_slice : escapingCarrier 0 = (0 : Space → Space) :=
  funext escapingCarrier_zero

/-- Off the initial time the witness *is* one of the certified translates. -/
theorem escapingCarrier_eq_slice {t : ℝ} (ht : t ≠ 0) :
    escapingCarrier t = shiftPhi (escapeCentre t) := by
  funext x
  rw [escapingCarrier_apply ht]
  show phifun (x - escapeCentre t) = phiSchwartz (x - escapeCentre t)
  exact (phiSchwartz_apply _).symm

/-- The first axis direction has unit length in the norm on `Space`. -/
theorem norm_basisVector_zero : ‖(basisVector (0 : Fin 3) : Space)‖ = 1 := by
  simp [basisVector, Pi.norm_single]

/-- The escaping centre is at distance `1/|t|` from the origin. -/
theorem norm_escapeCentre (t : ℝ) : ‖escapeCentre t‖ = |t|⁻¹ := by
  show ‖(t⁻¹ : ℝ) • (basisVector (0 : Fin 3) : Space)‖ = |t|⁻¹
  rw [norm_smul, norm_basisVector_zero, mul_one, Real.norm_eq_abs, abs_inv]

/-! ## §2 The certified bump vanishes far out, and the escape estimate -/

/-- A nonnegative radius outside which the certified bump field vanishes: the only quantitative
fact about `phifun` the witness needs, taken from the repository's own
`exists_phiSchwartz_support_radius` and its `shiftPhi_eq_zero_of_far`. -/
theorem exists_phifun_vanish_radius :
    ∃ R0 : ℝ, 0 ≤ R0 ∧ ∀ y : Space, R0 < ‖y‖ → phifun y = 0 := by
  obtain ⟨R0, hR0nonneg, hsub⟩ := exists_phiSchwartz_support_radius
  refine ⟨R0, hR0nonneg, fun y hy => ?_⟩
  have h1 : shiftPhi (0 : Space) y = 0 :=
    shiftPhi_eq_zero_of_far (0 : Space) y R0 hsub (by rw [dist_zero_right]; exact hy)
  simpa [shiftPhi, phiSchwartz_apply] using h1

/-- **The escape estimate.**  Fix a spatial point `x`, a time `s` and a vanishing radius `R0` for
`phifun`.  If `|s| < (R0 + ‖x‖ + 1)⁻¹`, then the whole unit ball about `x` lies *outside* the
translated bump: its centre `1/s` has already run past that ball. -/
theorem escapingCarrier_eq_zero_of_near (R0 : ℝ) (hR0nonneg : 0 ≤ R0)
    (hR0 : ∀ y : Space, R0 < ‖y‖ → phifun y = 0) (x : Space) (s : ℝ) (y : Space)
    (hy : y ∈ Metric.ball x (1 : ℝ)) (hs : |s| < (R0 + ‖x‖ + 1)⁻¹) :
    escapingCarrier s y = (0 : Space) := by
  rcases eq_or_ne s 0 with hs0 | hs0
  · rw [hs0]
    show (if (0 : ℝ) = 0 then (0 : Space) else phifun (y - escapeCentre 0)) = (0 : Space)
    exact if_pos rfl
  · rw [escapingCarrier_apply hs0]
    refine hR0 (y - escapeCentre s) ?_
    have hy1 : ‖y‖ < ‖x‖ + 1 := by
      have h1 : dist y x < (1 : ℝ) := Metric.mem_ball.mp hy
      rw [dist_eq_norm] at h1
      calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
        _ < 1 + ‖x‖ := by linarith
        _ = ‖x‖ + 1 := by ring
    have hA : (0 : ℝ) < R0 + ‖x‖ + 1 := by positivity
    have hbs : (0 : ℝ) < |s| := abs_pos.mpr hs0
    have hbig : R0 + ‖x‖ + 1 < |s|⁻¹ := (lt_inv_comm₀ hA hbs).mpr hs
    have htri : ‖escapeCentre s‖ ≤ ‖y - escapeCentre s‖ + ‖y‖ := by
      calc ‖escapeCentre s‖ = ‖(escapeCentre s - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖escapeCentre s - y‖ + ‖y‖ := norm_add_le _ _
        _ = ‖y - escapeCentre s‖ + ‖y‖ := by rw [norm_sub_rev]
    rw [norm_escapeCentre] at htri
    linarith

/-! ## §3 Joint smoothness: the case split is invisible to `C^∞` -/

/-- **The witness is jointly `C^∞` on all of `ℝ × ℝ³`.**  More than the carrier asks
(`SmoothVelocityBefore` only needs `ContDiffOn` on `[0,T) × ℝ³`), and it holds although the
definition is a case split: at every point of the initial hyperplane `{0} × ℝ³` the field is
*locally identically* zero by `escapingCarrier_eq_zero_of_near`, so there it is `C^∞` because it
is *literally* zero nearby; away from that hyperplane it is composition of smooth maps. -/
theorem contDiff_escapingCarrier :
    ContDiff ℝ ∞ (fun z : ℝ × Space => escapingCarrier z.1 z.2) := by
  obtain ⟨R0, hR0nonneg, hR0⟩ := exists_phifun_vanish_radius
  refine contDiff_iff_contDiffAt.mpr (fun p => ?_)
  rcases p with ⟨t, x⟩
  by_cases ht : t = 0
  · subst ht
    have hA : (0 : ℝ) < R0 + ‖x‖ + 1 := by positivity
    have hU : ((Ioo (-(R0 + ‖x‖ + 1)⁻¹) ((R0 + ‖x‖ + 1)⁻¹)) ×ˢ
        (Metric.ball x (1 : ℝ)) : Set (ℝ × Space)) ∈ 𝓝 (0, x) := by
      refine IsOpen.mem_nhds (IsOpen.prod isOpen_Ioo Metric.isOpen_ball) ⟨?_, ?_⟩
      · exact mem_Ioo.mpr ⟨neg_lt_zero.mpr (inv_pos.mpr hA), inv_pos.mpr hA⟩
      · exact Metric.mem_ball_self one_pos
    have heq : (fun z : ℝ × Space => escapingCarrier z.1 z.2)
        =ᶠ[𝓝 (0, x)] fun _ => (0 : Space) := by
      filter_upwards [hU] with z hz
      obtain ⟨hzs, hzy⟩ := Set.mem_prod.mp hz
      obtain ⟨hlo, hhi⟩ := Set.mem_Ioo.mp hzs
      have hz1 : |z.1| < (R0 + ‖x‖ + 1)⁻¹ := abs_lt.mpr ⟨by linarith, by linarith⟩
      exact escapingCarrier_eq_zero_of_near R0 hR0nonneg hR0 x z.1 z.2 hzy hz1
    have hzero : ContDiffAt ℝ ∞ (fun _ : ℝ × Space => (0 : Space)) (0, x) := contDiffAt_const
    exact hzero.congr_of_eventuallyEq heq
  · have hb : (0 : ℝ) < |t| := abs_pos.mpr ht
    have hU : ((Metric.ball t |t|) ×ˢ (univ : Set Space) : Set (ℝ × Space)) ∈ 𝓝 (t, x) := by
      refine IsOpen.mem_nhds (IsOpen.prod Metric.isOpen_ball isOpen_univ) ⟨?_, ?_⟩
      · exact Metric.mem_ball_self hb
      · exact mem_univ _
    have heq : (fun z : ℝ × Space => escapingCarrier z.1 z.2) =ᶠ[𝓝 (t, x)]
        (fun z : ℝ × Space =>
          phifun (z.2 - ((z.1 : ℝ)⁻¹ : ℝ) • (basisVector (0 : Fin 3) : Space))) := by
      filter_upwards [hU] with z hz
      obtain ⟨hzs, _⟩ := Set.mem_prod.mp hz
      have hnz : (z.1 : ℝ) ≠ 0 := by
        intro hzero
        have h1 : dist z.1 t < |t| := Metric.mem_ball.mp hzs
        rw [hzero, Real.dist_eq, zero_sub, abs_neg] at h1
        exact lt_irrefl _ h1
      exact escapingCarrier_apply hnz z.2
    have h1 : ContDiffAt ℝ ∞ (fun z : ℝ × Space => ((z.1 : ℝ)⁻¹ : ℝ)) (t, x) :=
      (contDiff_fst (𝕜 := ℝ)).contDiffAt.inv ht
    have h2 : ContDiffAt ℝ ∞
        (fun z : ℝ × Space => ((z.1 : ℝ)⁻¹ : ℝ) • (basisVector (0 : Fin 3) : Space)) (t, x) :=
      h1.smul_const (basisVector (0 : Fin 3))
    have h3 : ContDiffAt ℝ ∞
        (fun z : ℝ × Space =>
          z.2 - ((z.1 : ℝ)⁻¹ : ℝ) • (basisVector (0 : Fin 3) : Space)) (t, x) :=
      contDiffAt_snd.sub h2
    have h4 : ContDiffAt ℝ ∞
        (phifun ∘ (fun z : ℝ × Space =>
          z.2 - ((z.1 : ℝ)⁻¹ : ℝ) • (basisVector (0 : Fin 3) : Space))) (t, x) :=
      phifun_smooth.contDiffAt.comp (t, x) h3
    exact h4.congr_of_eventuallyEq heq

/-- The carrier's closed-slab smoothness clause, at every horizon. -/
theorem smoothVelocityBefore_escapingCarrier (T : ℝ) :
    SmoothVelocityBefore T escapingCarrier :=
  (contDiff_escapingCarrier.contDiffOn).mono (subset_univ _)

/-- The open-slab smoothness clause of `OpenSolClass`/`OpenRestartDatum`, at every horizon. -/
theorem smoothVelocityOnOpen_escapingCarrier (T : ℝ) :
    SmoothVelocityOnOpen T escapingCarrier :=
  (contDiff_escapingCarrier.contDiffOn).mono (subset_univ _)

/-! ## §4 Incompressibility, integrability and the pointwise start -/

/-- **Every slice is incompressible.**  For `t ≠ 0` the slice is a translate of the certified
divergence-free bump field, and divergence only re-evaluates at the translated base point
(`fderiv_shiftPhi`); for `t = 0` the slice is the zero field. -/
theorem escapingCarrier_divergence (t : ℝ) (x : Space) : divergence escapingCarrier t x = 0 := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    show (∑ i : Fin 3, fderiv ℝ (escapingCarrier 0) x (basisVector i) i) = 0
    have hzero : ∀ y : Space, fderiv ℝ (escapingCarrier 0) y = 0 := by
      intro y
      rw [escapingCarrier_zero_slice, fderiv_zero]
      simp
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hzero]
    simp
  · show (∑ i : Fin 3, fderiv ℝ (escapingCarrier t) x (basisVector i) i) = 0
    have hstep : ∀ i : Fin 3, fderiv ℝ (escapingCarrier t) x (basisVector i) i =
        fderiv ℝ (⇑phiSchwartz) (x - escapeCentre t) (basisVector i) i := by
      intro i
      rw [congrArg (fun v : Space → Space => fderiv ℝ v x (basisVector i) i)
        (escapingCarrier_eq_slice ht), fderiv_shiftPhi]
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    simpa [staticDivergence] using phiSchwartz_divfree (x - escapeCentre t)

theorem escapingCarrier_incompressible : Incompressible escapingCarrier :=
  fun t _ x => escapingCarrier_divergence t x

theorem escapingCarrier_incompressibleBefore (T : ℝ) : IncompressibleBefore T escapingCarrier :=
  fun t _ _ x => escapingCarrier_divergence t x

/-- The squared-density of a field is compactly supported whenever the field is: its support
sits inside the field's own support. -/
theorem hasCompactSupport_sumSq_density {u : VelocityField} (hu : HasCompactSupport u) :
    HasCompactSupport (fun x : Space => ∑ i : Fin 3, (u x i) ^ 2) :=
  hu.mono (by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hcon
    apply hx
    show ∑ i : Fin 3, (u x i) ^ 2 = 0
    exact Finset.sum_eq_zero (fun i _ => by simp [congrFun hcon i]))

/-- The norm-square density of a field is compactly supported whenever the field is. -/
theorem hasCompactSupport_normSq_density {u : VelocityField} (hu : HasCompactSupport u) :
    HasCompactSupport (fun x : Space => ‖u x‖ ^ 2) :=
  hu.mono (by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hcon
    apply hx
    show ‖u x‖ ^ 2 = 0
    rw [hcon, norm_zero, pow_two, mul_zero])

/-- **Every slice has finite energy in the `kineticEnergy` integrand** — the density whose
integral `kineticEnergy` is. -/
theorem integrable_sumSq_density_escapingCarrier (t : ℝ) :
    Integrable (fun x : Space => ∑ i : Fin 3, (escapingCarrier t x i) ^ 2) := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    rw [escapingCarrier_zero_slice]
    have hfun : (fun x : Space => ∑ i : Fin 3, ((0 : Space → Space) x i) ^ 2) = fun _ => 0 := by
      funext x
      show ∑ i : Fin 3, ((0 : Space → Space) x i) ^ 2 = 0
      exact Finset.sum_eq_zero (fun i _ => by simp)
    rw [hfun]
    exact integrable_zero Space ℝ volume
  · rw [escapingCarrier_eq_slice ht]
    have hcont : Continuous (fun x : Space => ∑ i : Fin 3, (shiftPhi (escapeCentre t) x i) ^ 2) :=
      continuous_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
        Continuous.pow ((continuous_apply i).comp (shiftPhi_continuous (escapeCentre t))) 2)
    exact hcont.integrable_of_hasCompactSupport
      (hasCompactSupport_sumSq_density (shiftPhi_hasCompactSupport (escapeCentre t)))

/-- **Every slice has finite energy in the norm form** that `SolClass.finite_energy` and
`OpenSolClass.finite_energy` state. -/
theorem integrable_normSq_density_escapingCarrier (t : ℝ) :
    Integrable (fun x : Space => ‖escapingCarrier t x‖ ^ 2) := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    rw [escapingCarrier_zero_slice]
    have hfun : (fun x : Space => ‖(0 : Space → Space) x‖ ^ 2) = fun _ => 0 := by
      funext x
      show ‖(0 : Space → Space) x‖ ^ 2 = 0
      simp
    rw [hfun]
    exact integrable_zero Space ℝ volume
  · rw [escapingCarrier_eq_slice ht]
    have hcont : Continuous (fun x : Space => ‖shiftPhi (escapeCentre t) x‖ ^ 2) :=
      (Continuous.norm (shiftPhi_continuous (escapeCentre t))).pow 2
    exact hcont.integrable_of_hasCompactSupport
      (hasCompactSupport_normSq_density (shiftPhi_hasCompactSupport (escapeCentre t)))

/-- At each point the witness is *locally identically* its initial value, on both sides of `0` —
stronger than the one-sided clause it is used to satisfy below. -/
theorem escapingCarrier_eventually_eq_atStart (x : Space) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t| < η → escapingCarrier t x = escapingCarrier 0 x := by
  obtain ⟨R0, hR0nonneg, hR0⟩ := exists_phifun_vanish_radius
  refine ⟨(R0 + ‖x‖ + 1)⁻¹, by positivity, fun t ht => ?_⟩
  rw [show escapingCarrier 0 x = (0 : Space) from escapingCarrier_zero x]
  exact escapingCarrier_eq_zero_of_near R0 hR0nonneg hR0 x t x (Metric.mem_ball_self one_pos) ht

/-- **So the repository's own named pointwise start clause holds.**  `RightContinuousAtStart` is
the obligation `OpenRestartDatum` records as missing from ITEM-6's `RestartPiece`: it is *not*
what the escape defeats. -/
theorem escapingCarrier_rightContinuousAtStart : RightContinuousAtStart escapingCarrier := by
  intro x
  obtain ⟨η, hη, hη'⟩ := escapingCarrier_eventually_eq_atStart x
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨η, hη, fun r hr hrd => ?_⟩
  have habs : |r| < η := by
    have h1 : dist r (0 : ℝ) < η := hrd
    rw [Real.dist_eq, sub_zero] at h1
    exact h1
  rw [hη' r habs, dist_self]
  exact hε

/-! ## §5 The energy: translation moves mass, it does not change it -/

/-- **Translation does not change the energy.**  Volume is translation-invariant on `ℝ³`, so the
integral of the squared bump field over a translate equals the integral at the origin. -/
theorem integral_phifun_shift (c : Space) :
    (∫ x : Space, ∑ i : Fin 3, (phifun (x - c) i) ^ 2) = bumpEnergy := by
  have hinv : (volume : Measure Space).IsAddLeftInvariant :=
    (isAddHaarMeasure_volume_pi (Fin 3)).toIsAddLeftInvariant
  unfold bumpEnergy
  let F : Space → ℝ := fun y => ∑ i : Fin 3, (phifun y i) ^ 2
  have hFcont : Continuous F :=
    continuous_finsetSum _ (fun i _ =>
      Continuous.pow ((continuous_apply i).comp phiSchwartz.continuous) 2)
  have hTmeas : AEMeasurable (fun x : Space => (-c) + x) volume :=
    (continuous_const.add continuous_id).measurable.aemeasurable
  have hFmeas : AEStronglyMeasurable F (volume.map fun x : Space => (-c) + x) :=
    hFcont.aestronglyMeasurable
  trans (∫ x : Space, F ((-c) + x))
  · refine integral_congr_ae (ae_of_all volume (fun x => ?_))
    show ∑ i : Fin 3, (phifun (x - c) i) ^ 2 = F ((-c) + x)
    rw [sub_eq_add_neg, add_comm x (-c)]
  · trans (∫ y : Space, F y ∂volume.map (fun x : Space => (-c) + x))
    · exact (integral_map hTmeas hFmeas).symm
    · rw [hinv.map_add_left_eq_self (-c)]

/-- The bump's energy is strictly positive: the density is continuous, compactly supported and
nonnegative, and `phifun` is not the zero field (`phiSchwartz_ne_zero`). -/
theorem bumpEnergy_pos : 0 < bumpEnergy := by
  obtain ⟨x0, hx0⟩ : ∃ x : Space, phifun x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply phiSchwartz_ne_zero
    exact DFunLike.coe_injective (by funext x; exact (phiSchwartz_apply x).trans (hcon x))
  unfold bumpEnergy
  have hcont : Continuous (fun x : Space => ∑ i : Fin 3, (phifun x i) ^ 2) :=
    continuous_finsetSum _ (fun i _ =>
      Continuous.pow ((continuous_apply i).comp phiSchwartz.continuous) 2)
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x0) hcont
    (hasCompactSupport_sumSq_density phifun_supp)
    (fun _x => Finset.sum_nonneg (fun i _ => sq_nonneg _)) ?_
  show ∑ i : Fin 3, (phifun x0 i) ^ 2 ≠ 0
  intro hsum
  apply hx0
  ext i
  have h1 : (phifun x0 i) ^ 2 ≤ ∑ j : Fin 3, (phifun x0 j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [hsum] at h1
  have h2 : (phifun x0 i) ^ 2 = 0 := by
    have h3 : (0 : ℝ) ≤ (phifun x0 i) ^ 2 := sq_nonneg _
    linarith
  rw [pow_two] at h2
  exact mul_self_eq_zero.mp h2

/-- **The energy of the witness, exactly**: `0` at the initial time and `bumpEnergy` at every
other time.  The energy does not decay towards its initial value — it simply is not there at
`t = 0`. -/
theorem kineticEnergy_escapingCarrier (t : ℝ) :
    kineticEnergy escapingCarrier t = if t = 0 then 0 else bumpEnergy := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    rw [if_pos rfl]
    have hae : (fun x : Space => ∑ i : Fin 3, (escapingCarrier 0 x i) ^ 2)
        =ᵐ[volume] (0 : Space → ℝ) := by
      refine ae_of_all volume (fun x => ?_)
      show ∑ i : Fin 3, (escapingCarrier 0 x i) ^ 2 = (0 : Space → ℝ) x
      simp [escapingCarrier_zero]
    exact integral_eq_zero_of_ae hae
  · have h1 : kineticEnergy escapingCarrier t
        = ∫ x : Space, ∑ i : Fin 3, (phifun (x - escapeCentre t) i) ^ 2 := by
      show (∫ x : Space, ∑ i : Fin 3, (escapingCarrier t x i) ^ 2) = _
      refine integral_congr_ae (ae_of_all volume (fun y => ?_))
      show ∑ i : Fin 3, (escapingCarrier t y i) ^ 2
          = ∑ i : Fin 3, (phifun (y - escapeCentre t) i) ^ 2
      rw [escapingCarrier_apply ht]
    rw [if_neg ht, h1, integral_phifun_shift]

/-- A uniform energy bound holds: what fails below is not a blow-up. -/
theorem escapingCarrier_energy_bdd :
    ∃ B : ℝ, ∀ t : ℝ, kineticEnergy escapingCarrier t ≤ B :=
  ⟨bumpEnergy, fun t => by
    rw [kineticEnergy_escapingCarrier]
    split_ifs with h <;> linarith [bumpEnergy_pos]⟩

/-- **The squared `L²` gap** between the slice at time `t` and the initial slice, as an energy:
the kinetic energy of the difference field.  This is the quantity `‖u ε - v ε‖_{L²}` named in
`Analysis.RestartAgreementOpen`'s "why the cheap routes fail". -/
def L2GapSq (u : VelocityEvolution) (t : ℝ) : ℝ :=
  kineticEnergy (fun s x => u s x - u 0 x) t

theorem L2GapSq_escapingCarrier_eq {t : ℝ} (ht : t ≠ 0) :
    L2GapSq escapingCarrier t = bumpEnergy := by
  have hdiff : (fun s x => escapingCarrier s x - escapingCarrier 0 x) = escapingCarrier := by
    funext s x
    show escapingCarrier s x - escapingCarrier 0 x = escapingCarrier s x
    rw [escapingCarrier_zero, sub_zero]
  unfold L2GapSq
  rw [hdiff, kineticEnergy_escapingCarrier, if_neg ht]

/-! ## §6 The failure, and the headline negation -/

/-- **The energy is not right-continuous at the start**: it is `0` at `t = 0` and `bumpEnergy > 0`
arbitrarily close to `0` on the right. -/
theorem not_tendsto_kineticEnergy_atStart :
    ¬ Tendsto (fun t : ℝ => kineticEnergy escapingCarrier t)
        (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 (kineticEnergy escapingCarrier 0)) := by
  intro h
  have h0 : kineticEnergy escapingCarrier 0 = (0 : ℝ) := by
    rw [kineticEnergy_escapingCarrier, if_pos rfl]
  rw [h0] at h
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ, hδ'⟩ := h (bumpEnergy / 2) (by linarith [bumpEnergy_pos])
  have hp : (0 : ℝ) < δ / 2 := by positivity
  have htd : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hp]
    linarith
  have hge := hδ' (Set.mem_Ioi.mpr hp) htd
  rw [kineticEnergy_escapingCarrier, if_neg (ne_of_gt hp), Real.dist_eq, sub_zero,
    abs_of_pos bumpEnergy_pos] at hge
  linarith [bumpEnergy_pos]

/-- **The `L²` gap to the initial slice does not tend to `0`**, although the slices converge to
it at every point of space (`escapingCarrier_rightContinuousAtStart`).  This is the exact failure
`Analysis.RestartAgreementOpen` bullet 2 and ledger `F-026` describe. -/
theorem not_tendsto_L2Gap_atStart :
    ¬ Tendsto (L2GapSq escapingCarrier) (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 0) := by
  intro h
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ, hδ'⟩ := h (bumpEnergy / 2) (by linarith [bumpEnergy_pos])
  have hp : (0 : ℝ) < δ / 2 := by positivity
  have htd : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hp]
    linarith
  have hge := hδ' (Set.mem_Ioi.mpr hp) htd
  rw [L2GapSq_escapingCarrier_eq (ne_of_gt hp), Real.dist_eq, sub_zero,
    abs_of_pos bumpEnergy_pos] at hge
  linarith [bumpEnergy_pos]

/-- **The route is not derivable from the carrier clauses.**  There is an evolution satisfying
every regularity, incompressibility, finite-energy, uniform-energy-bound and pointwise-start
clause that `SolvesBefore`/`SolClass`/`OpenSolClass`/`OpenRestartDatum` record, whose squared
`L²` gap to the initial slice nevertheless does not tend to `0`.

So the time-continuity input that `F-026` needs for the BKM/Kato energy argument, and that
`F-027`'s general-field carrier is told to carry in the class law, is *extra* hypothesis: it does
not follow from those clauses.  The witness is not a Navier–Stokes evolution — what is refuted is
the derivation, not the conclusion. -/
theorem not_carrier_clauses_give_L2_time_continuity :
    ∃ u : VelocityEvolution,
      (∀ T : ℝ, SmoothVelocityBefore T u) ∧
      (∀ T : ℝ, SmoothVelocityOnOpen T u) ∧
      (∀ T : ℝ, IncompressibleBefore T u) ∧
      Incompressible u ∧
      (∀ t : ℝ, Integrable (fun x : Space => ‖u t x‖ ^ 2)) ∧
      (∀ t : ℝ, Integrable (fun x : Space => ∑ i : Fin 3, (u t x i) ^ 2)) ∧
      (∃ B : ℝ, ∀ t : ℝ, kineticEnergy u t ≤ B) ∧
      RightContinuousAtStart u ∧
      ¬ Tendsto (L2GapSq u) (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 0) :=
  ⟨escapingCarrier,
   smoothVelocityBefore_escapingCarrier,
   smoothVelocityOnOpen_escapingCarrier,
   escapingCarrier_incompressibleBefore,
   escapingCarrier_incompressible,
   integrable_normSq_density_escapingCarrier,
   integrable_sumSq_density_escapingCarrier,
   escapingCarrier_energy_bdd,
   escapingCarrier_rightContinuousAtStart,
   not_tendsto_L2Gap_atStart⟩

/-! ## §7 What the missing input has to be -/

/-- **Pointwise convergence plus one integrable envelope is enough.**  Under the slices'
pointwise right-continuity at the start and a single integrable spatial envelope for the squared
slices, the energy is right-continuous at the start, by dominated convergence.  This is the
mechanism `Analysis.EnvelopePropagation` §3 names for rung P1, and it says the form the missing
hypothesis of `F-026` / `F-027`'s class law must take: an *envelope*, not more pointwise
regularity.  The witness shows the envelope is not free — `escapingCarrier` satisfies everything
else and admits no such envelope, since its squared slices have pairwise disjoint supports whose
individual integrals are all `bumpEnergy`. -/
theorem tendsto_kineticEnergy_atStart_of_dominated {u : VelocityEvolution}
    (hrc : RightContinuousAtStart u)
    (hcont : ∀ t : ℝ, Continuous (u t))
    {g : Space → ℝ} (hg : Integrable g)
    (hbdd : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      ∀ x : Space, ∑ i : Fin 3, (u t x i) ^ 2 ≤ g x) :
    Tendsto (fun t : ℝ => kineticEnergy u t)
        (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 (kineticEnergy u 0)) := by
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun x : Space => ∑ i : Fin 3, (u t x i) ^ 2) volume :=
    fun t => (continuous_finsetSum _ (fun i _ =>
      Continuous.pow ((continuous_apply i).comp (hcont t)) 2)).aestronglyMeasurable
  have hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      ∀ᵐ x ∂volume, ‖(fun y : Space => ∑ i : Fin 3, (u t y i) ^ 2) x‖ ≤ g x := by
    filter_upwards [hbdd] with t ht
    refine ae_of_all volume (fun x => ?_)
    have hnonneg : (0 : ℝ) ≤ ∑ i : Fin 3, (u t x i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact ht x
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun t : ℝ => ∑ i : Fin 3, (u t x i) ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 (∑ i : Fin 3, (u 0 x i) ^ 2)) := by
    refine ae_of_all volume (fun x => ?_)
    have hc : Continuous (fun v : Space => ∑ i : Fin 3, (v i) ^ 2) :=
      continuous_finsetSum _ (fun i _ => Continuous.pow (continuous_apply i) 2)
    exact hc.tendsto (u 0 x) |>.comp (hrc x)
  have hkey : Tendsto (fun t : ℝ => ∫ x : Space, ∑ i : Fin 3, (u t x i) ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)))
      (𝓝 (∫ x : Space, ∑ i : Fin 3, (u 0 x i) ^ 2)) :=
    tendsto_integral_filter_of_dominated_convergence g (Eventually.of_forall hmeas)
      hbound hg hlim
  show Tendsto (fun t : ℝ => kineticEnergy u t)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 (kineticEnergy u 0))
  exact hkey

/-! ## §8 The missing input cannot be supplied by an envelope either -/

/-- Beyond radius `R0` from the escaping centre, a nonzero slice of the witness has vanishing
`kineticEnergy` density: the translated bump is simply not there. -/
theorem slice_density_eq_zero_of_far (R0 : ℝ) (hR0 : ∀ y : Space, R0 < ‖y‖ → phifun y = 0)
    {t : ℝ} (ht : t ≠ 0) (x : Space) (hfar : R0 < ‖x - escapeCentre t‖) :
    ∑ i : Fin 3, (escapingCarrier t x i) ^ 2 = 0 := by
  rw [escapingCarrier_apply ht]
  have hzero : phifun (x - escapeCentre t) = (0 : Space) := hR0 _ hfar
  show ∑ i : Fin 3, (phifun (x - escapeCentre t) i) ^ 2 = 0
  rw [hzero]
  exact Finset.sum_eq_zero (fun i _ => by simp)

/-- **Two separated escape times have disjoint slice supports.**  If the escape centres of two
strictly positive times lie more than `2·R0` apart, no point of space carries density for both
translated bumps: the triangle inequality puts one of the two distances from the point to a centre
at or beyond `R0`, and past that radius the certified bump is identically zero
(`slice_density_eq_zero_of_far`).  This is the geometry the envelope count below runs on, stated
once with its own hypotheses instead of absorbed into the counting argument. -/
theorem escapingCarrier_density_disjoint_of_separated (R0 : ℝ)
    (hR0 : ∀ y : Space, R0 < ‖y‖ → phifun y = 0)
    {s t : ℝ} (hs : (0 : ℝ) < s) (ht : (0 : ℝ) < t)
    (hsep : (2 : ℝ) * R0 < ‖escapeCentre s - escapeCentre t‖) : ∀ x : Space,
    (∑ i : Fin 3, (escapingCarrier s x i) ^ 2 = 0) ∨
    (∑ i : Fin 3, (escapingCarrier t x i) ^ 2 = 0) := by
  intro x
  have htri : ‖escapeCentre s - escapeCentre t‖ ≤ ‖x - escapeCentre s‖ + ‖x - escapeCentre t‖ := by
    have h1 : escapeCentre s - escapeCentre t = (escapeCentre s - x) + (x - escapeCentre t) :=
      (sub_add_sub_cancel (escapeCentre s) x (escapeCentre t)).symm
    have h2 : ‖(escapeCentre s - x) + (x - escapeCentre t)‖ ≤
        ‖escapeCentre s - x‖ + ‖x - escapeCentre t‖ := norm_add_le _ _
    have h3 : ‖escapeCentre s - x‖ = ‖x - escapeCentre s‖ := norm_sub_rev _ _
    rw [← h1, h3] at h2
    exact h2
  rcases lt_trichotomy R0 ‖x - escapeCentre s‖ with hlt | heq | hgt
  · exact Or.inl (slice_density_eq_zero_of_far R0 hR0 (ne_of_gt hs) x hlt)
  · refine Or.inr (slice_density_eq_zero_of_far R0 hR0 (ne_of_gt ht) x ?_)
    linarith
  · refine Or.inr (slice_density_eq_zero_of_far R0 hR0 (ne_of_gt ht) x ?_)
    linarith

/-- **An envelope over `n` disjoint slices carries `n · bumpEnergy`.**  The measure-theoretic half
of the escape count, with the times left arbitrary: let `τ` be finitely many times whose witness
slices have pairwise disjoint supports and whose energies all equal `bumpEnergy`.  Then any
integrable `g` dominating every slice density pointwise satisfies
`(n : ℝ) * bumpEnergy ≤ ∫ g`.  Disjointness is paid for exactly once, where the pointwise sum of
the densities collapses to its single non-zero term; what remains is linearity of the Bochner
integral over a finite sum plus `integral_mono_ae`. -/
theorem card_bumpEnergy_le_integral_of_disjoint_envelope (n : ℕ) (g : Space → ℝ) (τ : Fin n → ℝ)
    (hg : Integrable g) (hnonneg : ∀ x : Space, 0 ≤ g x)
    (hdom : ∀ k : Fin n, ∀ x : Space, ∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2 ≤ g x)
    (hdisj : ∀ k l : Fin n, k ≠ l → ∀ x : Space,
      (∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2 = 0) ∨
        (∑ i : Fin 3, (escapingCarrier (τ l) x i) ^ 2 = 0))
    (heach : ∀ k : Fin n, ∫ x : Space, ∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2 = bumpEnergy) :
    (n : ℝ) * bumpEnergy ≤ ∫ x : Space, g x := by
  have hsum_le : ∀ x : Space,
      ∑ k : Fin n, ∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2 ≤ g x := by
    intro x
    by_cases hx : ∃ k : Fin n, (∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2) ≠ 0
    · obtain ⟨k, hk⟩ := hx
      have hzero_of_ne : ∀ l : Fin n, l ≠ k →
          ∑ i : Fin 3, (escapingCarrier (τ l) x i) ^ 2 = 0 := by
        intro l hl
        rcases hdisj l k hl x with h1 | h2
        · exact h1
        · exact absurd h2 hk
      have hsum1 : ∑ l : Fin n, ∑ i : Fin 3, (escapingCarrier (τ l) x i) ^ 2
          = ∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2 :=
        Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (fun l _ hl => hzero_of_ne l hl)
      rw [hsum1]
      exact hdom k x
    · have hsum : ∑ k : Fin n, ∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2 = 0 :=
        Finset.sum_eq_zero (fun k _ => by
          by_contra hl
          exact hx ⟨k, hl⟩)
      rw [hsum]
      exact hnonneg x
  have hsum_int : (∑ k : Fin n, ∫ x : Space, ∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2)
      ≤ ∫ x : Space, g x := by
    have hint : Integrable (fun x : Space => ∑ k : Fin n,
        ∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2) :=
      integrable_finsetSum Finset.univ (fun k _ =>
        integrable_sumSq_density_escapingCarrier (τ k))
    have hsum_eq_int : (∑ k : Fin n, ∫ x : Space, ∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2)
        = ∫ x : Space, ∑ k : Fin n, ∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2 :=
      (integral_finsetSum Finset.univ (fun k _ =>
        integrable_sumSq_density_escapingCarrier (τ k))).symm
    rw [hsum_eq_int]
    exact integral_mono_ae hint hg (ae_of_all volume hsum_le)
  have hsum_eq : (n : ℝ) * bumpEnergy = ∑ k : Fin n, bumpEnergy := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hle : (∑ k : Fin n, bumpEnergy) ≤ ∫ x : Space, g x := by
    rw [Finset.sum_congr rfl (fun k _ => (heach k).symm)]
    exact hsum_int
  linarith [hsum_eq, hle]

/-- **The escape beats every envelope.**  Negating exactly the domination hypothesis that
`tendsto_kineticEnergy_atStart_of_dominated` consumes: there is *no* integrable `g` with
`∑ i (escapingCarrier t x i)² ≤ g x` for all times right of `0` and every `x`.  The proof is the
escape made quantitative: at `n` well-separated times the translated bumps have pairwise disjoint
supports (they are `s = 2·R0 + 1` apart along the escaping axis), so an envelope would dominate
`n` copies of `bumpEnergy` for every `n` — and no integrable function has integrals that grow
without bound.  Together with §6 and §7 this says the time-continuity input ledger `F-026` needs,
and that `F-027`'s class law is told to carry, is genuinely new content: neither more pointwise
regularity (the witness has all of it) nor a domination hypothesis the clauses already give. -/
theorem not_exists_integrable_envelope_escapingCarrier :
    ¬ ∃ g : Space → ℝ, Integrable g ∧
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
        ∀ x : Space, ∑ i : Fin 3, (escapingCarrier t x i) ^ 2 ≤ g x := by
  rintro ⟨g, hg, henv⟩
  obtain ⟨R0, hR0nonneg, hR0⟩ := exists_phifun_vanish_radius
  have hmem : {t : ℝ | ∀ x : Space, ∑ i : Fin 3, (escapingCarrier t x i) ^ 2 ≤ g x}
      ∈ nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) := henv
  rw [Metric.mem_nhdsWithin_iff] at hmem
  obtain ⟨ε, hε, hsub⟩ := hmem
  have hpoint : ∀ t : ℝ, dist t (0 : ℝ) < ε → 0 < t → ∀ x : Space,
      ∑ i : Fin 3, (escapingCarrier t x i) ^ 2 ≤ g x := by
    intro t hd ht x
    have hball : t ∈ Metric.ball (0 : ℝ) ε := Metric.mem_ball.mpr hd
    exact hsub (Set.mem_inter hball (Set.mem_Ioi.mpr ht)) x
  -- the envelope is pointwise nonnegative, read off at one admissible time
  have hnonneg_g : ∀ x : Space, 0 ≤ g x := by
    intro x
    have hp : (0 : ℝ) < ε / 2 := by positivity
    have hdt : dist (ε / 2) (0 : ℝ) < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hp]
      linarith
    exact le_trans (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (hpoint (ε / 2) hdt hp x)
  have hbound : ∀ n : ℕ, (n : ℝ) * bumpEnergy ≤ ∫ x : Space, g x := by
    intro n
    let s : ℝ := 2 * R0 + 1
    let c : ℝ := 1 / ε + 1
    have hs : s = 2 * R0 + 1 := rfl
    have hc : c = 1 / ε + 1 := rfl
    have hspos : (0 : ℝ) < s := by
      rw [hs]
      linarith [hR0nonneg]
    have hcpos : (0 : ℝ) < c := by
      rw [hc]
      linarith [one_div_pos.mpr hε]
    have hclt : (1 : ℝ) / ε < c := by
      rw [hc]
      linarith [one_div_pos.mpr hε]
    let τ : Fin n → ℝ := fun k => (c + (k : ℝ) * s)⁻¹
    have hks : ∀ k : Fin n, (0 : ℝ) ≤ (k : ℝ) * s := by
      intro k
      exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt hspos)
    have hA : ∀ k : Fin n, (0 : ℝ) < c + (k : ℝ) * s := by
      intro k
      exact lt_of_lt_of_le hcpos (le_add_of_nonneg_right (hks k))
    have hτpos : ∀ k : Fin n, (0 : ℝ) < τ k := by
      intro k
      show (0 : ℝ) < (c + (k : ℝ) * s)⁻¹
      exact inv_pos.mpr (hA k)
    have hτlt : ∀ k : Fin n, τ k < ε := by
      intro k
      show (c + (k : ℝ) * s)⁻¹ < ε
      rw [show (c + (k : ℝ) * s)⁻¹ = 1 / (c + (k : ℝ) * s) from inv_eq_one_div _]
      refine (one_div_lt (hA k) hε).mpr ?_
      exact lt_of_lt_of_le hclt (le_add_of_nonneg_right (hks k))
    have hτsm : ∀ k : Fin n, dist (τ k) (0 : ℝ) < ε := by
      intro k
      rw [Real.dist_eq, sub_zero, abs_of_pos (hτpos k)]
      exact hτlt k
    have hinv : ∀ k : Fin n, (τ k)⁻¹ = c + (k : ℝ) * s := by
      intro k
      show ((c + (k : ℝ) * s)⁻¹)⁻¹ = c + (k : ℝ) * s
      rw [inv_inv]
    have hgap : ∀ (k l : Fin n), k ≠ l → (1 : ℝ) ≤ |(k : ℝ) - (l : ℝ)| := by
      intro k l hne
      have hne' : (k : ℕ) ≠ (l : ℕ) := fun hh => hne (Fin.ext hh)
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · have h3 : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        have h1 : (1 : ℝ) ≤ (l : ℝ) - (k : ℝ) := by linarith
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have h3 : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
        have h1 : (1 : ℝ) ≤ (k : ℝ) - (l : ℝ) := by linarith
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hsep : ∀ (k l : Fin n), k ≠ l →
        (2 : ℝ) * R0 < ‖escapeCentre (τ k) - escapeCentre (τ l)‖ := by
      intro k l hne
      show (2 : ℝ) * R0 < ‖((τ k)⁻¹ : ℝ) • basisVector (0 : Fin 3) -
          ((τ l)⁻¹ : ℝ) • basisVector (0 : Fin 3)‖
      rw [hinv k, hinv l, ← sub_smul, norm_smul, Real.norm_eq_abs, norm_basisVector_zero,
        mul_one]
      have hd : (c + (k : ℝ) * s) - (c + (l : ℝ) * s) = ((k : ℝ) - (l : ℝ)) * s := by ring
      rw [hd, abs_mul, abs_of_pos hspos]
      have hge : (1 : ℝ) * s ≤ |(k : ℝ) - (l : ℝ)| * s :=
        mul_le_mul_of_nonneg_right (hgap k l hne) (le_of_lt hspos)
      linarith [hR0nonneg, hge, hs]
    have hdisj : ∀ (k l : Fin n), k ≠ l → ∀ x : Space,
        (∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2 = 0) ∨
        (∑ i : Fin 3, (escapingCarrier (τ l) x i) ^ 2 = 0) :=
      fun k l hne =>
        escapingCarrier_density_disjoint_of_separated R0 hR0 (hτpos k) (hτpos l) (hsep k l hne)
    have henvτ : ∀ k : Fin n, ∀ x : Space,
        ∑ i : Fin 3, (escapingCarrier (τ k) x i) ^ 2 ≤ g x := by
      intro k x
      exact hpoint (τ k) (hτsm k) (hτpos k) x
    refine card_bumpEnergy_le_integral_of_disjoint_envelope n g τ hg hnonneg_g ?_ hdisj ?_
    · exact henvτ
    · intro k
      have hke : kineticEnergy escapingCarrier (τ k) = bumpEnergy := by
        rw [kineticEnergy_escapingCarrier, if_neg (ne_of_gt (hτpos k))]
      exact hke
  obtain ⟨n, hn⟩ := exists_nat_gt ((∫ x : Space, g x) / bumpEnergy)
  have hlt : (∫ x : Space, g x) < (n : ℝ) * bumpEnergy :=
    (div_lt_iff₀ bumpEnergy_pos).mp hn
  linarith [hbound n]

end Navier.Analysis.CarrierTimeContinuityObstruction

-- Self-audit (repository convention: the module prints its own raw axiom traces; the
-- transitive census over every declaration, private helpers included, is run by
-- `scripts/AuditAllAxioms.lean`, which imports `Navier` and therefore this module.
-- Every row below must print exactly [propext, Classical.choice, Quot.sound].
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapeCentre
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.bumpEnergy
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_apply
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_zero
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_zero_slice
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_eq_slice
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.norm_basisVector_zero
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.norm_escapeCentre
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.exists_phifun_vanish_radius
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_eq_zero_of_near
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.contDiff_escapingCarrier
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.smoothVelocityBefore_escapingCarrier
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.smoothVelocityOnOpen_escapingCarrier
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_divergence
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_incompressible
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_incompressibleBefore
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.hasCompactSupport_sumSq_density
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.hasCompactSupport_normSq_density
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.integrable_sumSq_density_escapingCarrier
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.integrable_normSq_density_escapingCarrier
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_eventually_eq_atStart
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_rightContinuousAtStart
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.integral_phifun_shift
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.bumpEnergy_pos
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.kineticEnergy_escapingCarrier
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_energy_bdd
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.L2GapSq
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.L2GapSq_escapingCarrier_eq
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.not_tendsto_kineticEnergy_atStart
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.not_tendsto_L2Gap_atStart
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.not_carrier_clauses_give_L2_time_continuity
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.tendsto_kineticEnergy_atStart_of_dominated
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.slice_density_eq_zero_of_far
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.escapingCarrier_density_disjoint_of_separated
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.card_bumpEnergy_le_integral_of_disjoint_envelope
#print axioms Navier.Analysis.CarrierTimeContinuityObstruction.not_exists_integrable_envelope_escapingCarrier
