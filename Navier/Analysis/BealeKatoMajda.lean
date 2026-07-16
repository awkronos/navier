import Navier.Analysis.Vorticity
import Navier.Breakdown.MaximalNonextension

/-!
# The Beale–Kato–Majda continuation criterion

Beale, Kato and Majda (*Comm. Math. Phys.* **94** (1984) 61–66; Majda–Bertozzi,
*Vorticity and Incompressible Flow* §3.4) proved that a classical solution of
the incompressible Euler/Navier–Stokes equations cannot lose regularity at a
finite time `T` while the vorticity supremum stays integrable in time:

  if `∫₀ᵀ ‖ω(·,t)‖_∞ dt < ∞` then the solution continues smoothly past `T`,

equivalently, blow-up at `T` forces `∫₀ᵀ ‖ω(·,t)‖_∞ dt = ∞`.

## What is certified here

The analytic **engine** of the criterion is a time-dependent (integral-form)
Grönwall a-priori bound.  Mathlib's `gronwallBound` only handles a *constant*
growth rate `K`; the vorticity-integral criterion needs the *time-dependent*
rate `g(t) = C‖ω(t)‖_∞`.  `gronwall_log_apriori` supplies exactly this:

  `Y' t ≤ g t · Y t`  (with `Y > 0`)  ⟹  `Y t ≤ Y 0 · exp (∫₀ᵗ g)`,

with `g` only required continuous **on** `[0,T]`, so it may itself be a genuine
PDE quantity.  This is a fully unconditional real-analysis theorem (`propext`,
`Classical.choice`, `Quot.sound` only).

`BKMControl` packages the criterion in this repository's classical-solution
framework: a regularity control `Y(t)` that dominates the velocity, driven by a
vorticity supremum majorant `g(t)`, under the **explicit** finite-integral
hypothesis `∃ B, ∀ t < T, ∫₀ᵗ g ≤ B` (the improper vorticity integral
converges — a genuine restriction, *not* forced by continuity, so the criterion
is non-vacuous even though blow-up of `ω` at `T` is permitted).  From it,
`BKMControl.velocity_bounded` derives a uniform velocity bound on `[0,T)`, and
`BKMControl.excludes_pointEvaluationBreakdown` shows such a control is logically
incompatible with the repository's `PointEvaluationBreakdownWitness` — i.e. a
finite vorticity integral rules out pointwise blow-up, consuming the existing
breakdown machinery of `Navier.Breakdown.MaximalNonextension`.

## What remains open (`BKMAnalyticResidual`)

The two genuinely Mathlib-absent PDE inputs that *produce* a `BKMControl` from a
Navier–Stokes solution — the Biot–Savart / log-Sobolev inequality that yields
the Grönwall differential inequality, and the Sobolev embedding that makes a
higher-order norm dominate the velocity — are named residuals with references,
`BKMAnalyticResidual`.  They are declared, never assumed: no `axiom`, and the
certified theorems below depend on none of them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral

namespace Navier.Analysis.BealeKatoMajda

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Breakdown

/-!
## The integral-form Grönwall a-priori bound (unconditional analytic engine)
-/

/-- **Time-dependent Grönwall a-priori bound.**  If a positive control `Y`,
continuous on `[0,T]` and differentiable on `(0,T)`, satisfies the vorticity-
driven differential inequality `Y' t ≤ g t · Y t` with rate `g` continuous on
`[0,T]`, then `Y t ≤ Y 0 · exp (∫₀ᵗ g)` throughout `[0,T]`.

This is the analytic heart of the Beale–Kato–Majda continuation mechanism.
Mathlib supplies only the constant-rate `gronwallBound`; the time-dependent
rate `g = C‖ω‖_∞` is what the vorticity-integral criterion requires. -/
theorem gronwall_log_apriori
    {Y Y' g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hgc : ContinuousOn g (Set.Icc 0 T))
    (hYc : ContinuousOn Y (Set.Icc 0 T))
    (hYderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hYpos : ∀ t ∈ Set.Icc 0 T, 0 < Y t)
    (hbound : ∀ t ∈ Set.Ioo 0 T, Y' t ≤ g t * Y t) :
    ∀ t ∈ Set.Icc 0 T, Y t ≤ Y 0 * Real.exp (∫ s in (0:ℝ)..t, g s) := by
  have hgint : IntegrableOn g (Set.Icc 0 T) volume :=
    hgc.integrableOn_compact isCompact_Icc
  set P : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, g s with hP
  set W : ℝ → ℝ := fun t => Real.log (Y t) - P t with hW
  have huIcc : Set.uIcc (0:ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hT
  have hPcont : ContinuousOn P (Set.Icc 0 T) := by
    have := continuousOn_primitive_interval (a := 0) (b := T) (f := g) (μ := volume)
      (by rw [huIcc]; exact hgint)
    rwa [huIcc] at this
  have hlogYcont : ContinuousOn (fun t => Real.log (Y t)) (Set.Icc 0 T) := by
    apply Real.continuousOn_log.comp hYc
    intro t ht; exact (ne_of_gt (hYpos t ht))
  have hWc : ContinuousOn W (Set.Icc 0 T) := hlogYcont.sub hPcont
  have hWderiv : ∀ x ∈ Set.Ioo 0 T, HasDerivAt W (Y' x / Y x - g x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc 0 T := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hgatx : ContinuousAt g x := hgc.continuousAt (Icc_mem_nhds hx.1 hx.2)
    have hgint0x : IntervalIntegrable g volume 0 x := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (le_of_lt hx.1)]
      exact hgc.mono (Set.Icc_subset_Icc le_rfl (le_of_lt hx.2))
    have hsmaf : StronglyMeasurableAtFilter g (nhds x) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hgc.mono Set.Ioo_subset_Icc_self) x hx
    have h1 : HasDerivAt (fun t => Real.log (Y t)) (Y' x / Y x) x :=
      (hYderiv x hx).log (ne_of_gt (hYpos x hxIcc))
    have h2 : HasDerivAt P (g x) x :=
      integral_hasDerivAt_right hgint0x hsmaf hgatx
    exact h1.sub h2
  have hWanti : AntitoneOn W (Set.Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hWc
    · rw [interior_Icc]; intro x hx
      exact (hWderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      rw [(hWderiv x hx).deriv]
      have hYx : 0 < Y x := hYpos x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      rw [sub_nonpos, div_le_iff₀ hYx]; linarith [hbound x hx]
  intro t ht
  have h0mem : (0:ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hWle : W t ≤ W 0 := hWanti h0mem ht ht.1
  have hW0 : W 0 = Real.log (Y 0) := by simp [hW, hP, integral_same]
  rw [hW0] at hWle
  have hstep : Real.log (Y t) ≤ Real.log (Y 0) + P t := by
    have : Real.log (Y t) - P t ≤ Real.log (Y 0) := hWle; linarith
  calc Y t = Real.exp (Real.log (Y t)) := (Real.exp_log (hYpos t ht)).symm
    _ ≤ Real.exp (Real.log (Y 0) + P t) := Real.exp_le_exp.mpr hstep
    _ = Real.exp (Real.log (Y 0)) * Real.exp (P t) := Real.exp_add _ _
    _ = Y 0 * Real.exp (P t) := by rw [Real.exp_log (hYpos 0 h0mem)]

/-!
## The criterion in the classical-solution framework
-/

/-- A **Beale–Kato–Majda control** for a velocity evolution `u` on `[0,T)`.

It packages the a-priori structure of the continuation criterion:
* `control` is a positive regularity quantity `Y(t)` (think a high Sobolev norm
  `‖u(t)‖_{Hˢ}`) with an explicit derivative `controlDeriv`;
* `rate` is a time-integrable supremum majorant of the vorticity,
  `‖ω(t,·)‖ ≤ rate t` for every `x` (think `C‖ω(t)‖_∞`);
* `gronwall_inequality` is the BKM differential inequality `Y' ≤ rate · Y`;
* `control_dominates_velocity` records that the regularity norm bounds the
  velocity pointwise (Sobolev embedding);
* `finite_vorticity_integral` is the **hypothesis of the criterion**: the
  improper vorticity-rate integral converges, `∃ B, ∀ t < T, ∫₀ᵗ rate ≤ B`.

The rate is only continuous on the half-open `[0,T)`, so it may blow up as
`t → T`; the finite-integral field is therefore a genuine restriction, not a
consequence of continuity.  A `BKMControl` is *constructed*, so nothing here is
assumed; the two Mathlib-absent PDE inputs that build one from a Navier–Stokes
solution are named in `BKMAnalyticResidual`. -/
structure BKMControl (u : VelocityEvolution) (T : ℝ) where
  /-- The positive regularity control `Y(t)`. -/
  control : ℝ → ℝ
  /-- Its pointwise derivative on `(0,T)`. -/
  controlDeriv : ℝ → ℝ
  /-- A time-integrable supremum majorant of the vorticity. -/
  rate : ℝ → ℝ
  rate_continuousOn : ContinuousOn rate (Set.Ico 0 T)
  control_continuousOn : ContinuousOn control (Set.Ico 0 T)
  control_hasDerivAt : ∀ t ∈ Set.Ioo 0 T, HasDerivAt control (controlDeriv t) t
  control_pos : ∀ t ∈ Set.Ico 0 T, 0 < control t
  /-- The Beale–Kato–Majda a-priori differential inequality. -/
  gronwall_inequality : ∀ t ∈ Set.Ioo 0 T, controlDeriv t ≤ rate t * control t
  /-- `rate t` dominates the vorticity supremum at time `t`. -/
  rate_dominates_vorticity :
    ∀ t ∈ Set.Ico 0 T, ∀ x : Space,
      officialEuclideanNorm (vorticity u t x) ≤ rate t
  /-- The regularity control dominates the velocity pointwise. -/
  control_dominates_velocity :
    ∀ t ∈ Set.Ico 0 T, ∀ x : Space, ‖u t x‖ ≤ control t
  /-- **The criterion's hypothesis**: the improper vorticity integral converges. -/
  finite_vorticity_integral :
    ∃ B : ℝ, ∀ t ∈ Set.Ico 0 T, (∫ s in (0:ℝ)..t, rate s) ≤ B

namespace BKMControl

variable {u : VelocityEvolution} {T : ℝ}

/-- **BKM continuation: finite vorticity integral ⟹ the velocity stays
uniformly bounded on `[0,T)`.**  No pointwise blow-up occurs before `T`. -/
theorem velocity_bounded (c : BKMControl u T) (hT : 0 < T) :
    ∃ M : ℝ, ∀ t ∈ Set.Ico 0 T, ∀ x : Space, ‖u t x‖ ≤ M := by
  obtain ⟨B, hB⟩ := c.finite_vorticity_integral
  refine ⟨c.control 0 * Real.exp B, ?_⟩
  have h0mem : (0:ℝ) ∈ Set.Ico 0 T := ⟨le_rfl, hT⟩
  have hc0pos : 0 < c.control 0 := c.control_pos 0 h0mem
  intro t ht x
  -- Icc 0 t ⊆ Ico 0 T since t < T
  have hIcc_sub : Set.Icc 0 t ⊆ Set.Ico 0 T := by
    intro s hs; exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hIoo_sub : Set.Ioo 0 t ⊆ Set.Ioo 0 T := by
    intro s hs; exact ⟨hs.1, lt_trans hs.2 ht.2⟩
  -- apply the sharp core on the closed sub-interval [0,t]
  have hcore := gronwall_log_apriori (Y := c.control) (Y' := c.controlDeriv)
    (g := c.rate) (T := t) ht.1
    (c.rate_continuousOn.mono hIcc_sub)
    (c.control_continuousOn.mono hIcc_sub)
    (fun s hs => c.control_hasDerivAt s (hIoo_sub hs))
    (fun s hs => c.control_pos s (hIcc_sub hs))
    (fun s hs => c.gronwall_inequality s (hIoo_sub hs))
    t ⟨ht.1, le_rfl⟩
  -- monotone exp of the finite-integral bound
  have hexp : Real.exp (∫ s in (0:ℝ)..t, c.rate s) ≤ Real.exp B :=
    Real.exp_le_exp.mpr (hB t ht)
  calc ‖u t x‖ ≤ c.control t := c.control_dominates_velocity t ht x
    _ ≤ c.control 0 * Real.exp (∫ s in (0:ℝ)..t, c.rate s) := hcore
    _ ≤ c.control 0 * Real.exp B := by
        exact mul_le_mul_of_nonneg_left hexp (le_of_lt hc0pos)

/-- **The criterion consumes the repository's breakdown machinery.**  A partial
classical solution carrying a `BKMControl` (finite vorticity integral) cannot
simultaneously be a `PointEvaluationBreakdownWitness`: the uniform velocity
bound contradicts pointwise blow-up.  Thus a finite vorticity integral excludes
the finite-time breakdown that `Navier.Breakdown.MaximalNonextension` uses to
deny global existence. -/
theorem excludes_pointEvaluationBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField}
    {GlobalSolution : VelocityEvolution → PressureEvolution → Prop}
    (w : PointEvaluationBreakdownWitness ν f u₀ T GlobalSolution)
    (c : BKMControl w.localSolution.velocity T) : False := by
  have hT : 0 < T := w.localSolution.terminalTime_pos
  obtain ⟨M, hM⟩ := c.velocity_bounded hT
  obtain ⟨t, ht0, htT, hlarge⟩ := w.point_norm_unbounded M
  exact (not_lt_of_ge (hM t ⟨ht0, htT⟩ w.point)) hlarge

end BKMControl

/-!
## Named analytic residuals (honest decomposition, not axioms)
-/

/-- The genuinely Mathlib-absent PDE inputs required to *construct* a
`BKMControl` from a Navier–Stokes solution.  Each is a named residual with a
literature reference; none is asserted here, and the certified theorems above
depend on none of them.

* `biotSavartLogInequality` — the Beale–Kato–Majda logarithmic estimate
  `‖∇u‖_∞ ≲ C(1 + ‖ω‖_∞ (1 + log⁺‖u‖_{Hˢ}) + ‖ω‖_2)`, giving the Grönwall
  differential inequality (BKM 1984, Lemma; Majda–Bertozzi §3.4).  ~400 LOC:
  Biot–Savart kernel + Calderón–Zygmund singular-integral bound, both absent
  from Mathlib.
* `sobolevEmbeddingDomination` — `‖u‖_∞ ≤ C‖u‖_{Hˢ}` for `s > 3/2`, the Sobolev
  embedding `Hˢ(ℝ³) ↪ L^∞`, making the regularity norm dominate the velocity.
* `higherNormControlContinuity` — continuity/differentiability in time of
  `t ↦ ‖u(t)‖_{Hˢ}` along a classical solution, the a-priori regularity of the
  control quantity. -/
inductive BKMAnalyticResidual where
  | biotSavartLogInequality
  | sobolevEmbeddingDomination
  | higherNormControlContinuity
  deriving DecidableEq, Repr, Fintype

/-- The three analytic residuals of the criterion remain explicitly visible. -/
def bkmAnalyticResiduals : Finset BKMAnalyticResidual := Finset.univ

theorem bkmAnalyticResiduals_card : bkmAnalyticResiduals.card = 3 := by
  decide

end Navier.Analysis.BealeKatoMajda
