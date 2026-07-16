import Navier.Analysis.BealeKatoMajda

/-!
# BKM log bootstrap: from the Biot–Savart log inequality to the criterion

The Beale–Kato–Majda continuation theorem is proved (BKM, CMP 94 (1984);
Majda–Bertozzi §3.4) by applying Grönwall **to a log-transformed control**:
the Biot–Savart log inequality only bounds `‖∇u‖_∞` by
`‖ω‖_∞·(1 + log(e + ‖u‖_{H³}))`, so the `H³` energy estimate delivers the
*log-linear* differential inequality

  `Y' ≤ g · Y · (1 + log Y)`,   `Y(t) = 1 + ‖u(t)‖²_{H³}`,  `g ≈ C(1 + ‖ω‖_∞)`,

not the linear one.  Setting `W = 1 + log Y` reduces it to `W' ≤ g·W`, which is
exactly `gronwall_log_apriori`; unwinding gives the doubly-exponential bound
`Y t ≤ exp((1 + log Y 0)·exp(∫₀ᵗ g) − 1)`.

## Certified here (no sorry)

* `gronwall_loglinear_apriori` — the log-transform bootstrap, unconditional.
* `LogBKMControl` — the criterion package with the log-linear inequality
  (the shape Biot–Savart actually delivers), plus non-vacuity witness.
* `LogBKMControl.velocity_bounded`, `LogBKMControl.excludes_pointEvaluationBreakdown`
  — finite vorticity integral ⟹ uniform velocity bound ⟹ no pointwise blow-up.

## Skeletons (honest `sorry`, truth-checked signatures)

The three named PDE inputs (`BKMAnalyticResidual` in `BealeKatoMajda.lean`) as
concrete sorried statements over `SchwartzVelocity`, with hypothesis-carried
majorants (Step-0e: avoids `⨆`-junk vacuity; each statement is monotone in its
majorant, so the hypothesis-carried form follows from the classical one):

* `biotSavartLogInequality` — BKM 1984 Lemma 1 / Majda–Bertozzi Prop. 3.8.
* `sobolevEmbeddingDomination` — `H³(ℝ³) ↪ L^∞` (Agmon/Sobolev, s = 3 > 3/2).
* `sobolevControlContinuity`, `katoCommutatorEstimate` — continuity and the
  `H³` energy/commutator estimate along a Schwartz-sliced classical solution
  (Kato–Ponce; Majda–Bertozzi §3.2.3).

`logBKMControl_of_schwartzSliced` then **derives** a `LogBKMControl` from the
skeletons — the composition type-checks end-to-end, so once the three analytic
sorries close, the criterion is fully built from solutions.
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
## The log-transform Grönwall bootstrap (unconditional)
-/

/-- **Log-linear Grönwall bootstrap.**  If `Y ≥ 1` satisfies
`Y' ≤ g·Y·(1 + log Y)` — the inequality shape the Biot–Savart log estimate
delivers — then `Y t ≤ exp((1 + log (Y 0))·exp(∫₀ᵗ g) − 1)`.

Proof: `W = 1 + log Y` satisfies `W' = Y'/Y ≤ g·W`, and `gronwall_log_apriori`
bounds `W`; exponentiating back gives the doubly-exponential bound.  This is
the exact mechanism of Beale–Kato–Majda's proof. -/
theorem gronwall_loglinear_apriori
    {Y Y' g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hgc : ContinuousOn g (Set.Icc 0 T))
    (hYc : ContinuousOn Y (Set.Icc 0 T))
    (hYderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hY1 : ∀ t ∈ Set.Icc 0 T, 1 ≤ Y t)
    (hbound : ∀ t ∈ Set.Ioo 0 T, Y' t ≤ g t * (Y t * (1 + Real.log (Y t)))) :
    ∀ t ∈ Set.Icc 0 T,
      Y t ≤ Real.exp ((1 + Real.log (Y 0)) *
        Real.exp (∫ s in (0:ℝ)..t, g s) - 1) := by
  have hYpos : ∀ t ∈ Set.Icc 0 T, 0 < Y t :=
    fun t ht => lt_of_lt_of_le one_pos (hY1 t ht)
  have hlognn : ∀ t ∈ Set.Icc 0 T, 0 ≤ Real.log (Y t) :=
    fun t ht => Real.log_nonneg (hY1 t ht)
  set W : ℝ → ℝ := fun t => 1 + Real.log (Y t) with hWdef
  have hWc : ContinuousOn W (Set.Icc 0 T) := by
    apply continuousOn_const.add
    apply Real.continuousOn_log.comp hYc
    intro t ht; exact ne_of_gt (hYpos t ht)
  have hWderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt W (Y' t / Y t) t := by
    intro t ht
    have := ((hYderiv t ht).log
      (ne_of_gt (hYpos t ⟨le_of_lt ht.1, le_of_lt ht.2⟩))).const_add 1
    simpa [hWdef] using this
  have hWpos : ∀ t ∈ Set.Icc 0 T, 0 < W t := by
    intro t ht
    have := hlognn t ht
    simp only [hWdef]; linarith
  have hWbound : ∀ t ∈ Set.Ioo 0 T, Y' t / Y t ≤ g t * W t := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [div_le_iff₀ (hYpos t htIcc)]
    calc Y' t ≤ g t * (Y t * (1 + Real.log (Y t))) := hbound t ht
      _ = g t * W t * Y t := by simp only [hWdef]; ring
  have hcore := gronwall_log_apriori hT hgc hWc hWderiv hWpos hWbound
  intro t ht
  have hWt := hcore t ht
  have hW0 : W 0 = 1 + Real.log (Y 0) := rfl
  have hlogYt : Real.log (Y t) ≤
      (1 + Real.log (Y 0)) * Real.exp (∫ s in (0:ℝ)..t, g s) - 1 := by
    have : W t = 1 + Real.log (Y t) := rfl
    rw [hW0] at hWt
    linarith [hWt]
  calc Y t = Real.exp (Real.log (Y t)) := (Real.exp_log (hYpos t ht)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlogYt

/-!
## The log-linear criterion package
-/

/-- A **log-linear Beale–Kato–Majda control**: like `BKMControl`, but with the
log-linear differential inequality `Y' ≤ rate·Y·(1 + log Y)` — the inequality
the Biot–Savart log estimate actually delivers (the linear `Y' ≤ rate·Y` is
NOT available for Navier–Stokes; only the log-degraded form is).  The finite
improper vorticity-rate integral remains the criterion's hypothesis. -/
structure LogBKMControl (u : VelocityEvolution) (T : ℝ) where
  /-- The regularity control `Y(t) ≥ 1` (think `1 + ‖u(t)‖²_{H³}`). -/
  control : ℝ → ℝ
  /-- Its pointwise derivative on `(0,T)`. -/
  controlDeriv : ℝ → ℝ
  /-- A time-integrable majorant of `C(1 + ‖ω(t)‖_∞)`-type quantities. -/
  rate : ℝ → ℝ
  rate_continuousOn : ContinuousOn rate (Set.Ico 0 T)
  control_continuousOn : ContinuousOn control (Set.Ico 0 T)
  control_hasDerivAt : ∀ t ∈ Set.Ioo 0 T, HasDerivAt control (controlDeriv t) t
  control_ge_one : ∀ t ∈ Set.Ico 0 T, 1 ≤ control t
  /-- The log-linear BKM differential inequality. -/
  loglinear_inequality : ∀ t ∈ Set.Ioo 0 T,
    controlDeriv t ≤ rate t * (control t * (1 + Real.log (control t)))
  /-- `rate t` dominates the vorticity supremum at time `t`. -/
  rate_dominates_vorticity :
    ∀ t ∈ Set.Ico 0 T, ∀ x : Space,
      officialEuclideanNorm (vorticity u t x) ≤ rate t
  /-- The regularity control dominates the velocity pointwise. -/
  control_dominates_velocity :
    ∀ t ∈ Set.Ico 0 T, ∀ x : Space, ‖u t x‖ ≤ control t
  /-- **The criterion's hypothesis**: the improper rate integral converges. -/
  finite_vorticity_integral :
    ∃ B : ℝ, ∀ t ∈ Set.Ico 0 T, (∫ s in (0:ℝ)..t, rate s) ≤ B

namespace LogBKMControl

variable {u : VelocityEvolution} {T : ℝ}

/-- **BKM continuation, log-linear form: finite vorticity integral ⟹ the
velocity stays uniformly bounded on `[0,T)`** (doubly-exponential bound). -/
theorem velocity_bounded (c : LogBKMControl u T) (hT : 0 < T) :
    ∃ M : ℝ, ∀ t ∈ Set.Ico 0 T, ∀ x : Space, ‖u t x‖ ≤ M := by
  obtain ⟨B, hB⟩ := c.finite_vorticity_integral
  refine ⟨Real.exp ((1 + Real.log (c.control 0)) * Real.exp B - 1), ?_⟩
  have h0mem : (0:ℝ) ∈ Set.Ico 0 T := ⟨le_rfl, hT⟩
  have hc0 : 1 ≤ c.control 0 := c.control_ge_one 0 h0mem
  intro t ht x
  have hIcc_sub : Set.Icc 0 t ⊆ Set.Ico 0 T := by
    intro s hs; exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hIoo_sub : Set.Ioo 0 t ⊆ Set.Ioo 0 T := by
    intro s hs; exact ⟨hs.1, lt_trans hs.2 ht.2⟩
  have hcore := gronwall_loglinear_apriori (Y := c.control)
    (Y' := c.controlDeriv) (g := c.rate) (T := t) ht.1
    (c.rate_continuousOn.mono hIcc_sub)
    (c.control_continuousOn.mono hIcc_sub)
    (fun s hs => c.control_hasDerivAt s (hIoo_sub hs))
    (fun s hs => c.control_ge_one s (hIcc_sub hs))
    (fun s hs => c.loglinear_inequality s (hIoo_sub hs))
    t ⟨ht.1, le_rfl⟩
  -- monotone: ∫₀ᵗ rate ≤ B and 1 + log(control 0) ≥ 1 > 0
  have hcoef : 0 ≤ 1 + Real.log (c.control 0) := by
    have := Real.log_nonneg hc0; linarith
  have hexp : Real.exp (∫ s in (0:ℝ)..t, c.rate s) ≤ Real.exp B :=
    Real.exp_le_exp.mpr (hB t ht)
  have hmono : (1 + Real.log (c.control 0)) *
      Real.exp (∫ s in (0:ℝ)..t, c.rate s) - 1 ≤
      (1 + Real.log (c.control 0)) * Real.exp B - 1 := by
    have := mul_le_mul_of_nonneg_left hexp hcoef
    linarith
  calc ‖u t x‖ ≤ c.control t := c.control_dominates_velocity t ht x
    _ ≤ Real.exp ((1 + Real.log (c.control 0)) *
        Real.exp (∫ s in (0:ℝ)..t, c.rate s) - 1) := hcore
    _ ≤ Real.exp ((1 + Real.log (c.control 0)) * Real.exp B - 1) :=
        Real.exp_le_exp.mpr hmono

/-- A log-linear control excludes the repository's pointwise finite-time
breakdown witness — same consumption as `BKMControl`, at the weaker (true for
Navier–Stokes) log-linear inequality. -/
theorem excludes_pointEvaluationBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField}
    {GlobalSolution : VelocityEvolution → PressureEvolution → Prop}
    (w : PointEvaluationBreakdownWitness ν f u₀ T GlobalSolution)
    (c : LogBKMControl w.localSolution.velocity T) : False := by
  have hT : 0 < T := w.localSolution.terminalTime_pos
  obtain ⟨M, hM⟩ := c.velocity_bounded hT
  obtain ⟨t, ht0, htT, hlarge⟩ := w.point_norm_unbounded M
  exact (not_lt_of_ge (hM t ⟨ht0, htT⟩ w.point)) hlarge

/-- Step-0e non-vacuity: the zero velocity carries a `LogBKMControl` on every
horizon (control `≡ 1`, rate `≡ 0`; `log 1 = 0`). -/
def controlZero (T : ℝ) : LogBKMControl (fun _ _ => 0) T where
  control := fun _ => 1
  controlDeriv := fun _ => 0
  rate := fun _ => 0
  rate_continuousOn := continuousOn_const
  control_continuousOn := continuousOn_const
  control_hasDerivAt := fun t _ => hasDerivAt_const t 1
  control_ge_one := fun t _ => le_rfl
  loglinear_inequality := fun t _ => by norm_num
  rate_dominates_vorticity := fun t _ x => by
    have hv : vorticity (fun _ _ => 0) t x = 0 := by
      simp [vorticity, staticCurl]
    rw [hv, (officialEuclideanNorm_eq_zero_iff 0).mpr rfl]
  control_dominates_velocity := fun t _ x => by norm_num
  finite_vorticity_integral := ⟨0, fun t _ => by simp⟩

end LogBKMControl

/-!
## Skeletons: the analytic inputs over Schwartz fields

Reference statements with honest `sorry` bodies.  Majorants are
hypothesis-carried (each classical statement is monotone in the corresponding
norm, so these forms follow from the textbook ones and avoid `⨆`-junk
vacuity).  Norm convention: `‖·‖` on `Space → Space` values is Mathlib's Pi
(sup) norm; all `ℝ³` norms are equivalent, constants are absorbed into `C`
(the official-norm comparison is the `currentSpaceNormEuclideanNormEquivalence`
encoding residual, tracked separately in `Problem.lean`).
-/

/-- The squared inhomogeneous `H³(ℝ³)` Sobolev norm of a Schwartz velocity
field: `∑_{n ≤ 3} ‖D^n u‖²_{L²}`.  Schwartz decay makes every summand a
genuine (finite) integral. -/
def sobolevH3NormSq (u : SchwartzVelocity) : ℝ :=
  ∑ n ∈ Finset.range 4, ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2

/-- The squared `H³` norm is nonnegative (each summand is an integral of a
square). -/
theorem sobolevH3NormSq_nonneg (u : SchwartzVelocity) :
    0 ≤ sobolevH3NormSq u := by
  apply Finset.sum_nonneg
  intro n _
  exact integral_nonneg (fun x => by positivity)

/-- **[SKELETON — BKM 1984, Lemma 1; Majda–Bertozzi Prop. 3.8; est ~400 LOC.]**
The Biot–Savart logarithmic inequality: for a divergence-free Schwartz field,
the velocity gradient is bounded by the vorticity sup norm times a *logarithm*
of the `H³` norm, plus the vorticity `L²` norm:

  `‖∇u‖_∞ ≤ C(1 + Mω·(1 + log(1 + Ms)) + √M₂)`

for any majorants `Mω ≥ ‖ω‖_∞`, `M₂ ≥ ‖ω‖²_{L²}`, `Ms ≥ ‖u‖²_{H³}`.  The
`log(1+‖·‖²)` form is equivalent to the textbook `log(e+‖·‖)` up to `C`.

Closure route: Biot–Savart representation `∇u = ∇K ∗ ω` (kernel absent from
Mathlib), near-field Calderón–Zygmund cancellation + cutoff at scale
`ρ = ‖u‖_{H³}^{-1}`-type log interpolation, far-field kernel in `L²(|x|>1)`
paired with `‖ω‖_{L²}`.  Genuinely Mathlib-absent: singular-integral theory. -/
theorem biotSavartLogInequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity), DivergenceFreeInitial u →
        ∀ Mω M₂ Ms : ℝ,
          (∀ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ≤ Mω) →
          (∫ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ^ 2) ≤ M₂ →
          sobolevH3NormSq u ≤ Ms →
          ∀ x : Space,
            ‖fderiv ℝ (⇑u) x‖ ≤
              C * (1 + Mω * (1 + Real.log (1 + Ms)) + Real.sqrt M₂) := by
  sorry

/-- **[SKELETON — Agmon/Sobolev embedding `H²(ℝ³) ↪ L^∞`, s = 3 > 3/2;
Majda–Bertozzi Lemma 3.2; est ~250 LOC.]**  The sup norm of a Schwartz field is
dominated by (the square root of) its `H³` norm: `‖u‖_∞ ≤ C·√Ms` for any
majorant `Ms ≥ ‖u‖²_{H³}`.  Closure route: Fourier inversion +
Cauchy–Schwarz against `(1+|ξ|²)^{-s}` (integrable for `s > 3/2`); needs the
Schwartz Fourier–Plancherel API, present in Mathlib, plus derivative-to-symbol
bookkeeping. -/
theorem sobolevEmbeddingDomination :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (Ms : ℝ), sobolevH3NormSq u ≤ Ms →
        ∀ x : Space, ‖(⇑u) x‖ ≤ C * Real.sqrt Ms := by
  sorry

/-- A classical solution whose nonnegative-time slices are Schwartz fields.
This is the regularity frame in which the `H³` energy method operates; the
persistence of Schwartz class itself is standard for smooth bounded-energy
solutions (rapid decay propagates; Majda–Bertozzi §3.1–3.2). -/
structure SchwartzSlicedSolution (ν : ℝ) (u₀ : SchwartzVelocity) where
  velocity : VelocityEvolution
  pressure : PressureEvolution
  slice : ℝ → SchwartzVelocity
  slice_eq : ∀ t : ℝ, 0 ≤ t → ⇑(slice t) = velocity t
  solution : IsClassicalSolution ν zeroForce u₀ velocity pressure

/-- **[SKELETON — higher-norm control continuity; Majda–Bertozzi §3.2.3;
est ~300 LOC.]**  Along a Schwartz-sliced classical solution the `H³`-norm
control `t ↦ ‖u(t)‖²_{H³}` is continuous on nonnegative time.  Closure route:
dominated convergence over the jointly-smooth slices with locally uniform
Schwartz seminorm bounds. -/
theorem sobolevControlContinuity
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀) :
    ContinuousOn (fun t => sobolevH3NormSq (S.slice t)) (Set.Ici 0) := by
  sorry

/-- **[SKELETON — Kato–Ponce commutator / `H³` energy estimate;
Majda–Bertozzi Prop. 3.7; Kato–Ponce CPAM 41 (1988); est ~600 LOC.]**
Along a Schwartz-sliced classical solution with a pointwise gradient majorant
`G`, the `H³` energy `t ↦ ‖u(t)‖²_{H³}` is differentiable on positive time
with derivative at most `C·G(t)·‖u(t)‖²_{H³}`: differentiating the `H³` energy,
the pressure term vanishes (divergence-free), the viscous term is dissipative
(`ν ≥ 0`), and the convection commutator is bounded by `C‖∇u‖_∞‖u‖²_{H³}`.

Statement shape: derivative existence and its bound are asserted together
(both are part of the classical estimate); the majorant `G` is
hypothesis-carried. -/
theorem katoCommutatorEstimate :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ν : ℝ}, 0 ≤ ν →
      ∀ {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀)
        {T : ℝ} (G : ℝ → ℝ),
        (∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Space,
          ‖fderiv ℝ (S.velocity t) x‖ ≤ G t) →
        ∀ t ∈ Set.Ioo (0:ℝ) T,
          ∃ D : ℝ,
            HasDerivAt (fun s => sobolevH3NormSq (S.slice s)) D t ∧
            D ≤ C * G t * sobolevH3NormSq (S.slice t) := by
  sorry


/-!
## The tower composes: solutions + analytic inputs ⟹ the criterion
-/

/-- **The BKM tower composes.**  A Schwartz-sliced classical solution with a
continuous vorticity-sup majorant `Mω` and vorticity-`L²` majorant `M₂` whose
combined improper integral is finite carries a `LogBKMControl` — so by
`LogBKMControl.velocity_bounded` the velocity is uniformly bounded on `[0,T)`
and no pointwise breakdown occurs.

This theorem consumes the four skeleton statements above; its own contribution
(the constant bookkeeping, the `(1 + a(1+L) + b) ≤ (1+a+b)(1+L)` absorption,
the `√s ≤ 1+s` domination rescale, and the assembly of all continuity/
derivative facts) is fully proved.  It certifies that once the analytic
sorries close, the criterion is *built from solutions* with no statement-level
gap. -/
theorem logBKMControl_of_schwartzSliced
    {ν T : ℝ} (hν : 0 ≤ ν) {u₀ : SchwartzVelocity}
    (S : SchwartzSlicedSolution ν u₀)
    (Mω M₂ : ℝ → ℝ)
    (hMωc : ContinuousOn Mω (Set.Ico 0 T))
    (hM₂c : ContinuousOn M₂ (Set.Ico 0 T))
    (hMω : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Space,
      officialEuclideanNorm (staticCurl (S.velocity t) x) ≤ Mω t)
    (hM₂ : ∀ t ∈ Set.Ico (0:ℝ) T,
      (∫ x : Space,
        officialEuclideanNorm (staticCurl (S.velocity t) x) ^ 2) ≤ M₂ t)
    (hfin : ∃ B : ℝ, ∀ t ∈ Set.Ico (0:ℝ) T,
      (∫ s in (0:ℝ)..t, (1 + Mω s + Real.sqrt (M₂ s))) ≤ B) :
    Nonempty (LogBKMControl S.velocity T) := by
  classical
  obtain ⟨CB, hCBpos, hBS⟩ := biotSavartLogInequality
  obtain ⟨CS, hCSpos, hSE⟩ := sobolevEmbeddingDomination
  obtain ⟨CK, hCKpos, hKato⟩ := katoCommutatorEstimate
  -- the H³ control and constants
  set N : ℝ → ℝ := fun s => sobolevH3NormSq (S.slice s) with hNdef
  set c : ℝ := max CS 1 with hcdef
  have hc1 : (1:ℝ) ≤ c := le_max_right _ _
  have hcpos : (0:ℝ) < c := lt_of_lt_of_le one_pos hc1
  set M : ℝ := max (CK * CB) 1 with hMdef
  have hM1 : (1:ℝ) ≤ M := le_max_right _ _
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hNnn : ∀ t : ℝ, 0 ≤ N t := fun t => sobolevH3NormSq_nonneg _
  have hMωnn : ∀ t ∈ Set.Ico (0:ℝ) T, 0 ≤ Mω t := by
    intro t ht
    exact le_trans (officialEuclideanNorm_nonneg _) (hMω t ht 0)
  -- divergence-free slices from incompressibility
  have hdivfree : ∀ t ∈ Set.Ico (0:ℝ) T, DivergenceFreeInitial (S.slice t) := by
    intro t ht x
    have hst : ⇑(S.slice t) = S.velocity t := S.slice_eq t ht.1
    show staticDivergence (fun y => (S.slice t) y) x = 0
    have hd := S.solution.incompressible t ht.1 x
    simpa [staticDivergence, divergence, spatialDerivative, hst] using hd
  -- gradient majorant from the Biot–Savart log inequality
  set G : ℝ → ℝ := fun t =>
    CB * (1 + Mω t * (1 + Real.log (1 + N t)) + Real.sqrt (M₂ t)) with hGdef
  have hGnn : ∀ t ∈ Set.Ico (0:ℝ) T, 0 ≤ G t := by
    intro t ht
    have hL : 0 ≤ Real.log (1 + N t) :=
      Real.log_nonneg (by linarith [hNnn t])
    have := hMωnn t ht
    have hb := Real.sqrt_nonneg (M₂ t)
    have hpar : 0 ≤ 1 + Mω t * (1 + Real.log (1 + N t)) + Real.sqrt (M₂ t) := by
      nlinarith
    exact mul_nonneg (le_of_lt hCBpos) hpar
  have hG : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Space,
      ‖fderiv ℝ (S.velocity t) x‖ ≤ G t := by
    intro t ht x
    have hst : ⇑(S.slice t) = S.velocity t := S.slice_eq t ht.1
    have hcurl : ∀ y : Space,
        officialEuclideanNorm (staticCurl (⇑(S.slice t)) y) ≤ Mω t := by
      intro y; rw [hst]; exact hMω t ht y
    have hcurl2 :
        (∫ y : Space,
          officialEuclideanNorm (staticCurl (⇑(S.slice t)) y) ^ 2) ≤ M₂ t := by
      rw [hst]; exact hM₂ t ht
    have := hBS (S.slice t) (hdivfree t ht) (Mω t) (M₂ t) (N t)
      hcurl hcurl2 le_rfl x
    rw [hst] at this
    exact this
  -- H³ derivative facts through `deriv` (no choice function needed)
  have hNderiv : ∀ t ∈ Set.Ioo (0:ℝ) T,
      HasDerivAt N (deriv N t) t ∧ deriv N t ≤ CK * G t * N t := by
    intro t ht
    obtain ⟨D, hD, hDle⟩ := hKato hν S G hG t ht
    have hd : deriv N t = D := hD.deriv
    rw [hd]
    exact ⟨hD, hDle⟩
  -- assemble the control
  refine ⟨{
    control := fun t => c * (1 + N t)
    controlDeriv := fun t => c * deriv N t
    rate := fun t => M * (1 + Mω t + Real.sqrt (M₂ t))
    rate_continuousOn := ?_
    control_continuousOn := ?_
    control_hasDerivAt := ?_
    control_ge_one := ?_
    loglinear_inequality := ?_
    rate_dominates_vorticity := ?_
    control_dominates_velocity := ?_
    finite_vorticity_integral := ?_ }⟩
  · -- rate continuity
    exact continuousOn_const.mul ((continuousOn_const.add hMωc).add
      (Real.continuous_sqrt.comp_continuousOn hM₂c))
  · -- control continuity
    exact continuousOn_const.mul (continuousOn_const.add
      ((sobolevControlContinuity S).mono Set.Ico_subset_Ici_self))
  · -- derivative
    intro t ht
    exact ((hNderiv t ht).1.const_add 1).const_mul c
  · -- control ≥ 1
    intro t ht
    nlinarith [hNnn t]
  · -- the log-linear inequality (constant bookkeeping chain)
    intro t ht
    have htIco : t ∈ Set.Ico (0:ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
    obtain ⟨-, hDle⟩ := hNderiv t ht
    have hL : 0 ≤ Real.log (1 + N t) :=
      Real.log_nonneg (by linarith [hNnn t])
    have hb : 0 ≤ Real.sqrt (M₂ t) := Real.sqrt_nonneg _
    have hmω := hMωnn t htIco
    have hn := hNnn t
    -- absorption: 1 + a(1+L) + b ≤ (1+a+b)(1+L)
    have habsorb : 1 + Mω t * (1 + Real.log (1 + N t)) + Real.sqrt (M₂ t) ≤
        (1 + Mω t + Real.sqrt (M₂ t)) * (1 + Real.log (1 + N t)) := by
      nlinarith
    have hGle : G t ≤ CB * ((1 + Mω t + Real.sqrt (M₂ t)) *
        (1 + Real.log (1 + N t))) := by
      exact mul_le_mul_of_nonneg_left habsorb (le_of_lt hCBpos)
    -- step 1: deriv N ≤ CK·G·N ≤ CK·G·(1+N)
    have hstep1 : deriv N t ≤ CK * G t * (1 + N t) := by
      refine le_trans hDle ?_
      have : 0 ≤ CK * G t := mul_nonneg (le_of_lt hCKpos) (hGnn t htIco)
      nlinarith
    -- step 2: expand G, absorb into rate shape
    have hfactor : 0 ≤ (1 + Mω t + Real.sqrt (M₂ t)) := by nlinarith
    have honePlusL : 0 ≤ 1 + Real.log (1 + N t) := by linarith
    have honePlusN : 0 ≤ 1 + N t := by linarith
    have hstep2 : CK * G t * (1 + N t) ≤
        (CK * CB) * ((1 + Mω t + Real.sqrt (M₂ t)) *
          (1 + Real.log (1 + N t))) * (1 + N t) := by
      have h1 : CK * G t ≤ (CK * CB) * ((1 + Mω t + Real.sqrt (M₂ t)) *
          (1 + Real.log (1 + N t))) := by
        calc CK * G t ≤ CK * (CB * ((1 + Mω t + Real.sqrt (M₂ t)) *
            (1 + Real.log (1 + N t)))) :=
              mul_le_mul_of_nonneg_left hGle (le_of_lt hCKpos)
          _ = (CK * CB) * ((1 + Mω t + Real.sqrt (M₂ t)) *
              (1 + Real.log (1 + N t))) := by ring
      exact mul_le_mul_of_nonneg_right h1 honePlusN
    have hstep3 : (CK * CB) * ((1 + Mω t + Real.sqrt (M₂ t)) *
        (1 + Real.log (1 + N t))) * (1 + N t) ≤
        M * ((1 + Mω t + Real.sqrt (M₂ t)) *
          (1 + Real.log (1 + N t))) * (1 + N t) := by
      have hMge : CK * CB ≤ M := le_max_left _ _
      have hnn : 0 ≤ (1 + Mω t + Real.sqrt (M₂ t)) *
          (1 + Real.log (1 + N t)) := mul_nonneg hfactor honePlusL
      have := mul_le_mul_of_nonneg_right hMge hnn
      exact mul_le_mul_of_nonneg_right this honePlusN
    -- step 4: log(c(1+N)) ≥ log(1+N)
    have hlogc : Real.log (1 + N t) ≤ Real.log (c * (1 + N t)) := by
      have h1N : (0:ℝ) < 1 + N t := by linarith
      rw [Real.log_mul (ne_of_gt hcpos) (ne_of_gt h1N)]
      have := Real.log_nonneg hc1
      linarith
    -- assemble
    have hrateNN : 0 ≤ M * (1 + Mω t + Real.sqrt (M₂ t)) :=
      mul_nonneg (le_of_lt hMpos) hfactor
    calc c * deriv N t
        ≤ c * (CK * G t * (1 + N t)) :=
          mul_le_mul_of_nonneg_left hstep1 (le_of_lt hcpos)
      _ ≤ c * (M * ((1 + Mω t + Real.sqrt (M₂ t)) *
            (1 + Real.log (1 + N t))) * (1 + N t)) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hcpos)
          exact le_trans hstep2 hstep3
      _ = M * (1 + Mω t + Real.sqrt (M₂ t)) *
            ((c * (1 + N t)) * (1 + Real.log (1 + N t))) := by ring
      _ ≤ M * (1 + Mω t + Real.sqrt (M₂ t)) *
            ((c * (1 + N t)) * (1 + Real.log (c * (1 + N t)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hrateNN
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (le_of_lt hcpos) honePlusN)
          linarith
  · -- rate dominates vorticity
    intro t ht x
    have h1 := hMω t ht x
    have hb : 0 ≤ Real.sqrt (M₂ t) := Real.sqrt_nonneg _
    have hmω := hMωnn t ht
    have hchain : Mω t ≤ M * (1 + Mω t + Real.sqrt (M₂ t)) := by
      nlinarith
    exact le_trans h1 hchain
  · -- control dominates velocity
    intro t ht x
    have hst : ⇑(S.slice t) = S.velocity t := S.slice_eq t ht.1
    have hemb := hSE (S.slice t) (N t) le_rfl x
    rw [hst] at hemb
    have hsqrt : Real.sqrt (N t) ≤ 1 + N t := by
      nlinarith [Real.sq_sqrt (hNnn t), Real.sqrt_nonneg (N t)]
    have hCSc : CS ≤ c := le_max_left _ _
    calc ‖S.velocity t x‖ ≤ CS * Real.sqrt (N t) := hemb
      _ ≤ CS * (1 + N t) :=
          mul_le_mul_of_nonneg_left hsqrt (le_of_lt hCSpos)
      _ ≤ c * (1 + N t) := by
          have h1N : 0 ≤ 1 + N t := by linarith [hNnn t]
          exact mul_le_mul_of_nonneg_right hCSc h1N
  · -- finite improper integral
    obtain ⟨B, hB⟩ := hfin
    refine ⟨M * B, ?_⟩
    intro t ht
    have : (∫ s in (0:ℝ)..t, M * (1 + Mω s + Real.sqrt (M₂ s))) =
        M * ∫ s in (0:ℝ)..t, (1 + Mω s + Real.sqrt (M₂ s)) :=
      intervalIntegral.integral_const_mul _ _
    rw [this]
    exact mul_le_mul_of_nonneg_left (hB t ht) (le_of_lt hMpos)

end Navier.Analysis.BealeKatoMajda
