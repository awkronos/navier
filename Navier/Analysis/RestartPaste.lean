import Navier.Analysis.CriticalControlDecomposition

/-!
# Brick (f) structural core: shifted restart strips and the interior-time paste

The continuation leaf `NormalizedContinuationFromCriticalControl N` of
`Navier/Analysis/CriticalControlDecomposition.lean` demands, for every admissible
`SolvesBefore ν T u p`, an extension `SolvesBefore ν (T + δ) u' p'` agreeing with
`u, p` on `[0, T)` with `δ` independent of the horizon.  The repository supplies
the analytic *estimates* around that leaf (`BealeKatoMajda.gronwall_log_apriori`,
`BKMLogBootstrap.gronwall_loglinear_apriori`, and brick (g)'s quantifier-order
audit), but NO mechanism exists to turn a local solution starting at a positive
time into a classical solution on a shifted half-open strip, and NO lemma glues
two such strips at an interior time.  Those two pieces are the structural half
of brick (f); this module certifies them and reduces the leaf to a named,
purely analytic engine hypothesis.

Certified here (no `sorry`):

* `SolvesFrom ν T₀ h w q` — the shifted-strip interface: classical PDE data on
  `[T₀, T₀ + h) × ℝ³` with the equation clauses required only on the TIME-OPEN
  part `(T₀, T₀ + h)`, and the energy inequality normalized at the strip's own
  start time `T₀`.  Both weakenings are necessary, not cosmetic: translating a
  solution rightwards copies its time derivative only strictly after the
  starting time (the translated function's left-side values are the glued
  solution's own history, about which the local piece says nothing), and
  `SolvesBefore`'s datum-level inequality `E(t) ≤ E(0)` does not transport to a
  monotonicity between two positive times.
* `timeDerivative_shift` — the chain-rule transport of the half-line time
  derivative through a right translation at interior times.
* `SolvesBefore.to_solvesFrom_shift` — every local solution shifted to start at
  `T₀ ≥ 0` is a `SolvesFrom` strip, energy normalization included.
* `restart_paste` — gluing a `SolvesBefore` piece and a `SolvesFrom` piece that
  agree on an overlap strip `[T₀, T)` produces `SolvesBefore ν (T + h)` with the
  normalized pressure gauge, plus both agreement clauses: exactly the
  continuation conclusion.
* `HorizonIndependentRestart N` — the residual analytic engine, stated in the
  leaf's own quantifier order (`∀ M ∃ h` horizon-independent), and
  `normalizedContinuation_of_horizonIndependentRestart` — the reduction
  `engine ⟹ NormalizedContinuationFromCriticalControl N`.

## What this file deliberately does NOT claim

* It does not construct `HorizonIndependentRestart N` for any `N`.  For the
  brick (g) candidate `N = bkmVorticityControl` the engine needs (i) slice-norm
  budget propagation under the vorticity-integral bound — the same missing
  `BKMControl` producer brick (g)'s header isolates — and (ii) a restart local
  existence whose horizon `h` depends on that budget, not on `T` (bricks
  (d)/(e) territory, themselves gated on brick (a)'s complete metric carrier).
* The engine is stated slightly STRONGER than the leaf in one deliberate
  respect: the restart strip's energy inequality is normalized at its start
  time.  This is the form a shifted local solution actually carries
  (`SolvesBefore.to_solvesFrom_shift`), and the form the paste consumes;
  a leaf witness obtained by other means may need that normalization
  separately.  In particular there is NO restriction lemma
  `SolvesBefore ν T' → SolvesFrom ν T₀ (T' - T₀)`: the datum-level inequality
  `E(t) ≤ E(0)` genuinely does not give `E(t) ≤ E(T₀)` at a positive start.
* No claim that the glued object is unique, or that the decomposition's
  conclusion solution agrees with the input past `T` — `SolvesBefore ν (T+δ)`
  constrains nothing at or beyond its own horizon, and the paste defines the
  extension from the restart piece on `[T, T + δ)` only up to that convention.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology

namespace Navier.Analysis.RestartPaste

open Navier Navier.Breakdown Navier.Analysis.GlobalRegularityEndpoint
open Navier.Analysis.CriticalControlDecomposition

/-! ## The shifted-strip interface -/

/-- **Classical data on the shifted half-open strip `[T₀, T₀ + h)`.**

The six fields mirror `SolvesBefore`, shifted to start at `T₀`: joint smoothness
of velocity and pressure on `[T₀, T₀+h) × ℝ³`, pointwise incompressibility on
the whole strip, the Navier–Stokes equation on the TIME-OPEN part
`(T₀, T₀+h)` (see the module header for why the starting time cannot be
included via translation), finite-energy slices, and the energy inequality
normalized at the strip's own start `T₀`. -/
structure SolvesFrom (ν T₀ h : ℝ) (w : VelocityEvolution) (q : PressureEvolution) :
    Prop where
  vel_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => w z.1 z.2)
      (Set.Ico T₀ (T₀ + h) ×ˢ (Set.univ : Set Space))
  pres_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)
      (Set.Ico T₀ (T₀ + h) ×ˢ (Set.univ : Set Space))
  incompressible :
    ∀ t : ℝ, T₀ ≤ t → t < T₀ + h → ∀ x : Space, divergence w t x = 0
  equation :
    ∀ t : ℝ, T₀ < t → t < T₀ + h → ∀ x : Space,
      timeDerivative w t x + convection w t x =
        ν • laplacian w t x - pressureGradient q t x
  finite_energy :
    ∀ t : ℝ, T₀ ≤ t → t < T₀ + h →
      MeasureTheory.Integrable (fun x : Space => ‖w t x‖ ^ 2)
  energy_le_start :
    ∀ t : ℝ, T₀ ≤ t → t < T₀ + h → kineticEnergy w t ≤ kineticEnergy w T₀

/-! ## Slice-congruence leaves -/

/-- Spatial observables built from a time-slice transfer across slice
equality at (possibly different) times (the peer precedent in
`AprioriCriticalControlQuantifiers` is `private`, so the four three-liners are
carried here too, in the generalized `u t = v s` form the shift needs). -/
private theorem divergence_congr {u v : VelocityEvolution} {t s : ℝ} (x : Space)
    (h : u t = v s) : divergence u t x = divergence v s x := by
  show ∑ i : Fin 3, fderiv ℝ (u t) x (basisVector i) i
      = ∑ i : Fin 3, fderiv ℝ (v s) x (basisVector i) i
  rw [h]

private theorem convection_congr {u v : VelocityEvolution} {t s : ℝ} (x : Space)
    (h : u t = v s) : convection u t x = convection v s x := by
  show fderiv ℝ (u t) x (u t x) = fderiv ℝ (v s) x (v s x)
  rw [h]

private theorem laplacian_congr {u v : VelocityEvolution} {t s : ℝ} (x : Space)
    (h : u t = v s) : laplacian u t x = laplacian v s x := by
  show ∑ i : Fin 3, fderiv ℝ (fun y : Space => fderiv ℝ (u t) y (basisVector i)) x
        (basisVector i)
      = ∑ i : Fin 3, fderiv ℝ (fun y : Space => fderiv ℝ (v s) y (basisVector i)) x
        (basisVector i)
  rw [h]

private theorem pressureGradient_congr {p q : PressureEvolution} {t s : ℝ} (x : Space)
    (h : p t = q s) : pressureGradient p t x = pressureGradient q s x := by
  show (fun i => fderiv ℝ (p t) x (basisVector i)) = (fun i => fderiv ℝ (q s) x (basisVector i))
  rw [h]

/-- Energy-slice congruence at possibly different times. -/
private theorem kineticEnergy_congr {u v : VelocityEvolution} {t s : ℝ} (h : u t = v s) :
    kineticEnergy u t = kineticEnergy v s := by
  unfold Navier.kineticEnergy
  rw [h]

private theorem integrable_energy_iff_slice {u v : VelocityEvolution} {t s : ℝ}
    (h : u t = v s) :
    MeasureTheory.Integrable (fun x : Space => ‖u t x‖ ^ 2) ↔
      MeasureTheory.Integrable (fun x : Space => ‖v s x‖ ^ 2) := by
  refine ⟨fun hu => ?_, fun hv => ?_⟩
  · have heq : (fun x : Space => ‖v s x‖ ^ 2) = (fun x : Space => ‖u t x‖ ^ 2) := by rw [← h]
    rw [heq]; exact hu
  · have heq : (fun x : Space => ‖u t x‖ ^ 2) = (fun x : Space => ‖v s x‖ ^ 2) := by rw [h]
    rw [heq]; exact hv

/-- If two velocity evolutions are eventually equal (slice-wise) as `t` varies,
their `Set.Ici 0` time derivatives agree — the generalized twin of
`timeDerivative_congr_before`, proved the same way (`EventuallyEq.fderivWithin_eq`
followed by applying the linear map to `1`). -/
private theorem timeDerivative_congr_eventually {u v : VelocityEvolution} {t : ℝ}
    (h : ∀ᶠ s in nhdsWithin t (Set.Ici (0 : ℝ)), u s = v s)
    (hpt : u t = v t) (x : Space) :
    timeDerivative u t x = timeDerivative v t x := by
  have hev : (fun s : ℝ => u s x) =ᶠ[nhdsWithin t (Set.Ici (0 : ℝ))]
      fun s : ℝ => v s x :=
    h.mono fun s hs => congrFun hs x
  simpa [timeDerivative] using congrArg (fun L : ℝ →L[ℝ] Space => L 1)
    (Filter.EventuallyEq.fderivWithin_eq hev (congrFun hpt x))

/-! ## Right-translation of smooth strips -/

/-- Contour-pulling a smooth spacetime function through the right translation
`z ↦ (z.1 - T₀, z.2)`: smoothness on `[0, h) × ℝ³` transports to smoothness on
`[T₀, T₀ + h) × ℝ³`. -/
private theorem contDiffOn_shift {T₀ h : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ × Space → E}
    (hF : ContDiffOn ℝ ∞ F (Set.Ico (0 : ℝ) h ×ˢ (Set.univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => F (z.1 - T₀, z.2))
      (Set.Ico T₀ (T₀ + h) ×ˢ (Set.univ : Set Space)) := by
  refine' hF.comp (((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn) ?_
  rintro ⟨a, b⟩ ⟨⟨ha1, ha2⟩, -⟩
  exact ⟨⟨sub_nonneg.mpr ha1, sub_lt_iff_lt_add'.mpr ha2⟩, Set.mem_univ _⟩

/-! ## Time-derivative transport through a right translation -/

/-- **Translation of the half-line time derivative.**  For `t > 0` and
`t - T₀ ∈ (0, δ)`, the time derivative of the right-shifted evolution `s ↦
v (s - T₀)` at `t` is the time derivative of `v` at `s := t - T₀`.  Both sides
are ordinary derivatives at strictly positive times, so each `fderivWithin ℝ ·
(Ici 0)` reduces to the full `fderiv` (`fderivWithin_of_mem_nhds`), and the
chain rule through the translation `r ↦ r - T₀` and the curve `u ↦ (u, x)`
identifies both with `fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (t - T₀, x)
(1, 0)`.  This is the one calculus leaf the shifted-strip interface needs; the
strict inequalities on `t` and `t - T₀` are exactly why `SolvesFrom`'s equation
clause is open at the strip start. -/
theorem timeDerivative_shift (v : VelocityEvolution) (δ T₀ t : ℝ) (x : Space)
    (ht : 0 < t) (hv :
      ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)
        (Set.Ico (0 : ℝ) δ ×ˢ (Set.univ : Set Space)))
    (hs : t - T₀ ∈ Set.Ioo (0 : ℝ) δ) :
    timeDerivative (fun s : ℝ => v (s - T₀)) t x = timeDerivative v (t - T₀) x := by
  have hF : DifferentiableAt ℝ (fun z : ℝ × Space => v z.1 z.2) ⟨t - T₀, x⟩ := by
    have hopen : Set.Ioo (0 : ℝ) δ ×ˢ (Set.univ : Set Space) ∈ 𝓝 ⟨t - T₀, x⟩ :=
      (IsOpen.prod isOpen_Ioo isOpen_univ).mem_nhds ⟨⟨hs.1, hs.2⟩, Set.mem_univ x⟩
    have hwd :
        DifferentiableWithinAt ℝ (fun z : ℝ × Space => v z.1 z.2)
          (Set.Ico (0 : ℝ) δ ×ˢ (Set.univ : Set Space)) ⟨t - T₀, x⟩ :=
      (hv ⟨t - T₀, x⟩ ⟨⟨hs.1.le, hs.2⟩, Set.mem_univ x⟩).differentiableWithinAt (by simp)
    have hwd' :
        DifferentiableWithinAt ℝ (fun z : ℝ × Space => v z.1 z.2)
          (Set.Ioo (0 : ℝ) δ ×ˢ (Set.univ : Set Space)) ⟨t - T₀, x⟩ :=
      hwd.mono (Set.prod_mono Set.Ioo_subset_Ico_self (Set.Subset.refl _))
    exact hwd'.differentiableAt hopen
  have hc : DifferentiableAt ℝ (fun u : ℝ => (u, x)) (t - T₀) :=
    DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const x)
  have hg : DifferentiableAt ℝ (fun u : ℝ => v u x) (t - T₀) := by
    show DifferentiableAt ℝ
      ((fun w : ℝ × Space => v w.1 w.2) ∘ (fun u : ℝ => (u, x))) (t - T₀)
    exact hF.comp (t - T₀) hc
  have hphi : DifferentiableAt ℝ (fun r : ℝ => r - T₀) t :=
    differentiableAt_id.sub (differentiableAt_const T₀)
  have hnt : Set.Ici (0 : ℝ) ∈ 𝓝 t :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ht)) Set.Ioi_subset_Ici_self
  have hns : Set.Ici (0 : ℝ) ∈ 𝓝 (t - T₀) :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hs.1)) Set.Ioi_subset_Ici_self
  have hgc : fderiv ℝ (fun u : ℝ => v u x) (t - T₀) =
      fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) ⟨t - T₀, x⟩ ∘SL
        fderiv ℝ (fun u : ℝ => (u, x)) (t - T₀) := by
    show fderiv ℝ
        ((fun w : ℝ × Space => v w.1 w.2) ∘ (fun u : ℝ => (u, x))) (t - T₀) = _
    exact fderiv_comp (t - T₀) hF hc
  have hcv : fderiv ℝ (fun u : ℝ => (u, x)) (t - T₀) =
      (ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Space) :=
    ((hasFDerivAt_id (t - T₀)).prodMk (hasFDerivAt_const x (t - T₀))).fderiv
  have hfphi : fderiv ℝ (fun r : ℝ => r - T₀) t = ContinuousLinearMap.id ℝ ℝ := by
    rw [fderiv_sub_const]
    simp
  show fderivWithin ℝ (fun r : ℝ => v (r - T₀) x) (Set.Ici 0) t 1 =
    fderivWithin ℝ (fun r : ℝ => v r x) (Set.Ici 0) (t - T₀) 1
  have hL : fderivWithin ℝ (fun r : ℝ => v (r - T₀) x) (Set.Ici 0) t 1 =
      fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) ⟨t - T₀, x⟩ (1, 0) := by
    show fderivWithin ℝ ((fun u : ℝ => v u x) ∘ (fun r : ℝ => r - T₀)) (Set.Ici 0) t 1 = _
    rw [fderivWithin_of_mem_nhds hnt, fderiv_comp t hg hphi, hfphi, hgc, hcv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply]
  have hR : fderivWithin ℝ (fun r : ℝ => v r x) (Set.Ici 0) (t - T₀) 1 =
      fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) ⟨t - T₀, x⟩ (1, 0) := by
    show fderivWithin ℝ
        ((fun z : ℝ × Space => v z.1 z.2) ∘ (fun u : ℝ => (u, x))) (Set.Ici 0) (t - T₀) 1 = _
    rw [fderivWithin_of_mem_nhds hns, fderiv_comp (t - T₀) hF hc, hcv]
    simp
  exact hL.trans hR.symm

/-! ## Shifted strips from local solutions -/

/-- Every local solution, translated to start at time `T₀ ≥ 0`, is a
`SolvesFrom` strip on `[T₀, T₀ + h)`.  The energy field is the point of the
whole lemma: the shifted solution's inequality is *automatically* normalized at
the shift time, because the shift sends the strip start to the original
initial time. -/
theorem SolvesBefore.to_solvesFrom_shift {ν T₀ h : ℝ} {v : VelocityEvolution}
    {q : PressureEvolution} (hT₀ : 0 ≤ T₀) (hs : SolvesBefore ν h v q) :
    SolvesFrom ν T₀ h (fun t => v (t - T₀)) (fun t => q (t - T₀)) := by
  obtain ⟨hu, hp, hinc, heq⟩ := hs.classical
  have huv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)
      (Set.Ico (0 : ℝ) h ×ˢ (Set.univ : Set Space)) := hu
  have hqv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)
      (Set.Ico (0 : ℝ) h ×ˢ (Set.univ : Set Space)) := hp
  refine' ⟨contDiffOn_shift (F := fun z : ℝ × Space => v z.1 z.2) huv,
    contDiffOn_shift (F := fun z : ℝ × Space => q z.1 z.2) hqv, ?_, ?_, ?_, ?_⟩
  · intro t ht1 ht2 x
    exact hinc (t - T₀) (sub_nonneg.mpr ht1) (sub_lt_iff_lt_add'.mpr ht2) x
  · intro t ht0 ht2 x
    have hts : t - T₀ ∈ Set.Ioo (0 : ℝ) h :=
      ⟨sub_pos.mpr ht0, sub_lt_iff_lt_add'.mpr ht2⟩
    have hzf : ν • laplacian v (t - T₀) x - pressureGradient q (t - T₀) x +
        zeroForce (t - T₀) x =
      ν • laplacian v (t - T₀) x - pressureGradient q (t - T₀) x := by
      rw [show zeroForce (t - T₀) x = (0 : Space) from rfl, add_zero]
    have heq' := Eq.trans
      (heq (t - T₀) (sub_nonneg.mpr ht0.le) (sub_lt_iff_lt_add'.mpr ht2) x) hzf
    rw [timeDerivative_shift v h T₀ t x (lt_of_le_of_lt hT₀ ht0) hu hts]
    exact heq'
  · intro t ht1 ht2
    exact (integrable_energy_iff_slice (rfl : (fun t' : ℝ => v (t' - T₀)) t = v (t - T₀))).mpr
      (hs.finite_energy (t - T₀) (sub_nonneg.mpr ht1) (sub_lt_iff_lt_add'.mpr ht2))
  · intro t ht1 ht2
    have h1 : kineticEnergy (fun t' : ℝ => v (t' - T₀)) t = kineticEnergy v (t - T₀) :=
      kineticEnergy_congr rfl
    have h2 : kineticEnergy (fun t' : ℝ => v (t' - T₀)) T₀ = kineticEnergy v 0 :=
      kineticEnergy_congr (congrArg v (sub_self T₀))
    rw [h1, h2]
    exact hs.energy_le_initial (t - T₀) (sub_nonneg.mpr ht1) (sub_lt_iff_lt_add'.mpr ht2)

/-- The shifted-strip interface is satisfiable: the zero pair is a
`SolvesFrom` witness at every shift time and strip length. -/
theorem solvesFrom_zero (ν T₀ h : ℝ) : SolvesFrom ν T₀ h (fun _ _ => 0) (fun _ _ => 0) := by
  refine' ⟨contDiffOn_const, contDiffOn_const, ?_, ?_, ?_, ?_⟩
  · intro t _ _ x
    simp [divergence, spatialDerivative]
  · intro t _ _ x
    have hpg : pressureGradient (fun _ _ => (0 : ℝ)) t x = 0 := by
      funext i
      simp [pressureGradient]
    simp [timeDerivative, convection, spatialDerivative, laplacian, hpg]
  · intro t _ _
    simp
  · intro t _ _
    simp [kineticEnergy]

/-! ## The interior-time paste -/

/-- **The brick (f) gluing lemma.**  A `SolvesBefore ν T u p` piece and a
restart `SolvesFrom ν T₀ (T - T₀ + h) w q` piece that agree on the overlap
strip `[T₀, T)` glue — piecewise at the cut time `T` — into a classical
solution on `[0, T + h)` in the normalized pressure gauge, extending `u` and
`p` verbatim on `[0, T)`.  This is exactly the conclusion body of
`NormalizedContinuationFromCriticalControl`; the whole analytic content of
continuation is thereby pushed into *supplying* the `SolvesFrom` witness with
`h` independent of `T`.  The pasting point `T` is handled from the restart
side, whose equation clause is open at `T₀ < T`; the `t = T₀` end of the
restart piece is never asked for an equation, because it is covered by the
`u`-piece whose clause is closed at `0 ≤ t`. -/
theorem restart_paste {ν T T₀ h : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    {w : VelocityEvolution} {q : PressureEvolution}
    (hT₀ : 0 ≤ T₀) (hT₀T : T₀ < T) (hh : 0 < h)
    (hsol : SolvesBefore ν T u p) (hnorm : PressureNormalizedBefore T p)
    (hw : SolvesFrom ν T₀ (T - T₀ + h) w q)
    (hq_norm : ∀ t : ℝ, T₀ ≤ t → t < T + h → q t 0 = 0)
    (hagree_v : ∀ t : ℝ, T₀ ≤ t → t < T → u t = w t)
    (hagree_p : ∀ t : ℝ, T₀ ≤ t → t < T → p t = q t) :
    ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
      SolvesBefore ν (T + h) u' p' ∧ PressureNormalizedBefore (T + h) p' ∧
        VelocityAgreesBefore T u u' ∧ PressureAgreesBefore T p p' := by
  have hstrip : T₀ + (T - T₀ + h) = T + h := by ring
  obtain ⟨hu, hp, hinc, heq⟩ := hsol.classical
  obtain ⟨wv, wp, winc, weq, wfe, wel⟩ := hw
  rw [hstrip] at wv wp winc weq wfe wel
  let u' : VelocityEvolution := fun t => if t < T then u t else w t
  let p' : PressureEvolution := fun t => if t < T then p t else q t
  have hTpos : 0 < T := lt_of_le_of_lt hT₀ hT₀T
  have hu' : ∀ s : ℝ, s < T → u' s = u s := fun s hs => if_pos hs
  have hp' : ∀ s : ℝ, s < T → p' s = p s := fun s hs => if_pos hs
  have hw' : ∀ s : ℝ, T ≤ s → u' s = w s := fun s hs => if_neg (not_lt.mpr hs)
  have hq' : ∀ s : ℝ, T ≤ s → p' s = q s := fun s hs => if_neg (not_lt.mpr hs)
  -- On the restart slab `t > T₀` the glued velocity equals `w`: below the cut
  -- this is exactly the overlap agreement, above it the second branch.
  have hw_on : ∀ s : ℝ, T₀ < s → u' s = w s := by
    intro s hs
    rcases lt_or_ge s T with hsT | hsT
    · rw [hu' s hsT, hagree_v s (le_of_lt hs) hsT]
    · exact hw' s hsT
  have hq_on : ∀ s : ℝ, T₀ < s → p' s = q s := by
    intro s hs
    rcases lt_or_ge s T with hsT | hsT
    · rw [hp' s hsT, hagree_p s (le_of_lt hs) hsT]
    · exact hq' s hsT
  have hvel_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u' z.1 z.2)
      (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) := by
    intro z hz
    rcases lt_or_ge z.1 T with htT | htT
    · have hbase : ContDiffWithinAt ℝ ∞ (fun zz : ℝ × Space => u zz.1 zz.2)
          (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) z := by
        refine' (hu z ⟨⟨hz.1.1, htT⟩, hz.2⟩).mono_of_mem_nhdsWithin ?_
        refine' mem_nhdsWithin.mpr ⟨Set.Iio T ×ˢ Set.univ, IsOpen.prod isOpen_Iio isOpen_univ,
          ⟨Set.mem_Iio.mpr htT, Set.mem_univ _⟩, ?_⟩
        rintro ⟨a, b⟩ ⟨⟨ha1, _⟩, ⟨⟨hle, hlt⟩, _⟩⟩
        exact ⟨⟨hle, Set.mem_Iio.mp ha1⟩, Set.mem_univ _⟩
      refine' hbase.congr_of_eventuallyEq_of_mem ?_ hz
      refine' eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds ((IsOpen.prod isOpen_Iio isOpen_univ).mem_nhds
          ⟨Set.mem_Iio.mpr htT, Set.mem_univ _⟩)) fun z' hz' => _
      exact congrFun (hu' z'.1 (Set.mem_Iio.mp hz'.1)) z'.2
    · have hT₀z : T₀ < z.1 := lt_of_lt_of_le hT₀T htT
      have hbase : ContDiffWithinAt ℝ ∞ (fun zz : ℝ × Space => w zz.1 zz.2)
          (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) z := by
        refine' (wv z ⟨⟨le_of_lt hT₀z, hz.1.2⟩, hz.2⟩).mono_of_mem_nhdsWithin ?_
        refine' mem_nhdsWithin.mpr ⟨Set.Ioi T₀ ×ˢ Set.univ, IsOpen.prod isOpen_Ioi isOpen_univ,
          ⟨Set.mem_Ioi.mpr hT₀z, Set.mem_univ _⟩, ?_⟩
        rintro ⟨a, b⟩ ⟨⟨ha1, _⟩, ⟨⟨hle, hlt⟩, _⟩⟩
        exact ⟨⟨le_of_lt (Set.mem_Ioi.mp ha1), hlt⟩, Set.mem_univ _⟩
      refine' hbase.congr_of_eventuallyEq_of_mem ?_ hz
      refine' eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds ((IsOpen.prod isOpen_Ioi isOpen_univ).mem_nhds
          ⟨Set.mem_Ioi.mpr hT₀z, Set.mem_univ _⟩)) fun z' hz' => _
      exact congrFun (hw_on z'.1 (Set.mem_Ioi.mp hz'.1)) z'.2
  have hpres_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p' z.1 z.2)
      (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) := by
    intro z hz
    rcases lt_or_ge z.1 T with htT | htT
    · have hbase : ContDiffWithinAt ℝ ∞ (fun zz : ℝ × Space => p zz.1 zz.2)
          (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) z := by
        refine' (hp z ⟨⟨hz.1.1, htT⟩, hz.2⟩).mono_of_mem_nhdsWithin ?_
        refine' mem_nhdsWithin.mpr ⟨Set.Iio T ×ˢ Set.univ, IsOpen.prod isOpen_Iio isOpen_univ,
          ⟨Set.mem_Iio.mpr htT, Set.mem_univ _⟩, ?_⟩
        rintro ⟨a, b⟩ ⟨⟨ha1, _⟩, ⟨⟨hle, hlt⟩, _⟩⟩
        exact ⟨⟨hle, Set.mem_Iio.mp ha1⟩, Set.mem_univ _⟩
      refine' hbase.congr_of_eventuallyEq_of_mem ?_ hz
      refine' eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds ((IsOpen.prod isOpen_Iio isOpen_univ).mem_nhds
          ⟨Set.mem_Iio.mpr htT, Set.mem_univ _⟩)) fun z' hz' => _
      exact congrFun (hp' z'.1 (Set.mem_Iio.mp hz'.1)) z'.2
    · have hT₀z : T₀ < z.1 := lt_of_lt_of_le hT₀T htT
      have hbase : ContDiffWithinAt ℝ ∞ (fun zz : ℝ × Space => q zz.1 zz.2)
          (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) z := by
        refine' (wp z ⟨⟨le_of_lt hT₀z, hz.1.2⟩, hz.2⟩).mono_of_mem_nhdsWithin ?_
        refine' mem_nhdsWithin.mpr ⟨Set.Ioi T₀ ×ˢ Set.univ, IsOpen.prod isOpen_Ioi isOpen_univ,
          ⟨Set.mem_Ioi.mpr hT₀z, Set.mem_univ _⟩, ?_⟩
        rintro ⟨a, b⟩ ⟨⟨ha1, _⟩, ⟨⟨hle, hlt⟩, _⟩⟩
        exact ⟨⟨le_of_lt (Set.mem_Ioi.mp ha1), hlt⟩, Set.mem_univ _⟩
      refine' hbase.congr_of_eventuallyEq_of_mem ?_ hz
      refine' eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds ((IsOpen.prod isOpen_Ioi isOpen_univ).mem_nhds
          ⟨Set.mem_Ioi.mpr hT₀z, Set.mem_univ _⟩)) fun z' hz' => _
      exact congrFun (hq_on z'.1 (Set.mem_Ioi.mp hz'.1)) z'.2
  have hinc' : IncompressibleBefore (T + h) u' := by
    intro t ht htTh x
    rcases lt_or_ge t T with htT | htT
    · rw [divergence_congr x (hu' t htT), hinc t ht htT x]
    · rw [divergence_congr x (hw' t htT),
        winc t (le_of_lt (lt_of_lt_of_le hT₀T htT)) htTh x]
  have heq' : SatisfiesNavierStokesBefore ν zeroForce (T + h) u' p' := by
    intro t ht htTh x
    rcases lt_or_ge t T with htT | htT
    · have hev : ∀ᶠ s in nhdsWithin t (Set.Ici (0 : ℝ)), u' s = u s := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
          (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr htT))] with s hs
        exact hu' s (Set.mem_Iio.mp hs)
      rw [timeDerivative_congr_eventually hev (hu' t htT) x,
        convection_congr x (hu' t htT), laplacian_congr x (hu' t htT),
        pressureGradient_congr x (hp' t htT)]
      exact heq t ht htT x
    · have hT₀t : T₀ < t := lt_of_lt_of_le hT₀T htT
      have hev : ∀ᶠ s in nhdsWithin t (Set.Ici (0 : ℝ)), u' s = w s := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
          (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hT₀t))] with s hs
        exact hw_on s (Set.mem_Ioi.mp hs)
      rw [timeDerivative_congr_eventually hev (hw' t htT) x,
        convection_congr x (hw' t htT), laplacian_congr x (hw' t htT),
        pressureGradient_congr x (hq' t htT)]
      exact (weq t hT₀t htTh x).trans
        (by rw [show zeroForce t x = (0 : Space) from rfl, add_zero])
  have hfe' : ∀ t : ℝ, 0 ≤ t → t < T + h →
      MeasureTheory.Integrable (fun x : Space => ‖u' t x‖ ^ 2) := by
    intro t ht htTh
    rcases lt_or_ge t T with htT | htT
    · exact (integrable_energy_iff_slice (hu' t htT)).mpr (hsol.finite_energy t ht htT)
    · exact (integrable_energy_iff_slice (hw' t htT)).mpr
        (wfe t (le_of_lt (lt_of_lt_of_le hT₀T htT)) htTh)
  have heli' : ∀ t : ℝ, 0 ≤ t → t < T + h →
      kineticEnergy u' t ≤ kineticEnergy u' 0 := by
    intro t ht htTh
    rcases lt_or_ge t T with htT | htT
    · calc kineticEnergy u' t = kineticEnergy u t := kineticEnergy_congr (hu' t htT)
        _ ≤ kineticEnergy u 0 := hsol.energy_le_initial t ht htT
        _ = kineticEnergy u' 0 := (kineticEnergy_congr (hu' 0 hTpos)).symm
    · calc kineticEnergy u' t = kineticEnergy w t := kineticEnergy_congr (hw' t htT)
        _ ≤ kineticEnergy w T₀ :=
          wel t (le_of_lt (lt_of_lt_of_le hT₀T htT)) htTh
        _ = kineticEnergy u T₀ := (kineticEnergy_congr (hagree_v T₀ (le_refl T₀) hT₀T)).symm
        _ ≤ kineticEnergy u 0 := hsol.energy_le_initial T₀ hT₀ hT₀T
        _ = kineticEnergy u' 0 := (kineticEnergy_congr (hu' 0 hTpos)).symm
  have hpnorm : PressureNormalizedBefore (T + h) p' := by
    intro t ht htTh
    rcases lt_or_ge t T with htT | htT
    · rw [hp' t htT]; exact hnorm t ht htT
    · rw [hq' t htT]; exact hq_norm t (le_of_lt (lt_of_lt_of_le hT₀T htT)) htTh
  exact ⟨u', p', ⟨⟨hvel_smooth, hpres_smooth, hinc', heq'⟩, hfe', heli'⟩, hpnorm,
    fun t _ htT => (hu' t htT).symm, fun t _ htT => (hp' t htT).symm⟩

/-! ## The engine, named -/

/-- **The pure analytic engine of brick (f)**, in the continuation leaf's own
quantifier order: a horizon-independent restart length `h = h(ν, M)`, and for
every admissible solution under the budget `N T u ≤ M` a restart strip starting
at some time `T₀ ∈ [0, T)` of the piece it replaces, reaching `T + h`, agreeing
on the overlap strip, with the pressure normalized on the whole strip.
`normalizedContinuation_of_horizonIndependentRestart` turns this into the leaf;
no consequence of the repository's bootstraps currently supplies it for any
PDE-meaningful `N` — see the module header and brick (g)'s module header for
the two named missing inputs. -/
def HorizonIndependentRestart (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ M : ℝ≥0, ∃ h : ℝ, 0 < h ∧
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ T₀ : ℝ, 0 ≤ T₀ ∧ T₀ < T ∧ ∃ w : VelocityEvolution, ∃ q : PressureEvolution,
          (∀ t : ℝ, T₀ ≤ t → t < T → u t = w t) ∧
          (∀ t : ℝ, T₀ ≤ t → t < T → p t = q t) ∧
          SolvesFrom ν T₀ (T - T₀ + h) w q ∧
          (∀ t : ℝ, T₀ ≤ t → t < T + h → q t 0 = 0)

/-- **The brick (f) reduction.**  The analytic engine implies the continuation
leaf: `h` plays the role of the uniform step `δ`, and `restart_paste` supplies
the glued extension.  With this implication, proving
`NormalizedContinuationFromCriticalControl N` is exactly proving
`HorizonIndependentRestart N` — a statement about shifted local solutions that
brick (d)/(e)-style budget-carrying existence theorems can discharge verbatim. -/
theorem normalizedContinuation_of_horizonIndependentRestart {N : CriticalQuantity}
    (hN : HorizonIndependentRestart N) : NormalizedContinuationFromCriticalControl N := by
  intro ν hν M
  obtain ⟨h, hh, heng⟩ := hN ν hν M
  refine' ⟨h, hh, fun u₀ hu₀ T hT u p hinit hsol hnorm hNbound => ?_⟩
  obtain ⟨T₀, hT₀, hT₀T, w, q, hv, hp, hw, hq⟩ := heng u₀ hu₀ T hT u p hinit hsol hnorm hNbound
  exact restart_paste hT₀ hT₀T hh hsol hnorm hw hq hv hp

end Navier.Analysis.RestartPaste

#print axioms Navier.Analysis.RestartPaste.timeDerivative_shift
#print axioms Navier.Analysis.RestartPaste.SolvesBefore.to_solvesFrom_shift
#print axioms Navier.Analysis.RestartPaste.solvesFrom_zero
#print axioms Navier.Analysis.RestartPaste.restart_paste
#print axioms Navier.Analysis.RestartPaste.normalizedContinuation_of_horizonIndependentRestart
