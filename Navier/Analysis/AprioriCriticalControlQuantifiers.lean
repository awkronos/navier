import Navier.Analysis.CriticalControlDecomposition
import Navier.Analysis.BealeKatoMajda

/-!
# Brick (g): the quantifier order of `APrioriCriticalControl`, truth-checked

The audit (`/tmp/handoff/audit/NOTES-ns-rh.md` §1.2) flags that the a-priori leaf
`APrioriCriticalControl N` of `Navier/Analysis/CriticalControlDecomposition.lean`
quantifies `∃ M` *before* `∀ T` *and* before `∀ u, p`, while the literature's
a-priori estimates carry the bound's constant *after* the horizon (and often
after the solution as well).  This module fixes the orders precisely and proves
the separations with checked witnesses, then isolates the exact remaining
estimate at the BKM vorticity candidate.

## The three orders (this file's definitions)

| name | prefix | mathematical identity |
|---|---|---|
| `APrioriCriticalControl N` (imported) | `∀ν ∀u₀ ∃M ∀T ∀u ∀p` | horizon- AND solution-uniform; this is what the decomposition consumes |
| `HorizonLocalCriticalControl N` | `∀ν ∀u₀ ∀T ∃M ∀u ∀p` | the literature's a-priori order: Ladyzhenskaya/Foias–Temam propagation, and the BKM log-bootstrap bound `exp((1 + log Y 0) · exp(∫ g))` which is doubly exponential in the horizon (`BealeKatoMajda.gronwall_log_apriori`) |
| `SolutionPointwiseCriticalControl N` | `∀ν ∀u₀ ∀T ∀u ∃M ∀p` | the order of a single supplied `BKMControl`/`LogBKMControl`: its `finite_vorticity_integral` field provides `B` per solution, per horizon |

`aPriori_le_horizonLocal` and `horizonLocal_le_solutionPointwise` prove the
inclusions, and **both implications are kernel-falsified by concrete
quantities**:

* `horizonGrowth T u = ofReal T` satisfies `HorizonLocalCriticalControl`
  (take `M = ⌈T⌉₊`) and fails `APrioriCriticalControl` — witness: the zero
  solution at horizon `M + 1`.  This is the T-slot strictness: any quantity
  whose best bound grows with the horizon (the BKM bootstrap's
  double-exponential is the archetype) lands exactly here.
* `terminalPointEval T u = ofReal (u T 0 0)` satisfies
  `SolutionPointwiseCriticalControl` and fails `HorizonLocalCriticalControl` —
  witness: `solvesBefore_zero_junk_terminal`, admissible solutions that equal
  zero on all of `[0,T)` but carry arbitrary terminal value at `t = T`.  This
  is the solution-slot strictness: `SolvesBefore ν T` constrains `u` only on
  `Ico 0 T` (every PDE and energy field quantifies `t < T`), so the admissible
  class is *not* determined by the datum off `[0,T)`, and any estimate
  sensitive to terminal-time values cannot be uniform over it.

## The surviving candidate and the exact remaining estimate

A candidate `N` immune to the terminal-junk witness must factor through the
slice field on `[0,T)` up to null sets; the a.e.-in-time integral of the
repository vorticity supremum does exactly that, and it is the quantity the
continuation machinery consumes: `bkmVorticityControl` below, with
`vorticityRate u t = ⨆ x, ofReal (officialEuclideanNorm (vorticity u t x))` —
the same majorand as `BKMControl.rate_dominates_vorticity`.
The BKM bootstrap *does* deliver, per solution carrying a `BKMControl`, a bound
of the `SolutionPointwise` order
(`bkmVorticityControl_le_ofReal_BKMControl_bound`), and `bkmVorticityControl`
is non-degenerate on the shear field `(0, x₀, 0)`
(`bkmVorticityControl_nondegenerate`), so it is not the `N ≡ 0` member whose
degeneracy is witnessed in `CriticalControlDecomposition`.  The remaining
estimate — `APrioriCriticalControl bkmVorticityControl`, isolated as the named
proposition `NSBKMUniformVorticityApriori` — is therefore strictly stronger
than the literature's order for this `N`, and no consequence of the bootstraps
currently in the repo: it needs (i) a `BKMControl`/`LogBKMControl` producer for
*every* member of the wide `SolvesBefore` class (open: the class carries no
`H³` slice-norm finiteness and no uniqueness; `BKMLogBootstrap.lean`'s header
states its inputs are not produced there), and (ii) a horizon-uniform
(`T`-free) version of the estimate, which for this `N` is global
vorticity-integral boundedness — conservation of difficulty: an a-priori proof
of (ii), combined with the BKM restart of brick (f), is global regularity
itself.

## Small-data contrast (recorded, not proved here)

For data small in the Lei–Lin mixed `X⁻¹ ∩ ν∫ X¹` budget
(`ContinuousLeiLinBanachContraction.admissibleNorm_continuousMildImage_sub_le_banach`,
factor `3/4`), the admissible-ball radius depends only on the datum, not on the
horizon, so once the ball's completeness/fixed-point primitives (brick (a))
land, the a-priori leaf for the `X`-budget quantity closes in the *strong*
order `APrioriCriticalControl` on the small-data subclass.  The hard case is
arbitrary Schwartz data (bricks (e)+(f)), where the literature supplies only
order (2).

## Non-claims

No `sorry`.  Nothing here proves `APrioriCriticalControl` for any
PDE-meaningful `N`, and nothing refutes the *conjectured* leaf for
`bkmVorticityControl` — the two witnesses refute the *converse implications*
between quantifier orders.  The monotonicity lemmas are what any future proof
must flow through.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped ENNReal NNReal

namespace Navier.Analysis.AprioriCriticalControlQuantifiers

open Navier Navier.Breakdown Navier.Analysis.GlobalRegularityEndpoint
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding

/-! ## The two weaker orders -/

/-- **Horizon-local a-priori control**: the literature's order.  The constant
`M` may depend on the horizon `T` (Ladyzhenskaya/Foias–Temam propagation; the
BKM log-bootstrap majorand is doubly exponential in `T`), but is uniform over
the admissible solution class at that horizon. -/
def HorizonLocalCriticalControl (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ T : ℝ, 0 < T → ∃ M : ℝ≥0, ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → N T u ≤ (M : ℝ≥0∞)

/-- **Solution-pointwise a-priori control**: the order of a single supplied
`BKMControl` / `LogBKMControl`, whose `finite_vorticity_integral` field provides
the integral bound for that one solution on that one horizon. -/
def SolutionPointwiseCriticalControl (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p →
      ∃ M : ℝ≥0, N T u ≤ (M : ℝ≥0∞)

/-- The decomposition's leaf is the strongest of the three orders. -/
theorem aPriori_le_horizonLocal {N : CriticalQuantity}
    (h : APrioriCriticalControl N) : HorizonLocalCriticalControl N := by
  intro ν hν u₀ hdiv T hT
  obtain ⟨M, hM⟩ := h ν hν u₀ hdiv
  exact ⟨M, fun u p hi hs => hM T hT u p hi hs⟩

/-- A horizon-local bound is uniform over the solutions of that horizon. -/
theorem horizonLocal_le_solutionPointwise {N : CriticalQuantity}
    (h : HorizonLocalCriticalControl N) : SolutionPointwiseCriticalControl N := by
  intro ν hν u₀ hdiv T hT u p hi hs
  obtain ⟨M, hM⟩ := h ν hν u₀ hdiv T hT
  exact ⟨M, hM u p hi hs⟩

/-- Monotonicity of the strong order: the leaf transfers to smaller quantities. -/
theorem APrioriCriticalControl.mono {N₁ N₂ : CriticalQuantity}
    (h : ∀ T u, N₁ T u ≤ N₂ T u) (h₂ : APrioriCriticalControl N₂) :
    APrioriCriticalControl N₁ := by
  intro ν hν u₀ hdiv
  obtain ⟨M, hM⟩ := h₂ ν hν u₀ hdiv
  exact ⟨M, fun T hT u p hi hs => le_trans (h T u) (hM T hT u p hi hs)⟩

theorem HorizonLocalCriticalControl.mono {N₁ N₂ : CriticalQuantity}
    (h : ∀ T u, N₁ T u ≤ N₂ T u) (h₂ : HorizonLocalCriticalControl N₂) :
    HorizonLocalCriticalControl N₁ := by
  intro ν hν u₀ hdiv T hT
  obtain ⟨M, hM⟩ := h₂ ν hν u₀ hdiv T hT
  exact ⟨M, fun u p hi hs => le_trans (h T u) (hM u p hi hs)⟩

/-! ## T-slot strictness: `HorizonLocalCriticalControl` ⇏ `APrioriCriticalControl` -/

/-- Horizon accumulation: `N T u = ofReal T`.  The canonical shape of a quantity
whose best bound grows with the horizon — the BKM log-bootstrap majorand is
pointwise ≥ this — and it separates the orders exactly. -/
def horizonGrowth : CriticalQuantity := fun T _ => ENNReal.ofReal T

theorem horizonLocal_horizonGrowth : HorizonLocalCriticalControl horizonGrowth := by
  intro ν _ u₀ _ T hT
  refine ⟨⟨|T|, abs_nonneg T⟩, fun _ _ _ _ => ?_⟩
  exact ENNReal.ofReal_le_coe.mpr (le_abs_self T)

theorem not_aPriori_horizonGrowth : ¬ APrioriCriticalControl horizonGrowth := by
  intro h
  obtain ⟨M, hM⟩ := h 1 zero_lt_one 0 ProblemStatements.divergenceFreeInitial_zero
  have hcon := hM ((M : ℝ) + 1) (by positivity) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ => rfl) (solvesBefore_zero 1 ((M : ℝ) + 1))
  have hle : ((M : ℝ) + 1) ≤ (M : ℝ) := ENNReal.ofReal_le_coe.mp hcon
  linarith

/-! ## Solution-slot strictness: `SolutionPointwiseCriticalControl` ⇏
`HorizonLocalCriticalControl` -/

/-- Terminal-coordinate evaluation: `N T u = ofReal (u T 0 0)`.  The class
`SolvesBefore ν T` constrains the velocity only on `Ico 0 T`, so the value of
an admissible `u` at `t = T` is unrestricted; no bound uniform over the class
exists for a quantity that sees that value. -/
def terminalPointEval : CriticalQuantity := fun T u => ENNReal.ofReal (u T (0 : Space) 0)

theorem solutionPointwise_terminalPointEval :
    SolutionPointwiseCriticalControl terminalPointEval := by
  intro ν _ u₀ _ T _ u p _ _
  refine ⟨⟨|u T (0 : Space) 0|, abs_nonneg _⟩, ?_⟩
  exact ENNReal.ofReal_le_coe.mpr (le_abs_self _)

/-! The PDE fields `divergence`, `convection`, `laplacian` are built from the
*slice* `u t`, so two velocities with equal slices at `t` agree in them —
transported by defeq-unfolding `show`s below rather than rewriting inside
opaque definition bodies. -/

private theorem divergence_congr_slice {u v : VelocityEvolution} (t : ℝ) (x : Space)
    (h : u t = v t) : divergence u t x = divergence v t x := by
  show ∑ i : Fin 3, fderiv ℝ (u t) x (basisVector i) i
      = ∑ i : Fin 3, fderiv ℝ (v t) x (basisVector i) i
  rw [h]

private theorem convection_congr_slice {u v : VelocityEvolution} (t : ℝ) (x : Space)
    (h : u t = v t) : convection u t x = convection v t x := by
  show fderiv ℝ (u t) x (u t x) = fderiv ℝ (v t) x (v t x)
  rw [h]

private theorem laplacian_congr_slice {u v : VelocityEvolution} (t : ℝ) (x : Space)
    (h : u t = v t) : laplacian u t x = laplacian v t x := by
  show ∑ i : Fin 3, fderiv ℝ (fun y : Space => fderiv ℝ (u t) y (basisVector i)) x
        (basisVector i)
      = ∑ i : Fin 3, fderiv ℝ (fun y : Space => fderiv ℝ (v t) y (basisVector i)) x
        (basisVector i)
  rw [h]

/-- **The terminal-junk admissibility lemma.**  A velocity that equals zero on
every time-slice of `[0,T)` and takes the constant value `c` at the terminal
time `T` is admissible for every viscosity and horizon, with zero pressure:
`SolvesBefore ν T` never evaluates the velocity at `t ≥ T`.  This is the exact
mechanism of the solution-slot separation, and the quantifier-domain fact brick
(f)/(g) consumers must respect: an a-priori `N` may only see the velocity a.e.
on `[0,T)`. -/
theorem solvesBefore_zero_junk_terminal (ν T : ℝ) (c : Space) :
    SolvesBefore ν T (fun t _ => if t = T then c else 0) (fun _ _ => 0) := by
  set u : VelocityEvolution := fun t _ => if t = T then c else 0 with hu
  obtain ⟨hv, hp, hinc, heq⟩ := zero_is_solution_before ν T
  have hslice : ∀ t, t < T → u t = fun _ => (0 : Space) := by
    intro t htT
    show (fun _ : Space => if t = T then (c : Space) else 0) = fun _ => (0 : Space)
    funext x
    exact if_neg (ne_of_lt htT)
  refine ⟨⟨?_, hp, ?_, ?_⟩, ?_, ?_⟩
  · -- joint smoothness: on `spacetimeBefore T` the junk field *is* the zero field
    refine hv.congr (fun z hz => ?_)
    have htT : z.1 < T := hz.1.2
    show u z.1 z.2 = (0 : Space)
    rw [hslice z.1 htT]
  · intro t ht htT x
    rw [divergence_congr_slice (v := fun _ _ => (0 : Space)) t x (hslice t htT)]
    exact hinc t ht htT x
  · intro t ht htT x
    rw [timeDerivative_congr_before (v := fun _ _ => (0 : Space))
        (fun s _ hs => hslice s hs) ht htT x]
    rw [convection_congr_slice (v := fun _ _ => (0 : Space)) t x (hslice t htT),
      laplacian_congr_slice (v := fun _ _ => (0 : Space)) t x (hslice t htT)]
    exact heq t ht htT x
  · intro t ht htT
    rw [hslice t htT]
    have hz : (fun x : Space => ‖(fun _ : Space => (0 : Space)) x‖ ^ 2) =
        fun _ : Space => (0 : ℝ) := by
      funext x
      simp
    rw [hz]
    exact integrable_zero Space ℝ volume
  · intro t ht htT
    have hleft : kineticEnergy u t = 0 := by
      unfold kineticEnergy
      rw [hslice t htT]
      simp
    have hright : 0 ≤ kineticEnergy u 0 := by
      unfold kineticEnergy
      refine integral_nonneg (fun x => ?_)
      positivity
    rw [hleft]
    linarith

theorem not_horizonLocal_terminalPointEval :
    ¬ HorizonLocalCriticalControl terminalPointEval := by
  intro h
  obtain ⟨M, hM⟩ := h 1 zero_lt_one 0 ProblemStatements.divergenceFreeInitial_zero
    1 zero_lt_one
  let c : Space := fun _ => ((M : ℝ) + 1)
  have hini : ∀ x : Space, (fun t _ => if t = (1 : ℝ) then c else 0) 0 x =
      (0 : SchwartzVelocity) x := by
    intro x
    show (if (0 : ℝ) = (1 : ℝ) then (c : Space) else (0 : Space)) = (0 : SchwartzVelocity) x
    rw [if_neg (by norm_num : ¬((0 : ℝ) = (1 : ℝ)))]
    simp
  have hsolve : SolvesBefore (1 : ℝ) 1 (fun t _ => if t = (1 : ℝ) then c else 0)
      (fun _ _ => 0) :=
    solvesBefore_zero_junk_terminal 1 1 c
  have hcon := hM _ _ hini hsolve
  have hut : (fun t _ => if t = (1 : ℝ) then c else 0) 1 (0 : Space) 0 = (M : ℝ) + 1 := by
    show (if (1 : ℝ) = (1 : ℝ) then (c : Space) else (0 : Space)) 0 = (M : ℝ) + 1
    rw [if_pos rfl]
  change ENNReal.ofReal ((fun t _ => if t = (1 : ℝ) then c else 0) 1 (0 : Space) 0) ≤ _ at hcon
  rw [hut] at hcon
  exact absurd (ENNReal.ofReal_le_coe.mp hcon) (by linarith)

/-! ## The BKM vorticity candidate -/

/-- Pointwise-in-time vorticity supremum, `ℝ≥0∞`-valued: the majorand
`‖ω(u t)‖_{L∞_x}` as used by `BKMControl.rate_dominates_vorticity`.  Defined as
an `iSup` of `ENNReal.ofReal`, so nonnegative and junk-tolerant wherever the
slice fails differentiability. -/
def vorticityRate (u : VelocityEvolution) (t : ℝ) : ℝ≥0∞ :=
  ⨆ x : Space, ENNReal.ofReal (officialEuclideanNorm (vorticity u t x))

/-- **The BKM vorticity-integral candidate quantity** for bricks (f)/(g):
improper-in-horizon integral of the vorticity supremum over closed sub-horizons
inside `[0,T)`; each `lintegral` is null-set insensitive, so the terminal-junk
witness above does not apply to it. -/
def bkmVorticityControl : CriticalQuantity :=
  fun T u => ⨆ s ∈ Ico 0 T, ∫⁻ t in Icc 0 s, vorticityRate u t

theorem vorticityRate_le_ofReal {u : VelocityEvolution} {T : ℝ}
    (c : BKMControl u T) {t : ℝ} (ht : t ∈ Ico 0 T) :
    vorticityRate u t ≤ ENNReal.ofReal (c.rate t) :=
  iSup_le (fun x => ENNReal.ofReal_le_ofReal (c.rate_dominates_vorticity t ht x))

/-- **The bootstrap closes at the solution-pointwise order.**  A velocity
carrying a `BKMControl` with integral bound `B` satisfies
`bkmVorticityControl T u ≤ ENNReal.ofReal B`.  The proof transfers
`rate_dominates_vorticity` through the interval integral on closed sub-horizons
`Icc 0 s ⊆ Ico 0 T`.  The estimate cannot be upgraded to
`HorizonLocalCriticalControl`, let alone the leaf order, for want of the
producer — see the module header. -/
theorem bkmVorticityControl_le_ofReal_BKMControl_bound
    {u : VelocityEvolution} {T : ℝ} (_hT : 0 < T) (c : BKMControl u T)
    {B : ℝ} (hB : ∀ t ∈ Ico 0 T, (∫ s in (0:ℝ)..t, c.rate s) ≤ B) :
    bkmVorticityControl T u ≤ ENNReal.ofReal B := by
  refine iSup₂_le (fun s hs => ?_)
  obtain ⟨hs0, hsT⟩ := hs
  have hsub : Icc (0 : ℝ) s ⊆ Ico (0 : ℝ) T := by
    rintro x hx
    exact ⟨hx.1, lt_of_le_of_lt hx.2 hsT⟩
  calc ∫⁻ t in Icc 0 s, vorticityRate u t
      ≤ ∫⁻ t in Icc 0 s, ENNReal.ofReal (c.rate t) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact vorticityRate_le_ofReal c (hsub ht)
    _ = ENNReal.ofReal (∫ t in Icc 0 s, c.rate t) := by
        refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
        · exact (c.rate_continuousOn.mono hsub).integrableOn_Icc
        · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact le_trans (officialEuclideanNorm_nonneg _)
            (c.rate_dominates_vorticity t (hsub ht) (0 : Space))
    _ = ENNReal.ofReal (∫ t in Ioc 0 s, c.rate t) := by
        congr 1
        exact integral_Icc_eq_integral_Ioc
    _ = ENNReal.ofReal (∫ t in (0:ℝ)..s, c.rate t) := by
        congr 1
        exact (integral_of_le hs0).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_mono (hB s ⟨hs0, hsT⟩)

/-! ## Non-degeneracy of the candidate (`N ≢ 0`) -/

/-- The linear shear `(0, x₀, 0)`, bundled as a continuous linear map. -/
private def shearCLM : Space →L[ℝ] Space where
  toFun := fun x => ![0, x 0, 0]
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp [Pi.add_apply]
  map_smul' := by
    intro c x
    ext i
    fin_cases i <;> simp [Pi.smul_apply]
  cont := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> (first | exact continuous_const | exact continuous_apply 0)

private theorem shearCLM_apply (x : Space) : shearCLM x = ![0, x 0, 0] := rfl

private theorem staticCurl_comp_zero (u : VelocityField) (x : Space) :
    staticCurl u x 0 =
      (fderiv ℝ u x (basisVector 1)) 2 - (fderiv ℝ u x (basisVector 2)) 1 := by
  simp only [staticCurl, Fin.sum_univ_three, Finset.sum_apply]
  simp [basisVector, cross_apply]
  ring

private theorem staticCurl_comp_one (u : VelocityField) (x : Space) :
    staticCurl u x 1 =
      (fderiv ℝ u x (basisVector 2)) 0 - (fderiv ℝ u x (basisVector 0)) 2 := by
  simp only [staticCurl, Fin.sum_univ_three, Finset.sum_apply]
  simp [basisVector, cross_apply]
  ring

private theorem staticCurl_comp_two (u : VelocityField) (x : Space) :
    staticCurl u x 2 =
      (fderiv ℝ u x (basisVector 0)) 1 - (fderiv ℝ u x (basisVector 1)) 0 := by
  simp only [staticCurl, Fin.sum_univ_three, Finset.sum_apply]
  simp [basisVector, cross_apply]
  ring

/-- The shear field has vorticity `(0, 0, 1)` at every time and point —
computed, not asserted. -/
private theorem vorticity_shear (t : ℝ) (x : Space) :
    vorticity (fun _ => ⇑shearCLM) t x = ![0, 0, 1] := by
  have hf : fderiv ℝ ⇑shearCLM x = shearCLM := shearCLM.hasFDerivAt.fderiv
  show staticCurl ⇑shearCLM x = ![0, 0, 1]
  ext i
  fin_cases i
  · show staticCurl ⇑shearCLM x 0 = ![0, 0, 1] 0
    rw [staticCurl_comp_zero, hf]
    simp [shearCLM_apply, basisVector]
  · show staticCurl ⇑shearCLM x 1 = ![0, 0, 1] 1
    rw [staticCurl_comp_one, hf]
    simp [shearCLM_apply, basisVector]
  · show staticCurl ⇑shearCLM x 2 = ![0, 0, 1] 2
    rw [staticCurl_comp_two, hf]
    simp [shearCLM_apply, basisVector]

/-- The candidate is not the degenerate member `N ≡ 0` witnessed in
`CriticalControlDecomposition`: `bkmVorticityControl 1 u_shear > 0` because the
shear field's vorticity is the constant nonzero vector `(0,0,1)`.  (The shear is
not in `SolvesBefore` — its slices are not `L²` — so this is the functional-level
non-degeneracy required by the audit rule; class-level non-degeneracy on a
genuine solution is recorded as the first missing exhibit in the notes.) -/
theorem bkmVorticityControl_nondegenerate :
    ∃ T u, 0 < bkmVorticityControl T u := by
  let u : VelocityEvolution := fun _ => ⇑shearCLM
  set ρ : ℝ := officialEuclideanNorm (![0, 0, 1] : Space) with hρ
  have hρpos : 0 < ρ := by
    refine lt_of_not_ge (fun h => ?_)
    have h0 : ![0, 0, 1] = (0 : Space) :=
      (officialEuclideanNorm_eq_zero_iff (![0, 0, 1] : Space)).mp
        (le_antisymm h (officialEuclideanNorm_nonneg _))
    have h2 := congrFun h0 2
    simp at h2
  have hrate : ∀ t, ENNReal.ofReal ρ ≤ vorticityRate u t := by
    intro t
    have h0 : (fun x : Space => ENNReal.ofReal (officialEuclideanNorm (vorticity u t x)))
        (0 : Space) = ENNReal.ofReal ρ := by
      show ENNReal.ofReal (officialEuclideanNorm (vorticity u t (0 : Space))) =
          ENNReal.ofReal ρ
      rw [vorticity_shear t 0, hρ]
    rw [← h0]
    exact le_iSup (fun x : Space => ENNReal.ofReal (officialEuclideanNorm (vorticity u t x))) 0
  have hge : ((1 : ℝ) / 2) ∈ Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨1, u, ?_⟩
  calc (0 : ℝ≥0∞)
      < ENNReal.ofReal ρ * ENNReal.ofReal (1 / 2 : ℝ) := by positivity
    _ = ∫⁻ t in Icc (0 : ℝ) (1 / 2), ENNReal.ofReal ρ := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Icc, sub_zero]
    _ ≤ ∫⁻ t in Icc (0 : ℝ) (1 / 2), vorticityRate u t :=
        lintegral_mono_ae (Filter.Eventually.of_forall (fun t => hrate t))
    _ ≤ ⨆ s ∈ Ico (0 : ℝ) 1, ∫⁻ t in Icc (0 : ℝ) s, vorticityRate u t :=
        le_iSup₂ (f := fun s (_hs : s ∈ Ico (0 : ℝ) 1) => ∫⁻ t in Icc (0 : ℝ) s,
          vorticityRate u t) ((1 : ℝ) / 2) hge

/-- The exact remaining estimate of brick (g), isolated as a named proposition.
Its precise type is `APrioriCriticalControl bkmVorticityControl`, i.e.

`∀ (ν : ℝ), 0 < ν → ∀ (u₀ : SchwartzVelocity), DivergenceFreeInitial u₀ →
   ∃ (M : ℝ≥0), ∀ (T : ℝ), 0 < T →
     ∀ (u : VelocityEvolution) (p : PressureEvolution),
       (∀ x, u 0 x = u₀ x) → SolvesBefore ν T u p →
       ⨆ s ∈ Ico 0 T, ∫⁻ t in Icc 0 s, ⨆ x,
         ENNReal.ofReal (officialEuclideanNorm (vorticity u t x)) ≤ ↑M`

— global-in-horizon, solution-uniform boundedness of the improper vorticity
integral, over *all* pointwise classical finite-energy solutions of the datum
in the normalized-pressure continuation class of brick (f).  Proving this for
the shear-free `SolvesBefore` members is the brick; see the module header for
the two named missing inputs (uniform BKM producer + horizon-uniformity, the
second equivalent to the crown's content by conservation of difficulty). -/
abbrev NSBKMUniformVorticityApriori : Prop :=
  APrioriCriticalControl bkmVorticityControl

end Navier.Analysis.AprioriCriticalControlQuantifiers

#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.aPriori_le_horizonLocal
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.horizonLocal_le_solutionPointwise
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.APrioriCriticalControl.mono
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.HorizonLocalCriticalControl.mono
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.horizonLocal_horizonGrowth
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.not_aPriori_horizonGrowth
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.solutionPointwise_terminalPointEval
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.solvesBefore_zero_junk_terminal
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.not_horizonLocal_terminalPointEval
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.vorticityRate_le_ofReal
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.bkmVorticityControl_le_ofReal_BKMControl_bound
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.bkmVorticityControl_nondegenerate
