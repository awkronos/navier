import Navier.Analysis.ParabolicCaccioppoli
import Navier.Analysis.CutoffEnergyIbp
import Navier.Breakdown.MaximalNonextension

/-!
# Pressure gauge freedom, the `L^r` no-go, and the normalized pressure

Blocker (b) of `ConditionalRegularity.prodiSerrin_interior_outerRegion_bounded`
is recorded as "an `L^r` pressure bound for `∫ χ² ⟨∇p, u⟩`; no
`MemLp`/`Integrable` estimate for `sol.pressure` exists in the estate".  This
file settles *why* no such estimate exists, and supplies the Pattern-A repair.

## The obstruction (certified, not conjectured)

`SatisfiesNavierStokesBefore` sees the pressure only through
`pressureGradient`, so the solution family is closed under adding an arbitrary
constant to the pressure (`PartialClassicalSolution.shiftPressure`).  A nonzero
constant is in no `L^r(ℝ³)` for `0 < r < ∞` because `volume (univ : Set Space)`
is infinite.  Hence:

* `not_forall_memLp_pressure` — **FALSE-as-stated.**  For every `r ≠ 0, ≠ ∞`,
  no theorem of the shape "*every* `PartialClassicalSolution` has
  `MemLp (sol.pressure t) r volume`" can be true, as soon as one solution
  exists.  This is a kernel-clean refutation of the blocker's naive statement
  shape, with the explicit witness `sol.shiftPressure 1`.
* `not_forall_memLp_pressure_zeroDatum` — the same no-go with the
  "as soon as one solution exists" caveat removed: `zeroSolution` exhibits the
  needed inhabitant (the rest state), so the refutation is unconditional for
  zero force and zero initial datum.

The endpoints are exactly where the hypotheses bite: at `r = ∞` a constant *is*
in `L^∞`, and at `r = 0` Mathlib's `MemLp` is vacuously true — both excluded by
`hr0`/`hrtop`, and neither excludable.

## The Pattern-A repair (certified)

Two objects survive the gauge freedom, and they are the ones an estimate must
be stated about:

* `pressureGradient` is gauge invariant (`pressureGradient_shiftPressure`), it
  is *determined pointwise by the velocity* through the momentum equation
  (`pressureGradient_eq_of_solution`), and therefore inherits `MemLp` from the
  three velocity terms with **no singular-integral input at all**
  (`memLp_pressureGradient_of_terms`, `integrable_pressureGradient_of_terms`).
  This is the entire `∇p` layer that blocker (b) was waiting on, and it never
  needed Calderón–Zygmund.  Its four `MemLp` premises are jointly satisfiable
  (`memLp_pressureGradient_of_terms_nonvacuous`, witnessed by the rest state),
  so the bundle sits at neither vacuity pole.
* The **normalized** pressure is unique: two pressures driving the same
  velocity differ by a spatial constant (`pressure_sub_const_of_sameVelocity`),
  so at most one of them lies in `L^r` (`pressure_eq_of_memLp`).  A pressure
  `L^r` estimate is therefore well-posed *only* after normalization, and once
  normalized it is unambiguous.

## Residual after this file

The derivative-free bound consumed by `CutoffEnergyIbp.cutoffEnergy_pressure_ibp`
— a local `L^r` bound on the *normalized* `p` itself — still needs the
Calderón–Zygmund representation `p = Σ RᵢRⱼ(uᵢuⱼ)` (named residual in
`SingularIntegralPrelims`).  What this file removes is the ambiguity that made
the target unstatable, and the whole `∇p` half of the blocker.

Axiom target: `⊆ {propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace Navier.Analysis.PressureNormalization

open Navier
open Navier.Breakdown
open Navier.Analysis.ParabolicCaccioppoli (contDiffAt_spatial_slice_before)

/-! ### The gauge group: adding a spatial constant to the pressure -/

/-- **Pressure gauge invariance of the gradient.**  `∇` annihilates the added
constant, with no differentiability hypothesis (`fderiv_add_const` is
unconditional). -/
theorem pressureGradient_add_const (p : PressureEvolution) (c : ℝ)
    (t : ℝ) (x : Space) :
    pressureGradient (fun s y => p s y + c) t x = pressureGradient p t x := by
  funext i
  simp [pressureGradient, fderiv_add_const]

/-- The Navier–Stokes system before `T` sees the pressure only through its
gradient, hence is invariant under adding a constant to the pressure. -/
theorem satisfiesNavierStokesBefore_add_const
    {ν : ℝ} {f : ForceField} {T : ℝ}
    {u : VelocityEvolution} {p : PressureEvolution} (c : ℝ)
    (h : SatisfiesNavierStokesBefore ν f T u p) :
    SatisfiesNavierStokesBefore ν f T u (fun s y => p s y + c) := by
  intro t ht0 htT x
  rw [pressureGradient_add_const]
  exact h t ht0 htT x

/-- Smoothness before `T` is preserved by adding a constant. -/
theorem smoothPressureBefore_add_const {T : ℝ} {p : PressureEvolution} (c : ℝ)
    (hp : SmoothPressureBefore T p) :
    SmoothPressureBefore T (fun s y => p s y + c) :=
  hp.add contDiffOn_const

/-- **The gauge action on solutions.**  Every `PartialClassicalSolution` yields
a one-parameter family of solutions with the *same velocity* and pressure
shifted by an arbitrary real constant.  This is the witness generator behind
the `L^r` no-go below. -/
def shiftPressure {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) (c : ℝ) :
    PartialClassicalSolution ν f u₀ T where
  terminalTime_pos := sol.terminalTime_pos
  velocity := sol.velocity
  pressure := fun s y => sol.pressure s y + c
  velocity_smooth := sol.velocity_smooth
  pressure_smooth := smoothPressureBefore_add_const c sol.pressure_smooth
  initial_condition := sol.initial_condition
  incompressible := sol.incompressible
  equation := satisfiesNavierStokesBefore_add_const c sol.equation

@[simp] theorem shiftPressure_velocity
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) (c : ℝ) :
    (shiftPressure sol c).velocity = sol.velocity := rfl

@[simp] theorem shiftPressure_pressure
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) (c : ℝ) (t : ℝ) (x : Space) :
    (shiftPressure sol c).pressure t x = sol.pressure t x + c := rfl

/-- The gauge shift does not move the pressure gradient. -/
theorem pressureGradient_shiftPressure
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) (c : ℝ) (t : ℝ) (x : Space) :
    pressureGradient (shiftPressure sol c).pressure t x
      = pressureGradient sol.pressure t x :=
  pressureGradient_add_const sol.pressure c t x

/-! ### The `L^r` no-go for the unnormalized pressure -/

/-- A nonzero constant is in no `L^r(ℝ³)` with `0 < r < ∞`: `volume` of `ℝ³` is
infinite.  Both hypotheses are sharp — a constant *is* in `L^∞`, and `MemLp _ 0`
holds for every function. -/
theorem not_memLp_const {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrtop : r ≠ (⊤ : ℝ≥0∞))
    {c : ℝ} (hc : c ≠ 0) :
    ¬ MemLp (fun _ : Space => c) r volume := by
  rw [memLp_const_iff hr0 hrtop]
  simp [measure_univ_of_isAddLeftInvariant (volume : Measure Space), hc]

/-- **FALSE-as-stated: no uniform `L^r` bound on the raw pressure.**  As soon as
one `PartialClassicalSolution` exists, the statement "every solution has
`sol.pressure t ∈ L^r`" is refuted, for every `r` with `r ≠ 0` and `r ≠ ∞`.

The explicit witness is `shiftPressure sol 1`: it has the same velocity, the
same initial datum and the same viscosity, and its pressure differs from
`sol.pressure` by the constant `1`, which is in no `L^r(ℝ³)`.

This is the reason blocker (b) of
`ConditionalRegularity.prodiSerrin_interior_outerRegion_bounded` has no
`MemLp` estimate for `sol.pressure` anywhere in the estate: there is none to
find.  The repair is normalization — see `pressure_eq_of_memLp`. -/
theorem not_forall_memLp_pressure
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) (t : ℝ)
    {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrtop : r ≠ (⊤ : ℝ≥0∞)) :
    ¬ ∀ sol' : PartialClassicalSolution ν f u₀ T,
        MemLp (fun x : Space => sol'.pressure t x) r volume := by
  intro H
  have h0 := H sol
  have h1 := H (shiftPressure sol 1)
  have hsub : MemLp
      ((fun x : Space => (shiftPressure sol 1).pressure t x)
        - fun x : Space => sol.pressure t x) r volume := h1.sub h0
  have hone : ((fun x : Space => (shiftPressure sol 1).pressure t x)
        - fun x : Space => sol.pressure t x) = fun _ : Space => (1 : ℝ) := by
    funext x
    simp
  rw [hone] at hsub
  exact not_memLp_const hr0 hrtop one_ne_zero hsub

/-- The same obstruction phrased as an existential witness: for every solution
and every finite positive exponent there is a gauge shift whose pressure slice
is not in `L^r`. -/
theorem exists_shift_pressure_not_memLp
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) (t : ℝ)
    {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrtop : r ≠ (⊤ : ℝ≥0∞)) :
    ∃ c : ℝ, ¬ MemLp (fun x : Space => (shiftPressure sol c).pressure t x)
      r volume := by
  by_cases h0 : MemLp (fun x : Space => sol.pressure t x) r volume
  · refine ⟨1, fun h1 => ?_⟩
    have hsub : MemLp
        ((fun x : Space => (shiftPressure sol 1).pressure t x)
          - fun x : Space => sol.pressure t x) r volume := h1.sub h0
    have hone : ((fun x : Space => (shiftPressure sol 1).pressure t x)
          - fun x : Space => sol.pressure t x) = fun _ : Space => (1 : ℝ) := by
      funext x
      simp
    rw [hone] at hsub
    exact not_memLp_const hr0 hrtop one_ne_zero hsub
  · refine ⟨0, fun h => h0 ?_⟩
    simpa using h

/-! ### The canonical object: `∇p` is determined by the velocity -/

/-- **The pressure gradient, solved for.**  Rearranging the momentum equation
expresses `∇p` pointwise through the velocity and the force alone:

  `∇p = ν Δu + f − ∂ₜu − (u·∇)u`.

No inversion of the Laplacian, no Leray projector, no singular integral. -/
theorem pressureGradient_eq_of_solution
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) (x : Space) :
    pressureGradient sol.pressure t x
      = ν • laplacian sol.velocity t x + f t x
          - timeDerivative sol.velocity t x
          - convection sol.velocity t x := by
  have h := sol.equation t ht0 htT x
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  linarith

/-- **`MemLp` for the pressure gradient, with no singular-integral input.**
The three velocity terms of the momentum equation plus the force control `∇p`
in every `L^r`.  This is the `∇p` half of blocker (b), discharged. -/
theorem memLp_pressureGradient_of_terms
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) {r : ℝ≥0∞}
    (hlap : MemLp (fun x : Space => laplacian sol.velocity t x) r volume)
    (hforce : MemLp (fun x : Space => f t x) r volume)
    (htime : MemLp (fun x : Space => timeDerivative sol.velocity t x) r volume)
    (hconv : MemLp (fun x : Space => convection sol.velocity t x) r volume) :
    MemLp (fun x : Space => pressureGradient sol.pressure t x) r volume := by
  have hrhs : MemLp (fun x : Space =>
      ν • laplacian sol.velocity t x + f t x
        - timeDerivative sol.velocity t x
        - convection sol.velocity t x) r volume :=
    (((hlap.const_smul ν).add hforce).sub htime).sub hconv
  have hfun : (fun x : Space => pressureGradient sol.pressure t x)
      = fun x : Space => ν • laplacian sol.velocity t x + f t x
          - timeDerivative sol.velocity t x
          - convection sol.velocity t x :=
    funext fun x => pressureGradient_eq_of_solution sol ht0 htT x
  rw [hfun]
  exact hrhs

/-- Integrable form of the same statement (`r = 1`). -/
theorem integrable_pressureGradient_of_terms
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    (hlap : Integrable (fun x : Space => laplacian sol.velocity t x) volume)
    (hforce : Integrable (fun x : Space => f t x) volume)
    (htime : Integrable (fun x : Space => timeDerivative sol.velocity t x) volume)
    (hconv : Integrable (fun x : Space => convection sol.velocity t x) volume) :
    Integrable (fun x : Space => pressureGradient sol.pressure t x) volume := by
  have h := memLp_pressureGradient_of_terms sol ht0 htT
    (r := 1) (memLp_one_iff_integrable.mpr hlap)
    (memLp_one_iff_integrable.mpr hforce)
    (memLp_one_iff_integrable.mpr htime)
    (memLp_one_iff_integrable.mpr hconv)
  exact memLp_one_iff_integrable.mp h

/-! ### Uniqueness of the normalized pressure -/

/-- Two pressures driving the same velocity (same viscosity, same force) have
the same gradient before `T`. -/
theorem pressureGradient_eq_of_sameVelocity
    {ν : ℝ} {f : ForceField} {T : ℝ} {u : VelocityEvolution}
    {p q : PressureEvolution}
    (hp : SatisfiesNavierStokesBefore ν f T u p)
    (hq : SatisfiesNavierStokesBefore ν f T u q)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) (x : Space) :
    pressureGradient p t x = pressureGradient q t x := by
  have h1 := hp t ht0 htT x
  have h2 := hq t ht0 htT x
  funext i
  have hi1 := congrFun h1 i
  have hi2 := congrFun h2 i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi1 hi2 ⊢
  linarith

/-- **The pressure is canonical modulo a spatial constant.**  Two smooth
pressures driving the same velocity differ, at each admissible time, by a
constant on `ℝ³`.  This is the well-posedness statement that makes
"normalized pressure" meaningful. -/
theorem pressure_sub_const_of_sameVelocity
    {ν : ℝ} {f : ForceField} {T : ℝ} {u : VelocityEvolution}
    {p q : PressureEvolution}
    (hpS : SmoothPressureBefore T p) (hqS : SmoothPressureBefore T q)
    (hp : SatisfiesNavierStokesBefore ν f T u p)
    (hq : SatisfiesNavierStokesBefore ν f T u q)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    ∃ c : ℝ, ∀ x : Space, p t x = q t x + c := by
  have hpd : Differentiable ℝ (p t) := fun x =>
    (contDiffAt_spatial_slice_before hpS ht0 htT x).differentiableAt (by simp)
  have hqd : Differentiable ℝ (q t) := fun x =>
    (contDiffAt_spatial_slice_before hqS ht0 htT x).differentiableAt (by simp)
  have hdiff : Differentiable ℝ (fun y : Space => p t y - q t y) :=
    hpd.sub hqd
  have hzero : ∀ x : Space, fderiv ℝ (fun y : Space => p t y - q t y) x = 0 := by
    intro x
    have hbasis : ∀ i : Fin 3,
        fderiv ℝ (fun y : Space => p t y - q t y) x (basisVector i) = 0 := by
      intro i
      have h := congrFun (pressureGradient_eq_of_sameVelocity hp hq ht0 htT x) i
      simp only [pressureGradient] at h
      have hs : fderiv ℝ (fun y : Space => p t y - q t y) x
          = fderiv ℝ (p t) x - fderiv ℝ (q t) x := fderiv_sub (hpd x) (hqd x)
      rw [hs]
      simp [h]
    ext v
    have hv : v = ∑ i : Fin 3, v i • basisVector i := by
      funext j
      simp [basisVector, Pi.single_apply]
    rw [hv, map_sum]
    simp [hbasis]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ x : Space, p t x - q t x = c :=
    ⟨p t 0 - q t 0, fun x => is_const_of_fderiv_eq_zero hdiff hzero x 0⟩
  exact ⟨c, fun x => by linarith [hc x]⟩

/-- **The normalized pressure is unique.**  If two pressures drive the same
velocity and *both* lie in `L^r` for some `0 < r < ∞`, they coincide.  Together
with `not_forall_memLp_pressure` this is the Pattern-A repair of blocker (b):
an `L^r` pressure estimate is false for the raw pressure and unambiguous for
the normalized one. -/
theorem pressure_eq_of_memLp
    {ν : ℝ} {f : ForceField} {T : ℝ} {u : VelocityEvolution}
    {p q : PressureEvolution}
    (hpS : SmoothPressureBefore T p) (hqS : SmoothPressureBefore T q)
    (hp : SatisfiesNavierStokesBefore ν f T u p)
    (hq : SatisfiesNavierStokesBefore ν f T u q)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrtop : r ≠ (⊤ : ℝ≥0∞))
    (hpL : MemLp (fun x : Space => p t x) r volume)
    (hqL : MemLp (fun x : Space => q t x) r volume) :
    ∀ x : Space, p t x = q t x := by
  obtain ⟨c, hc⟩ := pressure_sub_const_of_sameVelocity hpS hqS hp hq ht0 htT
  have hconst : MemLp (fun _ : Space => c) r volume := by
    have hsub : MemLp ((fun x : Space => p t x) - fun x : Space => q t x)
        r volume := hpL.sub hqL
    have hfun : ((fun x : Space => p t x) - fun x : Space => q t x)
        = fun _ : Space => c := by
      funext x
      simp only [Pi.sub_apply]
      linarith [hc x]
    rwa [hfun] at hsub
  have hc0 : c = 0 := by
    by_contra hne
    exact not_memLp_const hr0 hrtop hne hconst
  intro x
  rw [hc x, hc0, add_zero]


/-! ### The Caccioppoli pressure slot is itself gauge invariant -/

/-- **The cutoff flux of a divergence-free field vanishes.**  For a compactly
supported smooth cutoff `χ` and a divergence-free smooth field `w`,

  `∫ χ (∇χ · w) = 0`.

Proof: the transport integration by parts `integral_cutoff_transport_ibp` with
cutoff `χ²` and the *constant* scalar field `1` has zero left-hand side, so the
right-hand side `∫ ∇(χ²)·w = 2 ∫ χ (∇χ·w)` vanishes. -/
theorem integral_cutoff_flux_eq_zero {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    {w : VelocityField} (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ x, staticDivergence w x = 0) :
    ∫ x : Space, χ x * fderiv ℝ χ x (w x) = 0 := by
  have h := Navier.Analysis.CutoffIntegrationByParts.integral_cutoff_transport_ibp
    (χ := χ ^ 2) (F := fun _ : Space => (1 : ℝ)) (w := w)
    (Navier.Analysis.CutoffEnergyIbp.contDiff_sq hχ)
    (Navier.Analysis.CutoffEnergyIbp.hasCompactSupport_sq hχsupp)
    contDiff_const hw hdiv
  have hL : (∫ x : Space, (χ ^ 2) x *
      fderiv ℝ (fun _ : Space => (1 : ℝ)) x (w x)) = 0 := by
    simp
  have hR : (∫ x : Space, fderiv ℝ (χ ^ 2) x (w x) * (fun _ : Space => (1 : ℝ)) x)
      = 2 * ∫ x : Space, χ x * fderiv ℝ χ x (w x) := by
    have hpt : ∀ x : Space,
        fderiv ℝ (χ ^ 2) x (w x) * (fun _ : Space => (1 : ℝ)) x
          = 2 * (χ x * fderiv ℝ χ x (w x)) := by
      intro x
      rw [Navier.Analysis.CutoffEnergyIbp.fderiv_sq_apply hχ x (w x)]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  rw [hL, hR] at h
  linarith

/-- Continuity of the cutoff flux density `x ↦ χ x (∇χ(x) · w x)`. -/
theorem continuous_cutoffFlux {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {w : VelocityField} (hw : ContDiff ℝ ∞ w) :
    Continuous fun x : Space => χ x * fderiv ℝ χ x (w x) :=
  hχ.continuous.mul
    ((hχ.continuous_fderiv (by simp)).clm_apply hw.continuous)

/-- Compact support of the cutoff flux density. -/
theorem hasCompactSupport_cutoffFlux {χ : Space → ℝ}
    (hχsupp : HasCompactSupport χ) {w : VelocityField} :
    HasCompactSupport fun x : Space => χ x * fderiv ℝ χ x (w x) :=
  HasCompactSupport.mul_right (f' := fun x : Space => fderiv ℝ χ x (w x)) hχsupp

/-- **Gauge invariance of the Caccioppoli pressure slot.**  The derivative-free
pressure term produced by `CutoffEnergyIbp.cutoffEnergy_pressure_ibp` is
`2 ∫ p · χ (∇χ · u)`, and it is *unchanged* by the pressure gauge shift
`p ↦ p + c`, because the cutoff flux of the divergence-free velocity vanishes.

This is what makes the remaining blocker-(b) residual well posed despite
`not_forall_memLp_pressure`: the Caccioppoli inequality may be proved for any
normalization of the pressure, and by `pressure_eq_of_memLp` the `L^r`
normalization is the unique one. -/
theorem cutoffPressure_add_const {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    {w : VelocityField} (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ x, staticDivergence w x = 0)
    {P : Space → ℝ} (hP : Continuous P) (c : ℝ) :
    (∫ x : Space, (P x + c) * (χ x * fderiv ℝ χ x (w x)))
      = ∫ x : Space, P x * (χ x * fderiv ℝ χ x (w x)) := by
  have hgc : Continuous fun x : Space => χ x * fderiv ℝ χ x (w x) :=
    continuous_cutoffFlux hχ hw
  have hgs : HasCompactSupport fun x : Space => χ x * fderiv ℝ χ x (w x) :=
    hasCompactSupport_cutoffFlux hχsupp
  have hg : Integrable (fun x : Space => χ x * fderiv ℝ χ x (w x)) volume :=
    hgc.integrable_of_hasCompactSupport hgs
  have hPg : Integrable
      (fun x : Space => P x * (χ x * fderiv ℝ χ x (w x))) volume :=
    (hP.mul hgc).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (f := P) hgs)
  have hcg : Integrable
      (fun x : Space => c * (χ x * fderiv ℝ χ x (w x))) volume := hg.const_mul c
  have hpt : ∀ x : Space, (P x + c) * (χ x * fderiv ℝ χ x (w x))
      = P x * (χ x * fderiv ℝ χ x (w x))
        + c * (χ x * fderiv ℝ χ x (w x)) := fun x => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add hPg hcg, integral_const_mul,
    integral_cutoff_flux_eq_zero hχ hχsupp hw hdiv, mul_zero, add_zero]


/-! ### An explicit inhabitant: the rest state, and unconditional no-go -/

/-- **The rest state is a partial classical solution.**  Velocity and pressure
identically zero, zero force, zero initial datum.  Every clause is a derivative
of a constant.  This is the inhabitant that makes the `L^r` no-go below
unconditional, and it doubles as the non-vacuity witness for
`memLp_pressureGradient_of_terms`. -/
def zeroSolution (ν : ℝ) {T : ℝ} (hT : 0 < T) :
    PartialClassicalSolution ν zeroForce (fun _ : Space => (0 : Space)) T where
  terminalTime_pos := hT
  velocity := fun _ _ => 0
  pressure := fun _ _ => 0
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  initial_condition := rfl
  incompressible := by
    intro t _ _ x
    simp [divergence, spatialDerivative]
  equation := by
    intro t _ _ x
    have hp : pressureGradient (fun _ : ℝ => fun _ : Space => (0 : ℝ)) t x
        = 0 := by
      funext i
      simp [pressureGradient]
    simp [timeDerivative, convection, spatialDerivative, Navier.laplacian, hp,
      zeroForce]

@[simp] theorem zeroSolution_velocity (ν : ℝ) {T : ℝ} (hT : 0 < T) :
    (zeroSolution ν hT).velocity = fun _ _ => 0 := rfl

@[simp] theorem zeroSolution_pressure (ν : ℝ) {T : ℝ} (hT : 0 < T) :
    (zeroSolution ν hT).pressure = fun _ _ => 0 := rfl

/-- **Unconditional `L^r` no-go.**  Dropping the "as soon as one solution
exists" caveat of `not_forall_memLp_pressure`: for every viscosity, every
positive terminal time, every admissible time and every `0 < r < ∞`, the
statement "every partial classical solution with zero force and zero initial
datum has an `L^r` pressure slice" is false.  The two witnesses are
`zeroSolution` and its gauge shift by `1`. -/
theorem not_forall_memLp_pressure_zeroDatum
    (ν : ℝ) {T : ℝ} (hT : 0 < T) (t : ℝ)
    {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrtop : r ≠ (⊤ : ℝ≥0∞)) :
    ¬ ∀ sol : PartialClassicalSolution ν zeroForce (fun _ : Space => (0 : Space)) T,
        MemLp (fun x : Space => sol.pressure t x) r volume :=
  not_forall_memLp_pressure (zeroSolution ν hT) t hr0 hrtop

/-- **Non-vacuity of the `∇p` transport hypotheses.**  The four `MemLp`
premises of `memLp_pressureGradient_of_terms` are jointly satisfiable: the rest
state satisfies all four for every exponent, and the conclusion holds for it.
This rules out the unsatisfiable pole for that theorem's hypothesis bundle. -/
theorem memLp_pressureGradient_of_terms_nonvacuous
    (ν : ℝ) {T : ℝ} (hT : 0 < T) (t : ℝ) (r : ℝ≥0∞) :
    MemLp (fun x : Space =>
      Navier.laplacian (zeroSolution ν hT).velocity t x) r volume ∧
    MemLp (fun x : Space => zeroForce t x) r volume ∧
    MemLp (fun x : Space =>
      timeDerivative (zeroSolution ν hT).velocity t x) r volume ∧
    MemLp (fun x : Space =>
      convection (zeroSolution ν hT).velocity t x) r volume ∧
    MemLp (fun x : Space =>
      pressureGradient (zeroSolution ν hT).pressure t x) r volume := by
  have hlap : (fun x : Space =>
      Navier.laplacian (zeroSolution ν hT).velocity t x)
      = fun _ : Space => (0 : Space) := by
    funext x
    simp [Navier.laplacian]
  have hforce : (fun x : Space => zeroForce t x)
      = fun _ : Space => (0 : Space) := rfl
  have htime : (fun x : Space =>
      timeDerivative (zeroSolution ν hT).velocity t x)
      = fun _ : Space => (0 : Space) := by
    funext x
    simp [timeDerivative]
  have hconv : (fun x : Space =>
      convection (zeroSolution ν hT).velocity t x)
      = fun _ : Space => (0 : Space) := by
    funext x
    simp [convection, spatialDerivative]
  have hgrad : (fun x : Space =>
      pressureGradient (zeroSolution ν hT).pressure t x)
      = fun _ : Space => (0 : Space) := by
    funext x
    funext i
    simp [pressureGradient]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hlap]; exact MemLp.zero'
  · rw [hforce]; exact MemLp.zero'
  · rw [htime]; exact MemLp.zero'
  · rw [hconv]; exact MemLp.zero'
  · rw [hgrad]; exact MemLp.zero'

end Navier.Analysis.PressureNormalization
