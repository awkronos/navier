import Navier.Analysis.Enstrophy

/-!
# Leray–Hopf weak solutions (rung 4 skeleton tower)

Leray (1934) proved global existence of weak solutions: divergence-free
`L²` velocity fields satisfying the Navier–Stokes equations against
divergence-free test functions, with non-increasing kinetic energy.  This file
lays the weak layer over the repository's own objects (`SchwartzVelocity`
slices, the `officialInner` pairing, the repo's Fréchet operators), so the
Galerkin/compactness tower has a home with no floating restatement.

## Encoding decisions (Step-0e checked)

* Test functions are **Schwartz-sliced, divergence-free, compact-in-time**
  (`DivergenceFreeTestFunction`).  Quantifying over this subclass of the
  classical test class makes the existence statement weaker-or-equal to
  Leray's — hence still TRUE — while staying expressible with the repo's
  Fréchet operators.  Pressure is eliminated by divergence-free tests, as
  usual.
* The weak form keeps explicit `x`-integrability fields; for a Leray solution
  (`u ∈ L^∞_t L²_x`) each pairing is integrable, so the fields are honest
  rather than restrictive.
* **Anti-vacuity**: `zeroTestFunction` inhabits the test class (so
  `weak_form` quantifies over a nonempty type), and `zero_isLerayHopfWeak`
  shows the zero solution realizes the structure for zero data.  That the
  test class contains a NONZERO member — without which `weak_form` would be
  trivially satisfiable and existence vacuous — is the point of the
  `exists_nonzero_testFunction` skeleton (curl-of-bump construction).

## Certified here (no sorry)

* `DivergenceFreeTestFunction` + `zeroTestFunction` (inhabitant).
* `officialInner_zero_left` and the zero-solution smoke
  `zero_isLerayHopfWeak` — the structure is realizable, hence non-degenerate.

## Skeletons (honest `sorry`)

* `exists_nonzero_testFunction` — a nonzero divergence-free Schwartz test
  [curl of a scalar bump `(∂₂ψ, −∂₁ψ, 0)` + smooth time envelope;
  est ~120 LOC].
* `leray_weak_existence` — global existence of a Leray–Hopf weak solution for
  every `ν > 0` and divergence-free Schwartz datum
  [Leray, Acta Math. 63 (1934); Temam, *NSE* Ch. III (Galerkin + compactness
  + energy inequality); est ~1500 LOC].
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral

namespace Navier.Analysis.LerayWeak

open scoped ContDiff

open Navier
open Navier.Analysis.Enstrophy
open Navier.Analysis.OfficialABEncoding

/-!
## Test functions
-/

/-- A divergence-free, Schwartz-sliced, compact-in-time test function on
nonnegative spacetime. -/
structure DivergenceFreeTestFunction where
  /-- The Schwartz slice at each time. -/
  field : ℝ → SchwartzVelocity
  /-- Joint spacetime smoothness on the nonnegative-time half-space, in the
  repo's within-derivative convention. -/
  smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × Space => (field z.1) z.2)
    ((Set.Ici (0:ℝ)) ×ˢ (Set.univ : Set Space))
  /-- The test function vanishes beyond a finite horizon. -/
  compact_time : ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → field t = 0
  /-- Every slice is divergence-free. -/
  divergence_free : ∀ t : ℝ, DivergenceFreeInitial (field t)

/-- The zero test function (inhabitant of the test class). -/
def zeroTestFunction : DivergenceFreeTestFunction where
  field := fun _ => 0
  smooth := by
    have : (fun z : ℝ × Space => ((0 : SchwartzVelocity)) z.2) =
        fun _ : ℝ × Space => (0 : Space) := by
      funext z; simp
    simpa [this] using contDiffOn_const
  compact_time := ⟨1, one_pos, fun _ _ => rfl⟩
  divergence_free := by
    intro t x
    simp [staticDivergence]

instance : Inhabited DivergenceFreeTestFunction := ⟨zeroTestFunction⟩

/-- **[SKELETON — nonzero test function; curl-of-bump construction
`φ = (∂₂ψ, −∂₁ψ, 0)` for a scalar Schwartz bump `ψ`, divergence-free by
Clairaut, with a smooth compactly-supported time envelope; est ~120 LOC.]**
The test class contains a member with a nonzero slice.  This is the
anti-vacuity guarantee for `weak_form`: with only the zero test the weak
formulation would be trivially satisfiable and `leray_weak_existence`
vacuous. -/
theorem exists_nonzero_testFunction :
    ∃ φ : DivergenceFreeTestFunction, ∃ t : ℝ, 0 ≤ t ∧ φ.field t ≠ 0 := by
  sorry

/-!
## The Leray–Hopf weak solution concept
-/

/-- A Leray–Hopf weak solution with datum `u₀`: square-integrable slices,
exact initial attainment (representative choice), non-increasing kinetic
energy, and the weak-form identity against every divergence-free
Schwartz-sliced test function

  `∫_{t≥0} ∫ₓ ⟨u, ∂ₜφ + (u·∇)φ + νΔφ⟩ = −∫ₓ ⟨u₀, φ(0)⟩`

(pressure eliminated by divergence-free tests; the sign convention is the
standard integration by parts from `∂ₜu + (u·∇)u = νΔu − ∇p`).  The full
Leray energy *inequality* with the dissipation term and the `L²`-continuity
at `t = 0` are strictly stronger clauses that belong to the weak-derivative
layer; they are named residuals of the existence skeleton, not hidden. -/
structure IsLerayHopfWeakSolution
    (ν : ℝ) (u₀ : SchwartzVelocity) (u : VelocityEvolution) : Prop where
  square_integrable :
    ∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)
  initial_attained : ∀ x : Space, u 0 x = u₀ x
  energy_nonincreasing :
    ∀ t : ℝ, 0 ≤ t → kineticEnergy u t ≤ kineticEnergy u 0
  pairing_integrable :
    ∀ φ : DivergenceFreeTestFunction, ∀ t : ℝ, 0 ≤ t →
      Integrable (fun x : Space =>
        officialInner (u t x)
          (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
            spatialDerivative (fun s => (φ.field s : Space → Space)) t x
              (u t x) +
            ν • laplacian (fun s => (φ.field s : Space → Space)) t x))
  weak_form :
    ∀ φ : DivergenceFreeTestFunction,
      (∫ t in Set.Ici (0:ℝ), ∫ x : Space,
        officialInner (u t x)
          (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
            spatialDerivative (fun s => (φ.field s : Space → Space)) t x
              (u t x) +
            ν • laplacian (fun s => (φ.field s : Space → Space)) t x)) =
      -(∫ x : Space, officialInner (u₀ x) ((φ.field 0) x))

/-!
## Non-degeneracy smoke: the zero solution realizes the structure
-/

theorem officialInner_zero_left (y : Space) : officialInner 0 y = 0 := by
  simp [officialInner, officialEuclideanPoint]

/-- The zero velocity is a Leray–Hopf weak solution for the zero datum: the
structure is realizable (Step-0e non-vacuity anchor for the layer). -/
theorem zero_isLerayHopfWeak (ν : ℝ) :
    IsLerayHopfWeakSolution ν (0 : SchwartzVelocity) (fun _ _ => 0) where
  square_integrable := by
    intro t _
    refine (integrable_zero Space ℝ volume).congr ?_
    exact Filter.Eventually.of_forall fun x => by simp
  initial_attained := by intro x; simp
  energy_nonincreasing := by intro t _; simp [kineticEnergy]
  pairing_integrable := by
    intro φ t _
    refine (integrable_zero Space ℝ volume).congr ?_
    exact Filter.Eventually.of_forall fun x =>
      (officialInner_zero_left _).symm
  weak_form := by
    intro φ
    simp [officialInner_zero_left]

/-!
## Existence skeleton
-/

/-- **[SKELETON — Leray weak existence; Leray, Acta Math. 63 (1934); Temam,
*Navier–Stokes Equations* Ch. III; est ~1500 LOC.]**  For every viscosity
`ν > 0` and every divergence-free Schwartz datum there is a global
Leray–Hopf weak solution.

Closure route (Galerkin): finite-mode projection (the multi-frequency layer
of `MultiFrequencyMild` is the frequency-side laboratory), uniform energy
bounds from the skew-symmetry of the projected nonlinearity, Aubin–Lions
compactness to pass to the limit in the quadratic term, then the weak-form
identity against each Schwartz test.  Genuinely Mathlib-absent inputs:
Aubin–Lions, `L²`-Sobolev interpolation, weak compactness bookkeeping for
Bochner spaces. -/
theorem leray_weak_existence :
    ∀ ν : ℝ, 0 < ν →
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∃ u : VelocityEvolution, IsLerayHopfWeakSolution ν u₀ u := by
  sorry

end Navier.Analysis.LerayWeak
