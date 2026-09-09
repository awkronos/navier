import Navier.Analysis.CriticalControlDecomposition
import Navier.Analysis.WholeSpaceCutoffLimit

/-!
# Pressure-free whole-space critical evolution tests

The scalar cutoff identity in `WholeSpaceDuhamel` is exact, but each coordinate
retains a pressure pairing.  This module sums those identities against one
compactly supported divergence-free vector test.  The three pressure pairings
then cancel *before* any cutoff or far-field limit.

The resulting theorem is stated directly for
`CriticalControlDecomposition.SolvesBefore`, the local trajectory carried by
the continuation construction for `WholeSpaceGlobalRegularity`.  It is the
native weak Leray evolution identity on `R^3`: no lattice carrier, periodic
identification, pressure integrability at infinity, or global critical bound
is used.

This is a local Duhamel primitive, not a global-regularity proof.  Passing from
compact solenoidal tests to the noncompact backward heat--Leray test still
requires a divergence-preserving approximation with uniform derivative
control.  The theorem below removes the pressure tail from that remaining
limit problem.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff Interval BigOperators
open MeasureTheory Set

namespace Navier.Analysis.WholeSpaceCriticalEvolution

open Navier
open Navier.Breakdown
open Navier.Analysis.ParabolicCaccioppoli
open Navier.Analysis.CutoffIntegrationByParts
open Navier.Analysis.EnstrophyPointwise
open Navier.Analysis.WholeSpaceDuhamel
open Navier.Analysis.WholeSpaceCutoffLimit
open Navier.Analysis.CriticalControlDecomposition

/-- A compact vector test written in the coordinate form needed by the
finite-cutoff integration-by-parts API. -/
structure CompactSolenoidalTest where
  field : Space → Space
  smooth : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x => field x j)
  compact : ∀ j : Fin 3, HasCompactSupport (fun x => field x j)
  divergence_free : ∀ x : Space,
    ∑ j : Fin 3, fderiv ℝ (fun y => field y j) x (basisVector j) = 0

/-- A native smooth compact vector field with `staticDivergence = 0` produces
the coordinate test carrier used below.  This bridge keeps the hypothesis on
the repository's actual `R^3` divergence operator. -/
def CompactSolenoidalTest.ofNative
    (field : Space → Space) (hsmooth : ContDiff ℝ ∞ field)
    (hcompact : HasCompactSupport field)
    (hdiv : ∀ x : Space, staticDivergence field x = 0) :
    CompactSolenoidalTest where
  field := field
  smooth := fun j =>
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 3 => ℝ) j).contDiff.comp hsmooth
  compact := fun j =>
    hcompact.comp_left (g := fun v : Space => v j) (by simp)
  divergence_free := by
    intro x
    have hdiff : DifferentiableAt ℝ field x :=
      (hsmooth.differentiable (by norm_num)).differentiableAt
    rw [← hdiv x]
    unfold staticDivergence
    apply Finset.sum_congr rfl
    intro j _
    exact fderiv_component_apply field x (basisVector j) hdiff j

/-- Momentum paired with a compact solenoidal vector test. -/
def testedMomentum
    (φ : CompactSolenoidalTest) (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∑ j : Fin 3, cutoffMomentumCoordinate (fun x => φ.field x j) u j t

/-- The pressure-free transport and viscous right-hand side of the weak
Leray evolution equation. -/
def lerayWeakRhs
    (ν : ℝ) (φ : CompactSolenoidalTest) (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∑ j : Fin 3, (
    (∫ x : Space,
      fderiv ℝ (fun y => φ.field y j) x (u t x) * u t x j) +
    ν * (∫ x : Space, (∑ i : Fin 3,
      fderiv ℝ
        (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
        (basisVector i)) * u t x j))

/-- The sum of the three compact pressure pairings vanishes exactly for a
solenoidal vector test.  Compact support is used coordinatewise, so this
requires no normalization or tail condition on pressure. -/
theorem pressurePairing_sum_eq_zero
    (φ : CompactSolenoidalTest) (p : PressureField) (hp : ContDiff ℝ ∞ p) :
    ∑ j : Fin 3, (∫ x : Space,
      fderiv ℝ (fun y => φ.field y j) x (basisVector j) * p x) = 0 := by
  have hint : ∀ j : Fin 3, Integrable (fun x : Space =>
      fderiv ℝ (fun y => φ.field y j) x (basisVector j) * p x) := by
    intro j
    exact ((contDiff_fderiv_apply (φ.smooth j) (basisVector j)).continuous.mul
      hp.continuous).integrable_of_hasCompactSupport
        ((hasCompactSupport_fderiv_apply (φ.compact j) (basisVector j)).mul_right)
  rw [← integral_finsetSum Finset.univ (fun j _ => hint j)]
  have hzero : (fun x : Space => ∑ j : Fin 3,
      fderiv ℝ (fun y => φ.field y j) x (basisVector j) * p x) =
      (fun _ : Space => 0) := by
    funext x
    rw [← Finset.sum_mul, φ.divergence_free x, zero_mul]
  rw [hzero, integral_zero]

/-- **Pressure-free, time-integrated weak Leray evolution on `R^3`.**

For every compact smooth divergence-free vector test `φ` and every closed
interior interval `[a,b] ⊂ (0,T)`, a native partial classical solution obeys

`<u(b),φ> - <u(a),φ> = ∫_a^b [B(u,u;φ) + ν L(u;φ)] dt`.

The proof consumes the already checked coordinate Duhamel identity in each
component and cancels the pressure sum pointwise through `div φ = 0`. -/
theorem partialSolution_lerayWeakEvolution_timeIntegrated
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (φ : CompactSolenoidalTest)
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    testedMomentum φ sol.velocity b - testedMomentum φ sol.velocity a =
      ∫ t in a..b, lerayWeakRhs ν φ sol.velocity t := by
  have hcoord : ∀ j : Fin 3,
      cutoffMomentumCoordinate (fun x => φ.field x j) sol.velocity j b -
          cutoffMomentumCoordinate (fun x => φ.field x j) sol.velocity j a =
        ∫ t in a..b,
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j) +
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (basisVector j) *
              sol.pressure t x) := by
    intro j
    exact cutoffMomentumCoordinate_timeIntegrated sol (φ.smooth j)
      (φ.compact j) ha0 hab hbT j
  have hpSmooth : ∀ t ∈ Set.Icc a b, ContDiff ℝ ∞ (sol.pressure t) := by
    intro t ht
    exact pressure_slice_contDiff sol (ha0.le.trans ht.1) (ht.2.trans_lt hbT)
  have hfullContinuous : ∀ j : Fin 3, ContinuousOn (fun t : ℝ =>
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j) +
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (basisVector j) *
              sol.pressure t x)) (Set.Icc a b) := by
    intro j
    have hleft := cutoffTimeDerivative_continuousOn sol (φ.smooth j)
      (φ.compact j) ha0 hbT j
    refine hleft.congr ?_
    intro t ht
    exact (cutoff_testedMomentum_coordinate sol (φ.smooth j) (φ.compact j)
      (ha0.le.trans ht.1) (ht.2.trans_lt hbT) j).symm
  have hfullIntegrable : ∀ j : Fin 3, IntervalIntegrable (fun t : ℝ =>
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j) +
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (basisVector j) *
              sol.pressure t x)) volume a b := by
    intro j
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hfullContinuous j
  calc
    testedMomentum φ sol.velocity b - testedMomentum φ sol.velocity a =
        ∑ j : Fin 3,
          (cutoffMomentumCoordinate (fun x => φ.field x j) sol.velocity j b -
            cutoffMomentumCoordinate (fun x => φ.field x j) sol.velocity j a) := by
      simp only [testedMomentum, Finset.sum_sub_distrib]
    _ = ∑ j : Fin 3, ∫ t in a..b,
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j) +
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (basisVector j) *
              sol.pressure t x) := Finset.sum_congr rfl (fun j _ => hcoord j)
    _ = ∫ t in a..b, ∑ j : Fin 3,
          ((∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j) +
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (basisVector j) *
              sol.pressure t x)) := by
      symm
      simpa using (intervalIntegral.integral_finsetSum
        (μ := volume) (a := a) (b := b)
        (s := Finset.univ)
        (f := fun j t =>
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j) +
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (basisVector j) *
              sol.pressure t x))
        (fun j _ => hfullIntegrable j))
    _ = ∫ t in a..b, lerayWeakRhs ν φ sol.velocity t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using ht
      dsimp only
      let A : Fin 3 → ℝ := fun j =>
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j)
      let P : Fin 3 → ℝ := fun j =>
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (basisVector j) *
              sol.pressure t x)
      change (∑ j : Fin 3, (A j + P j)) = (∑ j : Fin 3, A j)
      rw [Finset.sum_add_distrib,
        show (∑ j : Fin 3, P j) = 0 from
          pressurePairing_sum_eq_zero φ (sol.pressure t) (hpSmooth t ht'),
        add_zero]

/-- The same pressure-free evolution theorem on the exact local/continuation
carrier used by `wholeSpaceGlobalRegularity_of_local_continuation_apriori`.
Only the classical fields of `SolvesBefore` are needed for this local identity;
its finite-energy fields remain available to later heat-kernel limit bounds. -/
theorem solvesBefore_lerayWeakEvolution_timeIntegrated
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    (φ : CompactSolenoidalTest)
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    testedMomentum φ u b - testedMomentum φ u a =
      ∫ t in a..b, lerayWeakRhs ν φ u t := by
  let sol : PartialClassicalSolution ν zeroForce (u 0) T :=
    { terminalTime_pos := hT
      velocity := u
      pressure := p
      velocity_smooth := hsol.classical.1
      pressure_smooth := hsol.classical.2.1
      initial_condition := rfl
      incompressible := hsol.classical.2.2.1
      equation := hsol.classical.2.2.2 }
  exact partialSolution_lerayWeakEvolution_timeIntegrated sol φ ha0 hab hbT

end Navier.Analysis.WholeSpaceCriticalEvolution
