import Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit

/-!
# Interval limit for the compact solenoidal heat evolution

The fixed-time spatial cutoff limits do not alone justify interchanging the
radius limit with the time integral.  The exact weak evolution supplies a
stronger fact that needs no such interchange: each compact-test time integral
is the difference of its two endpoint momentum pairings.  The already proved
Gaussian endpoint domination therefore gives the limit of the actual
interval integrals.

The identification of this endpoint difference with the interval integral of
`backwardHeatCurlRhs` — formerly the time-uniformity obligation recorded here —
is closed in `WholeSpaceSolenoidalHeatRhsIntervalIdentification`
(`SolvesBefore.intervalIntegral_backwardHeatCurlRhs_eq_momentumDiff`, via the
constant-majorant dominated convergence
`SolvesBefore.tendsto_intervalIntegral_atTopCompactBackwardHeatCurlTest_lerayWeakRhs`
and Hausdorff uniqueness against the limit below).  No time-uniform
continuity of the solution is required; the `energy_le_initial` field supplies
the constant majorant.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped Interval
open MeasureTheory Filter

namespace Navier.Analysis.WholeSpaceSolenoidalHeatIntegratedRhsLimit

open Navier
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.WholeSpaceCriticalEvolution
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit

/-- **The exact compact weak-evolution integrals have a cutoff-free limit.**
For every interior time interval, the limit follows from the original weak
evolution identity and the concrete Gaussian endpoint bounds.  This does not
assert an unproved interchange with the integral of the pointwise RHS limit.
-/
theorem SolvesBefore.tendsto_integral_compactBackwardHeatCurlTest_lerayWeakRhs
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {ta tb : ℝ} (hta0 : 0 < ta) (htab : ta ≤ tb) (htbT : tb < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    Tendsto (fun R : ℝ => ∫ s in ta..tb,
      lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s)
      atTop (nhds
        (backwardHeatCurlMomentum κ τ x₀ a u tb -
          backwardHeatCurlMomentum κ τ x₀ a u ta)) := by
  have hmoment :=
    SolvesBefore.tendsto_compactBackwardHeatCurlTest_testedMomentum_sub
      hsol hta0.le (htab.trans_lt htbT)
        (hta0.le.trans htab) htbT hκ hτ x₀ a
  apply hmoment.congr'
  filter_upwards with R
  exact solvesBefore_compactBackwardHeatCurlEvolution hT hsol
    (R := max 1 R) (lt_of_lt_of_le zero_lt_one (le_max_left 1 R))
    κ τ x₀ a hta0 htab htbT

end Navier.Analysis.WholeSpaceSolenoidalHeatIntegratedRhsLimit

#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatIntegratedRhsLimit.SolvesBefore.tendsto_integral_compactBackwardHeatCurlTest_lerayWeakRhs
