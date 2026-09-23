import Navier.Analysis.WienerRestartLeaf
import Navier.Analysis.AprioriCriticalControlQuantifiers

/-!
# The consumed `‖∇u‖∞` log bound (interface for the Littlewood–Paley lane)

`GradSupLogHyp` is the exact statement the damped `H³` estimate (primitive 5) consumes.
It is a STATIC inequality, applied at every time slice of a Wiener piece (those slices are
represented, `WienerRestartLeaf.piece_at`).  It is NOT proved here: its proof is the
Littlewood–Paley lane (`Navier/Analysis/LittlewoodPaleyBlock.lean`, primary orchestrator).
It is a travelling premise of every result that consumes it.

For a velocity field `v` represented by a bounded transverse profile `a`
(`WienerRestartLeaf.Rep v a`, i.e. `v x k = -(2π)⁻¹ Re 𝓕⁻(aₖ)(x)`), every real `y ≥ 0`
bounding the vorticity `staticCurl v` pointwise (in `officialEuclideanNorm`), and every
point and coordinate pair:

`|∂ⱼ vᵢ(x)| ≤ C y (1 + log(1 + Y/y) + log(1 + E/y))`,

`Y = (∫ ‖ξ‖⁶ ∑ᵢ |aᵢ(ξ)|²)^{1/2}` (Fourier `Ḣ³` of the profile),
`E = (∫ ∑ᵢ |aᵢ(ξ)|²)^{1/2}` (Fourier `L²` of the profile; by Plancherel
`E² = 4π² · kineticEnergy`), with one universal constant `C`.

Conventions: at `y = 0` Lean's `Y/0 = 0` makes the right side `0`; the statement then
asserts `∇v = 0` for a curl-free represented field, which is true (a transverse,
curl-free `L²` profile vanishes a.e.).  Both integrals are finite for represented fields
(bounded profile with every moment), so the Bochner-integral `0` convention for
non-integrable functions is never used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.WienerGradLog

open Navier Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerRestartLeaf

/-- Fourier `Ḣ³` norm of a profile, `(∫ ‖ξ‖⁶ ∑ᵢ |aᵢ|²)^{1/2}`. -/
def profH3 (a : ES → ComplexSpace) : ℝ :=
  Real.sqrt (∫ ξ, ‖ξ‖ ^ 6 * ∑ i : Fin 3, ‖a ξ i‖ ^ 2)

/-- Fourier `L²` norm of a profile, `(∫ ∑ᵢ |aᵢ|²)^{1/2}`. -/
def profL2 (a : ES → ComplexSpace) : ℝ :=
  Real.sqrt (∫ ξ, ∑ i : Fin 3, ‖a ξ i‖ ^ 2)

/-- **The consumed log bound on `‖∇u‖∞` (named premise).** -/
def GradSupLogHyp : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (v : VelocityField) (a : ES → ComplexSpace), Rep v a →
      ∀ y : ℝ, 0 ≤ y →
        (∀ x : Space, Navier.Analysis.OfficialABEncoding.officialEuclideanNorm
          (Navier.Analysis.Vorticity.staticCurl v x) ≤ y) →
        ∀ (x : Space) (i j : Fin 3),
          |fderiv ℝ v x (basisVector j) i| ≤
            C * y * (1 + Real.log (1 + profH3 a / y) + Real.log (1 + profL2 a / y))

end Navier.Analysis.WienerGradLog

set_option pp.fullNames true in
#check @Navier.Analysis.WienerGradLog.GradSupLogHyp
set_option pp.fullNames true in
#print Navier.Analysis.WienerGradLog.GradSupLogHyp
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerGradLog.GradSupLogHyp
