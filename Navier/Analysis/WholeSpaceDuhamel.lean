import Navier.Analysis.CutoffIntegrationByParts
import Navier.Analysis.ParabolicCaccioppoli
import Navier.Analysis.HeatSemigroupSmoothing
import Navier.Analysis.PressureNormalization

/-!
# Whole-space Duhamel: the finite-cutoff momentum identity

This file supplies the first pointwise-classical-solution leaf on the route to
the whole-space Duhamel formula used by
`ConditionalRegularity.prodiSerrin_layer_farField_bounded`.

The available `PartialClassicalSolution` record carries smoothness only on
compact subsets of `[0,T) × ℝ³`; it does not carry spatial decay of velocity,
its derivatives, or pressure.  Consequently the honest Gaussian cannot be
inserted directly into the estate's compact-support integration-by-parts
lemmas:

* `heatKernel_translate_not_hasCompactSupport` proves that every positive-time
  Gaussian translate has support all of `ℝ³`.
* `cutoff_testedMomentum_coordinate` proves the exact finite-cutoff momentum
  identity.  Convection, viscosity, and pressure derivatives are all moved
  onto a smooth compactly supported test `χ`, using only the fields of the
  actual solution record.
* `cutoff_pressurePairing_add_const` proves that the resulting pressure term is
  gauge invariant.  In contrast,
  `PressureNormalization.exists_shift_pressure_not_memLp` proves that a raw
  pressure `L^r` input cannot be obtained uniformly from the same record.

Thus the remaining transport to the Gaussian is explicit: approximate its
translate by compactly supported tests and justify the cutoff limit.  The
present hypotheses do not provide the derivative/pressure tail domination
needed for that limit, so this file does not assume it.

Pattern classification: `representationTransport`; status of these leaves:
`kernelClosed`; consumer status remains `scientificFrontier`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff
open MeasureTheory Set

namespace Navier.Analysis.WholeSpaceDuhamel

open Navier
open Navier.Breakdown
open Navier.Analysis.ParabolicCaccioppoli
open Navier.Analysis.CutoffIntegrationByParts
open Navier.Analysis.EnstrophyPointwise
open Navier.Analysis.HeatSemigroupSmoothing

/-- **The positive-time Gaussian is not a compactly supported test.**  Its
support is all of `ℝ³`, since it is strictly positive at every point.  If that
support were compact, Lebesgue measure of the whole space would be finite,
contradicting translation invariance.

This is the checked obstruction to applying `integral_cutoff_*_ibp` directly
with `χ(y) = G^ν_τ(x-y)`: a cutoff approximation and a justified limit are
mathematically necessary. -/
theorem heatKernel_translate_not_hasCompactSupport
    {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (x : Space) :
    ¬ HasCompactSupport (fun y : Space => heatKernel ν τ (x - y)) := by
  intro hcompact
  have hsupp : Function.support (fun y : Space => heatKernel ν τ (x - y)) = Set.univ := by
    ext y
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (heatKernel_pos hν hτ (x - y)).ne'
  have htop : IsCompact (Set.univ : Set Space) := by
    rw [← closure_univ, ← hsupp]
    exact hcompact
  have hfinite : volume (Set.univ : Set Space) ≠ ⊤ := htop.measure_ne_top
  exact hfinite (measure_univ_of_isAddLeftInvariant (volume : Measure Space))

/-- **The derivative-test pressure pairing is gauge invariant.**  Adding a
spatial constant `c` to the pressure contributes
`c ∫ ∂ⱼχ = 0`, with the last equality itself obtained from compact-support
integration by parts against the constant function `1`.

This is the pressure shape retained by `cutoff_testedMomentum_coordinate`.
It avoids the false raw-pressure route certified by
`PressureNormalization.exists_shift_pressure_not_memLp`. -/
theorem cutoff_pressurePairing_add_const
    {χ p : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    (hp : Continuous p) (j : Fin 3) (c : ℝ) :
    (∫ x : Space, fderiv ℝ χ x (basisVector j) * (p x + c)) =
      ∫ x : Space, fderiv ℝ χ x (basisVector j) * p x := by
  have hdχ : Continuous (fun x : Space => fderiv ℝ χ x (basisVector j)) :=
    (contDiff_fderiv_apply hχ (basisVector j)).continuous
  have hdχsupp : HasCompactSupport (fun x : Space => fderiv ℝ χ x (basisVector j)) :=
    hasCompactSupport_fderiv_apply hχsupp (basisVector j)
  have hIp : Integrable (fun x : Space => fderiv ℝ χ x (basisVector j) * p x) :=
    (hdχ.mul hp).integrable_of_hasCompactSupport hdχsupp.mul_right
  have hIc : Integrable (fun x : Space => c * fderiv ℝ χ x (basisVector j)) :=
    hdχ.integrable_of_hasCompactSupport hdχsupp |>.const_mul c
  have hzero : (∫ x : Space, fderiv ℝ χ x (basisVector j)) = 0 := by
    have h := integral_cutoff_directional_ibp hχ hχsupp
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => (1 : ℝ))) (basisVector j)
    simpa using h
  calc
    (∫ x : Space, fderiv ℝ χ x (basisVector j) * (p x + c))
        = ∫ x : Space,
            fderiv ℝ χ x (basisVector j) * p x +
              c * fderiv ℝ χ x (basisVector j) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = (∫ x : Space, fderiv ℝ χ x (basisVector j) * p x) +
          ∫ x : Space, c * fderiv ℝ χ x (basisVector j) :=
        integral_add hIp hIc
    _ = (∫ x : Space, fderiv ℝ χ x (basisVector j) * p x) +
          c * ∫ x : Space, fderiv ℝ χ x (basisVector j) := by
        rw [integral_const_mul]
    _ = ∫ x : Space, fderiv ℝ χ x (basisVector j) * p x := by rw [hzero]; ring

/-- **Finite-cutoff coordinate momentum identity for a whole-space classical
solution.**  For a smooth compactly supported scalar test `χ`, every coordinate
of the zero-force Navier--Stokes equation satisfies

`∫ χ ∂ₜuⱼ = ∫ (u·∇χ)uⱼ + ν∫ (Δχ)uⱼ + ∫ (∂ⱼχ)p`.

All integrals are over `ℝ³`.  Compact support makes every displayed slot
integrable, so no spatial decay of `u`, `Du`, or `p` is assumed.  The proof
uses incompressibility exactly once in `integral_cutoff_transport_ibp`; the
viscous and pressure terms use the corresponding Laplacian and directional
IBP leaves.  This is the strongest noncircular spatial-transport identity
currently supported by `PartialClassicalSolution` alone.

Named proof-producing consumer:
`WholeSpaceCutoffLimit.cutoffMomentumCoordinate_timeIntegrated`, which first
derives the tested momentum derivative and then integrates this identity on
closed interior time intervals.  The far-field branch is not yet a consumer:
it still needs the separate cutoff-to-Gaussian limit. -/
theorem cutoff_testedMomentum_coordinate
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) (j : Fin 3) :
    (∫ x : Space, χ x * timeDerivative sol.velocity t x j) =
      (∫ x : Space, fderiv ℝ χ x (sol.velocity t x) * sol.velocity t x j) +
      ν * (∫ x : Space, (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i)) *
          sol.velocity t x j) +
      (∫ x : Space, fderiv ℝ χ x (basisVector j) * sol.pressure t x) := by
  have huC : ContDiff ℝ ∞ (sol.velocity t) := velocity_slice_contDiff sol ht0 htT
  have hpC : ContDiff ℝ ∞ (sol.pressure t) := pressure_slice_contDiff sol ht0 htT
  let uj : Space → ℝ := fun x => sol.velocity t x j
  have hujC : ContDiff ℝ ∞ uj :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).contDiff.comp huC
  have hdiv : ∀ x, staticDivergence (sol.velocity t) x = 0 := by
    intro x
    simpa [staticDivergence, divergence, spatialDerivative] using
      sol.incompressible t ht0 htT x
  have hconv : ∀ x : Space,
      convection sol.velocity t x j = fderiv ℝ uj x (sol.velocity t x) := by
    intro x
    unfold convection spatialDerivative uj
    exact (fderiv_component_apply (sol.velocity t) x (sol.velocity t x)
      (huC.differentiable (by simp) x) j).symm
  have hlap : ∀ x : Space,
      laplacian sol.velocity t x j = ∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ uj z (basisVector i)) x (basisVector i) := by
    intro x
    unfold laplacian uj
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hDu : ContDiff ℝ ∞
        (fun y : Space => fderiv ℝ (sol.velocity t) y (basisVector i)) :=
      (huC.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const
    rw [← fderiv_component_apply
      (fun y : Space => fderiv ℝ (sol.velocity t) y (basisVector i)) x
      (basisVector i) (hDu.differentiable (by simp) x) j]
    have hinner :
        (fun z : Space => fderiv ℝ (sol.velocity t) z (basisVector i) j) =
          (fun z : Space => fderiv ℝ uj z (basisVector i)) := by
      funext z
      unfold uj
      exact (fderiv_component_apply (sol.velocity t) z (basisVector i)
        (huC.differentiable (by simp) z) j).symm
    rw [hinner]
  have hpress : ∀ x : Space,
      pressureGradient sol.pressure t x j = fderiv ℝ (sol.pressure t) x (basisVector j) :=
    fun _ => rfl
  have htransport := integral_cutoff_transport_ibp hχ hχsupp hujC huC hdiv
  have hviscous := integral_cutoff_laplacian_ibp hχ hχsupp hujC
  have hpressure := integral_cutoff_directional_ibp hχ hχsupp hpC (basisVector j)
  have hpoint : ∀ x : Space,
      χ x * timeDerivative sol.velocity t x j =
        -(χ x * fderiv ℝ uj x (sol.velocity t x)) +
        ν * (χ x * (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ uj z (basisVector i)) x (basisVector i))) -
        χ x * fderiv ℝ (sol.pressure t) x (basisVector j) := by
    intro x
    have h := congrArg (fun v : Space => v j) (sol.equation t ht0 htT x)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [hconv x, hlap x, hpress x] at h
    have hsolve : timeDerivative sol.velocity t x j =
        -fderiv ℝ uj x (sol.velocity t x) +
        ν * (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ uj z (basisVector i)) x (basisVector i)) -
        fderiv ℝ (sol.pressure t) x (basisVector j) := by
      simp [zeroForce] at h
      linarith
    rw [hsolve]
    ring
  have hItransport : Integrable (fun x : Space =>
      χ x * fderiv ℝ uj x (sol.velocity t x)) :=
    (hχ.continuous.mul
      ((hujC.continuous_fderiv (by norm_num)).clm_apply huC.continuous)
    ).integrable_of_hasCompactSupport hχsupp.mul_right
  have hIlap : Integrable (fun x : Space =>
      χ x * (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ uj z (basisVector i)) x (basisVector i))) :=
    (hχ.continuous.mul (continuous_finsetSum _ fun i _ =>
      (contDiff_fderiv_apply (contDiff_fderiv_apply hujC (basisVector i))
        (basisVector i)).continuous)).integrable_of_hasCompactSupport hχsupp.mul_right
  have hIpressure : Integrable (fun x : Space =>
      χ x * fderiv ℝ (sol.pressure t) x (basisVector j)) :=
    (hχ.continuous.mul (contDiff_fderiv_apply hpC (basisVector j)).continuous
    ).integrable_of_hasCompactSupport hχsupp.mul_right
  calc
    (∫ x : Space, χ x * timeDerivative sol.velocity t x j)
        = - (∫ x : Space, χ x * fderiv ℝ uj x (sol.velocity t x)) +
          ν * (∫ x : Space, χ x * (∑ i : Fin 3,
            fderiv ℝ (fun z => fderiv ℝ uj z (basisVector i)) x (basisVector i))) -
          (∫ x : Space, χ x * fderiv ℝ (sol.pressure t) x (basisVector j)) := by
      rw [show (fun x : Space => χ x * timeDerivative sol.velocity t x j) =
          (fun x : Space =>
            (-(χ x * fderiv ℝ uj x (sol.velocity t x)) +
              ν * (χ x * (∑ i : Fin 3,
                fderiv ℝ (fun z => fderiv ℝ uj z (basisVector i)) x (basisVector i)))) -
            χ x * fderiv ℝ (sol.pressure t) x (basisVector j)) from funext hpoint]
      have hsplit :
          (∫ x : Space,
              (-(χ x * fderiv ℝ uj x (sol.velocity t x)) +
                ν * (χ x * (∑ i : Fin 3,
                  fderiv ℝ (fun z => fderiv ℝ uj z (basisVector i)) x
                    (basisVector i)))) -
              χ x * fderiv ℝ (sol.pressure t) x (basisVector j)) =
            (∫ x : Space,
              -(χ x * fderiv ℝ uj x (sol.velocity t x)) +
                ν * (χ x * (∑ i : Fin 3,
                  fderiv ℝ (fun z => fderiv ℝ uj z (basisVector i)) x
                    (basisVector i)))) -
            (∫ x : Space, χ x * fderiv ℝ (sol.pressure t) x (basisVector j)) :=
        integral_sub (hItransport.neg.add (hIlap.const_mul ν)) hIpressure
      rw [hsplit]
      have hsum :
          (∫ x : Space,
              -(χ x * fderiv ℝ uj x (sol.velocity t x)) +
                ν * (χ x * (∑ i : Fin 3,
                  fderiv ℝ (fun z => fderiv ℝ uj z (basisVector i)) x
                    (basisVector i)))) =
            (∫ x : Space, -(χ x * fderiv ℝ uj x (sol.velocity t x))) +
            (∫ x : Space, ν * (χ x * (∑ i : Fin 3,
              fderiv ℝ (fun z => fderiv ℝ uj z (basisVector i)) x
                (basisVector i)))) :=
        integral_add hItransport.neg (hIlap.const_mul ν)
      rw [hsum, integral_neg, integral_const_mul]
    _ = (∫ x : Space, fderiv ℝ χ x (sol.velocity t x) * sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i)) *
              sol.velocity t x j) +
          (∫ x : Space, fderiv ℝ χ x (basisVector j) * sol.pressure t x) := by
      rw [htransport, hviscous, hpressure]
      ring

end Navier.Analysis.WholeSpaceDuhamel
