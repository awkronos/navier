import Navier.Analysis.CriticalMildWeightedBanach

/-!
# Period-one pressure recovery from the Leray-projected lattice equation

The critical mild carrier stores the unprojected transport convolution and
applies the Leray multiplier at each output mode.  This file recovers the
longitudinal component as the gradient of an explicit scalar pressure
coefficient.  The physical Fourier convention is

`exp (2 * pi * I * k dot x)`.

Consequently one spatial derivative contributes `2 * pi * I * k`.  The zero
mode is fixed to pressure coefficient zero; its gradient is zero and the Leray
map is the identity there.  The final theorem inserts the recovered pressure
into an actual period-one projected mode equation containing the repository's
countable transport convolution and the correctly scaled viscous symbol.

This is the coefficientwise pressure-recovery step.  Reconstructing a real
smooth periodic pressure field still requires Fourier reality and rapid-decay
properties for the time-dependent solution coefficients.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PeriodicPressureRecovery

open scoped BigOperators
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach

/-- The derivative multiplier for a period-one Fourier character. -/
def periodOneDerivative : ℂ := (2 * Real.pi : ℂ) * Complex.I

theorem periodOneDerivative_ne_zero : periodOneDerivative ≠ 0 := by
  unfold periodOneDerivative
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- The integer-lattice embedding loses no mode information. -/
theorem latticeFrequency_injective : Function.Injective latticeFrequency := by
  intro m n h
  apply Prod.ext
  · exact_mod_cast (show (m.1 : ℝ) = (n.1 : ℝ) by
      simpa [latticeFrequency] using congrFun h (0 : Fin 3))
  · apply Prod.ext
    · exact_mod_cast (show (m.2.1 : ℝ) = (n.2.1 : ℝ) by
        simpa [latticeFrequency] using congrFun h (1 : Fin 3))
    · exact_mod_cast (show (m.2.2 : ℝ) = (n.2.2 : ℝ) by
        simpa [latticeFrequency] using congrFun h (2 : Fin 3))

theorem latticeFrequency_ne_zero {k : LatticeMode} (hk : k ≠ 0) :
    latticeFrequency k ≠ 0 := by
  intro h
  apply hk
  apply latticeFrequency_injective
  have hz : latticeFrequency (0 : LatticeMode) = 0 := by
    ext i
    fin_cases i <;> simp [latticeFrequency]
  exact h.trans hz.symm

@[simp] theorem latticeFrequency_neg (k : LatticeMode) :
    latticeFrequency (-k) = -latticeFrequency k := by
  ext i
  fin_cases i <;> simp [latticeFrequency]

/-- Fourier coefficient of the gradient of a scalar period-one mode. -/
def periodOneGradientCoefficient (k : LatticeMode) (p : ℂ) : ComplexSpace :=
  fun i => periodOneDerivative * (latticeFrequency k i : ℂ) * p

/-- Zero-mean pressure multiplier for an arbitrary vector coefficient.

The sign matches the equation
`partial_t u + convection - nu * Delta u + gradient p = 0`: pressure restores
`P convection - convection`, the longitudinal part removed by Leray
projection. -/
def pressureCoefficient (k : LatticeMode) (z : ComplexSpace) : ℂ :=
  -(∑ i, (latticeFrequency k i : ℂ) * z i) /
    (periodOneDerivative *
      ((latticeFrequency k ⬝ᵥ latticeFrequency k : ℝ) : ℂ))

@[simp] theorem pressureCoefficient_zero_mode (z : ComplexSpace) :
    pressureCoefficient 0 z = 0 := by
  simp [pressureCoefficient, latticeFrequency]

@[simp] theorem periodOneGradientCoefficient_zero_mode (p : ℂ) :
    periodOneGradientCoefficient 0 p = 0 := by
  ext i
  fin_cases i <;> simp [periodOneGradientCoefficient, latticeFrequency]

/-- The recovered pressure gradient is exactly the component removed by the
frequencywise Leray projection, including at zero mode. -/
theorem periodOneGradient_pressureCoefficient
    (k : LatticeMode) (z : ComplexSpace) :
    periodOneGradientCoefficient k (pressureCoefficient k z) =
      complexLeray (latticeFrequency k) z - z := by
  by_cases hk : k = 0
  · subst k
    have hz : latticeFrequency (0 : LatticeMode) = 0 := by
      ext i
      fin_cases i <;> simp [latticeFrequency]
    rw [pressureCoefficient_zero_mode,
      periodOneGradientCoefficient_zero_mode, hz,
      complexLeray_zero_frequency]
    simp
  · have hq : latticeFrequency k ≠ 0 := latticeFrequency_ne_zero hk
    have hqq : latticeFrequency k ⬝ᵥ latticeFrequency k ≠ 0 :=
      (dotProduct_self_eq_zero.not.mpr hq)
    have hqqC :
        ((latticeFrequency k ⬝ᵥ latticeFrequency k : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hqq
    have hD : periodOneDerivative ≠ 0 := periodOneDerivative_ne_zero
    ext i
    change _ = complexLeray (latticeFrequency k) z i - z i
    rw [complexLeray_formula]
    unfold periodOneGradientCoefficient pressureCoefficient
    field_simp [hD, hqqC]
    ring

/-- The scalar multiplier preserves Fourier reality.  Thus a
conjugate-symmetric vector coefficient family produces conjugate-symmetric
pressure coefficients. -/
theorem pressureCoefficient_neg_conjugate
    (k : LatticeMode) (z : ComplexSpace) :
    pressureCoefficient (-k) (complexConjugate z) =
      starRingEnd ℂ (pressureCoefficient k z) := by
  simp only [pressureCoefficient, latticeFrequency_neg, Pi.neg_apply,
    Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib, neg_div,
    neg_dotProduct, dotProduct_neg, neg_neg, complexConjugate]
  simp [periodOneDerivative, map_sum]
  rw [map_ofNat]
  ring

/-- Restore the physical `2*pi*I` derivative phase to the countable lattice
transport convolution used by the critical mild carrier. -/
def periodOneConvectionCoefficient (k : LatticeMode)
    (u v : WeightedLatticeBanach) : ComplexSpace :=
  periodOneDerivative •
    WithLp.ofLp (weightedLatticeSpectralConvolution k u v)

/-- The positive viscous term `-nu * Delta u` at a period-one Fourier mode. -/
def periodOneViscousCoefficient (nu : ℝ) (k : LatticeMode)
    (z : ComplexSpace) : ComplexSpace :=
  ((nu * (2 * Real.pi) ^ 2 *
      (latticeFrequency k ⬝ᵥ latticeFrequency k) : ℝ) : ℂ) • z

/-- The pressure coefficient selected from the actual countable convection
coefficient. -/
def periodOnePressureCoefficient (k : LatticeMode)
    (u v : WeightedLatticeBanach) : ℂ :=
  pressureCoefficient k (periodOneConvectionCoefficient k u v)

@[simp] theorem periodOnePressureCoefficient_zero_mode
    (u v : WeightedLatticeBanach) :
    periodOnePressureCoefficient 0 u v = 0 := by
  simp [periodOnePressureCoefficient]

/-- A projected period-one lattice mode equation yields the corresponding
unprojected Navier--Stokes mode equation with the explicit recovered pressure.

The nonlinear coefficient is the repository's literal countable transport
convolution with its physical derivative phase restored.  The viscous factor
is `nu * (2*pi)^2 * |k|^2`, and the pressure gradient uses `2*pi*I*k`.
-/
theorem projected_mode_equation_to_unprojected
    (nu : ℝ) (k : LatticeMode)
    (timeDerivative velocity : ComplexSpace)
    (u v : WeightedLatticeBanach)
    (hprojected :
      timeDerivative +
          complexLeray (latticeFrequency k)
            (periodOneConvectionCoefficient k u v) +
          periodOneViscousCoefficient nu k velocity = 0) :
    timeDerivative + periodOneConvectionCoefficient k u v +
        periodOneViscousCoefficient nu k velocity +
        periodOneGradientCoefficient k
          (periodOnePressureCoefficient k u v) = 0 := by
  rw [periodOnePressureCoefficient,
    periodOneGradient_pressureCoefficient]
  calc
    timeDerivative + periodOneConvectionCoefficient k u v +
          periodOneViscousCoefficient nu k velocity +
          (complexLeray (latticeFrequency k)
            (periodOneConvectionCoefficient k u v) -
              periodOneConvectionCoefficient k u v) =
        timeDerivative +
          complexLeray (latticeFrequency k)
            (periodOneConvectionCoefficient k u v) +
          periodOneViscousCoefficient nu k velocity := by abel
    _ = 0 := hprojected

end Navier.Analysis.PeriodicPressureRecovery
