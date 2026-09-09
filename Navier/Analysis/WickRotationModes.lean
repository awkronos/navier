import Navier.Analysis.CriticalMildModeDifferentiation

/-!
# Wick rotation of one heat mode

For the entire scalar mode `Fₐ(z) = exp (-a z)`, restriction to positive real
time is the heat multiplier, whereas restriction to imaginary time has unit
modulus. Thus analytic continuation changes the real-time generator into a
skew generator and loses the strict parabolic damping estimate. The final theorem
links this calculation to the repository's literal lattice heat multiplier.

This is a statement about the linear multiplier of one Fourier mode.  It does
not identify the nonlinear real Navier--Stokes equation with a quantum or
Gross--Pitaevskii evolution.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.WickRotationModes

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.PeriodicPressureRecovery

/-- The entire complex-time continuation of the scalar heat mode with rate
`a`. -/
def entireHeatMode (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(a : ℂ) * z)

/-- Imaginary-time restriction `z = i s` of the entire heat mode. -/
def wickRotatedMode (a s : ℝ) : ℂ :=
  entireHeatMode a (Complex.I * (s : ℂ))

/-- The complex-time mode is entire. -/
theorem differentiable_entireHeatMode (a : ℝ) :
    Differentiable ℂ (entireHeatMode a) := by
  unfold entireHeatMode
  fun_prop

/-- On real time, the entire mode is exactly the scalar mode used by the
critical mild equation. -/
theorem entireHeatMode_real_eq_modeDecay (a t : ℝ) :
    entireHeatMode a (t : ℂ) = modeDecay a t := rfl

/-- Positive real time has the ordinary heat amplitude `exp (-a t)`. -/
theorem norm_entireHeatMode_real (a t : ℝ) :
    ‖entireHeatMode a (t : ℂ)‖ = Real.exp (-a * t) := by
  unfold entireHeatMode
  rw [Complex.norm_exp]
  congr 1
  norm_num [Complex.mul_re]

/-- The real-time generator is `-a`. -/
theorem hasDerivAt_entireHeatMode_real (a t : ℝ) :
    HasDerivAt (fun s : ℝ => entireHeatMode a (s : ℂ))
      (-(a : ℂ) * entireHeatMode a (t : ℂ)) t := by
  simpa [entireHeatMode_real_eq_modeDecay] using hasDerivAt_modeDecay a t

/-- Wick rotation changes the real-time generator `-a` into the skew generator
`-i a`. -/
theorem hasDerivAt_wickRotatedMode (a s : ℝ) :
    HasDerivAt (wickRotatedMode a)
      (-(Complex.I * (a : ℂ)) * wickRotatedMode a s) s := by
  unfold wickRotatedMode entireHeatMode
  have hlinear : HasDerivAt
      (fun r : ℝ => (-(a : ℂ) * Complex.I) * (r : ℂ))
      (-(a : ℂ) * Complex.I) s := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul
        (-(a : ℂ) * Complex.I)
  convert hlinear.cexp using 1 <;> ring_nf

/-- Every imaginary-time mode has unit modulus, at every rate and time. -/
theorem norm_wickRotatedMode (a s : ℝ) :
    ‖wickRotatedMode a s‖ = 1 := by
  unfold wickRotatedMode entireHeatMode
  rw [Complex.norm_exp]
  have hre : (-(a : ℂ) * (Complex.I * (s : ℂ))).re = 0 := by
    simp
  rw [hre, Real.exp_zero]

/-- A positive-rate heat mode contracts strictly at every positive real time. -/
theorem norm_entireHeatMode_real_lt_one
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ‖entireHeatMode a (t : ℂ)‖ < 1 := by
  rw [norm_entireHeatMode_real, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- The strict heat decay cannot be transferred through Wick rotation: the
rotated mode remains on the unit circle. -/
theorem not_norm_wickRotatedMode_lt_one (a s : ℝ) :
    ¬ ‖wickRotatedMode a s‖ < 1 := by
  rw [norm_wickRotatedMode]
  exact lt_irrefl 1

/-- More sharply, no positive exponential damping rate bounds a positive
imaginary-time mode.  This is an explicit failure of the real-time coercive
estimate after rotation. -/
theorem no_positive_exponential_damping_wick
    (a : ℝ) {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ¬ ‖wickRotatedMode a s‖ ≤ Real.exp (-c * s) := by
  rw [norm_wickRotatedMode]
  have hlt : Real.exp (-c * s) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact not_le_of_gt hlt

/-- At the repository's exact lattice rate `ν |k|²`, the real restriction of
the entire mode is the literal heat multiplier used in the mild equation. -/
theorem entireHeatMode_rawModeDecayRate_eq_complexHeatDecay
    (ν t : ℝ) (k : LatticeMode) :
    entireHeatMode (rawModeDecayRate ν k) (t : ℂ) =
      (complexHeatDecay ν t (latticeFrequency k) : ℂ) := by
  rw [entireHeatMode_real_eq_modeDecay]
  exact (complexHeatDecay_lattice_eq_modeDecay ν t k).symm

/-- Positive viscosity gives a positive decay rate at every nonzero lattice
mode. -/
theorem rawModeDecayRate_pos_of_ne_zero
    {ν : ℝ} (hν : 0 < ν) {k : LatticeMode} (hk : k ≠ 0) :
    0 < rawModeDecayRate ν k := by
  unfold rawModeDecayRate
  apply mul_pos hν
  apply sq_pos_of_pos
  rw [norm_pos_iff]
  intro hpoint
  apply latticeFrequency_ne_zero hk
  ext i
  have hi := congrArg
    (fun z : EuclideanSpace ℝ (Fin 3) => (z : Fin 3 → ℝ) i) hpoint
  simpa using hi

/-- For any positive lattice decay rate and positive time, the real heat mode
is strictly smaller in modulus than its Wick-rotated continuation. -/
theorem real_mode_strictly_damped_but_wick_mode_not
    {ν t : ℝ} {k : LatticeMode}
    (hrate : 0 < rawModeDecayRate ν k) (ht : 0 < t) :
    ‖(complexHeatDecay ν t (latticeFrequency k) : ℂ)‖ <
      ‖wickRotatedMode (rawModeDecayRate ν k) t‖ := by
  rw [← entireHeatMode_rawModeDecayRate_eq_complexHeatDecay,
    norm_wickRotatedMode]
  exact norm_entireHeatMode_real_lt_one hrate ht

/-- Concrete repository form: positive viscosity strictly damps every nonzero
lattice mode on real positive time, while the Wick-rotated mode has unit
amplitude. -/
theorem nonzero_lattice_mode_strictly_damped_but_wick_mode_not
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    {k : LatticeMode} (hk : k ≠ 0) :
    ‖(complexHeatDecay ν t (latticeFrequency k) : ℂ)‖ <
      ‖wickRotatedMode (rawModeDecayRate ν k) t‖ :=
  real_mode_strictly_damped_but_wick_mode_not
    (rawModeDecayRate_pos_of_ne_zero hν hk) ht

end Navier.Analysis.WickRotationModes
