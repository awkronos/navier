import Navier.Analysis.CriticalMildZeroMode

/-!
# Energy does not control the periodic critical terminal quantity

This module tests the energy-only route to the remaining periodic continuation
bound on the repository's actual weighted Fourier carrier.  A real-valued,
divergence-free pair of modes at frequencies `±(n+1,0,0)` has constant
physical Fourier `ℓ²` energy, while its `𝒳¹` contribution grows linearly with
the frequency.  Thus a frequency split must retain a high-frequency datum;
the energy inequality alone cannot yield the mixed terminal estimate.

This is an obstruction to that estimate route, not a counterexample to the
Navier--Stokes equation and not a proof that the periodic endpoint is false.
In particular, `CriticalMildOffZeroTerminalBound` permits its constant to
depend on the full initial datum, and positive-time heat smoothing restricts
the set of reachable terminal states.  The static family below refutes only a
uniform estimate based on energy alone; it does not refute that dynamical,
datum-dependent terminal bound.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.PeriodicEnergyCriticalObstruction

open scoped ENNReal
open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.CriticalMildZeroMode

/-- Positive axial frequency used by the test family. -/
def axialMode (n : ℕ) : LatticeMode := (((n + 1 : ℕ) : ℤ), (0, 0))

/-- A real unit polarization perpendicular to the axial frequency. -/
def transverseUnit : ComplexE3 :=
  WithLp.toLp 2 (Pi.single (1 : Fin 3) (1 : ℂ))

theorem norm_transverseUnit : ‖transverseUnit‖ = 1 := by
  simp [transverseUnit]

theorem axialMode_ne_zero (n : ℕ) : axialMode n ≠ 0 := by
  intro h
  have h0 := congrArg Prod.fst h
  simp [axialMode] at h0
  omega

theorem axialMode_ne_neg (n : ℕ) : axialMode n ≠ -axialMode n := by
  intro h
  have h0 := congrArg Prod.fst h
  simp [axialMode] at h0
  omega

theorem latticeModeSize_axialMode (n : ℕ) :
    latticeModeSize (axialMode n) = n + 1 := by
  have hsq : latticeModeSize (axialMode n) ^ 2 = (n + 1 : ℝ) ^ 2 := by
    unfold latticeModeSize axialMode
    rw [EuclideanSpace.norm_sq_eq]
    simp [complexFrequency_apply, latticeFrequency, Fin.sum_univ_three, sq_abs]
  have hnonneg := latticeModeSize_nonneg (axialMode n)
  have hpos : 0 ≤ (n + 1 : ℝ) := by positivity
  nlinarith

theorem latticeModeSize_neg_axialMode (n : ℕ) :
    latticeModeSize (-axialMode n) = n + 1 := by
  have hsq : latticeModeSize (-axialMode n) ^ 2 = (n + 1 : ℝ) ^ 2 := by
    unfold latticeModeSize axialMode
    rw [EuclideanSpace.norm_sq_eq]
    simp [complexFrequency_apply, latticeFrequency, Fin.sum_univ_three, sq_abs]
    ring
  have hnonneg := latticeModeSize_nonneg (-axialMode n)
  have hpos : 0 ≤ (n + 1 : ℝ) := by positivity
  nlinarith

/-- Stored coefficient corresponding to a unit physical Fourier amplitude. -/
def storedUnitAt (m : LatticeMode) : ComplexE3 :=
  latticeModeWeight m • transverseUnit

/-- The real two-mode datum at frequencies `±(n+1,0,0)`. -/
def highFrequencyPair (n : ℕ) : WeightedLatticeBanach :=
  lp.single 1 (axialMode n) (storedUnitAt (axialMode n)) +
    lp.single 1 (-axialMode n) (storedUnitAt (-axialMode n))

/-- Reality symmetry on the periodic lattice coefficients. -/
def LatticeHermitianReal (u : WeightedLatticeBanach) : Prop :=
  ∀ m i,
    complexEuclideanPoint (weightedLatticeCoefficient u (-m)) i =
      star (complexEuclideanPoint (weightedLatticeCoefficient u m) i)

/-- Physical Fourier `ℓ²` energy of the decoded coefficients. -/
def spectralL2Energy (u : WeightedLatticeBanach) : ℝ :=
  ∑' m : LatticeMode, weightedAmplitude u m ^ 2

/-- Low-frequency `𝒳¹` mass on a selected finite set. -/
def lowX1On (S : Finset LatticeMode) (u : WeightedLatticeBanach) : ℝ :=
  ∑ m ∈ S, latticeModeSize m * weightedAmplitude u m

/-- The complementary high-frequency `𝒳¹` tail. -/
def highX1Outside (S : Finset LatticeMode) (u : WeightedLatticeBanach) : ℝ :=
  normX1 latticeModeSize (weightedAmplitude u) - lowX1On S u

/-- Every finite frequency split is exact on the actual completed carrier. -/
theorem low_add_high_X1_eq (S : Finset LatticeMode)
    (u : WeightedLatticeBanach) :
    lowX1On S u + highX1Outside S u =
      normX1 latticeModeSize (weightedAmplitude u) := by
  unfold highX1Outside
  ring

theorem highX1Outside_nonneg (S : Finset LatticeMode)
    (u : WeightedLatticeBanach) : 0 ≤ highX1Outside S u := by
  unfold highX1Outside
  have hs := InW_latticeModeSize u
  have hsum : lowX1On S u ≤
      normX1 latticeModeSize (weightedAmplitude u) := by
    have h := hs.sum_le_tsum S (fun m _ =>
    mul_nonneg (latticeModeSize_nonneg m)
      (abs_nonneg (weightedAmplitude u m)))
    simpa [lowX1On, normX1, wNorm,
      abs_of_nonneg (weightedAmplitude_nonneg u _)] using h
  exact sub_nonneg.mpr hsum

/-- Cauchy--Schwarz gives the sharp finite-band energy estimate.  The first
factor records the unavoidable frequency/cardinality cost; the second is the
literal Fourier energy contained in the selected modes. -/
theorem lowX1On_le_frequencyCost_mul_energy (S : Finset LatticeMode)
    (u : WeightedLatticeBanach) :
    lowX1On S u ≤
      Real.sqrt (∑ m ∈ S, latticeModeSize m ^ 2) *
        Real.sqrt (∑ m ∈ S, weightedAmplitude u m ^ 2) := by
  exact Real.sum_mul_le_sqrt_mul_sqrt S latticeModeSize (weightedAmplitude u)

/-- The resulting honest frequency-split estimate for the terminal `𝒳¹`
quantity.  Energy controls the selected finite band with its explicit
frequency cost; a separate dynamical argument must control the complementary
tail. -/
theorem normX1_le_frequencyCost_mul_energy_add_high
    (S : Finset LatticeMode) (u : WeightedLatticeBanach) :
    normX1 latticeModeSize (weightedAmplitude u) ≤
      Real.sqrt (∑ m ∈ S, latticeModeSize m ^ 2) *
          Real.sqrt (∑ m ∈ S, weightedAmplitude u m ^ 2) +
        highX1Outside S u := by
  rw [← low_add_high_X1_eq S u]
  exact add_le_add (lowX1On_le_frequencyCost_mul_energy S u) le_rfl

@[simp] theorem weightedLatticeCoefficient_single_storedUnitAt
    (m : LatticeMode) :
    weightedLatticeCoefficient
        (lp.single 1 m (storedUnitAt m) : WeightedLatticeBanach) m =
      WithLp.ofLp transverseUnit := by
  simp [weightedLatticeCoefficient, storedUnitAt]
  have hm : latticeModeWeight m ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m))
  rw [← mul_smul, inv_mul_cancel₀ hm, one_smul]

@[simp] theorem weightedLatticeCoefficient_highFrequencyPair_pos (n : ℕ) :
    weightedLatticeCoefficient (highFrequencyPair n) (axialMode n) =
      WithLp.ofLp transverseUnit := by
  simp [highFrequencyPair, weightedLatticeCoefficient, storedUnitAt,
    axialMode_ne_neg n]
  have hm : latticeModeWeight (axialMode n) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight _))
  rw [← mul_smul, inv_mul_cancel₀ hm, one_smul]

@[simp] theorem weightedLatticeCoefficient_highFrequencyPair_neg (n : ℕ) :
    weightedLatticeCoefficient (highFrequencyPair n) (-axialMode n) =
      WithLp.ofLp transverseUnit := by
  simp [highFrequencyPair, weightedLatticeCoefficient, storedUnitAt,
    axialMode_ne_neg n]
  have hm : latticeModeWeight (-axialMode n) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight _))
  rw [← mul_smul, inv_mul_cancel₀ hm, one_smul]

theorem weightedLatticeCoefficient_highFrequencyPair_of_ne (n : ℕ)
    (m : LatticeMode) (hpos : m ≠ axialMode n) (hneg : m ≠ -axialMode n) :
    weightedLatticeCoefficient (highFrequencyPair n) m = 0 := by
  simp [highFrequencyPair, weightedLatticeCoefficient, lp.single_apply, hpos, hneg]

@[simp] theorem weightedAmplitude_highFrequencyPair_pos (n : ℕ) :
    weightedAmplitude (highFrequencyPair n) (axialMode n) = 1 := by
  rw [weightedAmplitude, weightedLatticeCoefficient_highFrequencyPair_pos]
  exact norm_transverseUnit

@[simp] theorem weightedAmplitude_highFrequencyPair_neg (n : ℕ) :
    weightedAmplitude (highFrequencyPair n) (-axialMode n) = 1 := by
  rw [weightedAmplitude, weightedLatticeCoefficient_highFrequencyPair_neg]
  exact norm_transverseUnit

theorem weightedAmplitude_highFrequencyPair_of_ne (n : ℕ)
    (m : LatticeMode) (hpos : m ≠ axialMode n) (hneg : m ≠ -axialMode n) :
    weightedAmplitude (highFrequencyPair n) m = 0 := by
  rw [weightedAmplitude, weightedLatticeCoefficient_highFrequencyPair_of_ne n m hpos hneg]
  exact norm_zero

theorem latticeHermitianReal_highFrequencyPair (n : ℕ) :
    LatticeHermitianReal (highFrequencyPair n) := by
  intro m i
  by_cases hpos : m = axialMode n
  · subst m
    rw [weightedLatticeCoefficient_highFrequencyPair_pos,
      weightedLatticeCoefficient_highFrequencyPair_neg]
    simp [transverseUnit, complexEuclideanPoint]
  · by_cases hneg : m = -axialMode n
    · subst m
      rw [neg_neg, weightedLatticeCoefficient_highFrequencyPair_pos,
        weightedLatticeCoefficient_highFrequencyPair_neg]
      simp [transverseUnit, complexEuclideanPoint]
    · have hnpos : -m ≠ axialMode n := by
        intro hm
        have : m = -axialMode n := by
          rw [← hm, neg_neg]
        exact hneg this
      have hnneg : -m ≠ -axialMode n := by
        intro hm
        have : m = axialMode n := neg_injective hm
        exact hpos this
      rw [weightedLatticeCoefficient_highFrequencyPair_of_ne n m hpos hneg,
        weightedLatticeCoefficient_highFrequencyPair_of_ne n (-m) hnpos hnneg]
      simp

theorem latticeDivergenceFree_highFrequencyPair (n : ℕ) :
    LatticeDivergenceFree (highFrequencyPair n) := by
  intro m
  by_cases hpos : m = axialMode n
  · subst m
    rw [weightedLatticeCoefficient_highFrequencyPair_pos]
    simp [axialMode, latticeFrequency, complexFrequency_apply,
      transverseUnit, complexEuclideanPoint, PiLp.inner_apply]
  · by_cases hneg : m = -axialMode n
    · subst m
      rw [weightedLatticeCoefficient_highFrequencyPair_neg]
      simp [axialMode, latticeFrequency, complexFrequency_apply,
        transverseUnit, complexEuclideanPoint, PiLp.inner_apply]
    · rw [weightedLatticeCoefficient_highFrequencyPair_of_ne n m hpos hneg]
      simp [complexEuclideanPoint]

theorem weightedAmplitude_highFrequencyPair (n : ℕ) :
    weightedAmplitude (highFrequencyPair n) =
      fun m => if m = axialMode n ∨ m = -axialMode n then 1 else 0 := by
  funext m
  by_cases hpos : m = axialMode n
  · simp [hpos]
  · by_cases hneg : m = -axialMode n
    · simp [hneg]
    · rw [weightedAmplitude_highFrequencyPair_of_ne n m hpos hneg]
      simp [hpos, hneg]

private theorem tsum_eq_add_of_support_pair {α : Type*} [DecidableEq α]
    (f : α → ℝ) (a b : α) (hab : a ≠ b)
    (hsupport : ∀ x, x ≠ a → x ≠ b → f x = 0) :
    (∑' x, f x) = f a + f b := by
  have hs : Summable f := by
    apply summable_of_ne_finset_zero (s := {a, b})
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hsupport x hx.1 hx.2
  rw [hs.tsum_eq_add_tsum_ite a]
  congr 1
  refine (tsum_eq_single b ?_).trans ?_
  · intro x hxb
    by_cases hxa : x = a
    · simp [hxa]
    · simp [hxa, hsupport x hxa hxb]
  · simp [hab.symm]

theorem spectralL2Energy_highFrequencyPair (n : ℕ) :
    spectralL2Energy (highFrequencyPair n) = 2 := by
  unfold spectralL2Energy
  rw [tsum_eq_add_of_support_pair
    (fun m : LatticeMode => weightedAmplitude (highFrequencyPair n) m ^ 2)
    (axialMode n) (-axialMode n) (axialMode_ne_neg n)]
  · norm_num
  · intro m hpos hneg
    rw [weightedAmplitude_highFrequencyPair_of_ne n m hpos hneg]
    norm_num

theorem normX1_highFrequencyPair (n : ℕ) :
    normX1 latticeModeSize (weightedAmplitude (highFrequencyPair n)) =
      2 * (n + 1) := by
  unfold normX1 wNorm
  rw [tsum_eq_add_of_support_pair
    (fun m : LatticeMode =>
      latticeModeSize m * |weightedAmplitude (highFrequencyPair n) m|)
    (axialMode n) (-axialMode n) (axialMode_ne_neg n)]
  · rw [latticeModeSize_axialMode, latticeModeSize_neg_axialMode]
    simp
    ring
  · intro m hpos hneg
    rw [weightedAmplitude_highFrequencyPair_of_ne n m hpos hneg]
    simp

@[simp] theorem weightedAmplitude_highFrequencyPair_zero (n : ℕ) :
    weightedAmplitude (highFrequencyPair n) 0 = 0 := by
  apply weightedAmplitude_highFrequencyPair_of_ne n
  · exact (axialMode_ne_zero n).symm
  · simpa using (neg_ne_zero.mpr (axialMode_ne_zero n)).symm

theorem normXm1_highFrequencyPair (n : ℕ) :
    normXm1 latticeModeSize (weightedAmplitude (highFrequencyPair n)) =
      2 * (n + 1 : ℝ)⁻¹ := by
  unfold normXm1 wNorm
  rw [tsum_eq_add_of_support_pair
    (fun m : LatticeMode =>
      (latticeModeSize m)⁻¹ * |weightedAmplitude (highFrequencyPair n) m|)
    (axialMode n) (-axialMode n) (axialMode_ne_neg n)]
  · rw [latticeModeSize_axialMode, latticeModeSize_neg_axialMode]
    simp
    ring
  · intro m hpos hneg
    rw [weightedAmplitude_highFrequencyPair_of_ne n m hpos hneg]
    simp

theorem mixedCriticalQty_highFrequencyPair (ν : ℝ) (n : ℕ) :
    mixedCriticalQty ν (highFrequencyPair n) =
      2 * (n + 1 : ℝ)⁻¹ + ν * (2 * (n + 1)) := by
  rw [mixedCriticalQty, weightedAmplitude_highFrequencyPair_zero,
    normXm1_highFrequencyPair, normX1_highFrequencyPair]
  ring

theorem offZeroMixedCriticalQty_highFrequencyPair (ν : ℝ) (n : ℕ) :
    offZeroMixedCriticalQty ν (highFrequencyPair n) =
      2 * (n + 1 : ℝ)⁻¹ + ν * (2 * (n + 1)) := by
  have hsplit := mixedCriticalQty_eq_zero_amplitude_add_offZero
    ν (highFrequencyPair n)
  rw [weightedAmplitude_highFrequencyPair_zero, zero_add] at hsplit
  calc
    offZeroMixedCriticalQty ν (highFrequencyPair n) =
        mixedCriticalQty ν (highFrequencyPair n) := hsplit.symm
    _ = _ := mixedCriticalQty_highFrequencyPair ν n

theorem mixedCriticalQty_highFrequencyPair_lower (ν : ℝ) (n : ℕ) :
    ν * (2 * (n + 1)) ≤ mixedCriticalQty ν (highFrequencyPair n) := by
  rw [mixedCriticalQty, normX1_highFrequencyPair]
  linarith [weightedAmplitude_nonneg (highFrequencyPair n) 0,
    normXm1_nonneg latticeModeSize_nonneg
      (weightedAmplitude (highFrequencyPair n))]

/-- There is no viscosity-dependent energy-only upper bound for the mixed
critical quantity on real, divergence-free periodic Fourier data. -/
theorem exists_real_divergenceFree_fixed_energy_above_mixed
    {ν C : ℝ} (hν : 0 < ν) :
    ∃ u : WeightedLatticeBanach,
      LatticeHermitianReal u ∧ LatticeDivergenceFree u ∧
      spectralL2Energy u = 2 ∧ C < mixedCriticalQty ν u := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (C / (2 * ν))
  refine ⟨highFrequencyPair n, latticeHermitianReal_highFrequencyPair n,
    latticeDivergenceFree_highFrequencyPair n,
    spectralL2Energy_highFrequencyPair n, ?_⟩
  have hscale : C < ν * (2 * (n + 1)) := by
    have hn' : C / (2 * ν) < (n : ℝ) := by simpa using hn
    have hden : 0 < 2 * ν := by positivity
    have : C < (2 * ν) * n := by
      simpa [mul_comm] using (div_lt_iff₀ hden).mp hn'
    nlinarith
  exact hscale.trans_le (mixedCriticalQty_highFrequencyPair_lower ν n)

/-- The same fixed-energy family is unbounded in the exact off-zero quantity
left by zero-mode conservation.  This shows why the periodic continuation
proof still needs a dynamical high-frequency estimate after energy control. -/
theorem exists_real_divergenceFree_fixed_energy_above_offZero
    {ν C : ℝ} (hν : 0 < ν) :
    ∃ u : WeightedLatticeBanach,
      LatticeHermitianReal u ∧ LatticeDivergenceFree u ∧
      spectralL2Energy u = 2 ∧ C < offZeroMixedCriticalQty ν u := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (C / (2 * ν))
  refine ⟨highFrequencyPair n, latticeHermitianReal_highFrequencyPair n,
    latticeDivergenceFree_highFrequencyPair n,
    spectralL2Energy_highFrequencyPair n, ?_⟩
  have hscale : C < ν * (2 * (n + 1)) := by
    have hn' : C / (2 * ν) < (n : ℝ) := by simpa using hn
    have hden : 0 < 2 * ν := by positivity
    have : C < (2 * ν) * n := by
      simpa [mul_comm] using (div_lt_iff₀ hden).mp hn'
    nlinarith
  rw [offZeroMixedCriticalQty_highFrequencyPair]
  have hinv : 0 ≤ 2 * (n + 1 : ℝ)⁻¹ := by positivity
  nlinarith

/-- Formal negation of an energy-only estimate for the exact remaining
off-zero critical quantity on all admissible lattice states.  Reachable mild
terminal states form a smaller class and its bound may depend on the complete
initial datum, so the missing continuation theorem can still hold by exploiting
positive-time smoothing and nonlinear dynamics. -/
theorem no_uniform_offZeroMixed_bound_from_energy (ν : ℝ) (hν : 0 < ν) :
    ¬ ∃ C : ℝ, ∀ u : WeightedLatticeBanach,
      LatticeHermitianReal u → LatticeDivergenceFree u →
      spectralL2Energy u = 2 → offZeroMixedCriticalQty ν u ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨u, hr, hdf, henergy, hlarge⟩ :=
    exists_real_divergenceFree_fixed_energy_above_offZero (C := C) hν
  exact (not_lt_of_ge (hC u hr hdf henergy)) hlarge

end Navier.Analysis.PeriodicEnergyCriticalObstruction
