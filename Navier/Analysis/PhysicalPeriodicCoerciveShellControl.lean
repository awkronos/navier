import Navier.Analysis.PhysicalPeriodicWeightedFluxCommutator

/-!
# A physical triad obstruction to pointwise viscous absorption

This file tests a natural frequency-local closure of the physical periodic
energy method.  The six-mode carrier below obeys the actual anti-Hermitian
reality condition and the lattice divergence constraint.  Its weighted
triad commutator is cubic in amplitude, while every viscous modal density is
quadratic.  Consequently no amplitude-independent pointwise absorption of
the weighted transfer by the three participating viscous densities can hold.

This does not obstruct a trajectory-dependent or time-integrated estimate.
It identifies why such an estimate must use dynamics beyond a pointwise
viscous comparison.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.PhysicalPeriodicCoerciveShellControl

open scoped ENNReal ComplexConjugate
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PhysicalPeriodicGlobalControl
open Navier.Analysis.PhysicalPeriodicEnergyEvolution
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.PhysicalPeriodicWeightedFluxCommutator

def triadP : LatticeMode := (3, (0, 0))
def triadQ : LatticeMode := (0, (4, 0))
def triadL : LatticeMode := (-3, (-4, 0))

def triadPCoefficient (r : ℝ) : ComplexSpace := ![0, (r : ℂ), 0]
def triadQCoefficient (r : ℝ) : ComplexSpace := ![(r : ℂ), 0, 0]
def triadLCoefficient (r : ℝ) : ComplexSpace := ![(-4 * r : ℝ), (3 * r : ℝ), 0]

def storedCoefficientAt (m : LatticeMode) (z : ComplexSpace) : ComplexE3 :=
  (latticeModeWeight m : ℂ) • WithLp.toLp 2 z

def weightedModeAtom (m : LatticeMode) (z : ComplexSpace) : WeightedLatticeBanach :=
  lp.single 1 m (storedCoefficientAt m z)

theorem weightedLatticeCoefficient_weightedModeAtom_same
    (m : LatticeMode) (z : ComplexSpace) :
    weightedLatticeCoefficient (weightedModeAtom m z) m = z := by
  simp [weightedModeAtom, storedCoefficientAt, weightedLatticeCoefficient]
  have hm : latticeModeWeight m ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m))
  rw [← mul_smul, inv_mul_cancel₀ hm, one_smul]

theorem weightedLatticeCoefficient_weightedModeAtom_of_ne
    (m n : LatticeMode) (z : ComplexSpace) (hn : n ≠ m) :
    weightedLatticeCoefficient (weightedModeAtom m z) n = 0 := by
  simp [weightedModeAtom, weightedLatticeCoefficient, lp.single_apply, hn]

def physicalModePair (m : LatticeMode) (z : ComplexSpace) : WeightedLatticeBanach :=
  weightedModeAtom m z + weightedModeAtom (-m) (-complexConjugate z)

theorem triadP_ne_neg : triadP ≠ -triadP := by
  intro h
  have := congrArg Prod.fst h
  norm_num [triadP] at this

theorem triadQ_ne_neg : triadQ ≠ -triadQ := by
  intro h
  have := congrArg (fun m : LatticeMode => m.2.1) h
  norm_num [triadQ] at this

theorem triadL_ne_neg : triadL ≠ -triadL := by
  intro h
  have := congrArg Prod.fst h
  norm_num [triadL] at this

theorem weightedLatticeCoefficient_physicalModePair_pos
    (m : LatticeMode) (z : ComplexSpace) (hm : m ≠ -m) :
    weightedLatticeCoefficient (physicalModePair m z) m = z := by
  unfold physicalModePair
  rw [congrFun (weightedLatticeCoefficient_add _ _) m]
  simp only [Pi.add_apply]
  rw [
    weightedLatticeCoefficient_weightedModeAtom_same,
    weightedLatticeCoefficient_weightedModeAtom_of_ne]
  · simp
  · exact hm

theorem weightedLatticeCoefficient_physicalModePair_neg
    (m : LatticeMode) (z : ComplexSpace) (hm : m ≠ -m) :
    weightedLatticeCoefficient (physicalModePair m z) (-m) =
      -complexConjugate z := by
  unfold physicalModePair
  rw [congrFun (weightedLatticeCoefficient_add _ _) (-m)]
  simp only [Pi.add_apply]
  rw [
    weightedLatticeCoefficient_weightedModeAtom_same,
    weightedLatticeCoefficient_weightedModeAtom_of_ne]
  · simp
  · exact hm.symm

theorem weightedLatticeCoefficient_physicalModePair_other
    (m n : LatticeMode) (z : ComplexSpace) (hnp : n ≠ m) (hnn : n ≠ -m) :
    weightedLatticeCoefficient (physicalModePair m z) n = 0 := by
  unfold physicalModePair
  rw [congrFun (weightedLatticeCoefficient_add _ _) n]
  simp only [Pi.add_apply]
  rw [
    weightedLatticeCoefficient_weightedModeAtom_of_ne m n z hnp,
    weightedLatticeCoefficient_weightedModeAtom_of_ne (-m) n
      (-complexConjugate z) hnn]
  exact add_zero 0

theorem physicalAntiHermitian_physicalModePair
    (m : LatticeMode) (z : ComplexSpace) (hm : m ≠ -m) :
    PhysicalAntiHermitian (physicalModePair m z) := by
  intro n
  by_cases hnp : n = m
  · subst n
    rw [weightedLatticeCoefficient_physicalModePair_neg m z hm,
      weightedLatticeCoefficient_physicalModePair_pos m z hm]
  · by_cases hnn : n = -m
    · subst n
      rw [neg_neg, weightedLatticeCoefficient_physicalModePair_pos m z hm,
        weightedLatticeCoefficient_physicalModePair_neg m z hm]
      ext i
      simp [complexConjugate]
    · have hnnp : -n ≠ m := by
        intro h
        apply hnn
        rw [← h, neg_neg]
      have hnnn : -n ≠ -m := by
        intro h
        exact hnp (neg_injective h)
      rw [weightedLatticeCoefficient_physicalModePair_other m (-n) z hnnp hnnn,
        weightedLatticeCoefficient_physicalModePair_other m n z hnp hnn]
      ext i
      simp [complexConjugate]

def physicalTriadCarrier (r : ℝ) : WeightedLatticeBanach :=
  physicalModePair triadP (triadPCoefficient r) +
    physicalModePair triadQ (triadQCoefficient r) +
      physicalModePair triadL (triadLCoefficient r)

theorem physicalAntiHermitian_add {u v : WeightedLatticeBanach}
    (hu : PhysicalAntiHermitian u) (hv : PhysicalAntiHermitian v) :
    PhysicalAntiHermitian (u + v) := by
  intro m
  rw [congrFun (weightedLatticeCoefficient_add u v) (-m),
    congrFun (weightedLatticeCoefficient_add u v) m]
  simp only [Pi.add_apply]
  rw [hu m, hv m]
  ext i
  simp [complexConjugate]
  abel

theorem physicalAntiHermitian_physicalTriadCarrier (r : ℝ) :
    PhysicalAntiHermitian (physicalTriadCarrier r) := by
  unfold physicalTriadCarrier
  exact physicalAntiHermitian_add
    (physicalAntiHermitian_add
      (physicalAntiHermitian_physicalModePair triadP (triadPCoefficient r)
        triadP_ne_neg)
      (physicalAntiHermitian_physicalModePair triadQ (triadQCoefficient r)
        triadQ_ne_neg))
    (physicalAntiHermitian_physicalModePair triadL (triadLCoefficient r)
      triadL_ne_neg)

theorem latticeDivergenceFree_physicalModePair
    (m : LatticeMode) (z : ComplexSpace) (hm : m ≠ -m)
    (hz : inner ℂ (complexFrequency (latticeFrequency m))
      (complexEuclideanPoint z) = 0)
    (hzn : inner ℂ (complexFrequency (latticeFrequency (-m)))
      (complexEuclideanPoint (-complexConjugate z)) = 0) :
    LatticeDivergenceFree (physicalModePair m z) := by
  intro n
  by_cases hnp : n = m
  · subst n
    rw [weightedLatticeCoefficient_physicalModePair_pos m z hm]
    exact hz
  · by_cases hnn : n = -m
    · subst n
      rw [weightedLatticeCoefficient_physicalModePair_neg m z hm]
      exact hzn
    · rw [weightedLatticeCoefficient_physicalModePair_other m n z hnp hnn]
      simp [complexEuclideanPoint]

theorem latticeDivergenceFree_physicalP (r : ℝ) :
    LatticeDivergenceFree (physicalModePair triadP (triadPCoefficient r)) := by
  apply latticeDivergenceFree_physicalModePair triadP (triadPCoefficient r)
    triadP_ne_neg
  · simp [triadP, triadPCoefficient, latticeFrequency, complexFrequency_apply,
      complexEuclideanPoint, PiLp.inner_apply, Fin.sum_univ_three]
  · simp [triadP, triadPCoefficient, latticeFrequency, complexFrequency_apply,
      complexEuclideanPoint, complexConjugate, PiLp.inner_apply, Fin.sum_univ_three]

theorem latticeDivergenceFree_physicalQ (r : ℝ) :
    LatticeDivergenceFree (physicalModePair triadQ (triadQCoefficient r)) := by
  apply latticeDivergenceFree_physicalModePair triadQ (triadQCoefficient r)
    triadQ_ne_neg
  · simp [triadQ, triadQCoefficient, latticeFrequency, complexFrequency_apply,
      complexEuclideanPoint, PiLp.inner_apply, Fin.sum_univ_three]
  · simp [triadQ, triadQCoefficient, latticeFrequency, complexFrequency_apply,
      complexEuclideanPoint, complexConjugate, PiLp.inner_apply, Fin.sum_univ_three]

theorem latticeDivergenceFree_physicalL (r : ℝ) :
    LatticeDivergenceFree (physicalModePair triadL (triadLCoefficient r)) := by
  apply latticeDivergenceFree_physicalModePair triadL (triadLCoefficient r)
    triadL_ne_neg
  · simp [triadL, triadLCoefficient, latticeFrequency, complexFrequency_apply,
      complexEuclideanPoint, PiLp.inner_apply, Fin.sum_univ_three]
    ring
  · simp [triadL, triadLCoefficient, latticeFrequency, complexFrequency_apply,
      complexEuclideanPoint, complexConjugate, PiLp.inner_apply, Fin.sum_univ_three]
    have hs3 : (starRingEnd ℂ) (3 : ℂ) = 3 := by
      change star (3 : ℂ) = 3
      exact star_ofNat 3
    have hs4 : (starRingEnd ℂ) (4 : ℂ) = 4 := by
      change star (4 : ℂ) = 4
      exact star_ofNat 4
    rw [hs3, hs4]
    ring

theorem latticeDivergenceFree_physicalTriadCarrier (r : ℝ) :
    LatticeDivergenceFree (physicalTriadCarrier r) := by
  unfold physicalTriadCarrier
  exact LatticeDivergenceFree.add
    (LatticeDivergenceFree.add
      (latticeDivergenceFree_physicalP r)
      (latticeDivergenceFree_physicalQ r))
    (latticeDivergenceFree_physicalL r)

theorem weightedLatticeCoefficient_physicalTriadCarrier_p (r : ℝ) :
    weightedLatticeCoefficient (physicalTriadCarrier r) triadP =
      triadPCoefficient r := by
  unfold physicalTriadCarrier
  rw [congrFun (weightedLatticeCoefficient_add _ _) triadP]
  simp only [Pi.add_apply]
  rw [congrFun (weightedLatticeCoefficient_add _ _) triadP]
  simp only [Pi.add_apply]
  rw [weightedLatticeCoefficient_physicalModePair_pos triadP
      (triadPCoefficient r) triadP_ne_neg,
    weightedLatticeCoefficient_physicalModePair_other triadQ triadP
      (triadQCoefficient r),
    weightedLatticeCoefficient_physicalModePair_other triadL triadP
      (triadLCoefficient r)]
  · simp
  all_goals norm_num [triadP, triadQ, triadL]

theorem weightedLatticeCoefficient_physicalTriadCarrier_q (r : ℝ) :
    weightedLatticeCoefficient (physicalTriadCarrier r) triadQ =
      triadQCoefficient r := by
  unfold physicalTriadCarrier
  rw [congrFun (weightedLatticeCoefficient_add _ _) triadQ]
  simp only [Pi.add_apply]
  rw [congrFun (weightedLatticeCoefficient_add _ _) triadQ]
  simp only [Pi.add_apply]
  rw [weightedLatticeCoefficient_physicalModePair_other triadP triadQ
      (triadPCoefficient r),
    weightedLatticeCoefficient_physicalModePair_pos triadQ
      (triadQCoefficient r) triadQ_ne_neg,
    weightedLatticeCoefficient_physicalModePair_other triadL triadQ
      (triadLCoefficient r)]
  · simp
  all_goals norm_num [triadP, triadQ, triadL]

theorem weightedLatticeCoefficient_physicalTriadCarrier_l (r : ℝ) :
    weightedLatticeCoefficient (physicalTriadCarrier r) triadL =
      triadLCoefficient r := by
  unfold physicalTriadCarrier
  rw [congrFun (weightedLatticeCoefficient_add _ _) triadL]
  simp only [Pi.add_apply]
  rw [congrFun (weightedLatticeCoefficient_add _ _) triadL]
  simp only [Pi.add_apply]
  rw [weightedLatticeCoefficient_physicalModePair_other triadP triadL
      (triadPCoefficient r),
    weightedLatticeCoefficient_physicalModePair_other triadQ triadL
      (triadQCoefficient r),
    weightedLatticeCoefficient_physicalModePair_pos triadL
      (triadLCoefficient r) triadL_ne_neg]
  · simp
  all_goals norm_num [triadP, triadQ, triadL]

theorem triad_sum_eq_zero : triadP + triadQ + triadL = 0 := by
  norm_num [triadP, triadQ, triadL]

theorem latticeModeSize_triadP : latticeModeSize triadP = 3 := by
  have hsq : latticeModeSize triadP ^ 2 = (3 : ℝ) ^ 2 := by
    unfold latticeModeSize triadP
    rw [EuclideanSpace.norm_sq_eq]
    simp [complexFrequency_apply, latticeFrequency, Fin.sum_univ_three, sq_abs]
  nlinarith [latticeModeSize_nonneg triadP]

theorem latticeModeSize_triadQ : latticeModeSize triadQ = 4 := by
  have hsq : latticeModeSize triadQ ^ 2 = (4 : ℝ) ^ 2 := by
    unfold latticeModeSize triadQ
    rw [EuclideanSpace.norm_sq_eq]
    simp [complexFrequency_apply, latticeFrequency, Fin.sum_univ_three, sq_abs]
  nlinarith [latticeModeSize_nonneg triadQ]

theorem latticeModeSize_triadL : latticeModeSize triadL = 5 := by
  have hsq : latticeModeSize triadL ^ 2 = (5 : ℝ) ^ 2 := by
    unfold latticeModeSize triadL
    rw [EuclideanSpace.norm_sq_eq]
    simp [complexFrequency_apply, latticeFrequency, Fin.sum_univ_three, sq_abs]
    norm_num
  nlinarith [latticeModeSize_nonneg triadL]

theorem projectedPhysicalTriadEnergy_physicalTriadCarrier_pq (r : ℝ) :
    projectedPhysicalTriadEnergy (physicalTriadCarrier r) triadP triadQ =
      16 * r ^ 3 := by
  rw [projectedPhysicalTriadEnergy_eq (physicalTriadCarrier r)
      (latticeDivergenceFree_physicalTriadCarrier r) triadP triadQ,
    physicalTriadEnergy_eq (physicalTriadCarrier r)
      (physicalAntiHermitian_physicalTriadCarrier r)
      triadP triadQ triadL triad_sum_eq_zero,
    weightedLatticeCoefficient_physicalTriadCarrier_p,
    weightedLatticeCoefficient_physicalTriadCarrier_l,
    weightedLatticeCoefficient_physicalTriadCarrier_q]
  simp [triadQ, triadPCoefficient, triadQCoefficient, triadLCoefficient,
    latticeFrequency, complexFrequency_apply, complexEuclideanPoint,
    PiLp.inner_apply, complexBilinearPairing, Fin.sum_univ_three]
  ring

theorem weightedProjectedTriadPair_physicalTriadCarrier (r : ℝ) :
    weightedProjectedTriadPair (physicalTriadCarrier r)
        triadP triadQ triadL = 16 * r ^ 3 := by
  rw [weightedProjectedTriadPair_eq_weightGap (physicalTriadCarrier r)
      (physicalAntiHermitian_physicalTriadCarrier r)
      (latticeDivergenceFree_physicalTriadCarrier r)
      triadP triadQ triadL triad_sum_eq_zero,
    projectedPhysicalTriadEnergy_physicalTriadCarrier_pq]
  have hpq : triadP + triadQ = -triadL := by
    norm_num [triadP, triadQ, triadL]
  have hpl : triadP + triadL = -triadQ := by
    norm_num [triadP, triadQ, triadL]
  rw [hpq, hpl, latticeModeWeight_eq_one_add_size,
    latticeModeWeight_eq_one_add_size, latticeModeSize_neg,
    latticeModeSize_neg, latticeModeSize_triadL, latticeModeSize_triadQ]
  ring

theorem rawSpectralDissipationDensity_physicalTriadCarrier_p (r : ℝ) :
    rawSpectralDissipationDensity (physicalTriadCarrier r) triadP =
      9 * r ^ 2 := by
  unfold rawSpectralDissipationDensity weightedAmplitude complexEuclideanNorm
  rw [latticeModeSize_triadP,
    weightedLatticeCoefficient_physicalTriadCarrier_p,
    EuclideanSpace.norm_sq_eq]
  simp [triadPCoefficient, complexEuclideanPoint, Fin.sum_univ_three, sq_abs]
  norm_num

theorem rawSpectralDissipationDensity_physicalTriadCarrier_q (r : ℝ) :
    rawSpectralDissipationDensity (physicalTriadCarrier r) triadQ =
      16 * r ^ 2 := by
  unfold rawSpectralDissipationDensity weightedAmplitude complexEuclideanNorm
  rw [latticeModeSize_triadQ,
    weightedLatticeCoefficient_physicalTriadCarrier_q,
    EuclideanSpace.norm_sq_eq]
  simp [triadQCoefficient, complexEuclideanPoint, Fin.sum_univ_three, sq_abs]
  norm_num

theorem rawSpectralDissipationDensity_physicalTriadCarrier_l (r : ℝ) :
    rawSpectralDissipationDensity (physicalTriadCarrier r) triadL =
      625 * r ^ 2 := by
  unfold rawSpectralDissipationDensity weightedAmplitude complexEuclideanNorm
  rw [latticeModeSize_triadL,
    weightedLatticeCoefficient_physicalTriadCarrier_l,
    EuclideanSpace.norm_sq_eq]
  simp [triadLCoefficient, complexEuclideanPoint, Fin.sum_univ_three]
  simp only [mul_pow, sq_abs]
  ring

theorem triadDissipation_physicalTriadCarrier (r : ℝ) :
    rawSpectralDissipationDensity (physicalTriadCarrier r) triadP +
        rawSpectralDissipationDensity (physicalTriadCarrier r) triadQ +
      rawSpectralDissipationDensity (physicalTriadCarrier r) triadL =
        650 * r ^ 2 := by
  rw [rawSpectralDissipationDensity_physicalTriadCarrier_p,
    rawSpectralDissipationDensity_physicalTriadCarrier_q,
    rawSpectralDissipationDensity_physicalTriadCarrier_l]
  ring

/-- For every proposed amplitude-independent absorption constant there is an
actual finite-support physical divergence-free carrier on which one weighted
triad pair exceeds that constant times all three participating viscous
densities. -/
theorem exists_physical_triad_above_viscous_absorption (C : ℝ) :
    ∃ (u : WeightedLatticeBanach) (i j l : LatticeMode),
      PhysicalAntiHermitian u ∧ LatticeDivergenceFree u ∧ i + j + l = 0 ∧
      C * (rawSpectralDissipationDensity u i +
          rawSpectralDissipationDensity u j +
          rawSpectralDissipationDensity u l) <
        |weightedProjectedTriadPair u i j l| := by
  let r : ℝ := 41 * (|C| + 1)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  refine ⟨physicalTriadCarrier r, triadP, triadQ, triadL,
    physicalAntiHermitian_physicalTriadCarrier r,
    latticeDivergenceFree_physicalTriadCarrier r,
    triad_sum_eq_zero, ?_⟩
  rw [triadDissipation_physicalTriadCarrier,
    weightedProjectedTriadPair_physicalTriadCarrier,
    abs_of_pos (by positivity : 0 < 16 * r ^ 3)]
  have hC : C ≤ |C| := le_abs_self C
  dsimp [r]
  nlinarith [abs_nonneg C]

/-- Pointwise viscous absorption of the actual physical weighted triad
commutator cannot hold with a universal amplitude-independent constant.  This
rules out that static closure of the existing commutator estimate; summed or
time-integrated trajectory estimates are not addressed. -/
theorem no_uniform_weightedTriadPair_viscous_absorption :
    ¬ ∃ C : ℝ, ∀ (u : WeightedLatticeBanach) (i j l : LatticeMode),
      PhysicalAntiHermitian u → LatticeDivergenceFree u → i + j + l = 0 →
      |weightedProjectedTriadPair u i j l| ≤
        C * (rawSpectralDissipationDensity u i +
          rawSpectralDissipationDensity u j +
          rawSpectralDissipationDensity u l) := by
  rintro ⟨C, hC⟩
  obtain ⟨u, i, j, l, hphysical, hdiv, hsum, hstrict⟩ :=
    exists_physical_triad_above_viscous_absorption C
  exact (not_lt_of_ge (hC u i j l hphysical hdiv hsum)) hstrict

end Navier.Analysis.PhysicalPeriodicCoerciveShellControl
