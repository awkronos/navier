import Navier.Analysis.CriticalMildSmallDataGlobal
import Navier.Analysis.CriticalMildTrajectoryReality

/-!
# Reality transport for the global small-data mild trajectory

`CriticalMildSmallDataGlobal.smallDataGlobal_navierStokesBody_on_positiveTime`
identifies the official `Navier.Problem` momentum equation at every positive
time for the global small-data mild driver, but its docstring names one
premise the constructing lane did not discharge: the reality (anti-Hermitian)
transport of the global driver, `∀ s, LatticeAntiHermitian
(smallDataGlobalDriver ν hν a ha ha16 s)`.  This file discharges it.

The argument is the fixed-point one.  The horizon-`n` gap endomap
`gapBallImageNat` maps the closed anti-Hermitian path subspace of the
radius-`2‖a‖` ball into itself when the datum is anti-Hermitian — the heat
and Duhamel terms of `criticalMildImage` preserve the raw sign law
(`CriticalMildTrajectoryReality.criticalMildImage_antiHermitian`) — contains
the zero path, and is a strict contraction.  Banach's principle restricted to
the closed subspace produces a real fixed point, and uniqueness of the gap
fixed point in the whole ball forces it to be the chosen `localGapPath`.
Horizon coherence and the `toNNReal` gluing then transport reality to
`globalGapPath` and to the all-time driver.  The small-data official momentum
identity for anti-Hermitian data becomes unconditional
(`smallDataGlobal_navierStokesBody_on_positiveTime_of_real`), and the
physical carrier is Hermitian at every time
(`smallDataGlobalDriver_physicalHermitian`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Navier.Analysis.CriticalMildGlobalTrajectoryReality

open Set Topology
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildTrajectoryReality
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.CriticalMildSmallDataGlobal

private def RealityPathSet (T R : ℝ) : Set (CriticalMildPathBall T R) :=
  {u | ∀ τ : Icc (0 : ℝ) T, LatticeAntiHermitian (u.1 τ)}

private theorem isClosed_realityPathSet (T R : ℝ) :
    IsClosed (RealityPathSet T R) := by
  rw [show RealityPathSet T R =
      ⋂ τ : Icc (0 : ℝ) T, ⋂ k : LatticeMode, ⋂ i : Fin 3,
        {u : CriticalMildPathBall T R |
          weightedLatticeCoefficient (u.1 τ) (-k) i =
            (-complexConjugate (weightedLatticeCoefficient (u.1 τ) k)) i} by
    ext u
    simp only [RealityPathSet, Set.mem_ofPred, mem_iInter]
    constructor
    · intro hu τ k i
      exact congrArg (fun z : ComplexSpace => z i) (hu τ k)
    · intro hu τ k
      ext i
      exact hu τ k i]
  apply isClosed_iInter
  intro τ
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro i
  let Lneg : WeightedLatticeBanach →L[ℂ] ℂ :=
    (complexE3CoordinateCLM i).comp (weightedLatticePointCLM (-k))
  let Lpos : WeightedLatticeBanach →L[ℂ] ℂ :=
    (complexE3CoordinateCLM i).comp (weightedLatticePointCLM k)
  have heval : Continuous (fun u : CriticalMildPathBall T R => u.1 τ) :=
    (continuous_eval_const τ).comp continuous_subtype_val
  apply isClosed_eq
  · exact Lneg.continuous.comp heval
  · exact (continuous_neg.comp
      (continuous_star.comp (Lpos.continuous.comp heval)))

private theorem zero_mem_realityPathSet (T R : ℝ) (hR : 0 ≤ R) :
    (⟨0, zero_mem_criticalMildPathBall T R hR⟩ : CriticalMildPathBall T R) ∈
      RealityPathSet T R := by
  intro τ k
  rw [show weightedLatticeCoefficient
      ((⟨0, zero_mem_criticalMildPathBall T R hR⟩ : CriticalMildPathBall T R).1 τ)
        (-k) = 0 by simp [weightedLatticeCoefficient],
    show weightedLatticeCoefficient
      ((⟨0, zero_mem_criticalMildPathBall T R hR⟩ : CriticalMildPathBall T R).1 τ)
        k = 0 by simp [weightedLatticeCoefficient]]
  ext i
  simp [complexConjugate]

/-- **The gap endomap preserves the reality subspace.**  For an
anti-Hermitian datum, the horizon-`n` small-data gap endomap maps the closed
anti-Hermitian path subspace of the radius-`2‖a‖` ball into itself: the
`IccExtend` clamp of a real path is real, and the mild image of a real
continuous path under a real datum is real. -/
theorem gapBallImageNat_mapsTo_reality
    (ν : ℝ) (hν : 0 < ν) {a : WeightedLatticeBanach} (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (hareal : LatticeAntiHermitian a) (n : ℕ) :
    MapsTo (gapBallImageNat ν hν a ha ha16 n)
      (RealityPathSet (↑n) (2 * ‖a‖)) (RealityPathSet (↑n) (2 * ‖a‖)) := by
  intro u hureal τ
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  let ext : ℝ → WeightedLatticeBanach := criticalMildPathExtension (↑n) hn u.1
  have hextreal : ∀ s, LatticeAntiHermitian (ext s) := by
    intro s
    exact hureal (projIcc (0 : ℝ) (↑n) hn s)
  show LatticeAntiHermitian
      (criticalMildImage ν hν a ext
        (criticalMildPathBallExtension_divergenceFree hn u) τ.1 τ.2.1)
  refine criticalMildImage_antiHermitian ν hν hareal ext
      (continuous_criticalMildPathExtension (↑n) hn u.1)
      (criticalMildPathBallExtension_divergenceFree hn u) hextreal
      (smallData_hR2 a) τ.2.1 ?_
  intro s _
  exact criticalMildPathBallExtension_norm_le hn u s

/-- Banach's principle restricted to the closed reality subspace produces an
anti-Hermitian fixed point of the horizon-`n` gap endomap. -/
theorem exists_gapBallImageNat_fixedPoint_reality
    (ν : ℝ) (hν : 0 < ν) {a : WeightedLatticeBanach} (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (hareal : LatticeAntiHermitian a) (n : ℕ) :
    ∃ u : CriticalMildPathBall (↑n) (2 * ‖a‖),
      Function.IsFixedPt (gapBallImageNat ν hν a ha ha16 n) u ∧
      (∀ τ : Icc (0 : ℝ) ↑n, LatticeAntiHermitian (u.1 τ)) := by
  let F := gapBallImageNat ν hν a ha ha16 n
  have hc : ContractingWith ⟨(3 * ν⁻¹) * (2 * (2 * ‖a‖)), by positivity⟩ F :=
    gapBallImage_contractingWith ν hν a ha (Nat.cast_nonneg n)
      (smallData_hR2 a) (smallData_gap_budget_le ν hν a ha16)
      (smallData_gap_contraction_lt_one ν hν a ha16)
  have hmaps : MapsTo F (RealityPathSet (↑n) (2 * ‖a‖))
      (RealityPathSet (↑n) (2 * ‖a‖)) :=
    gapBallImageNat_mapsTo_reality ν hν ha ha16 hareal n
  let z : CriticalMildPathBall (↑n) (2 * ‖a‖) :=
    ⟨0, zero_mem_criticalMildPathBall (↑n) (2 * ‖a‖) (smallData_hR2 a)⟩
  obtain ⟨u, hureal, hfix, _⟩ :=
    (hc.restrict hmaps).exists_fixedPoint'
      (isClosed_realityPathSet (↑n) (2 * ‖a‖)).isComplete hmaps
      (zero_mem_realityPathSet (↑n) (2 * ‖a‖) (smallData_hR2 a))
      (edist_ne_top z (F z))
  exact ⟨u, hfix, hureal⟩

/-- **Reality of the chosen local gap path.**  The `Classical.choose`
horizon-`n` gap path equals the real fixed point constructed above by
uniqueness, so it is anti-Hermitian at every time of `Icc 0 n`. -/
theorem localGapPath_antiHermitian
    (ν : ℝ) (hν : 0 < ν) {a : WeightedLatticeBanach} (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (hareal : LatticeAntiHermitian a) (n : ℕ)
    (τ : Icc (0 : ℝ) ↑n) :
    LatticeAntiHermitian ((localGapPath ν hν a ha ha16 n).1 τ) := by
  obtain ⟨u, hu, hureal⟩ :=
    exists_gapBallImageNat_fixedPoint_reality ν hν ha ha16 hareal n
  have h_eq : u = localGapPath ν hν a ha ha16 n :=
    gapBallImageNat_fixedPoint_unique ν hν a ha ha16 n hu
      (localGapPath_isFixedPt ν hν a ha ha16 n)
  rw [← h_eq]
  exact hureal τ

/-- **Reality of the glued global gap path.**  Each evaluation of
`globalGapPath` is an evaluation of a real local gap path at horizon `⌈t⌉₊`. -/
theorem globalGapPath_antiHermitian
    (ν : ℝ) (hν : 0 < ν) {a : WeightedLatticeBanach} (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (hareal : LatticeAntiHermitian a) (t : NNReal) :
    LatticeAntiHermitian (globalGapPath ν hν a ha ha16 t) :=
  localGapPath_antiHermitian ν hν ha ha16 hareal ⌈(t : ℝ)⌉₊
    ⟨t, ⟨t.2, Nat.le_ceil _⟩⟩

/-- **Reality transport of the global small-data driver — the premise named
and undischarged by `smallDataGlobal_navierStokesBody_on_positiveTime`.**
For an anti-Hermitian datum, the all-time driver is anti-Hermitian at every
real time (negative times reuse the value at zero through `toNNReal`). -/
theorem smallDataGlobalDriver_antiHermitian
    (ν : ℝ) (hν : 0 < ν) {a : WeightedLatticeBanach} (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (hareal : LatticeAntiHermitian a) (s : ℝ) :
    LatticeAntiHermitian (smallDataGlobalDriver ν hν a ha ha16 s) :=
  globalGapPath_antiHermitian ν hν ha ha16 hareal s.toNNReal

/-- **Goal L, official equation — unconditional for anti-Hermitian data.**
The exact-conditional
`CriticalMildSmallDataGlobal.smallDataGlobal_navierStokesBody_on_positiveTime`
with its single undischarged premise removed: for a small (threshold
`rawMildViscosity ν₀ / 16`), divergence-free, **anti-Hermitian** datum, the
reconstructed physical mild velocity satisfies the repository's official
momentum equation at every strictly positive time of every finite horizon,
driven by the global small-data mild trajectory itself.  No transport
assumption remains. -/
theorem smallDataGlobal_navierStokesBody_on_positiveTime_of_real
    (ν₀ : ℝ) (hν₀ : 0 < ν₀) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ rawMildViscosity ν₀ / 16) (hadf : LatticeDivergenceFree a)
    (hareal : LatticeAntiHermitian a)
    {T t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ∀ x : Space, timeDerivative
        (physicalMildVelocity (smallDataGlobalDriver (rawMildViscosity ν₀)
          (by unfold rawMildViscosity; positivity) a ha ha16)) t x +
        convection
          (physicalMildVelocity (smallDataGlobalDriver (rawMildViscosity ν₀)
            (by unfold rawMildViscosity; positivity) a ha ha16)) t x =
      ν₀ • laplacian
          (physicalMildVelocity (smallDataGlobalDriver (rawMildViscosity ν₀)
            (by unfold rawMildViscosity; positivity) a ha ha16)) t x -
        pressureGradient
          (physicalMildPressure (smallDataGlobalDriver (rawMildViscosity ν₀)
            (by unfold rawMildViscosity; positivity) a ha ha16)) t x +
        zeroForce t x :=
  smallDataGlobal_navierStokesBody_on_positiveTime ν₀ hν₀ a ha ha16 hadf
    (fun s => smallDataGlobalDriver_antiHermitian
      (rawMildViscosity ν₀) (by unfold rawMildViscosity; positivity)
      ha ha16 hareal s) ht

/-- **Hermitian symmetry of the physical carrier at every time.**  The
anti-Hermitian raw driver transports through the `i/(2π)` normalization to
the Hermitian coefficient symmetry of a real-valued physical periodic
velocity, for every real time of the global small-data trajectory. -/
theorem smallDataGlobalDriver_physicalHermitian
    (ν₀ : ℝ) (hν₀ : 0 < ν₀) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ rawMildViscosity ν₀ / 16)
    (hareal : LatticeAntiHermitian a) (t : ℝ) :
    LatticeHermitian (physicalCarrier (smallDataGlobalDriver
      (rawMildViscosity ν₀) (by unfold rawMildViscosity; positivity)
      a ha ha16 t)) :=
  latticeHermitian_physicalCarrier
    (smallDataGlobalDriver_antiHermitian (rawMildViscosity ν₀)
      (by unfold rawMildViscosity; positivity) ha ha16 hareal t)

#print axioms Navier.Analysis.CriticalMildGlobalTrajectoryReality.gapBallImageNat_mapsTo_reality
#print axioms Navier.Analysis.CriticalMildGlobalTrajectoryReality.exists_gapBallImageNat_fixedPoint_reality
#print axioms Navier.Analysis.CriticalMildGlobalTrajectoryReality.localGapPath_antiHermitian
#print axioms Navier.Analysis.CriticalMildGlobalTrajectoryReality.globalGapPath_antiHermitian
#print axioms Navier.Analysis.CriticalMildGlobalTrajectoryReality.smallDataGlobalDriver_antiHermitian
#print axioms Navier.Analysis.CriticalMildGlobalTrajectoryReality.smallDataGlobal_navierStokesBody_on_positiveTime_of_real
#print axioms Navier.Analysis.CriticalMildGlobalTrajectoryReality.smallDataGlobalDriver_physicalHermitian

end Navier.Analysis.CriticalMildGlobalTrajectoryReality
