import Navier.Analysis.CriticalMildRealityPreservation
import Navier.Analysis.CriticalMildPathFixedPoint

/-!
# Reality of the constructed critical mild trajectory

This continues the literal convolution sign law through the Bochner integral
and the actual local contraction construction.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildTrajectoryReality

open MeasureTheory Set Topology
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
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.CriticalMildRealityPreservation

/-- The literal nonlinear Bochner integral stays in the anti-Hermitian raw
carrier when the evolving path does. -/
theorem criticalMildDuhamel_antiHermitian
    (ν : ℝ) (hν : 0 < ν) (u : ℝ → WeightedLatticeBanach)
    (huc : Continuous u) (hdiv : ∀ s, LatticeDivergenceFree (u s))
    (hreal : ∀ s, LatticeAntiHermitian (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    LatticeAntiHermitian (criticalMildDuhamel ν hν u hdiv t) := by
  intro k
  have hint := integrableOn_criticalMildPathIntegrand
    ν hν u huc hdiv hR ht huR
  ext i
  let Lneg : WeightedLatticeBanach →L[ℂ] ℂ :=
    (complexE3CoordinateCLM i).comp (weightedLatticePointCLM (-k))
  let Lpos : WeightedLatticeBanach →L[ℂ] ℂ :=
    (complexE3CoordinateCLM i).comp (weightedLatticePointCLM k)
  change Lneg (∫ s in Ioc 0 t, criticalMildPathIntegrand ν hν u hdiv t s) =
    -star (Lpos (∫ s in Ioc 0 t, criticalMildPathIntegrand ν hν u hdiv t s))
  rw [← Lneg.integral_comp_comm hint, ← Lpos.integral_comp_comm hint]
  change (∫ s, Lneg (criticalMildPathIntegrand ν hν u hdiv t s)
      ∂volume.restrict (Ioc 0 t)) =
    -star (∫ s, Lpos (criticalMildPathIntegrand ν hν u hdiv t s)
      ∂volume.restrict (Ioc 0 t))
  have hconj :
      star (∫ s, Lpos (criticalMildPathIntegrand ν hν u hdiv t s)
        ∂volume.restrict (Ioc 0 t)) =
        ∫ s, star (Lpos (criticalMildPathIntegrand ν hν u hdiv t s))
          ∂volume.restrict (Ioc 0 t) := by
    symm
    exact integral_conj
  rw [hconj, ← MeasureTheory.integral_neg]
  apply integral_congr_ae
  filter_upwards with s
  have hs := criticalMildPathIntegrand_antiHermitian
    ν hν u hdiv hreal t s k
  have hcoord := congrArg (fun z : ComplexSpace => z i) hs
  simpa [Lneg, Lpos, weightedLatticePointCLM, complexE3CoordinateCLM,
    complexConjugate] using hcoord

/-- The same-weight heat flow preserves raw anti-Hermitian coefficients. -/
theorem weightedHeatFlow_antiHermitian
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    {u : WeightedLatticeBanach} (hu : LatticeAntiHermitian u) :
    LatticeAntiHermitian (weightedHeatFlow ν τ hν hτ u) := by
  intro k
  rw [weightedLatticeCoefficient_weightedHeatFlow,
    weightedLatticeCoefficient_weightedHeatFlow,
    latticeFrequency_neg, hu k]
  exact complexFrequencyHeatLeray_neg_antiHermitian ν τ
    (latticeFrequency k) (weightedLatticeCoefficient u k)

theorem LatticeAntiHermitian.add {u v : WeightedLatticeBanach}
    (hu : LatticeAntiHermitian u) (hv : LatticeAntiHermitian v) :
    LatticeAntiHermitian (u + v) := by
  intro k
  rw [congrFun (weightedLatticeCoefficient_add u v) (-k),
    congrFun (weightedLatticeCoefficient_add u v) k]
  simp only [Pi.add_apply]
  rw [hu k, hv k]
  ext i
  simp [complexConjugate]
  abel

/-- The exact mild self-map preserves reality whenever its input path and
initializer are real in the raw normalization. -/
theorem criticalMildImage_antiHermitian
    (ν : ℝ) (hν : 0 < ν) {u₀ : WeightedLatticeBanach}
    (hu₀ : LatticeAntiHermitian u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hdiv : ∀ s, LatticeDivergenceFree (u s))
    (hreal : ∀ s, LatticeAntiHermitian (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    LatticeAntiHermitian (criticalMildImage ν hν u₀ u hdiv t ht) := by
  apply LatticeAntiHermitian.add
  · exact weightedHeatFlow_antiHermitian ν t hν.le ht hu₀
  · exact criticalMildDuhamel_antiHermitian
      ν hν u huc hdiv hreal hR ht huR

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
    simp only [RealityPathSet, mem_setOf_eq, mem_iInter]
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

/-- The actual contraction endomap maps the closed reality subspace to itself. -/
theorem criticalMildPathBallImage_mapsTo_reality
    (ν : ℝ) (hν : 0 < ν) {u₀ : WeightedLatticeBanach}
    (hu₀ : LatticeAntiHermitian u₀) {T R : ℝ}
    (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbudget : ‖u₀‖ + (2 * Real.sqrt T / Real.sqrt ν) * R ^ 2 ≤ R) :
    MapsTo (criticalMildPathBallImage ν hν u₀ hT hR hbudget)
      (RealityPathSet T R) (RealityPathSet T R) := by
  intro u hureal τ
  let ext := criticalMildPathExtension T hT u.1
  have hextreal : ∀ s, LatticeAntiHermitian (ext s) := by
    intro s
    exact hureal (projIcc (0 : ℝ) T hT s)
  exact criticalMildImage_antiHermitian ν hν hu₀ ext
    (continuous_criticalMildPathExtension T hT u.1)
    (criticalMildPathBallExtension_divergenceFree hT u) hextreal hR τ.2.1
    (fun s _ => criticalMildPathBallExtension_norm_le hT u s)

/-- Banach contraction on the closed anti-Hermitian subspace constructs an
actual real raw mild trajectory, together with its literal mild equation. -/
theorem exists_criticalMild_trajectory_antiHermitian
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (hu₀ : LatticeAntiHermitian u₀) {T R : ℝ}
    (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbudget : ‖u₀‖ + (2 * Real.sqrt T / Real.sqrt ν) * R ^ 2 ≤ R)
    (hcontr : (4 * Real.sqrt T / Real.sqrt ν) * R < 1) :
    ∃ u : CriticalMildPathBall T R,
      (∀ τ : Icc (0 : ℝ) T, LatticeAntiHermitian (u.1 τ)) ∧
      (∀ τ : Icc (0 : ℝ) T,
        LatticeHermitian (physicalCarrier (u.1 τ))) ∧
      (∀ (τ : Icc (0 : ℝ) T) (x : Space),
        complexEuclideanPoint
            (complexOfReal
              (physicalFourierReconstruction (physicalCarrier (u.1 τ)) x)) =
          complexFourierReconstruction (physicalCarrier (u.1 τ)) x) ∧
      (∀ τ : Icc (0 : ℝ) T,
        u.1 τ = criticalMildImage ν hν u₀
          (criticalMildPathExtension T hT u.1)
          (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) := by
  let F := criticalMildPathBallImage ν hν u₀ hT hR hbudget
  let z : CriticalMildPathBall T R :=
    ⟨0, zero_mem_criticalMildPathBall T R hR⟩
  have hc := criticalMildPathBallImage_contractingWith
    ν hν u₀ hT hR hbudget hcontr
  have hmaps : MapsTo F (RealityPathSet T R) (RealityPathSet T R) :=
    criticalMildPathBallImage_mapsTo_reality ν hν hu₀ hT hR hbudget
  obtain ⟨u, hureal, hfix, _⟩ :=
    (hc.restrict hmaps).exists_fixedPoint'
      (isClosed_realityPathSet T R).isComplete hmaps
      (zero_mem_realityPathSet T R hR) (edist_ne_top z (F z))
  have hphysical : ∀ τ : Icc (0 : ℝ) T,
      LatticeHermitian (physicalCarrier (u.1 τ)) := fun τ =>
    latticeHermitian_physicalCarrier (hureal τ)
  refine ⟨u, hureal, hphysical, ?_, ?_⟩
  · intro τ x
    exact complexOfReal_physicalFourierReconstruction (hphysical τ) x
  intro τ
  have hτ := congrArg (fun w : CriticalMildPathBall T R => w.1 τ) hfix
  simpa [F, Function.IsFixedPt, criticalMildPathBallImage] using hτ.symm

end Navier.Analysis.CriticalMildTrajectoryReality
