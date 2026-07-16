import Navier.Problem
import Navier.OfficialProblem
import Navier.OfficialSurfaceSignatures
import Navier.Analysis.Covariance
import Navier.Analysis.CriticalL3
import Navier.Analysis.CriticalL3Integrable
import Navier.Analysis.CriticalLp
import Navier.Analysis.CriticalProfileAction
import Navier.Analysis.ESSInputs
import Navier.Analysis.CKNCylinderGeometry
import Navier.Analysis.CKNMeasureTransport
import Navier.Analysis.CKNDensity
import Navier.Analysis.CKNIntegralScaling
import Navier.Analysis.OfficialABEncoding
import Navier.Analysis.EnergyNormBridge
import Navier.Analysis.EnergyOfficialClause
import Navier.Analysis.LerayProjection
import Navier.Analysis.FrequencyHeatLeray
import Navier.Analysis.FrequencyDuhamel
import Navier.Analysis.ComplexLerayProjection
import Navier.Analysis.ComplexLerayNorm
import Navier.Analysis.ComplexFrequencyHeatLeray
import Navier.Analysis.VectorCalculus
import Navier.Analysis.EnergyPressureCancellation
import Navier.Analysis.EnergyPressureIntegral
import Navier.Analysis.EnergyConvectionCancellation
import Navier.Analysis.EnergyConvectionIntegral
import Navier.Analysis.EnergyTimeDerivative
import Navier.Analysis.EnergyViscousDissipation
import Navier.Analysis.EnergyViscousIntegral
import Navier.Analysis.EnergyPointwiseBalance
import Navier.Analysis.EnergyInstantaneousIntegralBalance
import Navier.Analysis.EnergyDerivativeUnderIntegral
import Navier.Analysis.Vorticity
import Navier.Analysis.BealeKatoMajda
import Navier.Analysis.BKMLogBootstrap
import Navier.Analysis.Enstrophy
import Navier.Analysis.FrequencyCascadeObstruction
import Navier.Analysis.MultiFrequencyMild
import Navier.Analysis.LerayWeak
import Navier.Analysis.ViscosityTransport
import Navier.Analysis.ViscosityAdmissibility
import Navier.Analysis.ViscosityForceDecay
import Navier.Analysis.ViscosityEndpoints
import Navier.Scaling
import Navier.EnergyObstruction
import Navier.ConventionBridges
import Navier.Analysis.SchwartzConventionEquivalence
import Navier.Analysis.CoordinatePDEBridge
import Navier.Analysis.HalfSpaceSmoothnessBridge
import Navier.Breakdown.MaximalNonextension
import Navier.Breakdown.Restriction
import Navier.Breakdown.ForceRecovery
import Navier.Breakdown.OfficialCDEncoding
import Navier.Routes.R7.ExactSymbol
import Navier.Routes.R7.Triad
import Navier.Routes.R7.ScaledTriad
import Navier.Routes.R7.PhaseSymbol
import Navier.Routes.R7.SymmetrizedPhase
import Navier.Routes.R7.SymmetrizedWitness
import Navier.Routes.R7.WeightedShellTransfer
import Navier.Routes.R7.FieldLeakage
import Navier.Routes.R7.FullFieldLeakage
import Navier.Routes.R7.FullSixModePairClassification
import Navier.Routes.R7.FullSixModeReceiverRates
import Navier.Routes.R7.FullSixModeBalance
import Navier.Routes.R7.GeneratedSupport
import Navier.Routes.R7.FiniteConvolution
import Navier.Routes.R7.FiniteAmplitudeDynamics
import Navier.Routes.R7.FiniteReality
import Navier.Routes.R7.FiniteSupportClosureObstruction
import Navier.Routes.R7.GeneratedSupportStrictGrowth
import Navier.Disposition
import Navier.Frontier
import Navier.ClayFrontier
import Navier.AxiomAudit

/-!
# Navier

Umbrella module for the official A--D surfaces, parabolic and viscosity
covariance, viscosity-one endpoint reductions, critical `L3` scaling,
point-breakdown consumers, vector-calculus and guarded energy-identity leaves,
algebraic scaling facts, frequencywise heat--Leray infrastructure, the R7
symmetrized and recursively generated finite Fourier tests, proof-bearing
dispositions, finite frontier map, and raw public axiom audit.
The Clay endpoint remains conjectural; importing this module does not claim a
solution of the Millennium Prize Problem.
-/
