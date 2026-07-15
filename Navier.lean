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
import Navier.Analysis.OfficialABEncoding
import Navier.Analysis.LerayProjection
import Navier.Analysis.VectorCalculus
import Navier.Analysis.EnergyPressureCancellation
import Navier.Analysis.EnergyPressureIntegral
import Navier.Analysis.Vorticity
import Navier.Analysis.ViscosityTransport
import Navier.Analysis.ViscosityAdmissibility
import Navier.Analysis.ViscosityForceDecay
import Navier.Analysis.ViscosityEndpoints
import Navier.Scaling
import Navier.EnergyObstruction
import Navier.ConventionBridges
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
import Navier.Disposition
import Navier.Frontier
import Navier.ClayFrontier
import Navier.AxiomAudit

/-!
# Navier

Umbrella module for the official A--D surfaces, parabolic and viscosity
covariance, viscosity-one endpoint reductions, critical `L3` scaling,
point-breakdown consumers, vector-calculus leaves, algebraic scaling facts,
the R7 symmetrized finite Fourier tests, proof-bearing dispositions, finite
frontier map, and raw public axiom audit.
The Clay endpoint remains conjectural; importing this module does not claim a
solution of the Millennium Prize Problem.
-/
