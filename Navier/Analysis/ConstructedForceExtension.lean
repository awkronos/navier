import Navier.Breakdown.NativeConstructionEndpoint
import Navier.Construction.R3ActualCandidate
import Navier.Analysis.HalfSpaceSmoothnessBridge

/-!
# A global smooth extension for the constructed force

The selected candidate already carries a force smooth on all Euclidean
spacetime.  Compact spatial localization preserves that global smoothness,
as do coordinate transport and viscosity rescaling.  Thus the constructed
statement-C force has an explicit global smooth extension at every positive
viscosity, without invoking the general Seeley extension theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Navier.Analysis.ConstructedForceExtension

open Navier
open Navier.Analysis.EuclideanPDETransport
open Navier.Analysis.HalfSpaceSmoothnessBridge
open Navier.Analysis.ViscosityTransport
open Navier.Analysis.ViscosityAdmissibility

/-- Multiplication by the outer spatial cutoff preserves the global
smoothness retained by the selected force. -/
theorem compactForce_contDiff
    {f : EVelocityField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Navier.Construction.R3CompactCandidate.compactForce f) :=
  (Navier.Construction.R3CompactCandidate.outerCutoff_smooth.comp contDiff_snd).smul hf

/-- The exact selected compact candidate retains global, rather than merely
half-space, smoothness of its force. -/
theorem selected_compact_candidate_contDiff :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ f := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, hforcing, _⟩ :=
    Navier.Construction.ActualCandidateAssembly.selected_witness
  exact ⟨_, _, _, Navier.Construction.R3CompactCandidate.of_localized_fields hc,
    compactForce_contDiff hforcing⟩

/-- Euclidean-to-native coordinate transport preserves global spacetime
smoothness of a force. -/
theorem nativeForce_contDiff {f : EVelocityField}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => nativeForce f z.1 z.2) := by
  have hi := hf.comp spacetimeToEuclidean_contDiff
  have ho := toNative.contDiff.comp hi
  simpa [nativeForce, spacetimeToEuclidean, Function.comp_def] using ho

/-- The exact selected native force is globally smooth on all real
spacetime, before any viscosity rescaling. -/
theorem selected_native_force_contDiff :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ (fun z : ℝ × Space => nativeForce f z.1 z.2) := by
  obtain ⟨u, p, f, hcandidate, hf⟩ := selected_compact_candidate_contDiff
  exact ⟨u, p, f, hcandidate, nativeForce_contDiff hf⟩

/-- Time dilation and constant amplitude scaling preserve global smoothness
of a force.  Positivity is unnecessary for this analytic fact. -/
theorem viscosityScaledForce_contDiff (a : ℝ) {f : ForceField}
    (hf : ContDiff ℝ ∞ (fun z : ℝ × Space => f z.1 z.2)) :
    ContDiff ℝ ∞
      (fun z : ℝ × Space => viscosityScaledForce a f z.1 z.2) := by
  have hcomp := hf.comp (contDiff_viscosityTimeMap a)
  have hscaled := hcomp.const_smul (a ^ 2)
  simpa only [viscosityScaledForce, viscosityTimeMap, Function.comp_apply] using hscaled

/-- A globally smooth force is its own explicit half-space extension. -/
theorem globalExtension_of_contDiff {f : ForceField}
    (hf : ContDiff ℝ ∞ (fun z : ℝ × Space => f z.1 z.2)) :
    Nonempty (HalfSpaceSmoothExtension f) := by
  exact ⟨{
    extension := fun z => f z.1 z.2
    smooth := hf
    agrees := fun _ _ _ => rfl
  }⟩

/-- Statement C strengthened by requiring the chosen admissible force to
come with an explicit globally smooth spacetime extension. -/
def WholeSpaceBreakdownWithGloballySmoothForce : Prop :=
  ∀ nu : ℝ, 0 < nu →
    ∃ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ ∧
      ∃ f : ForceField, ForcedDataRapidDecay f ∧
        ContDiff ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) ∧
        Nonempty (HalfSpaceSmoothExtension f) ∧
        ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
          IsClassicalSolution nu f u₀ u p

/-- The strengthened surface directly implies the original official
alternative C by forgetting the explicit extension witness. -/
theorem WholeSpaceBreakdownWithGloballySmoothForce.toWholeSpaceBreakdown
    (h : WholeSpaceBreakdownWithGloballySmoothForce) :
    ProblemStatements.WholeSpaceBreakdown := by
  intro nu hnu
  obtain ⟨u₀, hu₀, f, hf, _, _, hbad⟩ := h nu hnu
  exact ⟨u₀, hu₀, f, hf, hbad⟩

/-- The exact selected construction inhabits the strengthened endpoint at
every positive viscosity.  Its explicit extension is the globally defined
selected force itself after compact localization, coordinate transport, and
viscosity rescaling. -/
theorem constructedWholeSpaceBreakdownWithGloballySmoothForce :
    WholeSpaceBreakdownWithGloballySmoothForce := by
  obtain ⟨eu, ep, ef, hcandidate, hef⟩ := selected_compact_candidate_contDiff
  have hnative : ContDiff ℝ ∞
      (fun z : ℝ × Space => nativeForce ef z.1 z.2) :=
    nativeForce_contDiff hef
  have hadmissible : ForcedDataRapidDecay (nativeForce ef) :=
    R3CompactCandidate.nativeForce_forcedDataRapidDecay hcandidate
  intro nu hnu
  refine ⟨viscosityScaledSchwartzDatum nu 0,
    divergenceFreeInitial_viscosityScaledSchwartzDatum nu 0
      ProblemStatements.divergenceFreeInitial_zero,
    viscosityScaledForce nu (nativeForce ef),
    Navier.Analysis.ViscosityForceDecay.forcedDataRapidDecay_viscosityScaled
      nu hnu (nativeForce ef) hadmissible,
    viscosityScaledForce_contDiff nu hnative,
    globalExtension_of_contDiff (viscosityScaledForce_contDiff nu hnative), ?_⟩
  rintro ⟨u, p, hsolution⟩
  have hback := isClassicalSolution_viscosity_to_one
    nu hnu (viscosityScaledForce nu (nativeForce ef))
      (viscosityScaledSchwartzDatum nu 0) u p hsolution
  rw [viscosityScaledForce_inv nu hnu.ne' (nativeForce ef),
    viscosityScaledSchwartzDatum_inv nu hnu.ne' 0] at hback
  exact Navier.Construction.ComparatorBridge.compact_candidate_excludes_global_solution
    hcandidate (IsClassicalSolution.toGlobalSolutionRn hback)

/-- The strengthened selected-force endpoint preserves the original exact
statement-C theorem. -/
theorem constructedWholeSpaceBreakdown :
    ProblemStatements.WholeSpaceBreakdown :=
  constructedWholeSpaceBreakdownWithGloballySmoothForce.toWholeSpaceBreakdown

#print axioms selected_compact_candidate_contDiff
#print axioms selected_native_force_contDiff
#print axioms constructedWholeSpaceBreakdownWithGloballySmoothForce
#print axioms constructedWholeSpaceBreakdown

end Navier.Analysis.ConstructedForceExtension
