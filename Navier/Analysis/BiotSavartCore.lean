import Navier.Analysis.Vorticity

/-!
# Core Schwartz curl for the Biot--Savart chain

This upstream file keeps the actual curl inside Schwartz space without
depending on the later BKM bootstrap.  The namespace and theorem names are the
same ones consumed by the bootstrap and the physical-space recovery chain.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix LineDeriv

namespace Navier.Analysis.BealeKatoMajda

open Navier
open Navier.Analysis.Vorticity

/-- The coordinate curl of a Schwartz velocity, retained as a Schwartz map. -/
def staticCurlSchwartz (u : SchwartzVelocity) : SchwartzVelocity :=
  ∑ i : Fin 3,
    SchwartzMap.postcompCLM (𝕜 := ℝ)
      (crossProduct (basisVector i)).toContinuousLinearMap
      (∂_{basisVector i} u)

@[simp] theorem staticCurlSchwartz_apply (u : SchwartzVelocity) (x : Space) :
    staticCurlSchwartz u x = staticCurl (⇑u) x := by
  simp [staticCurlSchwartz, staticCurl,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

end Navier.Analysis.BealeKatoMajda
