import Navier.Analysis.GalerkinModeData

/-!
# Leray–Hopf weak existence: the assembled headline, downstream of the basis

This file is the downstream home of the three declarations that used to sit in
`Navier.Analysis.LerayWeak`: `exists_galerkinModeData`,
`galerkin_approximation_exists`, and `leray_weak_existence` — same namespace,
same names, same types, so no consumer changes.

**Why the relocation (2026-08-18, lane NK2; prescribed by the wave-N3
receipt).**  The finite-mode Galerkin construction is assembled in
`Navier.Analysis.GalerkinBasis.exists_galerkinModeData` from the certified
divergence-free basis, modulo exactly the three named residuals
`hspace`/`htime`/`hweak`.  The upstream copy in `LerayWeak` was a *duplicate*
`sorry` of that same construction which could never consume it:
`GalerkinBasis.lean` imports `LerayWeak.lean`, so the upstream file sits
strictly below the basis chain (the import cycle `LerayWeak → GalerkinBasis →
LerayWeak` is forbidden).  The duplicate is deleted; the declarations live
here, one import hop above both layers.  The remaining `sorryAx` reach of the
headline `leray_weak_existence` is exactly the named residuals
`hspace`/`htime`/`hweak` (GalerkinBasis) and `exists_lerayLimitData`
(LerayWeak) — no monolithic upstream sorry any more.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.LerayWeak

/-- **Finite-mode Galerkin construction** [Temam, *NSE* III.3;
Constantin–Foias, *NSE* II; Leray, Acta Math. 63 (1934) §§18–20].
Projecting NSE onto the first `m` divergence-free modes of the certified
basis gives a `C¹` ODE on a finite subspace whose field
`F_m = −ν A_m + P_m B` is dissipative-plus-skew; the certified coefficient
flow, modal realization, a priori bounds, and initial-mode `L²` convergence
are assembled in `GalerkinBasis.exists_galerkinModeData`.  The genuinely
analytic estimates — spatial translation equicontinuity (`hspace`), time
equicontinuity (`htime`), and asymptotic weak-form consistency (`hweak`) —
remain NAMED RESIDUALS of that construction; this declaration is the
composition that brings the assembled data back to the `LerayWeak`
namespace. -/
theorem exists_galerkinModeData (ν : ℝ) (hν : 0 < ν)
    (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀) :
    Nonempty (GalerkinModeData ν u₀) :=
  GalerkinBasis.exists_galerkinModeData ν hν u₀ hu₀

/-- **Galerkin approximants exist** — a composition of the finite-mode data
construction with the certified transport
`galerkinApproximation_of_modeData`. -/
theorem galerkin_approximation_exists (ν : ℝ) (hν : 0 < ν)
    (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀) :
    Nonempty (GalerkinApproximation ν u₀) :=
  galerkinApproximation_of_modeData ν u₀ (exists_galerkinModeData ν hν u₀ hu₀).some

/-- **Leray weak existence** [Leray, Acta Math. 63 (1934); Temam, *Navier–
Stokes Equations* Ch. III].  For every viscosity `ν > 0` and every
divergence-free Schwartz datum there is a global Leray–Hopf weak solution.

This is a genuine composition of the Galerkin decomposition:
`galerkin_approximation_exists` builds the uniformly-bounded approximants and
`leray_of_galerkinApproximation` (via `aubin_lions_l2loc_compactness`) passes
to the limit.  The remaining `sorryAx` reach lives in named,
reference-grounded, strictly-lower leaves — `hspace`/`htime`/`hweak` in
`GalerkinBasis` and `exists_lerayLimitData` in `LerayWeak` — not here. -/
theorem leray_weak_existence :
    ∀ ν : ℝ, 0 < ν →
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∃ u : VelocityEvolution, IsLerayHopfWeakSolution ν u₀ u := by
  intro ν hν u₀ hu₀
  exact (galerkin_approximation_exists ν hν u₀ hu₀).elim
    (fun G => leray_of_galerkinApproximation ν hν u₀ hu₀ G)

end Navier.Analysis.LerayWeak
