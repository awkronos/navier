import Navier.Analysis.BiotSavartKernel
import Navier.Analysis.Vorticity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Singular-integral preliminaries: log optimization and the BKM shape reduction

This file builds the algebraic infrastructure that reduces the Biot–Savart log
inequality (the hardest Mathlib-absent input of the Beale–Kato–Majda criterion)
to its genuinely deep core: the Calderón–Zygmund near-field cancellation bound.

## Certified here (no sorry)

* `log_subadditive_prod` — `log(1+ab) ≤ log(1+a) + log(1+b)`, the key
  log-subadditivity governing how the cutoff optimization introduces the `log⁺`.
* `sqrt_le_one_add_self` — `√s ≤ 1+s`, absorbing the root into the linear term.
* `log_absorption` — `1 + M(1+log(1+L)) ≤ (1+M)(1+log(1+L))`, the constant
  absorption step used in the BKM assembly chain.
* `bkm_shape_absorption` — the three-term version with `√M₂`, the exact algebraic
  step from `logBKMControl_of_schwartzSliced` extracted as a named lemma.
* `sobolev_root_absorption` — `C·√Ms ≤ C·(1+Ms)`.

## Honest residual

The Calderón–Zygmund theorem (`L^∞ → BMO` / weak-`(1,1)` for homogeneous
kernels on `ℝ³`; Stein, *Singular Integrals* 1970 Ch. II §4; Grafakos §4.3;
genuinely Mathlib-absent) is named in `BealeKatoMajda.lean` as
`BKMAnalyticResidual.biotSavartLogInequality`.

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace Navier.Analysis.SingularIntegralPrelims

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BiotSavartKernel

/-!
## Elementary log inequalities
-/

/-- **Log-subadditivity on products.**  For `a, b ≥ 0`,
`log(1 + a·b) ≤ log(1 + a) + log(1 + b)`.

Follows from `1 + ab ≤ (1+a)(1+b)` and the monotonicity of `log`. -/
theorem log_subadditive_prod {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.log (1 + a * b) ≤ Real.log (1 + a) + Real.log (1 + b) := by
  have h1 : (0 : ℝ) < 1 + a * b := by nlinarith
  have h2 : (0 : ℝ) < 1 + a := by nlinarith
  have h3 : (0 : ℝ) < 1 + b := by nlinarith
  have hkey : 1 + a * b ≤ (1 + a) * (1 + b) := by nlinarith
  have hlog := Real.log_le_log h1 hkey
  rwa [Real.log_mul (ne_of_gt h2) (ne_of_gt h3)] at hlog

/-- **`log` is nonnegative on `[1, ∞)`.** -/
theorem log_nonneg_of_ge_one {Y : ℝ} (hY : 1 ≤ Y) :
    0 ≤ Real.log Y :=
  Real.log_nonneg hY

/-- **Square-root domination.**  For `s ≥ 0`, `√s ≤ 1 + s`. -/
theorem sqrt_le_one_add_self {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt s ≤ 1 + s := by
  nlinarith [sq_nonneg (1 - Real.sqrt s), Real.sq_sqrt hs,
    Real.sqrt_nonneg s]

/-- **The log-absorption (constant bookkeeping) lemma.**  For `M, L ≥ 0`,
`1 + M·(1 + log(1+L)) ≤ (1+M)·(1 + log(1+L))`. -/
theorem log_absorption {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) :
    1 + M * (1 + Real.log (1 + L)) ≤
      (1 + M) * (1 + Real.log (1 + L)) := by
  have hlog : 0 ≤ Real.log (1 + L) :=
    Real.log_nonneg (by nlinarith)
  nlinarith

/-!
## The BKM shape absorption (assembly-chain algebra)
-/

/-- **The BKM three-term absorption lemma.**  For `Mω, L, M₂ ≥ 0`,

  `1 + Mω·(1 + log(1+L)) + √M₂ ≤ (1 + Mω + √M₂)·(1 + log(1+L))`.

This is the exact algebraic step (proven inline via `nlinarith` in
`logBKMControl_of_schwartzSliced`, line 458 of `BKMLogBootstrap.lean`) that
absorbs the Biot–Savart additive bound into the multiplicative log-linear
Grönwall rate.  Extracted as a named, reusable lemma. -/
theorem bkm_shape_absorption {Mω L M₂ : ℝ}
    (hMω : 0 ≤ Mω) (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂) :
    1 + Mω * (1 + Real.log (1 + L)) + Real.sqrt M₂ ≤
      (1 + Mω + Real.sqrt M₂) * (1 + Real.log (1 + L)) := by
  have hlog : 0 ≤ Real.log (1 + L) :=
    Real.log_nonneg (by nlinarith)
  have hsqrt : 0 ≤ Real.sqrt M₂ := Real.sqrt_nonneg _
  nlinarith

/-- **Sobolev root absorption.**  `C·√Ms ≤ C·(1+Ms)` for `Ms, C ≥ 0` —
absorbs the Sobolev root into the linear control term (velocity-domination
step of the BKM assembly). -/
theorem sobolev_root_absorption {Ms C : ℝ} (hMs : 0 ≤ Ms) (hC : 0 ≤ C) :
    C * Real.sqrt Ms ≤ C * (1 + Ms) := by
  exact mul_le_mul_of_nonneg_left (sqrt_le_one_add_self hMs) hC

/-- The Calderón–Zygmund theorem is the genuinely Mathlib-absent deep input.
Named as a residual so the assembly chain can cite the open leaf precisely. -/
inductive CalderonZygmundResidual where
  | czWeakTypeBound
  | czBMOBound
  deriving DecidableEq, Repr

end Navier.Analysis.SingularIntegralPrelims
