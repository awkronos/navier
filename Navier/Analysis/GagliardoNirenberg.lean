import Navier.Analysis.BealeKatoMajda
import Navier.Analysis.BKMLogBootstrap
import Navier.Analysis.SobolevEmbedding

/-!
# Gagliardo-Nirenberg interpolation inequalities for the BKM assembly

The Gagliardo-Nirenberg (GN) inequality on ℝⁿ states that for 0 ≤ j < m,
1 ≤ p, q, r ≤ ∞, and j/m ≤ a ≤ 1,

  ‖Dʲu‖_{L^p} ≤ C·‖Dᵐu‖_{L^r}^a·‖u‖_{L^q}^{1-a}

where 1/p = j/n + a·(1/r − m/n) + (1−a)·(1/q).
Reference: Nirenberg, Ann. Scuola Norm. Sup. Pisa (3) 13 (1959), 115–162.

## Honest analysis

The specific inequality suggested in `BKMLogBootstrapAnalysis.lean` (line 296),

  `‖D²u‖_∞ ≤ C·‖D²u‖_{L²}^{1/4}·‖D³u‖_{L²}^{3/4}`

is **not a valid inequality for all Schwartz functions on ℝ³**.  Under spatial
scaling u_δ(x) = u(δx), the LHS scales as δ² while the RHS scales as δ^{5/4}.
For δ → ∞ (spread-out functions), the RHS cannot dominate the LHS with a
universal constant.  The standard GN parameter equation with p = ∞, r = 2,
q = 2, j = 2, m = 3, n = 3 requires a = 7/6 > 1, which is outside the
admissible range j/m ≤ a ≤ 1.

The correct approach for the n = 3 case of `exists_sobolevOrderEnergyEstimate`
is the Kato-Ponce commutator estimate (Kato-Ponce, CPAM 41 (1988) 891-907),
a genuinely Mathlib-absent theorem requiring the paraproduct decomposition
(~2000 LOC).  The GN inequality does not provide a shortcut.

## What IS available

The existing Sobolev embedding theorems (all kernel-clean or carrying a single
named residual):

* `exists_agmonSupBound` — H²(ℝ³) ↪ L^∞ : ‖u‖_∞ ≤ C·√(sobolevH2NormSq u)
* `sobolevEmbeddingDomination_H3` — H³(ℝ³) ↪ L^∞ : ‖u‖_∞ ≤ C·√Ms
* `sobolevH3NormSq_dominates_H2` — ∫ ‖D²u‖² ≤ sobolevH3NormSq u

None of these provide a bound on `‖D²u‖_∞` without controlling D⁴u or D⁵u.
The missing inequality is genuinely Mathlib-absent.

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace Navier.Analysis.GagliardoNirenberg

open Navier
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.SobolevEmbedding

/-!
## Pointwise norm bound on the second derivative

The Schwartz seminorm at order (0, 2) bounds the pointwise norm of the second
iterated derivative.  This is a direct consequence of
`SchwartzMap.norm_iteratedFDeriv_le_seminorm`.  No further analytic content.
-/

/-- **Pointwise bound on the second derivative by the Schwartz seminorm.**
For any Schwartz velocity field u and any point x, the norm of the second
iterated derivative at x is bounded by the Schwartz seminorm of order (0, 2),
which is finite for any Schwartz field. -/
theorem norm_iteratedFDeriv_two_le_seminorm (u : SchwartzVelocity) (x : Space) :
    ‖iteratedFDeriv ℝ 2 (⇑u) x‖ ≤ (SchwartzMap.seminorm ℝ 0 2 : SchwartzVelocity → ℝ) u :=
  u.norm_iteratedFDeriv_le_seminorm ℝ 2 x

end Navier.Analysis.GagliardoNirenberg