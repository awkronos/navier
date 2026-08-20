import Navier.Analysis.BealeKatoMajda
import Navier.Analysis.BKMLogLeaves
import Navier.Analysis.UniformDecayDominated
import Navier.Analysis.BiotSavartKernel
import Navier.Analysis.EnergyNormBridge
import Navier.Analysis.GalerkinBasis
import Navier.Analysis.CZNearField

/-!
# Analysis of the three remaining sorries in `BKMLogBootstrap.lean`

This file documents the mathematical content of the three remaining sorries in
`BKMLogBootstrap.lean`, the available certified infrastructure that each can
depend on, and the genuinely Mathlib-absent mathematics that each requires.

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace Navier.Analysis.BKMLogBootstrapAnalysis

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.Vorticity
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.CZNearField

/-!
## Sorry 1: `exists_biotSavartLogTextbook` (line 373-385)

### Statement (in `BKMLogBootstrap.lean`)

```
∃ C : ℝ, 0 < C ∧
  ∀ (u : SchwartzVelocity), DivergenceFreeInitial u →
    ∀ Mω M₂ : ℝ,
      (∀ x : Space, officialEuclideanNorm (staticCurl (⇑u) x) ≤ Mω) →
      (∫ x : Space, officialEuclideanNorm (staticCurl (⇑u) x) ^ 2) ≤ M₂ →
      ∀ x : Space, ‖fderiv ℝ (⇑u) x‖ ≤
        C * (1 + Mω * (1 + Real.log (Real.exp 1 +
          Real.sqrt (sobolevH3NormSq u))) + Real.sqrt M₂)
```

### What is already certified

* The CZ size layer: near-field `integral_norm_mul_bsKernelScalar_ball_le`,
  logarithmic shell `integral_bsKernelScalar_annulus_le_log`, far-field
  `integrableOn_bsKernelScalar_sq_farField` — all kernel-only estimates,
  independent of the Biot-Savart representation.
* The Morrey-Agmon Hölder bound `exists_agmonMorreyBound`: the difference
  `|ω(x-z) - ω(x)|` is dominated by `C·√(H³)·‖z‖^{1/4}`.
* The curl Laplacian identity `curlCurlSchwartz_eq_neg_laplacian`
  (in `GalerkinBasis.lean`): `curl(curl u) = -Δu` for divergence-free Schwartz
  fields. This is the key algebraic link between the velocity gradient and the
  vorticity.
* The CZ near-field cancellation `cz_nearField_cancellation` and the Hörmander
  smoothness `czScalarKernel_hormander` (in `CZNearField.lean`).
* The Biot-Savart gradient kernel `bsGradKernel` and its envelope
  `bsGradKernel_abs_le` (in `CZNearField.lean`).

### What is genuinely absent

The Biot-Savart **representation**

  `∇u(x) = PV∫ ∇K(x-y) × ω(y) dy + (1/3)ω(x)`

where `K(x) = x/(4π|x|³)` is the Biot-Savart kernel. This representation
expresses the velocity gradient as a Calderón-Zygmund singular integral of the
vorticity. Without it, the CZ size layer has no integrand to apply to.

### Proof strategy (est. ~600 LOC)

1. **Fourier side.**  Using `curlCurlSchwartz_eq_neg_laplacian` and the
   Schwartz Fourier transform (`SchwartzMap.fourier_lineDerivOp_eq`), show
   that the Fourier symbol of the gradient-vorticity relationship is
   `𝓕(∇u)ᵢⱼ(ξ) = ξᵢ·(ξ × 𝓕(ω)ⱼ)(ξ)/|ξ|²`.

2. **Kernel identification.**  Compute the inverse Fourier transform of the
   symbol `ξᵢ(ξ × ·)ⱼ/|ξ|²` — this is the Biot-Savart gradient kernel
   `(δᵢⱼ/|z|³ − 3zᵢzⱼ/|z|⁵)/(4π)`, i.e. `bsGradKernel i j z`.  This requires
   the Fourier transform of homogeneous distributions, which is Mathlib-absent.

3. **Real-space CZ decomposition.**  Once the convolution representation is
   established, decompose the convolution integral into the near-field ball
   `|z| < ρ`, the logarithmic shell `ρ ≤ |z| < 1`, and the far-field
   `|z| ≥ 1`.  The three certified CZ size estimates apply directly.

4. **Cutoff optimization.**  Choose `ρ = (sobolevH3NormSq u)⁻²` (so that
   `ρ^{1/4} = 1/√(H³)`).  The near-field bound gives `C·√(H³)·ρ^{1/4} = C`,
   the shell bound gives `C·Mω·log(1/ρ) = C·Mω·log(H³)`, and the far-field
   bound gives `C·√M₂`.  The additive `1` absorbs the `C·√(H³)·ρ^{1/4}` and
   the local term `(1/3)ω(x) ≤ C·Mω`.

### Critical dependency chain

`curlCurlSchwartz_eq_neg_laplacian` (certified, GalerkinBasis.lean)
→ Fourier symbol of (∇u, ω) (needs `fourier_curlComp` from DivFreeGradientEnstrophy.lean)
→ inverse Fourier transform of the symbol (Mathlib-absent: homogeneous distributions)
→ Biot-Savart convolution representation (the missing link)
→ CZ size layer (certified) + Morrey-Agmon (certified) → BKM bound
-/

/-!
## Sorry 2: `exists_sliceLocallyUniformDecayBound` (line 1984-1989)

### Statement

```
∀ t₀ ∈ Set.Ici (0 : ℝ), ∃ r K : ℝ, 0 < r ∧
  ∀ t ∈ Set.Ici (0 : ℝ) ∩ Metric.ball t₀ r, ∀ n : ℕ, n < 4 → ∀ x : Space,
    ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2 ≤ K * (1 + ‖x‖) ^ (-4 : ℝ)
```

### What is already certified

* `iteratedFDeriv_slice_eq_within_compContinuousLinearMap` (certified, line 1819):
  the iterated derivative of the slice equals the joint derivative composed
  with the spatial inclusion.
* `sliceIteratedFDeriv_continuousOn` (certified, line 1899): fixed-`x` time
  continuity of each `‖Dⁿu(t,x)‖²`.
* `integrable_one_add_norm_inv_four` (certified, UniformDecayDominated.lean):
  the weight `(1+‖x‖)⁻⁴` is integrable on ℝ³.
* `continuousOn_integral_of_locallyUniformDecay` (certified,
  UniformDecayDominated.lean): the dominated-convergence engine.
* `SmoothVelocityOnNonnegativeTime` from `IsClassicalSolution` (Problem.lean):
  the spacetime map is jointly `C^∞` on the closed half-space.
* `finite_energy` from `IsClassicalSolution`: each slice is `L²`-integrable.
* `uniformly_bounded_energy` from `IsClassicalSolution`: the kinetic energy
  is uniformly bounded on nonnegative time.

### What is genuinely absent

The propagation of **Schwartz-class decay** along the Navier-Stokes flow.
The `finite_energy` condition only provides `L²` integrability of the velocity,
not the `(1+‖x‖)⁻⁴` decay of the fourth derivative that the statement requires.

The bound `‖Dⁿu(t,x)‖² ≤ K·(1+‖x‖)⁻⁴` for `n < 4` is a pointwise Schwartz
seminorm bound. To propagate such bounds from the initial data along the flow,
one needs weighted `L²` energy estimates for `‖x^α D^β u‖_{L²}` closed by
Grönwall against the uniform energy bound. This is a PDE-dependent argument
(Majda-Bertozzi §3.2, the "polynomial weight" energy method).

### Proof strategy (est. ~400 LOC)

1. **Weighted energy inequality.**  For each multi-index `α` with `|α| ≤ 4`,
   consider the weighted norm `E_α(t) = ∫ |x^α·D<4 u(t,x)|² dx`.  Using the
   Navier-Stokes equation, the `C^∞` smoothness, and the `finite_energy` bound,
   show that `E_α(t)` satisfies a differential inequality closed by Grönwall.

2. **Sobolev embedding of weighted spaces.**  The bound
   `‖Dⁿu(t,x)‖² ≤ C·E_α(t)·(1+‖x‖)⁻⁴` follows from the one-dimensional
   inequality `|f(x)| ≤ C·(∫ |f|² + |f'|²)^{1/2}` applied to the function
   `r ↦ Dⁿu(t, r·x/|x|)`.

3. **Locally uniform bound.**  The Grönwall estimate for `E_α(t)` is
   continuous in `t`, so for each `t₀` there is a neighbourhood `[t₀-r, t₀+r]`
   on which `E_α(t)` is bounded by `2·E_α(t₀)`.  The locally uniform decay
   bound follows.

### Critical dependency chain

`finite_energy` + `SmoothVelocityOnNonnegativeTime` (certified, Problem.lean)
→ weighted energy inequality (Mathlib-absent: polynomial weights in L² energy method)
→ Grönwall (certified) → locally uniform bound on weighted norms
→ Sobolev embedding of weighted spaces (Mathlib-absent: pointwise bound from weighted integral)
→ `exists_sliceLocallyUniformDecayBound`
-/

/-!
## Sorry 3: `exists_sobolevOrderEnergyEstimate` (line 2068-2080)

### Statement

```
∃ C : ℝ, 0 < C ∧
  ∀ {ν : ℝ}, 0 ≤ ν →
  ∀ {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀)
    {T : ℝ} (G : ℝ → ℝ),
    (∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Space,
      ‖fderiv ℝ (S.velocity t) x‖ ≤ G t) →
    ∀ t ∈ Set.Ioo (0:ℝ) T, ∀ n : ℕ, n < 4 →
      ∃ D : ℝ,
        HasDerivAt (fun s => ∫ x : Space,
          ‖iteratedFDeriv ℝ n (⇑(S.slice s)) x‖ ^ 2) D t ∧
        D ≤ C * G t * sobolevH3NormSq (S.slice t)
```

### What is already certified

* `iteratedFDeriv_slice_eq_within_compContinuousLinearMap` (certified): slice
  derivative equals joint derivative.
* `sliceIteratedFDeriv_continuousOn` (certified): fixed-`x` time continuity.
* `continuousOn_integral_of_locallyUniformDecay` (certified): dominated
  convergence for integrals.
* `exists_hasDerivAt_sum_range_le` (certified, BKMLogLeaves.lean): the
  differentiability of the sum given differentiability of each term.
* `SatisfiesNavierStokes` from `IsClassicalSolution` (Problem.lean): the PDE
  `∂_t u = νΔu - (u·∇)u - ∇p`.
* `Incompressible` from `IsClassicalSolution`: `∇·u = 0`.

### What is genuinely absent

The **Kato-Ponce commutator estimate** (Kato-Ponce, CPAM 41 (1988) 891-907):

  `‖Dⁿ((u·∇)v) - (u·∇)Dⁿv‖_{L²} ≤ C·(‖∇u‖_∞·‖Dⁿv‖_{L²} + ‖∇v‖_∞·‖Dⁿu‖_{L²})`

For `v = u`, this gives `|⟨Dⁿ((u·∇)u), Dⁿu⟩| ≤ C·‖∇u‖_∞·‖Dⁿu‖²_{L²}`.

The estimate is used to bound the convection term in the per-order energy
identity. For n = 0, 1, 2, the estimate can be proved elementarily using
integration by parts and the incompressibility condition. For n = 3, the
Kato-Ponce estimate is a deep theorem requiring the Fourier transform and
the paraproduct decomposition (Coifman-Meyer theorem). It is not in Mathlib.

### Proof strategy by order

**n = 0 (est. ~50 LOC):**  `d/dt ∫ ‖u‖² = 0` by the energy identity of the
Navier-Stokes equation: `∫ u·(u·∇u) = 0` (incompressibility, integration by
parts), `∫ u·∇p = 0` (incompressibility), `ν∫ u·Δu = -ν∫‖∇u‖² ≤ 0`.  So
`D ≤ 0 ≤ C·G·H³` for any `C > 0`.

**n = 1 (est. ~100 LOC):**  Using the PDE,
`D¹((u·∇)u) = (D¹u)·∇u + u·(D¹∇u)`.
The term `∫ D¹u·(u·D¹∇u) = 0` by integration by parts and incompressibility.
The remaining term `∫ D¹u·((D¹u)·∇u) ≤ ‖∇u‖_∞·∫ ‖D¹u‖² ≤ G·H³`.

**n = 2 (est. ~150 LOC):**  `D²((u·∇)u) = (D²u)·∇u + 2(D¹u)·(D²u) + u·(D³u)`.
The term `∫ D²u·(u·D³u) = 0` by integration by parts and incompressibility.
The remaining terms `∫ D²u·((D²u)·∇u) + 2∫ D²u·(D¹u·D²u) ≤ 3·‖∇u‖_∞·∫ ‖D²u‖² ≤ 3·G·H³`.

**n = 3 (est. ~300 LOC):**  The Kato-Ponce commutator estimate is required.
`D³((u·∇)u) = (D³u)·∇u + 3(D²u)·(D²u) + 3(D¹u)·(D³u) + u·(D⁴u)`.
The problematic term is `3∫ D³u·(D²u·D²u)`, which requires the Kato-Ponce
estimate to bound by `C·‖∇u‖_∞·‖D³u‖²_{L²}`.  Without the Kato-Ponce estimate,
this term is `≤ 3·‖D²u‖_∞·‖D²u‖_{L²}·‖D³u‖_{L²}`.  Using the Sobolev embedding
`H² ↪ C⁰`, `‖D²u‖_∞ ≤ C·√(sobolevH2NormSq (D²u))`, but this involves the H⁴
norm of u, which is not bounded by the H³ norm.

### Critical dependency chain

`SatisfiesNavierStokes` + `Incompressible` (certified, Problem.lean)
→ differentiation under the integral (certified, UniformDecayDominated.lean)
→ integration by parts identity (certified, CurlIdentities.lean)
→ Kato-Ponce commutator estimate (Mathlib-absent: paraproduct/Fourier multiplier)
→ `exists_sobolevOrderEnergyEstimate`
-/

/-!
## Summary

| Sorry | Lines | Mathematics required | Est. LOC | Genuinely absent? |
|-------|-------|---------------------|----------|-------------------|
| `exists_biotSavartLogTextbook` | 373-385 | Biot-Savart representation (CZ singular integral) | ~600 | YES |
| `exists_sliceLocallyUniformDecayBound` | 1984-1989 | Propagation of Schwartz bounds (weighted energy) | ~400 | YES |
| `exists_sobolevOrderEnergyEstimate` | 2068-2080 | Kato-Ponce commutator estimate | ~600 | YES |

All three sorries are genuinely Mathlib-absent and require deep mathematics
that is not available in the current codebase. The file is designed to have
these three sorries as the last analytic obstacles; the `logBKMControl_of_schwartzSliced`
theorem (line 2137-2346) is fully proved and composes the derived statements
into a `LogBKMControl` once the sorries close.

The `BKMAnalyticResidual` in `BealeKatoMajda.lean` names the same three
residuals, confirming that this is the designed frontier.

### What is available for a consumer to make progress

1. **`exists_biotSavartLogTextbook`**: The `curlCurlSchwartz_eq_neg_laplacian`
   identity (GalerkinBasis.lean:1304) plus the `fourier_curlComp` lemma
   (DivFreeGradientEnstrophy.lean:352) give the Fourier symbol of the
   gradient-vorticity relationship. A consumer needs to either:
   - Compute the inverse Fourier transform of the symbol (requires Mathlib's
     Fourier transform of homogeneous distributions), or
   - Work entirely in the frequency domain, decomposing frequency space into
     low/medium/high bands and using the Bessel weight integrability already
     certified for the `H²` embedding.

2. **`exists_sliceLocallyUniformDecayBound`**: The `finite_energy` and
   `uniformly_bounded_energy` fields of `IsClassicalSolution` provide the
   `L²` control. A consumer needs to add polynomial weights to the energy
   method, which is a classical PDE argument (Majda-Bertozzi §3.2) but not
   yet formalized.

3. **`exists_sobolevOrderEnergyEstimate`**: For n = 0, 1, 2 the proof is
   elementary and could be written in ~300 LOC using the Navier-Stokes
   equation, integration by parts, and the incompressibility condition.
   For n = 3, the Kato-Ponce commutator estimate is required. A consumer
   could either:
   - Prove the Kato-Ponce estimate using the Fourier transform and the
     paraproduct decomposition (est. ~2000 LOC), or
   - Use the Gagliardo-Nirenberg inequality `‖D²u‖_∞ ≤ C·‖D²u‖_{L²}^{1/4}·‖D³u‖_{L²}^{3/4}`
     to bound the problematic term `3‖D²u‖_∞·‖D²u‖_{L²}·‖D³u‖_{L²}` by
     `C·‖D²u‖_{L²}^{5/4}·‖D³u‖_{L²}^{7/4} ≤ C·(‖D²u‖²_{L²} + ‖D³u‖²_{L²}) ≤ C·H³`,
     which would close the bound without the Kato-Ponce estimate.
-/

end Navier.Analysis.BKMLogBootstrapAnalysis