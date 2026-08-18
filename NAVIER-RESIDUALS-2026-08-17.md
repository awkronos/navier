# Navier Residual Ledger — 2026-08-17

**UPDATED 2026-08-17 — Wave Ω580-N2 discrepancy audit**

The previous snapshot reported "9 compiler sorries" vs "12 source-grep sorries" (diff=3).
This update reconciles that discrepancy with the current build state.

## Discrepancy resolution

| Bucket | Previous | Current | Notes |
|--------|----------|---------|-------|
| Compiler `declaration uses sorry` | 9 | 10 | One GalerkinBasis sorry now visible despite build error |
| Source `^ *sorry$` blocks | 12 | 24 | The 12 counted "declarations" (one per theorem), the 24 counts all `sorry` blocks (some theorems use >1 `sorry`) |
| Diff | 3 | 14 | The 3-gap was GalerkinBasis sorries in declarations the compiler could not reach (build regression at line 3550) |
| Remainder of 14-gap | — | 14 | Multi-sorry theorems (GalerkinBasis `integral_fderiv_sq_eq_enstrophy_of_divFree` has 2 sorries; GalerkinBasis `exists_galerkinModeData` has 2; EnstrophyForPartialClassical has 10 sorries in multiple declarations) |

### The original 3-gap (now stale)

At ledger snapshot `42acbbe` (build GREEN, 8730 jobs):
- **Compiler (9)**: 3 BKMLogBootstrap + 2 LerayWeak + 4 ConditionalRegularity
- **Grep (12)**: above 9 + 3 GalerkinBasis sorries (hspace, htime, hweak)
- **Cause of gap**: GalerkinBasis sorries lived in code not reachable by the main import chain's elaboration path at that snapshot. The build still passed because GalerkinBasis compiled independently (its `.olean` was present).

As of `af10eb8`, **GalerkinBasis has a build error** at line 3550 (`unexpected token '/--'; expected 'lemma'`) plus missing identifiers `schwartz_differentiable`, `coordinateDerivativeField` at lines 3560-3562. The 4 sorry blocks inside it (lines 3559, 3654, 3657, 3679) are now in code the compiler cannot reach. This is N1's file — not touched by this wave.

### Current N2 sorry inventory

| File | Line | Declaration | Tier | Status |
|------|------|-------------|------|--------|
| BKMLogBootstrap | 376 | `exists_biotSavartLogTextbook` | CONJECTURE | Requires Biot-Savart representation (singular integral) |
| BKMLogBootstrap | 1499 | `exists_locallyUniformSliceDecay` | CONJECTURE | Second conjunct proved (`sliceIteratedFDeriv_continuousOn`); first conjunct requires PDE decay bound |
| BKMLogBootstrap | 1575 | `exists_sobolevOrderEnergyEstimate` | CONJECTURE | Kato-Ponce commutator ~600 LOC |
| LerayWeak | 1495 | `exists_galerkinModeData` | SORRY-in-progress | Blocked on 3 GalerkinBasis sub-obligations (hspace/htime/hweak) + GalerkinBasis build error |
| LerayWeak | 5526 | `exists_lerayLimitData` | CONDITIONAL | Blocked on `exists_galerkinModeData` + uniform test function control |

No dead-code sorries found in N2 files (BKMLogBootstrap, LerayWeak).

**Build**: succeeds for all files except GalerkinBasis (N1 error). Five `declaration uses sorry` in N2 scope.

---

## Original entry (2026-08-17)

**Build**: GREEN, 8730 jobs, 12 sorries  
**Commit**: `42acbbe`  
**Date**: 2026-08-17  

All 12 sorries are named, reference-grounded residuals — bare `sorryAx` in all
cases; no custom axioms leak from closed theorems.  Spot-check: `#print axioms
Navier.Analysis.LerayWeak.spaceEquicontinuous_of_dissipation_bound` returns
`{propext, Classical.choice, Quot.sound}` only.

---

## File: `Navier/Analysis/GalerkinBasis.lean` (3 sorries)

### 1. GalerkinBasis.lean:3642 — `hspace` (space equicontinuity)

| Field | Value |
|---|---|
| **Tier** | `SORRY-in-progress` |
| **Statement** | `SpaceEquicontinuous (W.modalApprox cChoice)` |
| **Blocks** | `exists_galerkinLimitData` (Galerkin compactness assembly) |
| **Approach exists** | `spaceEquicontinuous_of_dissipation_bound` (CERTIFIED, LerayWeak.lean:1249).  The dissipation bound is available via `modalApprox_uniformEnstrophyBound` (GalerkinBasis.lean:??).  For the finite-mode divergence-free truncation, `‖ω‖_{L²} = ‖∇u_m‖_{L²}` holds, so the enstrophy bound *is* a gradient bound and the Brezis Prop. 9.3 modulus `δ = √(ε/(C+1))` applies. |
| **What blocks** | Wiring the enstrophy bound into the dissipation-bound lemma's `hdiss` hypothesis. |

### 2. GalerkinBasis.lean:3645 — `htime` (time equicontinuity)

| Field | Value |
|---|---|
| **Tier** | `CONJECTURE` |
| **Statement** | `TimeEquicontinuous (W.modalApprox cChoice)` |
| **Blocks** | `exists_galerkinLimitData` (Galerkin compactness assembly) |
| **Approach exists** | `modalApprox_timeEquicontinuous_of_uniformDerivative` (GalerkinBasis.lean:2737) — requires a **uniform derivative bound** `‖-(ν·A·c) + B(c)‖ ≤ K` for the projected ODE vector field. |
| **What blocks** | No uniform derivative bound lemma exists for the specific `stokesOperator` + `convectionOperator` combination on the finite-mode truncation.  A Simon-type estimate (Reed–Simon I, §II.1) would supply `∂ₜu_m ∈ L²(0,T; H⁻¹)`, from which time equicontinuity would follow by the Aubin–Lions compactness argument (~100 LOC). |

### 3. GalerkinBasis.lean:3667 — `hweak` (weak consistency)

| Field | Value |
|---|---|
| **Tier** | `SORRY-in-progress` |
| **Statement** | `∀ phi : DivergenceFreeTestFunction, lim_{m→∞} weakFormResidual nu u0 (W.modalApprox cChoice m) phi = 0` |
| **Blocks** | `exists_galerkinLimitData` (Galerkin compactness assembly) |
| **Approach exists** | Galerkin equation written against each mode, then limit passage through the certified fixed-time spatial limit passages: `tendsto_integral_of_dominated_l2loc`, `tendsto_integral_convection_of_l2loc`, and their assembly `tendsto_integral_weakPairingDensity_of_l2loc` (all in `LerayWeak.lean`). |
| **What blocks** | Interchange of `lim_m` with `∫_{(0,T]} dt`: `DivergenceFreeTestFunction` imposes no uniform-in-time control on Schwartz seminorms, so no `m`-uniform integrable majorant exists.  Three routes: (i) add a uniform-in-time seminorm field to the test function class (statement-level change); (ii) avoid `t`-majorant entirely; (iii) use a limit representative with compactly supported slices (Aubin–Lions does not provide this). |

---

## File: `Navier/Analysis/LerayWeak.lean` (2 sorries)

### 4. LerayWeak.lean:1495 — `exists_galerkinModeData`

| Field | Value |
|---|---|
| **Tier** | `SORRY-in-progress` |
| **Statement** | `Nonempty (GalerkinModeData ν u₀)` — constructs the finite-mode truncation with ODE forward extension, equicontinuity, measurability, and initial convergence. |
| **Blocks** | `galerkin_approximation_exists` (feed-forward to `leray_of_galerkinApproximation`) |
| **Approach exists** | The three `hspace`/`htime`/`hweak` sub-obligations above are themselves certified breakouts.  `jointly_measurable` is discharged by `galerkinModalApprox_jointlyMeasurable` (CERTIFIED).  `initial_converges_L2` by `proj_initial_converges_L2`.  `bound_nonneg` / `bound` by `modalApprox_uniformEnstrophyBound` + the dissipation integral banked in `EnergyDissipation`. |
| **What blocks** | The same 3 sub-obligations above (hspace, htime, hweak).  Algebraically: 0 BLOCKS summing the certified parts. |

### 5. LerayWeak.lean:5526 — `exists_lerayLimitData`

| Field | Value |
|---|---|
| **Tier** | `CONDITIONAL` |
| **Statement** | `Nonempty (LerayLimitData ν u₀)` — extracts a limit from the Galerkin approximants via Banach–Alaoglu / Aubin–Lions on the bounded sequence. |
| **Blocks** | `leray_of_galerkinApproximation` (headline: `∃ u, IsLerayHopfWeakSolution ν u₀ u`) |
| **Approach exists** | From the compactness of the Galerkin sequence (supplied by `exists_galerkinModeData`), the limit extraction is a textbook functional-analytic argument (~200 LOC): Banach–Alaoglu for `L∞L²(0,T; L²)`, Aubin–Lions for `L²(0,T; H¹₀) ∩ H¹(0,T; H⁻¹) → L²(0,T; L²_loc)`, then verify the limit is a Leray–Hopf weak solution. |
| **What blocks** | Blocked on `exists_galerkinModeData` (sorry #4).  Inductive: once #4 closes, the limit extraction is purely functional analysis against certified `LerayWeak` infrastructure. |

---

## File: `Navier/Analysis/BKMLogBootstrap.lean` (3 sorries)

### 6. BKMLogBootstrap.lean:376 — `exists_biotSavartLogTextbook`

| Field | Value |
|---|---|
| **Tier** | `CONJECTURE` |
| **Statement** | Biot–Savart representation `∇u = PV(∇K ∗ ω)` for divergence-free Schwartz fields, which converts the BKM kernel estimates into a bound on `‖∇u‖_∞`. |
| **Blocks** | BKM blow-up criterion field `biotSavartLogGradientBound` |
| **Approach exists** | Elementary kernel algebra and far-field `L²` tail bound certified in `BiotSavartKernel`.  Near-field cancellation named as a residual in `SingularIntegralPrelims`.  The Biot–Savart representation for *divergence-free Schwartz fields* specifically (not the full Calderón–Zygmund theory) is the remaining piece — not yet in Mathlib, and the repo's `BiotSavartKernel` stops short of `∇∗(K∗ω)` as a pointwise equality. |
| **What blocks** | The singular-integral understanding of the Biot–Savart kernel.  The `H³ ↪ L^∞` Sobolev embedding (`SobolevEmbedding`) carries its own disclosed `sorryAx` (Plancherel assembly), so even the closing embedding is not yet residual-free. |

### 7. BKMLogBootstrap.lean:1499 — `exists_locallyUniformSliceDecay`

| Field | Value |
|---|---|
| **Tier** | `CONJECTURE` |
| **Statement** | Along a Schwartz-sliced classical solution, for each order `n < 4`, there is a single integrable `g : Space → ℝ` dominating `‖D^n u(t,·)‖²` uniformly for `t ≥ 0`. |
| **Blocks** | Local uniform `t`-continuity of the `H³` Sobolev energy (`BKMLogLeaves` continuity chain) |
| **Approach exists** | Fixed-`x` time continuity (`sliceIteratedFDeriv_continuousOn`), dominated-convergence step itself, and the assembly of four orders into `H³` norm (`continuousOn_sum_range`) are all certified. |
| **What blocks** | Propagation of Schwartz bounds with *locally-in-time uniform seminorms* along the Navier–Stokes flow — the PDE-dependent lemma that dominated convergence via `joint smoothness + Schwartz slices` is *provably insufficient* (witness: `v t x := t³·ψ(t² x)`, `L²` norm is constant for all `t ≠ 0`, jumps at `t = 0`).  Must use the Navier–Stokes clauses of `IsClassicalSolution` (`equation`, `incompressible`, `finite_energy`, `uniformly_bounded_energy`). |

### 8. BKMLogBootstrap.lean:1575 — `exists_sobolevOrderEnergyEstimate`

| Field | Value |
|---|---|
| **Tier** | `CONJECTURE` |
| **Statement** | Along a Schwartz-sliced classical solution with pointwise gradient majorant `G`, for each `n < 4` the order-`n` energy is differentiable on `t > 0` with `d/dt ≤ C·G(t)·‖u(t)‖²_{H³}`. |
| **Blocks** | BKM `H³` energy estimate (Majda–Bertozzi Prop. 3.7; Kato–Ponce 1988) |
| **Approach exists** | Summation of the four orders into a single `hasDerivAt_sum_range_le` certified in `BKMLogLeaves`.  Pressure term vanishes (divergence-free); viscous term `−2ν∫‖D^{n+1}u‖² ≤ 0`. |
| **What blocks** | The Kato–Ponce commutator bound `|⟨D^n(u·∇u), D^n u⟩| ≤ C‖∇u‖_∞‖u‖²_{H^n}` for `n ≤ 3` — not yet in Mathlib.  Estimated ~600 LOC. |

---

## File: `Navier/Analysis/ConditionalRegularity.lean` (4 sorries)

### 9. ConditionalRegularity.lean:731 — `prodiSerrin_layer_farField_bounded`

| Field | Value |
|---|---|
| **Tier** | `CONJECTURE` |
| **Statement** | With per-slice `L^p` integrability (`p > 3`), a partial classical solution is uniformly bounded on `[0,δ]` for `‖x‖ ≥ ϱ` (outer region, initial layer). |
| **Blocks** | Prodi–Serrin conditional regularity |
| **Approach exists** | Kato mild-solution short-time `L^∞` bound + heat semigroup `L^p → L^∞` smoothing.  `HeatSemigroupSmoothing` now lands Gaussian kernel, `L^s` norms, and convolution smoothing bound `|∫ G_t^ν(x−y) f(y)| ≤ C t^{-3/(2r)} ‖f‖_r`. |
| **What blocks** | No Duhamel representation of an arbitrary `PartialClassicalSolution` in the repo — integration by parts against the heat kernel with boundary terms controlled by spatial derivative decay (not supplied by the per-slice `L^p` hypothesis alone).  The Leray projector as a pointwise object is also absent from Mathlib. |

### 10. ConditionalRegularity.lean:808 — `prodiSerrin_interior_outerRegion_bounded`

| Field | Value |
|---|---|
| **Tier** | `CONJECTURE` |
| **Statement** | The critical mixed-norm bound `L^q(0,T; L^p)` (`3/p + 2/q = 1`) gives a uniform velocity bound on `(δ,T)` for `‖x‖ ≥ ϱ`. |
| **Blocks** | Prodi–Serrin conditional regularity |
| **Approach exists** | Parabolic Moser/De Giorgi iteration, Caccioppoli inequality for local energy, Biot–Savart representation of pressure.  `ParabolicCaccioppoli` now lands the first two rungs: `local_energy_balance` and the numeric De Giorgi–Moser engine `deGiorgiMoser_tendsto_zero`.  `BiotSavartKernel` lands the kernel's elementary algebra and far-field `L²` tail bound. |
| **What blocks** | The integrated Caccioppoli inequality `cutoff_local_energy_inequality` (blocked on cutoff integration by parts vs local energy identity, and an `L^r` pressure bound).  The near-field Calderón–Zygmund cancellation remains a named residual in `SingularIntegralPrelims`. |

### 11. ConditionalRegularity.lean:878 — `constantinFefferman_layer_farField_bounded`

| Field | Value |
|---|---|
| **Tier** | `CONJECTURE` |
| **Statement** | With uniform `L²` mass bracket, a finite-energy partial classical solution is uniformly bounded on `[0,δ]` for `‖x‖ ≥ ϱ` (outer region, initial layer). |
| **Blocks** | Constantin–Fefferman conditional regularity |
| **Approach exists** | Same Kato mild-solution short-time `L^∞` bound as #9, with the `L²` mass replacing `L^p` slice control. |
| **What blocks** | Identical to #9: Duhamel representation of `PartialClassicalSolution` + pointwise Leray projector not available.  The kernel `L^s` norms and convolution layer exist (`HeatSemigroupSmoothing`, `heatKernel_convolution_smoothing_le`). |

### 12. ConditionalRegularity.lean:971 — `constantinFefferman_interior_outerRegion_bounded`

| Field | Value |
|---|---|
| **Tier** | `CONJECTURE` |
| **Statement** | The uniform `L²` mass bracket + depleted cross-product bound gives a uniform velocity bound on `(δ,T)` for `‖x‖ ≥ ϱ`. |
| **Blocks** | Constantin–Fefferman conditional regularity |
| **Approach exists** | Enstrophy identity (`vorticityTransportEquation` in `Navier.Analysis.Enstrophy`), `H² ↪ L^∞` Sobolev embedding, vortex-stretching algebra.  The singular-integral layer is the same Mathlib gap as in the BKM tower. |
| **What blocks** | `Enstrophy` lands the pointwise vortex-stretching identity but the integral enstrophy budget remains open.  `BiotSavartKernel` stops at the far-field tail; near-field cancellation in `SingularIntegralPrelims`.  `SobolevEmbedding` carries its own disclosed Plancherel `sorryAx`. |

---

## Tier summary

| Tier | Count | Files |
|---|---|---|
| `SORRY-in-progress` | 3 | GalerkinBasis (hspace), GalerkinBasis (hweak), LerayWeak (exists_galerkinModeData) |
| `CONDITIONAL` | 1 | LerayWeak (exists_lerayLimitData) |
| `CONJECTURE` | 8 | GalerkinBasis (htime), BKMLogBootstrap (3), ConditionalRegularity (4) |

## Axiom spot-check

`#print axioms spaceEquicontinuous_of_dissipation_bound` → `{propext, Classical.choice, Quot.sound}`.
No custom axioms, no `sorryAx`.  THEOREM-tier closed work remains sound.