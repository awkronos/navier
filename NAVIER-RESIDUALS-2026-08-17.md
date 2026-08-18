# Navier Residual Ledger — 2026-08-17

**UPDATED 2026-08-18 — Wave N5 count reconciliation (compiler-verified at `2c69626`)**

This supersedes the 2026-08-17 Wave Ω580-N2 audit that previously occupied this
header.  That audit was measured against a stale or divergent checkout: on `main`
at `2c69626` there is **no GalerkinBasis build error** (the file elaborates clean,
exit 0), there are exactly **12** source `sorry` tokens — not 24 — and no
`EnstrophyForPartialClassical` file exists in this checkout.  The corrected,
compiler-verified picture:

## Count reconciliation (2026-08-18, HEAD `2c69626`)

| Measure | Count | Basis |
|---|---|---|
| Compiler `declaration uses sorry` warnings | **10** | per-file `lake env lean` receipts below; every file exit 0, zero errors |
| Source `^ *sorry$` tokens | **12** | 10 sorry-carrying declarations; `GalerkinBasis.exists_galerkinModeData` carries 3 named-residual tokens (`hspace`/`htime`/`hweak`) that roll up into a single compiler declaration warning |
| 2026-08-18 proof-report row | 9 | snapshot at git_head `7e23b4a`, six commits behind HEAD — predates `42acbbe`, which added the GalerkinBasis declaration (+1 compiler warning, +3 source tokens). Temporal snapshot skew, not phantom source annotations |

### Compiler receipts at `2c69626` (`lake env lean <file>`, all exit 0)

| File | Warnings | Declaration sites |
|---|---|---|
| `Navier/Analysis/BKMLogBootstrap.lean` | 3 | :364, :1491, :1563 |
| `Navier/Analysis/LerayWeak.lean` | 2 | :1492, :5522 |
| `Navier/Analysis/ConditionalRegularity.lean` | 4 | :721, :791, :866, :951 |
| `Navier/Analysis/GalerkinBasis.lean` | 1 | :3549 (`exists_galerkinModeData`; tokens at :3642/:3645/:3667) |
| **Total** | **10** | |

Line-number convention: the compiler reports the **declaration** line; the site
inventory below cites the **sorry-token** line (e.g. BKM declaration :364 vs
token :376).  Compare like with like when auditing.

### Coverage notes (count-neutral, zero sorries each)

- `Navier/Analysis/GalerkinHMinusOne.lean` — 269-line infrastructure stub toward
  the `htime` residual, currently **untracked** in this checkout and outside
  every import chain (the proof-report row's `coverage_gap`), no sorries.
- `Navier/Analysis/CutoffEnergyIbp.lean` — added by `2c69626`, not yet imported
  by the umbrella, no sorries.

### The original 9-vs-12 gap (fully explained)

- The **9** was compiler truth at `7e23b4a` (the 2026-08-18 proof-report row's
  git_head): 3 BKMLogBootstrap + 2 LerayWeak + 4 ConditionalRegularity
  declaration warnings.  `GalerkinBasis.exists_galerkinModeData` did not exist
  yet at that snapshot (verified: zero `sorry` tokens in the file at `7e23b4a`).
- The **12** is the source `sorry`-token count from `42acbbe` onward: the same
  9 declaration sites plus the 3 GalerkinBasis named-residual tokens
  (`hspace`, `htime`, `hweak`) that `42acbbe` introduced inside
  `exists_galerkinModeData`.
- Both numbers were correct for their snapshots and measures; no source
  annotation was phantom.  The stale artifacts were this ledger's Ω580-N2
  header claims (24 blocks / 14-gap / build error / `EnstrophyForPartialClassical`),
  now retracted.

---

## Wave 2026-08-18 NK2 — LerayWeak relocation dedup (−1 compiler sorry; compiler-verified)

Receipt: `lake env lean Navier/Analysis/LerayWeak.lean` — exit 0, sorry
warnings **2 → 1** (decl :1492 `exists_galerkinModeData` deleted upstream;
decl `exists_lerayLimitData` now at :5526).  `lake build
Navier.Analysis.LerayWeakExistence` — exit 0, zero sorry warnings (the new
file carries no `sorry` token).  `lake env lean Navier.lean` — exit 0.
`#print axioms`: `leray_weak_existence`, `exists_galerkinModeData`,
`galerkin_approximation_exists`, `exists_lerayLimitData` are all
`[propext, sorryAx, Classical.choice, Quot.sound]` — kernel axioms plus
`sorryAx` via the named residuals only; no custom axioms, no `native_decide`.

### #4 — LerayWeak :1492/:1495 `exists_galerkinModeData` → **RELOCATED-DEDUPED** (duplicate-sorry closure)

N3's recorded follow-up, executed: the three declarations
`exists_galerkinModeData`, `galerkin_approximation_exists`, and
`leray_weak_existence` moved (same namespace, same names, same types) to the
new downstream file `Navier/Analysis/LerayWeakExistence.lean` (`import
Navier.Analysis.GalerkinBasis`), where `exists_galerkinModeData` is the
one-line composition `GalerkinBasis.exists_galerkinModeData`.  The upstream
copy was a **duplicate monolithic `sorry`** of a construction that already
exists downstream modulo exactly `hspace`/`htime`/`hweak`; `LerayWeak` is
strictly upstream of the basis chain and could never consume it.
Deletion-mandate evidence: zero code references to the three declarations
outside `LerayWeak.lean` itself (repo-wide grep 2026-08-18); build green
before and after; full names unchanged, so even nominal consumers are
unaffected.  Effect: estate compiler sorry census **10 → 9** declaration
warnings (LerayWeak 2 → 1; GalerkinBasis unchanged at 1; the new file 0).
When N1's three residuals land, the headline `leray_weak_existence` becomes
`sorryAx`-free with no further wiring.

### #5 — LerayWeak `exists_lerayLimitData` (:5526) → unchanged (N3 typed no-go stands)

Re-checked at this HEAD: the sole residue remains the `hweak` hypothesis of
`exists_lerayLimitData_of_weakClauses` (the `lim_m ↔ ∫ dt` interchange with no
uniform-in-time test-class control).  Nothing committed since N3
(`GalerkinHMinusOne`, `DivFreeGradientEnstrophy`) bears on it.  No edit.

### #10 pressure input — **SHARPENED** (NK2, kernel-clean): the Caccioppoli pressure slot no longer needs `∇p`

`CutoffEnergyIbp.cutoffEnergy_pressure_ibp` (NEW, certified this wave):
one more transport IBP against incompressibility moves the derivative off the
pressure in the capstone identity — `−∫ χ² (u·∇)p = 2∫ p·χ (u·∇χ)` — so the
integrated Caccioppoli assembly consumes the pressure through a
**derivative-free local `L^r` bound on `p` itself**.  Receipt: `lake env lean
Navier/Analysis/CutoffEnergyIbp.lean` exit 0, zero errors, zero `sorry`
tokens; `#print axioms cutoffEnergy_pressure_ibp` =
`[propext, Classical.choice, Quot.sound]` (kernel-clean).  N4's blocker (b)
for #10 (`ConditionalRegularity.prodiSerrin_interior_outerRegion_bounded`)
is thereby reduced from "an `L^r` pressure bound for `∫ χ² ⟨∇p, u⟩`" to: an
`L^r_loc` bound on `p` (Biot–Savart/CZ pressure representation — still a
named residual, genuinely Mathlib-absent) plus the time-integrated assembly
(FTC in `t` of the slice identity).  Sorry census unchanged: 0 tokens in the
file, before and after.

---

## Wave 2026-08-18 N3 — LerayWeak pair attack: two typed no-gos (compiler-verified)

Receipt: `lake env lean Navier/Analysis/LerayWeak.lean` at HEAD — exit 0, zero
errors, exactly 2 `declaration uses sorry` warnings (declarations :1492 and
:5522; tokens :1495/:5526).  Sorry delta this lane: **2 → 2** (no regression,
no new axioms, no statement edits).  No code changed; the closures below were
analyzed to their exact blocking lemmas and are banked as typed no-gos.

### #4 — LerayWeak.lean:1495 `exists_galerkinModeData` → **BLOCKED-ON-N1** (dependency no-go)

The identical construction already exists downstream as
`GalerkinBasis.exists_galerkinModeData` (:3549), fully assembled modulo exactly
the three named residuals `hspace`/`htime`/`hweak` (:3642/:3645/:3667) — lane
N1's active targets this wave.  LerayWeak is strictly *upstream* of the basis
(chain `LerayWeak → SchwartzL2Pairing → GalerkinRawFamily → GalerkinBasis`), so
an in-file closure cannot consume that construction; closing :1495 *is* proving
those three estimates, and any closure via the downstream theorem would still
compile to `declaration uses sorry` until N1 lands.  Basis-free routes were
re-checked and fail: any non-dense mode family fails `weak_consistent`,
including the `span{u₀}` collapse (convection self-pairing `⟨u₀,(u₀·∇)u₀⟩ = 0`
by skew-symmetry, so the 1-mode ODE is linear and global — but the weak-form
residual against transverse tests does not tend to 0).  Component status:
`hspace` is mechanically reducible from certified pieces
(`spaceEquicontinuous_of_dissipation_bound` :1249 + Brezis slice estimate +
banked dissipation budget, per the :1479 docstring); `htime` needs the
`H⁻¹` time-derivative bound (the untracked `GalerkinHMinusOne.lean` stub is
infrastructure toward it); `hweak` is the deep one (nonlinear test-projection
residual, under active reduction in recent commits).
**Follow-up after N1 lands:** relocate `exists_galerkinModeData` /
`galerkin_approximation_exists` / `leray_weak_existence` downstream of
`GalerkinBasis` (or re-export) to wire the headline to :3549.

### #5 — LerayWeak.lean:5526 `exists_lerayLimitData` → **CONDITIONAL, re-diagnosed** (statement-level no-go)

The original entry's "blocked on #4; once #4 closes, purely functional
analysis" is **stale and is corrected here**.  The limit extraction is already
certified in-file: `exists_galerkinLimit_energy_le` (:4325) discharges
`energy_le`/`sq_integrable`/joint measurability, and
`pairing_integrable`/`datum_pairing_integrable` are unconditional via the
certified Cauchy–Schwarz layer.  The sole residue is the hypothesis `hweak` of
the certified reducer `exists_lerayLimitData_of_weakClauses` (:5389): the
`weak_form` `lim_m ↔ ∫_{(0,T]} dt` interchange.  Obstruction (full witness in
the :5488 docstring): `DivergenceFreeTestFunction` (:124) imposes **no
uniform-in-time seminorm control**, so no `m`-uniform integrable majorant
exists.  Re-verified this wave that the same witness also closes the
non-domination standard routes: weak `L²`-spacetime (`∂ₜφ ∉ L²((0,T)×Space)`),
`H⁻¹`–`H¹` duality (`φ ∉ L²(0,T;H¹)`), Vitali/uniform-integrability
(`sup_m ∫_E |g_m| = ∞` on small `E`), and time-truncation
(`‖φ(t)‖_{L²} ↛ 0` at the horizon, so the cut-off error integral does not
vanish).  Not FALSIFIED: under Bochner's junk-value convention both sides can
vanish on the pure witness (`φ(0) = 0`), and the modified witness
(witness + bump, `⟨u₀, φ(0)⟩ ≠ 0`) makes the statement *undetermined* rather
than provably false for the non-explicit Aubin–Lions limit.  Routes remaining
are the docstring's: (i) test-class repair = statement change = owner-level
decision (deliberately not taken), (ii) a non-majorant argument (no known
mathematics), (iii) a compact-slice limit representative (Aubin–Lions does
not provide one).

---

## Wave 2026-08-18 N2 — BKMLogBootstrap triple attack: one DECOMPOSED, two typed no-gos (compiler-verified)

Receipts: `lake env lean Navier/Analysis/BKMLogBootstrap.lean` — exit 0, zero
errors, exactly 3 `declaration uses sorry` warnings (declarations :364, :1498,
:1582; tokens :376, :1503, :1594 — the latter two shifted by the decomposition
below).  Full `lake build` GREEN, zero errors, estate declaration-sorry delta
this lane: **10 → 10** (BKMLogBootstrap 3 → 3: the #7 residual moved into a
strictly-lower declaration; none added, none closed).  `#print axioms`:
`exists_sliceLocallyUniformDecayBound` and the derived
`exists_locallyUniformSliceDecay` both show `[propext, sorryAx,
Classical.choice, Quot.sound]` (bare `sorryAx`, no custom axioms — the same
profile the inline-sorry form carried); the certified leaf
`sliceIteratedFDeriv_continuousOn` remains kernel-only.  No statement edits,
no deleted content.

### #6 — BKMLogBootstrap.lean:376 `exists_biotSavartLogTextbook` → **typed no-go (CONJECTURE, unchanged)**

Two route probes, both negative.  (i) In-repo reconstruction of `fderiv u`
from `staticCurl u`: confirmed absent — `CurlIdentities` carries only the
algebra (`staticCurl_staticGradient_eq_zero`,
`staticDivergence_staticCurl_eq_zero`, …); `BiotSavartKernel`, `CZNearField`,
`SingularIntegralPrelims` carry kernel size/cancellation layers; the pointwise
representation `∇u = PV(∇K ∗ ω)` exists nowhere (Mathlib-absent).  (ii) Agmon
bypass: `exists_agmonSupBound` applies to the field itself, not to `fderiv`,
and even a componentwise `H² ↪ L^∞` on `∂_j u_i` yields only
`‖Du‖∞ ≤ C·√(H³ u)` — strictly weaker than the target's
`C·(1 + Mω(1 + log(e + √H³)) + √M₂)`: for the scaling family `ω = εφ(k·)`,
`k = ε⁻⁴`, one has `√(H³ u) ~ ε⁻¹` while the target RHS stays
`O(1 + ε·log(1/ε))`, so the log-producing shell decomposition around the
representation is unavoidable.  Residual unchanged: the Biot–Savart
*representation* for divergence-free Schwartz fields; est ~400 LOC after it.

### #7 — BKMLogBootstrap.lean:1499 `exists_locallyUniformSliceDecay` → **DECOMPOSED**

The bundled conjunctive residual is split per repo convention.  The genuinely
PDE-dependent conjunct is extracted as the strictly-lower named residual
`exists_sliceLocallyUniformDecayBound` (declaration :1498, token :1503), and
`exists_locallyUniformSliceDecay` (:1511) is now **derived** (certified,
sorry-free) from it plus the previously certified
`sliceIteratedFDeriv_continuousOn` — same name, same type, zero downstream
churn (`sobolevOrderIntegralContinuity` untouched).  The new residual's
docstring sharpens the insufficiency witness: for
`v t x := (t − t₀)³·ψ((t − t₀)² x)`, `ψ = exp(−‖·‖²)`, the decay bound *itself*
(not merely a dominating integral) fails at every `t₀` and every `r > 0`:
`sup_{t ∈ B(t₀,r)} ‖v(t,x)‖² = C·‖x‖⁻³` (attained at
`|t − t₀| = (3/4)^{1/4}·‖x‖^{-1/2}`), which overtakes any `K·(1+‖x‖)⁻⁴` — so
even the local-in-time form cannot follow from joint smoothness alone.
Remaining content: polynomially weighted Schwartz seminorm propagation along
the flow (weighted energy inequalities closed by Grönwall against
`uniformly_bounded_energy`); the repo's cutoff-IBP stack (`CutoffEnergyIbp`,
completed at `2c69626`) is compact-support only and does not transport to
polynomial weights without a priori decay (the bootstrap gap).  Est ~250 LOC,
unchanged.

### #8 — BKMLogBootstrap.lean:1575 `exists_sobolevOrderEnergyEstimate` → **typed no-go (CONJECTURE, unchanged)**

Two route probes, both negative.  (i) `n = 0` split via the certified `Energy*`
stack: every instantaneous-balance theorem is guard-carried —
`integral_kineticEnergyDensity_timeDerivative_eq_neg_viscousDissipation`
requires nine flux/derivative integrability hypotheses that are exactly the
missing decay data (#7's residual in disguise), so the `n = 0` case is not
currently certifiable either, and no statement-level split is possible without
weakening the theorem (not taken).  (ii) `n ≥ 1` Kato–Ponce: no commutator
bound of any form exists in the repo (the only `commutator` hits are the
Galerkin projection commutators in `GalerkinBasis`, a different object);
`|⟨Dⁿ(u·∇u), Dⁿu⟩| ≤ C‖∇u‖∞‖u‖²_{Hⁿ}` remains Mathlib-absent.  Residual
unchanged (declaration now :1582, token :1594); est ~600 LOC.

---

## Wave 2026-08-18 NK1 — BKMLogBootstrap: the near-field Hölder leaf CERTIFIED (Morrey–Agmon `H² ↪ C^{0,1/4}`)

Receipts: `lake env lean Navier/Analysis/BKMLogBootstrap.lean` — exit 0, zero
errors, exactly 3 `declaration uses sorry` warnings (declarations :373, :1984,
:2068; tokens :385, :1989, :2080 — shifted from N2's :364/:1498/:1582 by the
~500-line insertion).  Sorry delta this lane: file **3 → 3**, no declaration
moved onto or off `sorryAx`; `#print axioms exists_agmonMorreyBound` →
`[propext, Classical.choice, Quot.sound]` (kernel axioms only, no
`native_decide`).  No statement weakened, nothing deleted.

**Banked certified asset (toward #6, `exists_biotSavartLogTextbook`).**
`exists_agmonMorreyBound` — for every Schwartz velocity field `u` and all
`x y : Space`,

  `‖u x − u y‖ ≤ C·√(sobolevH2NormSq u)·‖x − y‖^{1/4}`.

This is the *difference* companion of the certified Agmon leaf
`exists_agmonSupBound`, and it is the near-field input the BKM cutoff argument
actually consumes: the cancellation factor `|ω(x−z) − ω(x)|` is
`O(‖z‖^{1/4}·√(H² ω))`, i.e. at `H³`-of-`u` cost (one derivative up), **not**
the `H⁴` cost of the Lipschitz/`‖∇ω‖∞` route recorded in the size-layer
docstrings.  With cutoff `ρ ≈ ‖u‖_{H³}^{-4}` the near field is `O(1)` and the
shell (`integral_bsKernelScalar_annulus_le_log`, already certified) delivers
exactly the `log(e + ‖u‖_{H³})` factor — so after this leaf the *entire*
analytic content of #6 is isolated in the Biot–Savart representation
`∇u = PV(∇K ∗ ω)` (plus its local term and the curl-component bridge
`‖Dⁿ(staticCurl u)‖ ≤ ‖D^{n+1}u‖`).

**Route (all inside `Navier/Analysis/BKMLogBootstrap.lean`, after
`sobolevEmbeddingDomination`).**  Inversion phase-twist
(`norm_fourierInv_sub_le`: `𝓕⁻g(y₁) − 𝓕⁻g(y₂) = ∫ (𝐞⟪ξ,y₁⟫ − 𝐞⟪ξ,y₂⟫)·g`,
via `Real.fourierInv_eq` + `integral_sub`, no translation-symbol identity
needed); phase bound `‖𝐞 a − 𝐞 b‖ ≤ min 2 (4π|a−b|)`
(`norm_fourierChar_coe_sub_le`, via `Complex.norm_exp_sub_one_le` on the disk
and the trivial cap `2` off it); the single global pointwise step
`min(2, 2t)² ≤ 4√t` (`min_two_two_mul_sq_le`) replacing the frequency split —
no radial/shell integration is needed for this leaf; Bessel half-moment
integrability `∫ (1+‖ξ‖²)⁻²√‖ξ‖ < ∞` at exponent `7/2 > 3`
(`integrable_sqrt_norm_mul_bessel_sq_inv`, same Japanese-bracket source as the
Agmon weight); phase-weighted Cauchy–Schwarz
(`integral_phase_mul_le_sqrt_weighted`, the in-file Hölder pattern with the
phase retained in the weight factor); weighted Plancherel
(`exists_weighted_plancherel`) for the surviving `L²` mass; model transport
back to `Space` through `euclModel`/`realToCx` with constants absorbed.

**Residual ledger for #6 (unchanged tier, CONJECTURE; sharper content).**
Remaining: (i) the PV representation with local term — genuinely
Mathlib-absent (N2 probe stands); (ii) the curl-component bridge feeding
`staticCurl u` into `exists_agmonMorreyBound` (componentwise Schwartz
extraction + `iteratedFDeriv` count); (iii) the shell mean-zero of
`bsGradKernel` (needed to subtract `ω(x)` inside the near field) and the
ε→0 PV limit assembly.  Est for the remainder: ~300 LOC on top of the
representation.  The `:1984`/`:2068` residuals (#7 decay propagation, #8
Kato–Ponce) were not re-attacked this lane (owner scope: BKM chain).

---

## Original entry (2026-08-17)

**Build**: GREEN, 8730 jobs, 12 source `sorry` tokens (= 10 compiler `declaration uses sorry` warnings after the GalerkinBasis 3-token roll-up — see the reconciliation above)  
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

**N4 sweep audit 2026-08-18** (lane N4; docstring side committed as
`d7bacfd`): all four leaves
re-attacked; two full attempt cycles each (certified-reduction survey +
machine search over the imported environment). Verdict: **all four remain
CONJECTURE-tier no-gos**, blocked on the same Mathlib-absent infrastructure
recorded below — `exact?` over the full analysis DAG closes neither the
`L^p`-slice (`p > 3`) nor the `L²`-mass pointwise far-field goal, and the
environment census finds zero `MemLp`/`Integrable` conclusions for
`sol.pressure` and no kernel-clean Biot–Savart representation of `∇u`.
Frontier deltas since this ledger's snapshot, verified against the
compiler: (i) `CutoffEnergyIbp.cutoffEnergy_ibp_eq` (commit `2c69626`)
discharges #10's former blocker (a); (ii) the `H³(ℝ³) ↪ L^∞` Sobolev
embedding has been **kernel-clean since `19192df` (2026-07-27)** —
`#print axioms Navier.Analysis.SobolevEmbedding.sobolevEmbeddingDomination_H3`
→ `{propext, Classical.choice, Quot.sound}` — so #12's "closing embedding
carries a Plancherel `sorryAx`" note was already stale at this ledger's
writing; corrected below. Sorry census unchanged: 4 compiler sorries in
this file (721/791/866/951), 9 repo-wide.

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
| **What blocks** | The integrated Caccioppoli inequality `cutoff_local_energy_inequality`.  Former blocker (a) — cutoff integration by parts against the local energy identity — is now **certified** (`CutoffEnergyIbp.cutoffEnergy_ibp_eq`, commit `2c69626`, N4-verified 2026-08-18).  Remaining: (b) an `L^r` pressure bound for the cutoff pressure term `∫ χ² ⟨∇p, u⟩`, plus the assembly/iteration step.  The Calderón–Zygmund `L^r` boundedness behind (b) remains a named residual in `SingularIntegralPrelims` (the pointwise Hörmander core is now certified in `CZNearField`). |

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
| **What blocks** | `Enstrophy` lands the pointwise vortex-stretching identity but the integral enstrophy budget remains open.  `BiotSavartKernel` stops at the far-field tail; no kernel-clean Biot–Savart representation of `∇u` exists (the only `biotSavart` decls route through the open leaf `exists_biotSavartLogTextbook`).  **Correction (N4, 2026-08-18):** the closing Sobolev embedding is no longer a blocker on soundness grounds — `sobolevEmbeddingDomination_H3` is kernel-clean since `19192df`; the residual caveat is that it accepts `SchwartzVelocity` slices, with slice-Schwartz control itself open (`exists_locallyUniformSliceDecay`). |

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