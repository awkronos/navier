# RST-NAVCLL-1116 — flow — ContinuousLeiLinSpace surface coverage (landed 49abd65)

## What landed for a consumer

Nine examples appended to the "Surface tests" section of
Navier/Analysis/ContinuousLeiLinSpace.lean, exercising eight public names that
had no test AND no consumer anywhere in ~/navier before this change (selected by
`git grep -l <name> -- '*.lean'`, each appearing only at its own declaration and
its own `#print axioms` line):

- fourier_schwartz_convolution_integrable — complex Fourier convolution of two
  Schwartz profiles is Bochner integrable, hypothesis-free at its own data.
- integral_left_frequency_kernel / integral_right_frequency_kernel — the two
  Tonelli factorizations evaluated at Schwartz Fourier norm data: product-kernel
  integral = X1 mass x X0 mass (and the symmetric reading).
- frequency_weighted_norm_product_split — the derivative allocation at zero
  input frequency, where the first summand carries nothing.
- continuousLeray_weighted_norm_le — the pointwise Leray contraction consumed at
  the output-frequency weight the X1 estimates carry.
- integrable_continuousLerayE / weighted_continuousLerayE_mass_le — Bochner
  integrability and weighted-mass contraction at a Schwartz profile on the
  Hermitian carrier itself (h : SchwartzMap ES ComplexE3).
- es_measurableSpace_coherent / complexE3_measurableSpace_coherent — each Borel
  instance path composed to the generated sigma algebra.

Diff: +62 lines, 0 deleted, 0 modified. No declaration, statement or proof of an
existing theorem touched; the file's axiom census is byte-identical. Nothing was
restated from mathlib. weighted_convolution_mass_le was deliberately left alone
(it already has four live consumers: ContinuousLeiLinPressureReconstruction,
ContinuousLeiLinRecentTailJoint, ContinuousLeiLinRecentTailMoment,
Transfer/MildSelfMapDefectBudget).

## Measurements

- Warm-build law honoured: the seat already had a populated .lake (packages
  symlinked to ~/.lean-cache/mathlib/1f414401..., 1075 oleans, 6.1G build). No
  cold full build was run. No estate-builder refusal (no rc 76).
- Baseline `lake build Navier.Analysis.ContinuousLeiLinSpace` on the untouched
  base: rc 0, module 11s, graph 22.0s, 9063 jobs.
- Staleness trap checked before probing: `git diff --name-only 566e10e..origin/main`
  names only four docs/receipts paths — no sibling touched FourierMajorant or
  ComplexLerayNorm — so the module olean (18:51) was already post-change and no
  forced rebuild was needed.
- Post-edit `lake build Navier.Analysis.ContinuousLeiLinSpace`: rc 0, 9063 jobs,
  "Build completed successfully". Zero errors/warnings in the added range.
- Lock-free single-file probe `lake env lean Navier/Analysis/ContinuousLeiLinSpace.lean`:
  rc 0. 49 `#print axioms` receipt lines; the only axiom set appearing anywhere
  is [propext, Classical.choice, Quot.sound]; zero `sorryAx` and zero
  `native_decide` occurrences in the whole build log; zero `sorry` tokens in the
  file. Census coverage: 48 exported theorems vs 49 censused names,
  `comm -23 <theorems> <censused>` empty — every exported theorem is censused.
- Trunk readback after landing: `git rev-parse origin/main` =
  49abd6511a6d96101f1633d81ab504e39d57bfe3 = the pushed sha; origin/main's copy
  of the module holds 25 examples (16 at base + 9 new) and contains the new
  `fourier_schwartz_convolution_integrable f g` reference.

## Two honest disclosures

1. First draft fed the Hermitian multiplier `(a : C) • (1 : ComplexE3)` and
   failed six times with `failed to synthesize instance OfNat ComplexE3 1`:
   this mathlib gives EuclideanSpace C (Fin 3) (= WithLp 2) no One/OfNat
   instance, so the unit-vector route is closed. Rewritten at a Schwartz profile
   on the carrier, using the codomain-polymorphic
   `SchwartzMap.integrable_pow_mul (mu) (k : N)`
   (Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1116) — the file's
   own schwartz_integrable_X1 is its C case.
2. The train printed `LANDING UNCERTIFIED -- fold legs did not run:
   backward_path, drop_check, merge_tree, stale_revert (instrument absent or
   trunk unnamed)` on the same row that reports ok:true, attempt 1, transport
   direct_push, sha==readback. Per the wave law (memory 1113) that string means
   the fold instruments were absent, not that a check failed. The push itself is
   independently verified above by the native trunk readback. Its first run
   refused before any attempt with `ledger_unresolvable` (--orch is the campaign
   board name, not a persona); re-run with `--orch OMNI-SHARPEN-1112` recorded
   to campaigns/OMNI-SHARPEN-1112/ledgers/SWARM-LEDGER.jsonl.
   The same run notes the BOARD publish (a different plane) was refused with
   carrier_union_loss and a peer path that does not exist on this host
   (/Users/schizodactyl/.local/git/projects-awkronos-patents.git/scripts/
   ledger-append.py: No such file or directory) — code landing is unaffected;
   that is a board-side residual for the substrate owner.
- Commit message: the first wording-only message was refused by
  closure-gate-commit-msg.sh (S15.6, content floor keyed on carried Lean
  content), so the landed commit body carries the nine raw receipt lines.

## PRIOR ART (read before writing; consumed, not re-derived)

- The module at base 566e10e — its existing 13-example "Surface tests" section
  (the orphan lane's already-landed predecessor) and its 49-line `#print axioms`
  tail. My block extends that section; no already-exercised name is re-tested.
- The RSI row itself (code_map_rsi_targets, generation
  93fa7be454194153a23d95d38f5a69cf, tier T0, class priority, score 0.9004) whose
  recommendedAction is "Treat exported names as stable API and prioritize tests
  before changing it" — the reason the deliverable is tests, not an API edit.
- Navier/Analysis/ComplexLerayNorm.lean and Navier/Analysis/FourierMajorant.lean
  (the module's two imports) for complexLeray, complexEuclideanLeray,
  complexEuclideanNorm/Point, spaceProj, complexFrequency and
  complexEuclideanLeray_formula — all transported, none restated.
- Mathlib SchwartzMap Basic.lean 1100-1130 for integrable_pow_mul/integrable/
  continuous, plus the PiLp/WithLp instance surface (which is where the missing
  OfNat was found).
- Repo-wide consumer census of every candidate name (`git grep -l`), which chose
  the eight and excluded weighted_convolution_mass_le.
- Estate laws: the brief's warm-build law and stale-olean trap; the closure-gate
  raw-receipt law (memory 1113); `--orch is a board name` (memory 1114).
