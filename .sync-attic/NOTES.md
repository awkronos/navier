- 2026-07-22 (fable-portfolio-close-20260722): manifest.json + test_registry.py working-tree
  mods were stale sync-mirror regressions (content predates HEAD 6b87af1/425c164: NOW moved
  backward, registry_id fields + PRODI1959 + snapshot tests deleted; disk mtime 07-15 20:57
  = syncthing overwrite). Diffs preserved as *.stale-mirror-20260715.patch; HEAD content
  restored via `git show HEAD:path`. .codex-orchestrator-prompt.md (stale 07-14 Codex
  dispatch prompt, not repo source) atticked as codex-orchestrator-prompt.md.stale-20260714.
- 2026-07-22 DEFECT AT HEAD (named, not in this lane's slice): commit 73b2d54
  ("stalled-lane fold") regressed scripts/registry_core.py (-237 lines: dropped
  PINNED_OPEN_*_DISPOSITIONS hardening from 27a8cb2, git-snapshot binding from
  ed49f4e) and refolded data/attack_registry.json+docs to the OLD validator
  generation, while tests/test_registry.py kept the hardened-generation tests.
  Result: HEAD suite = 26 failed. Pre-fold (2fe0648) was green in situ (3
  archive-only env failures). The atticked "stale-mirror" manifest/test pair
  was the old-generation pair coherent with the regressed validator (65 pass)
  — adopting it would lock in the regression; rejected. Repair = reconcile
  validator generation with post-fold data (standalone campaign).
- 2026-07-22 n=2/n=3 rung attempt (fable lane): FourierWeightedPlancherel.n23-attempt-20260722.lean
  holds the pd-wrapper + generic/concrete multiplier-collapse drafts. BLOCKER: whnf
  deterministic timeout (2M heartbeats) elaborating any lemma whose LHS integrand is
  ‖ξ‖^k * ‖(𝓕 (pd j f)) ξ‖^2 under ∑ j (both variable-k and concrete k=2,4; both raw
  ∂_ and opaque-def pd forms). n=1 rung (committed, 852aacd) compiles in the same file.
  Suspect: FourierTransform instance whnf on 𝓢(ES,ℂ) inside the weighted-integrand
  statement context. Next session: try (a) stating with Real.fourierIntegral directly
  instead of the 𝓕 instance, (b) set_option maxHeartbeats 4000000 + diagnostics true
  to name the loop, (c) an abbrev for (𝓕 (pd j f)) bound OUTSIDE the integral.
