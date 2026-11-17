# RST-NAVCLL-1116 recommendation

Row is closed for its own scope: the T0 priority row asked for tests before
changes, and eight previously un-consumed, un-tested public names now have
compiler-checked examples on trunk (49abd65).

Next, in value order:

1. Two names still have neither a test nor any consumer:
   fourier_schwartz_integrable_left_frequency_kernel and
   fourier_schwartz_integrable_right_frequency_kernel. Each is one application
   of the module's own X1 lemma; a follow-on lane should pin them at
   `f g : SchwartzMap ES C` the same way this lane pinned the two integral
   factorizations, so the whole Tonelli block is consumer-tested.
2. The analytic work the docstrings point at is NOT in this file: the
   time-dependent Bochner representative is owned by
   Navier/Analysis/ContinuousLeiLinDissipation.lean
   (normXm1_continuousDuhamel_mass_le_of_jointIntegrable). Route any proof
   budget there rather than re-opening this module's API.
3. By law of this mathlib, do not build Hermitian-carrier examples on
   `(1 : EuclideanSpace C (Fin 3))` — no One/OfNat instance exists. Use
   `SchwartzMap ES ComplexE3` profiles, or the file's own complexEuclideanPoint
   on the coordinate carrier. Worth a line in the next navier lane brief.
4. Substrate residual (not product work, measured this run): the board-publish
   leg of main-push-train on OMNI-SHARPEN-1112 refuses with carrier_union_loss
   and a peer ledger-append.py path absent on this host, and the fold legs
   (backward_path, drop_check, merge_tree, stale_revert) report
   not_run_instrument_absent. Code landing is unaffected (direct_push, sha ==
   readback verified on origin/main), but receipts for this campaign are not
   reaching the board plane. That blocks auditable landing proof for the whole
   wave, so it is worth one substrate fix before the next dispatch.
