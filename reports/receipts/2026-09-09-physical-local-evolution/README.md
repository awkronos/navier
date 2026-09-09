# Physical local evolution — 2026-09-09

All six source files were checked independently by root with the project
single-file compiler under `~/.claude/hooks/lean-build-lock.sh 600`.
All source and raw audit processes exited zero. The exact-source physical
control audit includes the clarified period-one normalization comment.
Source hashes and unfiltered compiler/axiom logs accompany this receipt.
Every audited endpoint uses only `propext`, `Classical.choice`, `Quot.sound`.

The constructed local trajectory starts from the supplied physical,
divergence-free weighted initial datum. It is continuous, remains real under
the physical Fourier decoder, has decoded spatial summability of order
2 + 1/4 at each positive interior time, and has absolutely summable actual
mode time derivatives satisfying the unprojected physical mode equation.
The horizon is positive and selected from viscosity and the initial norm;
it is not arbitrary. The extension outside that horizon is only a clamped
representative, and the equation is asserted only on the local interval.

The nonlinear energy-transfer series is absolutely summable on the actual
weighted carrier. Its countable triad involution cancels the real transfer.
Physical mean transport preserves modal amplitude and viscosity gives the
exact modal heat contraction. These algebraic identities do not bound the
global critical norm.

Rust integration tests now exercise a genuinely interacting real triad:
modal energy changes while total energy is conserved to the stated numerical
tolerance. A physical mean changes the phase by the Galilean multiplier.
All five Fourier-convention tests and strict all-target Clippy pass.

Remaining original obligations: locally uniform all-order time/spatial jets,
Fourier product reconstruction, and horizon-independent physical critical
control. A/B are not closed by this local construction or energy cancellation.
