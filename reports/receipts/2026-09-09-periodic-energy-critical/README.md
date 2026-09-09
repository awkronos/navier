# Periodic energy / critical-tail receipt

This receipt audits the zero-mode reduction and the explicit fixed-energy,
high-frequency obstruction on the repository's actual periodic Fourier
carrier.

The obstruction family consists of conjugate modes at
`±(n+1,0,0)` with a real transverse polarization.  It satisfies the lattice
reality and divergence-free conditions, has decoded Fourier `ℓ²` energy `2`,
and has off-zero mixed quantity

`2/(n+1) + 2ν(n+1)`.

Therefore energy alone cannot bound the off-zero critical quantity uniformly
over all admissible states.  This does **not** refute the live terminal bound:
its constant may depend on the full initial datum and it quantifies only over
reachable mild terminal states, where positive-time smoothing and dynamics
remain available.

The exact remaining periodic analytic input is a horizon-independent,
datum-dependent bound for `CriticalMildOffZeroTerminalBound`.  The checked
frequency split controls every selected finite band by its physical Fourier
energy and explicit frequency cost; it leaves the complementary `𝒳¹` tail as
the genuinely dynamical residual.

Files in this receipt:

- `Audit.lean.txt`: exact type and raw transitive-axiom queries.
- `source-compile.log`: current-source compiler results.
- `consumer-audit.log`: raw `#check` / `#print axioms` output.
- `hashes.txt`: SHA-256 hashes of the two audited source files.
