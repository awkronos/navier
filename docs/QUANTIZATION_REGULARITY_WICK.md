# Regularity, quantization, topology, and imaginary time

The useful throughline is a distinction between a field, its coordinates,
its topological invariants, and the estimates governing its evolution.
The following native examples prove particular connections and refute specific
overextensions. They do not assert an equivalence of quantum and classical
Navier–Stokes dynamics.

## A smooth field can have singular phase velocity

In units hbar/m = 1, the Madelung variables are

```text
rho = |psi|^2
j = Im(conj(psi) grad psi)
v = j/rho, on rho > 0.
```

[QuantumVortexRegularity](../Navier/Analysis/QuantumVortexRegularity.lean)
uses actual real Fréchet derivatives to define the current. It proves that a
smooth wavefunction gives a smooth decoder at every nonzero point. At a node,
the opposite conclusion is possible: for `psi(z)=z`, the wavefunction,
density `x^2+y^2`, and current `(-y,x)` are all smooth, while decoded velocity
is unbounded in every punctured neighborhood of zero. Along the positive real
axis its magnitude is exactly `1/r`.

This refutes the implication from smooth wavefunction to locally bounded
decoded velocity at a node. It also shows why a singular phase description
does not alone establish blowup of the underlying wavefunction. The module
additionally proves that this field is harmonic and, held constant in time,
solves the free Schrodinger equation `i*d_t psi = -(1/2)*Delta psi` with actual
derivative operators. It has no claimed global finite-energy property and is
not presented as a Gross–Pitaevskii or Navier–Stokes solution.

## Quantization and winding

For a single-valued nonzero complex phase on a closed loop, the total phase
change is an integer multiple of `2*pi`. The resulting circulation is
`2*pi*n*hbar/m`. The integer records winding; it is not an upper bound on
spatial derivatives or on velocity near a zero. The unit vortex above is the
basic example of this distinction.

[QuantumVortexWinding](../Navier/Analysis/QuantumVortexWinding.lean) proves
necessity and sufficiency for the explicit real-parameter family
`exp(i*kappa*theta)`: closure at `2*pi` is equivalent to integer `kappa`.
It computes the integer-loop phase current and circulation, and derives the
obstruction to a differentiable periodic real phase lift for nonzero charge.
For the same wavefunction `psi(z)=z`, it also computes the circulation of the
actual decoded velocity, using its Euclidean dot product with the unit-circle
tangent, and obtains exactly `2*pi`.

Nonzero winding obstructs a single-valued periodic real phase lift. General
homotopy invariance additionally concerns a whole deformation that stays
nonzero on the loop. Neither the existence of a named integer nor a plot of
phase establishes an estimate for the full PDE.

The native proof covers these explicit phase loops and the differentiable
periodic-lift obstruction. A general winding-degree theorem, homotopy
invariance, and the nonvanishing continuous disk-extension obstruction are
not claimed as formalized here.

For geometric treatments and their hypotheses, see
[Khesin–Misiołek–Modin](https://arxiv.org/abs/1711.00321) and the
[Khesin–Modin preprint](https://arxiv.org/abs/2607.01024), which discusses
noncritical zeros, the Madelung momentum map, and circulation quantization.
These cited results are not claimed as formalized in this repository.

## Catastrophes of the zero set

[QuantumVortexTopologyChange](../Navier/Analysis/QuantumVortexTopologyChange.lean)
constructs the smooth polynomial field

```text
psi(t,x,y) = (x^2-t) + i*y.
```

There are no zeros for negative time, one zero at time zero, and exactly two
zeros `(sqrt(t),0)` and `(-sqrt(t),0)` for positive time. The actual spatial
Jacobian has determinant `2*x`: it degenerates at the event and has opposite
signs at the two later zeros. Thus the zero set can undergo a fold while the
field remains jointly smooth. The local orientation calculation is not a
separate proof of winding numbers of this polynomial's roots.

The polynomial is not asserted to solve Schrödinger, Gross–Pitaevskii, or
Navier–Stokes. For a genuine PDE result, Enciso and Peralta-Salas prove
[quantum vortex reconnections in smooth Gross–Pitaevskii solutions](https://arxiv.org/abs/1905.02467).
That external theorem establishes that reconnection and smooth wavefunction
evolution can coexist; it is not part of our Lean proof closure.

## Wick rotation preserves an analytic formula, not its damping estimate

[WickRotationModes](../Navier/Analysis/WickRotationModes.lean) constructs the
entire function `F_a(z)=exp(-a*z)`. Its real-time restriction has generator
`-a` and modulus `exp(-a*t)`. Its imaginary-time restriction has generator
`-i*a` and modulus exactly one. The module proves that no positive exponential
damping estimate transfers to the rotated mode.

The final consumer identifies `a=nu*|k|^2` with the repository's literal
lattice heat multiplier. This connects the linear formulas used by the
Navier solver to the oscillatory Schrödinger multiplier, while disproving
preservation of strict damping even for one nonzero mode.

It does not supply analytic continuation of arbitrary smooth nonlinear
solutions, preserve their real-valuedness, or turn the nonlinear
incompressible Navier–Stokes equation into Gross–Pitaevskii. In particular,
heat smoothing cannot be imported through this calculation as a quantum
regularity theorem, or vice versa.

## Consequence for A and B

Topology constrains permissible phase configurations. Global regularity
requires quantitative control of the actual evolving field. The existing
Navier energy and Fourier-moment estimates address the latter obligation.
None of the quantum, fold, or Wick examples establishes or refutes the
arbitrary-data global Navier–Stokes statements A and B. Their value is to rule
out invalid transfers and identify exactly what a future comparison must prove.
