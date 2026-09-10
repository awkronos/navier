# Madelung correspondence and the constructed flow

The relationship is through hydrodynamic representations, not an established
map from this repository's selected counterexample to an ordinary linear
Schrödinger solution. The native uniqueness result compares velocities with
the same force and initial data before time one. It supplies neither a unique
wavefunction nor a global smooth continuation.

## Scalar correspondence

On a region where a scalar wavefunction is nonzero, write

\[
\psi=\sqrt{\rho}\,e^{iS/\hbar},\qquad
u_\psi=\frac{\hbar}{m}\frac{\operatorname{Im}(\bar\psi\nabla\psi)}{|\psi|^2}
=\frac{\nabla S}{m}.
\]

Here `u_ψ` denotes fluid velocity, not viscosity. The usual Schrödinger equation
produces a continuity equation and an Euler-type momentum equation with quantum
potential

\[
Q=-\frac{\hbar^2}{2m}\frac{\Delta\sqrt\rho}{\sqrt\rho}.
\]

It does not supply the Navier–Stokes viscous term. For a smooth local phase,
the resulting velocity has zero curl. Nonzero density and the topology of the
phase matter; a fluid formulation alone does not automatically reconstruct a
single-valued wavefunction. See [Carles, Danchin and Saut (2012)](https://arxiv.org/html/1111.4670v1)
and [Wallstrom (1994)](https://journals.aps.org/pra/abstract/10.1103/PhysRevA.49.1613).

## A checked obstruction from the selected construction

`ConstructedFiniteTimeObstruction.selected_candidate_no_regular_madelung_lift`
applies the quantitative decoder bound to the actual selected finite-energy
candidate. Suppose a representation on `[0,1) × K` obeys

\[
u=\frac{\hbar}{m}\frac{\operatorname{Im}(\bar\psi\nabla\psi)}{|\psi|^2},
\quad |\psi|\ge c>0,\quad |\nabla\psi|\le M<\infty.
\]

The pointwise Cauchy–Schwarz inequality gives

\[
|u|\le\frac{\hbar}{m}\frac{|\nabla\psi|}{|\psi|}
\le\frac{\hbar M}{mc}.
\]

The Lean statement uses the equivalent directional pairing
`inner u d = (hbar/m) * Im(D psi d / psi)` and the spatial Fréchet operator
norm. It works in the construction's actual three-dimensional Euclidean
space, requires spatial differentiability on the support, and quantifies over
every fixed real ratio `hbar/m` (using its absolute value in the bound).
The shared estimate lives in `QuantumVortexRegularity`; the planar decoder
and the three-dimensional obstruction consume that same estimate.

That bound contradicts the selected candidate's unbounded velocity on its
fixed compact support as time approaches one. Thus any such representation
must lose at least one stated property: agreement with the velocity, a uniform
positive lower bound on amplitude, or a uniform bound on its spatial gradient.
This is a necessary-condition argument; it constructs no wavefunction.

The strengthened theorem
`selected_candidate_madelung_amplitude_or_derivative_degenerates` localizes
this failure to every terminal window: for every `c > 0`, derivative threshold
`M`, and `δ > 0`, an agreeing nonzero differentiable decoder has a point on
the actual support with `1 - δ < t < 1` where `‖ψ‖ < c` or `M < ‖Dψ‖`.
The original no-regular-lift consumer now uses this theorem.

## Exact PDE frontier

`PeriodicMildOfficialEquation.mildFixedPoint_officialMomentum_positiveTime`
identifies the bounded periodic mild fixed point with the official Fréchet
momentum equation on `0 < t < T`. This includes physical convection,
viscosity, pressure, and the time derivative. Arbitrary-data continuation
and joint smoothness through the initial time remain required for full B.

`WholeSpaceSolenoidalHeatIntegratedRhsLimit` proves convergence of the actual
compact-test weak RHS time integrals to the cutoff-free endpoint momentum
difference. Its proof consumes the exact weak evolution and Gaussian endpoint
limits. Identifying this with the time integral of the pointwise RHS limit
still requires a uniform-integrability argument. These are direct analytic
advances toward A/B; the quantum decoder bound does not supply continuation.

More generally, a representation whose reconstruction yields a continuous
velocity through `[0,1] × K` contradicts
`ConstructedFiniteTimeObstruction.selected_candidate_no_continuous_extension`.
The sharper competitor theorem also applies if the reconstructed velocity solves
the same forced equation with the same data and the required slab-local energy
and smoothness properties; agreement then follows from comparison.

A fluid singularity therefore does not by itself prove that a wavefunction
is singular. The division by density can fail at a zero of an otherwise smooth
wavefunction. Conversely, one cannot use regularity of a wave equation to
continue this fluid unless the reconstruction stays regular as well.

## Rotational and viscous representations

[Meng and Yang (2024)](https://journals.aps.org/prresearch/abstract/10.1103/PhysRevResearch.6.043130)
develop a Navier–Stokes representation using a two-component wavefunction and a
nonlinear Schrödinger–Pauli equation with imaginary diffusion. Their effective
spin system is non-Hermitian. This is a closer research connection than the
ordinary scalar Madelung transform.

Applying such a representation here would require construction of the lift,
transport of this exact external force, valid global charts or gauge data,
compatibility of energy classes, and control of the reconstruction up to the
terminal time. None of those inputs is supplied by citing the representation.
The classical uniqueness theorem also does not remove phase/gauge freedom in
the lifted variables.

The website continues to compute the original periodic velocity equation. A
wavefunction representation is not assumed to be faster or numerically
faithful without an independent benchmark and equation-level verification.
