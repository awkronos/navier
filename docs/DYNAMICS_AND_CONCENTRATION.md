# Breakdown, uniqueness, and concentration

The checked result constructs a particular forced incompressible flow in
three-dimensional whole space. The chosen initial velocity is zero. The force
is smooth on all spacetime and satisfies the required decay bounds. For the
selected unit-viscosity witness, velocity and pressure are classical before
time one, kinetic energy is uniformly bounded on `[0,1)`, and peak speed is
unbounded toward that deadline. The original endpoint transports the
nonexistence result to every positive viscosity; it does not assert the same
numerical deadline under every scaling.

## Which uniqueness is proved?

Fix `T < 1`. A competitor must have the same initial velocity and force, satisfy
the same incompressible Navier–Stokes equation, and be smooth with uniformly
finite energy on the closed slab `[0,T]`. Then its velocity equals the
constructed velocity throughout that slab. The competitor need not be compactly
supported. Pressure is determined only up to its usual time-dependent gauge.

The strongest checked obstruction allows a separate competitor energy bound on
each such slab. It still excludes a competitor continuous through time one on
the construction's fixed compact spatial support. It does not classify weak
continuations after that time, establish typicality under arbitrary forcing,
or prove stability of the singularity under perturbations.

Exact declarations and compiler receipts are linked in [the result map](RESULT_MAP.md).

## What finite energy permits

Write `E(t) = (1/2) ∫ |u(t,x)|² dx` and suppose `E(t) ≤ E₀`. For any speed
threshold `M > 0`, let `A_M(t) = {x : |u(t,x)| ≥ M}`. Direct integration gives

```math
M^2 |A_M(t)| \leq \int_{A_M(t)} |u(t,x)|^2\,dx \leq 2E_0,
\qquad |A_M(t)| \leq \frac{2E_0}{M^2}.
```

Thus a uniform energy bound bounds the volume occupied by very fast motion,
without bounding its maximum speed. This elementary measure estimate is an
analytical consequence explained here, not an additional Lean endpoint.
It does not determine a unique shape, concentration rate, or spectrum.

## Concentration is not density compression

The equation imposes `div u = 0`. While the velocity is smooth, its material
flow map preserves volume: the determinant of its spatial Jacobian obeys
`d(det DΦ)/dt = (div u)(t,Φ) det DΦ`, so it remains one when initially one.
Stretching in some directions can accompany squeezing in others.

A region selected by a speed threshold is not a fixed material parcel. Its
shrinking volume therefore does not contradict incompressibility. Nor does the
construction require the whole fixed spatial support to shrink to a point.
The result concerns concentration of velocity and loss of classical regularity,
not compression of mass density.

For numerical computation, ever smaller active scales make finite spatial
resolution consequential; finite-grid diagnostics cannot certify the continuum
singularity. For information compression, the theorem alone supplies no new
coding bound or compression algorithm. The repository's periodic Taylor–Green
simulator is a separate computed flow, not a discretization of this construction.
