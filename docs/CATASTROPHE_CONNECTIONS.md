# Catastrophes, concentration, and global control

Catastrophe theory studies degeneracies of equilibria and their unfoldings.
For example, the cusp potential `V(x;a,b)=x^4/4+a*x^2/2+b*x` has equilibrium
equation `x^3+a*x+b=0`; simultaneous vanishing of the first and second
potential derivatives gives the discriminant `4*a^3+27*b^2=0`.
This is a useful local model of changing equilibrium structure. It is not a
classification of all singularities of an infinite-dimensional evolution PDE.
See [Zeeman's exposition](https://imechanica.egr.uh.edu/sites/default/files/1976%20zeeman%20catastrophe%20theory.pdf).

## The actual similarity coordinate

The executable construction solves

```text
F(q;tau,z) = q - z^2*q^(2h) - tau = 0,
tau > 0, q > 0, 0 < 2h < 1.
```

At this root, direct substitution gives

```text
∂F/∂q = 1 - 2h*z^2*q^(2h-1)
       = 1 - 2h + 2h*tau/q
       > 1 - 2h > 0.
```

Thus the physical scalar branch does not develop a fold before the deadline.
The native [similarity-coordinate module](../Navier/Construction/SimilarityCoordinates.lean)
constructs the unique positive root, proves positive slope, and constructs its
smooth inverse. The quantitative identity above is an algebraic explanation;
this note does not claim a separate audited Lean declaration for that bound.
The [Rust evaluator](../solver/src/construction.rs) uses safeguarded Newton
iteration on this branch.

The finite-stage concentration model has amplitude scale `tau^(-1/2-h)` and
volume scale `tau^(3/2-h)`. Their squared-amplitude-times-volume scale is
`tau^(1/2-3h)`: increasing local speed is compatible with decreasing scaled
energy when `h<1/6`. These are profile scaling laws, not a claim that the finite
grid computes the full selected infinite construction or its exact energy.

## Useful transfer and its limits

Normal-form reasoning can organize parameter sweeps, identify loss of
stability, and suggest observables for concentration. A genuine reduction
from Navier–Stokes would also need a proved invariant or center manifold,
remainder estimates, and control of discarded Fourier modes. A fitted cusp
diagram alone supplies none of these.

The existing Kagami catastrophe KAN uses polynomial-gradient features followed
by bounded `softsign`. That bounded output is useful for its neural-network
role, but replacing physical flow dynamics by it would artificially suppress
the growth under investigation. No such replacement is made here.

The direct proof target is the actual energy balance
`dE_N/dt = 2*flux_N - 2*mu*dissipation_N`, established in
[PhysicalPeriodicEnergyBalance](../Navier/Analysis/PhysicalPeriodicEnergyBalance.lean).
The weighted triad cancellation in
[PhysicalPeriodicWeightedFluxCommutator](../Navier/Analysis/PhysicalPeriodicWeightedFluxCommutator.lean)
leaves a higher-moment bound, with no favorable sign established. Finding a
coercive estimate for the actual evolving flow is useful to A/B; describing
its dynamics with catastrophe terminology does not discharge that estimate.
