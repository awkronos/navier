# Fourier triads, viscous absorption and SU(3)

A Fourier mode is a spatial velocity pattern, with a wavevector, polarization,
phase and amplitude. The quadratic advection term couples two modes to their
sum wavevector. Pairing that output with velocity in the energy equation gives
a cubic interaction among three modes with `p + q + l = 0`.

These are field modes, not three particles. Fluid particles follow the combined
velocity field. The gravitational three-body problem instead evolves three
positions and momenta under gravitational forces. A three-mode truncation is
not generally an invariant subsystem of the full fluid equation: interactions
can generate other modes. Coupling and complicated dynamics alone imply neither
a collision nor a loss of Navier regularity.

## Exact physical obstruction

[PhysicalPeriodicCoerciveShellControl.lean](../Navier/Analysis/PhysicalPeriodicCoerciveShellControl.lean)
constructs a finite-support carrier using

```
p = (3, 0, 0)       A_p = r (0, 1, 0)
q = (0, 4, 0)       A_q = r (1, 0, 0)
l = (-3, -4, 0)     A_l = r (-4, 3, 0)
```

The negative modes obey `A_(-k) = -conj(A_k)`. These are the repository's raw
coefficients `A = -2πi û`; the decoded velocity is real. Every polarization is
transverse to its wavevector, so the field is divergence-free. This particular
example is planar, embedded in the three-dimensional carrier.

The checked quantities are an actual selected weighted triad pair and its three
participating raw viscous densities:

```
weightedProjectedTriadPair = 16 r³
D_p + D_q + D_l = 650 r²
```

Thus no constant `C`, independent of amplitude, can make
`|weightedProjectedTriadPair| ≤ C (D_p + D_q + D_l)` hold for all physical states.
The proof constructs `r = 41 (|C| + 1)` for every real `C`.

Absorption means paying for the nonlinear term using a dissipative term in an
estimate. This theorem rules out this particular pointwise, triad-wise payment
with an amplitude-independent constant. It does not rule out summed
cancellation, time-integrated estimates, small-data absorption, or estimates
restricted by the actual evolution. Unweighted nonlinear energy transfer still
cancels. Weighting finer scales changes what the cancellation controls.

## Which SU(3) connection survives?

[TriadUnitarySymmetry.lean](../Navier/Analysis/TriadUnitarySymmetry.lean) imports
the same three wavevectors. SU(3) consists of complex unitary three-by-three
matrices with determinant one. Merely having three modes is not a symmetry proof.

Physical translation multiplies each mode by `exp(2πi k·x)`. Because the three
wavevectors sum to zero, the three phases multiply to one. Lean proves that
their diagonal matrix belongs to SU(3) and commutes with the heat generator.
This is a restricted diagonal action supplied by translation symmetry.

Full mode mixing fails. The exact heat generator on these modes is
`-μ diag(9,16,25)`. Lean constructs a determinant-one unitary cyclic permutation
and proves that it does not commute with this generator for every `μ > 0`.
The permutation cannot be a spatial rotation either: rotations preserve length,
whereas it exchanges frequencies of lengths three and four.

This rules out the full SU(3) modal-action candidate on this triad. It does not
exclude unrelated representations or identify fluid modes with particle color.
No SU(3) conservation law has been supplied that controls the missing Navier
high-frequency bound.

## Consequence for global regularity

[PhysicalPeriodicTotalEnergyControl.lean](../Navier/Analysis/PhysicalPeriodicTotalEnergyControl.lean)
proves datum-only total and off-zero energy bounds along actual physical mild
charts. Energy control, higher graph control, strong time derivatives and the
native globally smooth PDE carrier are distinct proof obligations. A and B
remain open; the triad result eliminates one insufficient estimate, not either
original endpoint.

For the fluid interpretation of mode-to-mode transfers, see
[Ding, Chung and Illingworth, *Journal of Fluid Mechanics*](https://doi.org/10.1017/jfm.2024.1193).
Native theorem types and raw axiom audits determine the formal claims above.
