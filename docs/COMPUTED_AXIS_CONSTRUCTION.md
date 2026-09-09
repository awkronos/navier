# Computed analytic-axis construction

This note specifies the executable construction stage in
[`solver/src/construction.rs`](../solver/src/construction.rs), the diagnostics it
returns, and its relationship to the checked forced-breakdown theorem. It is a
numerical-method description, not a proof receipt.

## Mathematical role

The checked theorem is the forced whole-space alternative C: for every positive
viscosity there are admissible data and a smooth rapidly decaying force for
which no global smooth bounded-energy classical solution exists. The selected
velocity is classical before its finite deadline and has bounded energy, while
its speed becomes unbounded. Pre-deadline comparison transfers that growth to
every same-data, same-force smooth finite-energy competitor in the proved
class.

This does not decide unforced alternative A. The quantifiers differ:

```text
forced C, checked here:
  for every viscosity, there exist data and a force that obstruct global
  classical continuation

unforced A, open here:
  for every viscosity and every admissible datum, with force equal to zero,
  there exists a global classical solution
```

The numerical evaluator realizes the first computable local component of the
forced construction: the nonlinear analytic-axis profile and its similarity
reconstruction. The Lean witness additionally contains matching, asymptotic
background, oscillatory corrections, mean corrections, and localization. The
evaluator must therefore be read as a finite stage of the construction rather
than a discretization of the final selected field.

## Similarity reconstruction

Let `tau = 1 - t`, `A = 1/2 + h`, and `D = 1/2 - h`. For cylindrical radius
`r` and height `z`, the code obtains the unique positive `q` from

```text
q - z^2 q^(2h) = tau,
eta = z q^(-D),
X = r^2 / (2q),
Y = Lambda X.
```

The axis iteration supplies profiles `Phi(Y,eta)` and `u(Y,eta)` around explicit
leading profiles. With `F` the normalized swirl profile, `U` the full axial
profile, and `v0` the incompressibility-determined radial profile, the physical
field is reconstructed as

```text
u1 = v0 x1/(2q) - q^(-A-1/2) F x2,
u2 = v0 x2/(2q) + q^(-A-1/2) F x1,
u3 = q^(-A) U,
p  = q^(-2A) Pi.
```

The implementation solves the scalar `q` equation by safeguarded Newton
iteration inside a bracket, verifies its scaled residual, and rejects times
below floating-point resolution at the root. It evaluates the radial series by Horner's rule and interpolates in
`eta` with a four-point cubic formula. The displayed domain stays inside
`|eta| <= 0.8` and `Y <= 3.2`, away from the evaluator's chart boundary.

## Axis fixed-point map

At each of 257 equally spaced nodes on `-1 <= eta <= 1`, the implementation
constructs the Appendix-A axis pressure datum by deterministic quadrature,
forms the explicit leading profiles, and expands `Phi` and the axial correction
as power series in `Y` through degree 12.

For a coefficient sequence `a_n`, the radial inverse used in the iteration is

```text
(J_nu a)_(n+1) = a_n / ((n+1)(n+nu)),
(J_nu a)_0 = 0.
```

The angular update applies the lower-triangular inverse of
`1 + J_2 chi/2`; the axial update applies `J_1`. Products are truncated Cauchy
products. Radial averages, radial integrals, and logarithmic radial derivatives
are exact coefficient operations at the retained order. Axial derivatives use
a fourth-order centered stencil in the interior and fourth-order one-sided
stencils at the first two and last two nodes. The fixed-point
map runs for 18 iterations by default.

The pressure axis uses the complete piecewise schedule represented in the
source. Its finite middle interval is integrated deterministically; the two
infinite tails are integrated analytically. This is a numerical evaluation of
the formula, not an interval-certified enclosure of its exact real value.

The complete default configuration is:

| Parameter | Default | Implementation role |
| --- | ---: | --- |
| `h` | `0.001` | similarity exponent offset, constrained by `0 < h < 0.01` |
| `j0` | `0.001` | axial leading-profile offset, constrained by `0 < j0 <= 0.05` |
| schedule `lambda` | `0.04` | Appendix-A transition rate, constrained by `2h < lambda < 0.1` |
| schedule `m` | `1` | Appendix-A schedule length parameter |
| radial scale `Lambda` | `48` | scale separating leading and corrected profiles |
| pressure amplitude | `2` | normalization for the axis pressure datum |
| radial order | `12` | highest retained power of `Y` |
| `eta` nodes | `257` | axial-similarity collocation nodes on `[-1,1]` |
| iterations | `18` | fixed-point updates |

The constructor enforces the displayed elementary ranges, but the manuscript's
full proof also selects parameters through existential smallness and largeness
thresholds. These defaults are reproducible numerical choices; their successful
finite evaluation is not a machine-certified discharge of every global
parameter inequality in the proof.

## Diagnostics and residual semantics

The evaluator reports three different kinds of quantity. They answer different
questions and should not be combined into one score.

| Diagnostic | Definition | Interpretation |
| --- | --- | --- |
| `fixedPointDelta` | largest retained-coefficient change in the final update | Iteration stability at the chosen order and nodes; zero may reflect floating-point stagnation |
| `angularEquationRms` | RMS defect in the retained angular profile equation | Internal Appendix-B profile consistency on `Y <= 3.2`, `|eta| <= 0.8` |
| `axialEquationRms` | RMS defect in the retained axial profile equation | Same, for the axial equation |
| `pressureEquationRms` | RMS defect in the radial pressure balance | Same, for centrifugal pressure balance |
| `divergenceRms` | RMS of a finite-difference evaluation of `div u` | Physical-reconstruction check on the sampled grid |
| `momentumResidualRms` | RMS of `R = partial_t u + (u dot grad)u - Delta u + grad p` | Magnitude of the force required by this truncated field on the sampled grid |
| `domainKineticEnergy` | tensor-trapezoidal integral of `|u|^2/2` | Energy only in the displayed bounded similarity chart |
| `maxSpeed` | largest sampled Euclidean speed | Grid-dependent lower observation of the chart maximum |
| `minNormalizedSwirl` | minimum sampled retained `Phi` | Positivity check for the normalized swirl factor |

The physical derivatives use symmetric finite differences with step
`2e-4` times the relevant domain half-extent, floored at `1e-8`. Time
differentiation uses `tau` step `max(2e-4 tau, 1e-10)` and accounts for
`t = 1 - tau`. Viscosity is normalized to one in the residual above.

The profile defects and physical momentum residual are not competing estimates
of one error. The first three are defects of the truncated Appendix-B profile
equations in similarity variables. The momentum residual differentiates the
reconstructed leading field in physical spacetime and is the force that this
finite stage would require. It contains precisely the singular behavior that
the later construction layers are designed to cancel and regularize.

At `tau = 0.05` on a `7^3` grid, the focused Rust test currently reports:

```text
angular profile RMS       1.9921418144623968e-6
axial profile RMS         1.7733879359490666e-8
pressure profile RMS      3.3903453327861445e-9
divergence RMS            8.500463463624519e-3
momentum residual RMS     1.4123532691928133e5
maximum sampled speed     1.004429420038561e1
displayed-domain energy   2.4958636773964515e-1
minimum normalized swirl  2.6162692837448365e-1
```

These values are regression observations at one coarse grid. In particular,
the large momentum residual is not evidence against the theorem: the omitted
correction layers are introduced precisely to alter and regularize the residual
of the singular leading field. Conversely, small retained profile defects do
not certify those omitted layers or the continuum theorem.

## Included and omitted construction layers

| Layer | Executable evaluator | Checked selected witness |
| --- | --- | --- |
| Appendix-A axis pressure schedule | Deterministic quadrature plus analytic tails | Yes |
| Appendix-B nonlinear analytic-axis iteration | Finite radial order and finite `eta` grid | Yes, as exact analytic construction data |
| Similarity-coordinate velocity and pressure reconstruction | Sampled inside a bounded chart | Yes |
| Incompressibility-determined radial velocity | Reconstructed and checked numerically | Yes, exactly in the formal construction |
| Annular moment matching and cone modulation | Omitted | Yes |
| Positive-order Borel background | Omitted | Yes |
| Primary covariance waves | Omitted | Yes |
| Particular, signed, and mean correction cycles | Omitted | Yes |
| Final spacetime localization and compact smooth force | Omitted | Yes |
| Finite-energy comparison and noncontinuation argument | Not numerical | Yes, in Lean |

The numerical `residual` array should consequently be labeled “finite-stage
momentum residual” or “required finite-stage force.” It must not be labeled as
the theorem's selected smooth force.

## Reproduction and acceptance

Run the focused native checks with:

```bash
cd solver
cargo test construction::tests -- --nocapture
```

The focused tests check the defining similarity-coordinate equation,
floating-point rejection, the derivative of a manufactured quartic profile,
fixed-point refinement, finite reconstruction, similarity scaling, residual
step-halving behavior, and radial-order refinement.
In the refinement check, orders 8, 12, and 16 successively reduce all three
profile-equation defects. The angular defect approaches the axial-grid and
floating-point floor at this fixed `eta` discretization, so this test is a
regression and refinement check rather than a continuum-convergence theorem.
The WebAssembly build exports the same Rust evaluator as `ConstructionAxis`; it
does not maintain a separate JavaScript implementation. Instance metadata
reports the actual configuration, the selected `sigma`, and swirl
normalization alongside the included and omitted layers.

Numerical acceptance requires finite outputs, the expected array lengths, a
positive domain extent, and explicit display of the measured defects. Formal
acceptance of the theorem remains the single-file Lean compiler check, original
consumer, and raw transitive-axiom audit recorded under
[`reports/receipts/`](../reports/receipts/).
