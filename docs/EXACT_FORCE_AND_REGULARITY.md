# Exact constructed force and the regularity obstruction

This note records what the selected whole-space force is, which properties are
proved for that same force, and exactly which competing solution classes are
excluded. It describes the current Lean declarations; it does not add a
physical interpretation or claim an unforced result.

## Construction of the force

[`ActualCandidateAssembly.selected_witness`](../Navier/Construction/ActualCandidateAssembly.lean#L1184)
fixes
[`selectedBudget` and `selectedThreshold`](../Navier/Construction/ActualCandidateConstruction.lean#L212),
then applies the proved
[`witness`](../Navier/Construction/ActualCandidateAssembly.lean#L1160) theorem
to the concrete
[`selectedPotentialStages`, `selectedDirectStages`, and `selectedPressureStages`](../Navier/Construction/ActualCandidateAssembly.lean#L1172).
The theorem obtains one integer schedule satisfying
[`MixedCandidateWitness.SelectedSchedule`](../Navier/Construction/MixedCandidateWitness.lean#L32),
forms the three convergent
[`SolenoidalDiagonal.potentialSum`](../Navier/Construction/SolenoidalDiagonal.lean#L44)
series, and retains the joint residual-limit extensions used at the terminal
boundary. It returns one force `forcing` together with the candidate equation,
global `C∞` smoothness of `forcing`, terminal derivative data, and the weighted
derivative estimates.

At viscosity one, the force is fixed by the displayed velocity and pressure
through the actual residual equation on `0 < t < 1`:

```text
forcing = ∂t u + (u·∇)u − Δu + ∇p.
```

The force is therefore not an independently tuned perturbation after the
velocity is chosen. The schedule and series form a kernel-checked,
noncomputable classical existential construction. The repository does not
pretend that this large construction has a short elementary closed form or
that it is the executable field shown by the numerical simulator; the latter
is a separate periodic experiment.

The periodic local fields are converted to whole-space fields in
[`R3CompactCandidate`](../Navier/Construction/R3CompactCandidate.lean). Write
`χ` for `SpatialLocalization.spatialCutoff`. The second cutoff and the
resulting force are

```text
χout(x) = χ(x / 2)
F(t,x) = χout(x) forcing(t,x).
```

The original cutoff support lies in the closed cylinder

```text
x₀² + x₁² ≤ 1/16,    |x₂| ≤ 1/4.
```

The outer cutoff equals one on that cylinder. It therefore leaves the force
unchanged where the localized velocity and pressure can be nonzero. Outside
the cylinder, local equality with the periodic construction and vanishing of
the localized fields prove the same equation directly. The force is supported
inside `outerSupport`, the image of this cylinder under `x ↦ 2x`; this is one
fixed compact spatial set.

The selected periodic force is globally `C∞`, and multiplication by the
globally smooth outer cutoff preserves global `C∞` regularity. On physical
time `t ≥ 0`, the resulting force also vanishes after one finite time supplied
by `CompactFutureTimeSupport`. Thus its support on the official half-space is
contained in a bounded spatial region times a finite time interval. The formal
support property does not say that the globally defined smooth extension
vanishes at every negative time.

`EuclideanPDETransport.nativeForce` changes only the normed coordinate
presentation:

```text
Fnative(t,x) = toNative(F(t, toEuclidean(x))).
```

For any viscosity `ν > 0`, `ViscosityTransport.viscosityScaledForce` then
uses the exact equation-preserving scaling

```text
Fν(t,x) = ν² Fnative(ν t,x).
```

The zero Schwartz initial velocity remains zero under the corresponding
scaling. Coordinate transport and positive viscosity scaling preserve the
equation, smoothness, force decay, and the original nonexistence conclusion.
The refined speed-transfer and force-nonzero declarations below are stated in
the normalized unit-viscosity, deadline-one coordinates; this note does not
silently promote them to new native theorems quantified over every viscosity.

## Regularity and decay proved for the force

The selected Euclidean force is `ContDiff ℝ ∞` on all real spacetime, not
merely smooth within `t ≥ 0`. Its native and viscosity-scaled forms have the
same global smoothness.

On the official nonnegative-time domain it satisfies `ForcedDataRapidDecay`:
every order of the full within-Fréchet derivative is bounded after
multiplication by every polynomial space-time weight required by the
whole-space alternative C surface. `ForceCoordinateEquivalence` proves that
this is equivalent, under the same smoothness, to weighted bounds for every
genuine recursively taken ordered time/spatial coordinate partial. The reverse
finite-dimensional estimate has the explicit word-count factor `4^n` at order
`n`.

These are `C∞` and rapid-decay statements. They do not assert analyticity.
They also do not identify the globally defined extension with a globally
compactly supported function at negative times.

## Exact comparison and obstruction

For every `T < 1`, `ComparatorBridge.compact_candidate_unique_on_Icc`
compares the constructed velocity with an arbitrary competitor only on the
closed slab `[0,T]`. The competitor needs:

- `C∞` velocity and pressure on that slab;
- finite kinetic energy with one bound on that slab;
- incompressibility and the same forced Navier–Stokes equation for `0 < t < T`;
- the same zero initial velocity.

It needs no compact support, spatial decay, pressure normalization, future-time
extension, or energy bound beyond that slab. The theorem proves pointwise
equality with the constructed velocity throughout `[0,T]`.

`ConstructedFiniteTimeObstruction.compact_candidate_agrees_with_locally_finite_energy_competitor`
applies these slab comparisons for every `T < 1`. Its new sharp consequence,
`compact_candidate_transfers_speed_unbounded`, says that every competitor
which is smooth before time one, solves the same forced equation from rest, and
has a possibly different finite-energy bound on each compact slab must itself
satisfy `SpeedUnboundedAtOne`. In explicit quantifiers: for every `M > 0` and
every `δ > 0`, some `0 < t < 1` with `1 - δ < t` and some point `x` satisfy
`M < ‖v(t,x)‖`.

This transfer theorem assumes no trace, continuity, boundedness, or solution
after `t = 1`, and no energy constant uniform as `T → 1`. It is therefore the
sharpest current statement of what uniqueness forces on a presingular smooth
finite-energy competitor.

`compact_candidate_force_nonzero_before_one` also proves that this normalized
force is not identically zero on physical presingular spacetime: there are
`0 < t < 1` and `x` with `F(t,x) ≠ 0`. The proof is structural. If the force
vanished there, the smooth zero velocity and zero pressure would satisfy every
local comparison hypothesis, so speed transfer would make the identically
zero velocity unbounded. `selected_force_nonzero_before_one` places this fact,
global force smoothness, and candidate finite energy on the same actual
selected witness.

Two nonextension results follow for the same selected witness:

1. No velocity continuous on `[0,1]` over the candidate's fixed compact
   support can agree with it at every earlier time, because continuity on that
   compact cylinder gives a uniform speed bound.
2. No same-force competitor in the local class above can additionally be
   continuous through time one on that compact support.

Every official Clay-class global smooth bounded-energy competitor transports
into this excluded class, so the original all-positive-viscosity forced
alternative C consumer remains a consequence. The proof does not assume in
advance that a competitor agrees with the candidate; slab uniqueness derives
that agreement from the PDE and initial data.

## Scope limits

The result is for a specifically constructed nonzero smooth force and zero
initial velocity. It does not prove the zero-force global-regularity alternative
A or an unforced blowup statement. It does not provide a velocity that is
smooth through `t = 1`; it proves that the selected velocity and every
competitor in the comparison class have unbounded speed approaching that time.

The current theorems make no exclusion claim about weak, discontinuous,
different-force, different-initial-data, or non-finite-energy continuations.
They also make no assertion that any such continuation exists. Pressure is
used in the smooth presingular comparison equation, but no terminal pressure
trace, support, decay, or gauge bound is assumed.

## Principal Lean declarations

- `Navier.Construction.ActualCandidateAssembly.selected_witness`
- `Navier.Construction.R3CompactCandidate.of_localized_fields`
- `Navier.Analysis.ConstructedForceExtension.selected_compact_candidate_contDiff`
- `Navier.Analysis.ForceCoordinateEquivalence.forcedDataRapidDecay_iff_successivePartials`
- `Navier.Construction.ComparatorBridge.compact_candidate_unique_on_Icc`
- `Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_transfers_speed_unbounded`
- `Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_forces_speed_blowup_in_every_smooth_competitor`
- `Navier.Analysis.ConstructedFiniteTimeObstruction.selected_force_has_compact_physical_support`
- `Navier.Analysis.ConstructedFiniteTimeObstruction.selected_force_nonzero_before_one`
- `Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown`
