# Polya strategy map

Status: **DECOMPOSED**
Polya catalogue snapshot inspected:
**af887a8a62849bd90f3822a349912ba6039acc2d**

This map is based on theorem signatures in Polya/Strategies, not strategy
names. A Polya theorem may close an abstract/topological leaf only after the
Navier-specific data bundle and all analytic hypotheses have been constructed.
It cannot manufacture the missing global a priori estimate.

## 1. Live theorem-shape matches

| Polya theorem | Exact proved shape | Navier use | Required Navier bridge | Route/status |
|---|---|---|---|---|
| Polya.Strategies.FixedPointBanach.apply | A contracting self-map on a nonempty complete metric space has a unique fixed point | Duhamel local solution in a chosen solution space | construct the complete metric space; prove heat/Duhamel self-map and contraction estimates | R2; genuinely applicable after analytic data, but only local/small-data unless a new global gain is proved |
| Polya.Strategies.Bootstrap.apply | A nonempty open-and-closed subset of a preconnected space is universal | continuity method for a time set on which an a priori bound holds | define the good-time set and prove nonempty, open, and closed using PDE estimates | B4/R1/R8; applicable as the final topological step, never the estimate itself |
| Polya.Strategies.VitaliCovering.apply | Select a pairwise-disjoint subfamily such that every original member intersects a selected member of quantitatively comparable size | select parabolic cylinders in CKN/defect analysis | encode cylinders as the family, radius as size, prove the covering hypotheses, then derive the required enlargement inclusion geometrically | R4/R9; applicable to geometric selection, not epsilon regularity itself |
| Polya.Strategies.CompactnessNormalFamilies.apply | Arzelà–Ascoli compactness for a closed equicontinuous family of bounded continuous maps from a compact domain to a compact metric codomain | compactness of uniformly bounded/equicontinuous smooth approximants on a compact cylinder | establish compact domain/range, continuity, equicontinuity, closedness, and connect the limit to the PDE | R4/R10; applicable only to this strong compact setting, not a substitute for weak/Aubin–Lions compactness |
| Polya.Strategies.BanachSteinhaus.apply | Pointwise-bounded continuous linear maps on a Banach space are uniformly operator bounded | uniform bounds for a genuinely linear family such as regularized Stokes/pressure operators | identify continuous linear maps and prove pointwise boundedness on the exact Banach spaces | P1/P7; applicable support lemma, not to the nonlinear Navier–Stokes solution map |
| Polya.Strategies.TriangleInequality.apply | \(\|a+b\|\leq\|a\|+\|b\|\) in a seminormed additive group | split linear and Duhamel terms or frequency blocks | instantiate the actual normed object | P2/R2/R5; low-level exact match |
| Polya.Strategies.ImplicitFunctionTheorem.apply | A Mathlib ImplicitFunctionData bundle yields a local inverse near its base point | optional local solution/manifold chart after encoding a nonlinear PDE map | build Fréchet differentiability and inverse-linearization data in the selected Banach spaces | P4/R2; exact abstract match, but heavier than the semigroup route and wholly local |

These seven entries are the complete live map for the present architecture.
“Applicable” means the conclusion type has a legitimate downstream consumer;
none of the necessary PDE hypotheses is currently realized in Navier.

## 2. Route composition

Only the following compositions are sanctioned:

1. a Navier-specific contraction estimate plus
   FixedPointBanach.apply produces a local mild solution;
2. Navier-specific openness/closedness estimates plus Bootstrap.apply extend a
   bound through a connected time interval;
3. a Navier-specific bad-cylinder family plus VitaliCovering.apply produces a
   disjoint selection used by a CKN estimate;
4. Navier-specific equicontinuity and compact-range estimates plus
   CompactnessNormalFamilies.apply produce a compact family; a separate
   sequential-compactness and PDE-limit bridge must extract the strong local
   limit.

Polya/Compose.lean currently contains combinatorial compositions such as
pigeonhole/averaging, bijection/pigeonhole, double-counting/mean, and
extremal/descent. None has a theorem shape that establishes a Navier–Stokes
critical estimate, so no Compose theorem is mapped into the attack graph.

## 3. Catalogue/name mismatches

The following names sound relevant but their live theorem signatures are for a
different mathematical object. They are explicitly quarantined.

| Catalogue name | Actual live theorem domain | Why it does not fill the Navier role |
|---|---|---|
| EnergyMethod | finite additive-combinatorics additive energy and small difference sets | not the PDE kinetic-energy identity or local energy inequality |
| DyadicDecomposition | a finite subset of natural numbers and dyadic pigeonholing | not Littlewood–Paley projections, Besov norms, or paraproducts |
| Localization | commutative-ring localization | not cutoffs, partitions of unity, or local PDE estimates |
| InductiveScaling | a natural-number/algorithmic recurrence | not Navier–Stokes rescaling or epsilon iteration |
| MaximumPrinciple | a finite-graph/discrete boundary maximum principle | the vector Navier–Stokes system has no such direct scalar maximum principle |
| HoldersInequality | finite real sums | not measure-theoretic mixed spacetime Hölder |
| MinkowskisInequality | finite real \(L^p\) sums | not Bochner/mixed spacetime Minkowski |
| IntegrationByParts | one-dimensional real interval integration | not the divergence theorem on \(\mathbb R^3\), pressure cancellation, or weak PDE integration by parts |
| MonotoneConvergence | a bounded monotone sequence in an order topology | not the measure-theoretic monotone convergence theorem |
| LocalGlobal | Chinese remainder theorem for natural congruences | not local-to-global PDE regularity |
| RestrictionToAnalyze | agreement of functions on a finite union of restrictions | not spatial/frequency restriction of a solution |
| LPDuality | finite-dimensional linear-programming weak duality | not \(L^p\) functional duality |
| ModelCompactness | compactness theorem for first-order logical theories | not compactness of solutions or measures |
| InvariantArgument | invariance along a reflexive-transitive relation | viscosity dissipates energy; no suitable invariant is supplied |

Using one of these strategies solely because its name resembles a PDE method
would be catalogue laundering. A future Polya addition for a genuine PDE
energy identity, Littlewood–Paley theory, mixed-norm inequalities, or
Aubin–Lions compactness must have a new theorem signature and its own audit; it
must not be claimed through these entries.

## 4. Strategy acceptance gate

A Polya invocation enters the formal roadmap only when:

- its exact theorem statement is recorded;
- every Data field is produced from lower Navier nodes;
- the output type is consumed by a named Navier bridge;
- the equation/domain/solution class matches;
- the invocation does not accept the target or its equivalent as data; and
- a fresh Lean check and axiom audit confirms the instantiated theorem.

Until those conditions hold, this document is a strategy-selection map, not a
formal dependency or closure claim.
