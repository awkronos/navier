# NAVIER-INTAKE-578accbf — typed NOOP receipt (2026-11-19)

Item: arXiv 2611.24340, "On the Critical Exponent for a Time--Space Fractional
Reaction--Diffusion Equation with a Slowly Varying Time-Dependent Source",
Ahmad Z. Fino & Mohamed Majdoub, submitted 2026-11-18, math.AP.

The paper classifies Fujita-type critical exponents for the SCALAR Cauchy problem
  ∂_t^α u + (−Δ)^(θ/2) u = h(t) u^p,  α ∈ (0,1], θ ∈ (0,2], h(t) ~ t^γ ℓ(t) (Karamata ℓ),
with p_c(γ) = 1 + θ(γ+1)/N (α=1) and p_c(γ,α) = 1 + θ(γ+α)/(Nα) (α<1), extending
Meier (1990) to the nonlocal setting.

Verdict: NOOP — off-carrier. navier formalizes the Navier–Stokes system
(bilinear transport (u·∇)u, incompressibility, pressure). Its OPEN obligations are:
1. open_A_whole_space_unforced — Clay global regularity (whole space).
2. open_B_periodic_unforced — Clay global regularity (periodic).
3. open_bkm_vorticity_integral_divergence_residual — quantitative power-law envelopes
   V u t ~ (1−t)^{−α}, α>1, for the CONSTRUCTED forced-NS vorticity rate. The frontier
   map states this surviving work is "construction work, not a scalar argument".
4. open_mild_assembly_leaves_instantiation — non-degenerate mild fixed point on the
   NS Wiener carrier.
None states, imports, or consumes a semilinear power-source critical exponent, a
Caputo time-fractional derivative, or Karamata slow variation. The matched profile
keyword "blow-up" is shared vocabulary between scalar Fujita blow-up and NS
breakdown, not a dependency. The repository's only "Fujita" occurrences are 10
citations of Fujita–Kato 1964 (NS initial-value theory) in doc comments — a
different contribution.

No change made to navier. Seat holds a read-only depth-50 checkout at origin/main
(a72c19b), zero writes (git status shows only the lane.log the dispatcher created).

Commands that measured this (all run in the seat, /Users/timothyjacoby/lane-seats/SWARM-1031/NAVIER-INTAKE-578accbf):
- curl -sL https://arxiv.org/abs/2611.24340 | abstract parse → verbatim abstract above, rc=0
- git grep -n -i 'fujita' -- '*.lean' '*.md' '*.yaml' | wc -l → 10, rc=0; every hit a Fujita–Kato NS citation
- git grep -n -i -E 'caputo|karamata|semilinear|meier|slowly.?varying|reaction.?diffusion|fujita exponent|critical exponent' -- '*.lean' '*.md' '*.yaml' → no output, rc=1
- git grep -c 'status: "OPEN"' formalization.yaml → 4, rc=0
- python3 ~/.claude/scripts/prior_art.py <seat> fujita → "PRIOR ART: none found", rc=0
