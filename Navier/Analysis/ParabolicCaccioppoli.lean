import Navier.Analysis.LocalEnstrophyBalance
import Navier.Breakdown.MaximalNonextension
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Parabolic Caccioppoli layer: local energy identity and the
De Giorgi–Moser iteration engine

This module builds the first two self-contained rungs of the parabolic
Caccioppoli / Moser–De Giorgi layer consumed (as a named residual) by
`ConditionalRegularity.prodiSerrin_interior_outerRegion_bounded` and
`ConditionalRegularity.constantinFefferman_interior_outerRegion_bounded`.
Both rungs are kernel-checked with no new hypotheses:

* `local_energy_balance` — the **pointwise local energy identity** of a
  `PartialClassicalSolution`: testing the momentum equation with `u` gives

  `2⟨u, ∂ₜu⟩ = −(u·∇)|u|² + νΔ(|u|²) − 2ν|∇u|² − 2(u·∇)p + 2⟨u,f⟩`,

  the integrand of every parabolic Caccioppoli inequality.  Multiplied by a
  compactly supported cutoff `φ²` and integrated by parts, the `−(u·∇)|u|²`
  transport and `νΔ(|u|²)` viscous terms convert into the cutoff remainders
  `∫ |u|² (u·∇)φ²` and `ν ∫ |u|² Δ(φ²)`, while `−2ν|∇u|² φ²` is the
  sign-definite dissipation the iteration spends.  The integral step is the
  `CutoffIntegrationByParts` pattern; it is **not** landed here — see the
  frontier note below.
* `deGiorgiMoser_tendsto_zero` and its supporting lemmas — the **numeric
  engine of Moser/De Giorgi iteration**: a nonnegative sequence satisfying
  the superlinear geometric recurrence `A (k+1) ≤ C · b^k · (A k)²`
  (`C, b ≥ 1`) and the smallness condition `C · b² · A 0 ≤ 1/2` decays at
  least geometrically, `A k ≤ (1/2)^{k+1}`, hence tends to `0` and passes
  below any positive threshold.  This is the exact closing step of both
  Moser's `L^∞` iteration and De Giorgi's level-set argument: there `A k`
  is the energy on the `k`-th shrunken parabolic cylinder (Moser) or the
  `k`-th level-set measure/integral (De Giorgi), the exponent `2` is the
  quadratic gain (the classical parabolic gain `1 + 2/n` follows the same
  schema with fractional exponents), and `b^k` is the cylinder-shrinking
  cost.

## Frontier note (the missing rungs, precisely)

The two `ConditionalRegularity` outer-region leaves are **not** closed here.
The exact missing lemmas, in dependency order, are:

1. `cutoff_local_energy_inequality` — the integrated Caccioppoli inequality:
   for a smooth cutoff `φ` compactly supported in a parabolic cylinder,
   `sup_t ∫ |u|² φ² + ν ∬ |∇u|² φ² ≤ C ∬ |u|² (|∂ₜφ|φ + |∇φ|² + |Δφ|)
     + C ∬ (|u|² + |p|) |u| φ |∇φ|`.
   Blocked on: (a) cutoff integration by parts against `local_energy_balance`
   — the `CutoffIntegrationByParts` module lands this pattern for the
   enstrophy density `|ω|²` and the same route applies to `|u|²`; and
   (b) an `L^r` bound on the pressure `p`, which is a Calderón–Zygmund
   singular integral of `u ⊗ u` — the near-field cancellation is a named
   honest residual of `SingularIntegralPrelims` and is absent from Mathlib.
2. `parabolic_sobolev_gain` — the parabolic Sobolev embedding converting
   `sup_t ∫ |u|² φ² + ∬ |∇u|² φ²` into `∬ |u|^{2(1+2/3)} φ^{2(1+2/3)}`
   (the `2(n+2)/n` energy-space embedding).  Blocked on a Sobolev
   inequality on `ℝ³`; the in-repo `SobolevEmbedding` assembly still
   carries its disclosed Plancherel `sorryAx`.
3. `serrin_local_bound` — per-cylinder `L^∞` control of `u` on `Q_{r/2}`
   from the critical mixed norm on `Q_r`, by iterating
   `cutoff_local_energy_inequality` through `parabolic_sobolev_gain` with
   `deGiorgiMoser_tendsto_zero` as the closing engine, uniformly in the
   cylinder centre given the global mixed-norm bound `M`
   [Serrin, Arch. Ration. Mech. Anal. 9 (1962) 187–195].

Rungs 1(b) and 2 are genuine analysis gaps (Calderón–Zygmund theory and the
Sobolev inequality), not elaboration work.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix ContDiff

open Set MeasureTheory Filter

namespace Navier.Analysis.ParabolicCaccioppoli

open Navier
open Navier.Breakdown
open Navier.Analysis.Enstrophy
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.EnstrophyPointwise
open Navier.Analysis.LocalEnstrophyBalance
  (officialInner_add_right officialInner_sub_right officialInner_smul_right)

/-! ### Spatial-slice smoothness on the half-open window -/

/-- **Spatial-slice smoothness bridge, half-open variant.**  Joint `C^∞`
regularity of an evolution on `spacetimeBefore T = [0,T) ×ˢ univ` restricts
to full Fréchet `C^∞` regularity of every spatial slice at `t ∈ [0,T)`.
This is `VorticityTransport.contDiffAt_spatial_slice` with the closed
half-space `Ici 0` replaced by `Ico 0 T`; the proof is identical because the
slice embedding `y ↦ (t,y)` still lands inside the constraint set. -/
theorem contDiffAt_spatial_slice_before {β : Type*} [NormedAddCommGroup β]
    [NormedSpace ℝ β] {F : ℝ → Space → β} {T : ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Space => F z.1 z.2) (spacetimeBefore T))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) (x : Space) :
    ContDiffAt ℝ ∞ (F t) x := by
  have hmem : (t, x) ∈ spacetimeBefore T :=
    Set.mem_prod.mpr ⟨⟨ht0, htT⟩, Set.mem_univ x⟩
  have hG : ContDiffWithinAt ℝ ∞ (fun z : ℝ × Space => F z.1 z.2)
      (spacetimeBefore T) (t, x) := hF (t, x) hmem
  have he : ContDiffWithinAt ℝ ∞ (fun y : Space => (t, y)) Set.univ x :=
    (contDiffAt_const.prodMk contDiffAt_id).contDiffWithinAt
  have hmaps : Set.MapsTo (fun y : Space => (t, y)) Set.univ
      (spacetimeBefore T) := by
    intro y _
    exact Set.mem_prod.mpr ⟨⟨ht0, htT⟩, Set.mem_univ y⟩
  have hcomp := ContDiffWithinAt.comp x hG he hmaps
  rw [show ((fun z : ℝ × Space => F z.1 z.2) ∘ (fun y : Space => (t, y))) =
      F t from rfl] at hcomp
  exact hcomp.contDiffAt Filter.univ_mem

/-- Every spatial slice of a partial classical solution's velocity is `C^∞`. -/
theorem velocity_slice_contDiff {ν : ℝ} {f : ForceField} {u₀ : VelocityField}
    {T : ℝ} (sol : PartialClassicalSolution ν f u₀ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    ContDiff ℝ ∞ (sol.velocity t) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    contDiffAt_spatial_slice_before sol.velocity_smooth ht0 htT x

/-- Every spatial slice of a partial classical solution's pressure is `C^∞`. -/
theorem pressure_slice_contDiff {ν : ℝ} {f : ForceField} {u₀ : VelocityField}
    {T : ℝ} (sol : PartialClassicalSolution ν f u₀ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    ContDiff ℝ ∞ (sol.pressure t) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    contDiffAt_spatial_slice_before sol.pressure_smooth ht0 htT x

/-! ### The pressure-gradient inner product as a directional derivative -/

/-- **Inner product against a coordinate gradient.**  For any vector `a` and
scalar field `q`, `⟨a, (∂₁q, ∂₂q, ∂₃q)⟩ = (Dq) a`: pure linearity of the
Fréchet derivative (a continuous linear map, so no differentiability
hypothesis is needed), expanded on the standard basis
`basisVector i = Pi.single i 1`.  This is the `(u·∇)p` slot of the local
energy identity. -/
theorem officialInner_fderiv_basis (a : Space) (q : Space → ℝ) (x : Space) :
    officialInner a (fun i => fderiv ℝ q x (basisVector i)) =
      fderiv ℝ q x a := by
  have hdecomp : a = ∑ i : Fin 3, a i • basisVector i := by
    rw [show (∑ i : Fin 3, a i • basisVector i) = ∑ i : Fin 3, Pi.single i (a i)
        from Finset.sum_congr rfl fun i _ => by
          ext j
          simp only [basisVector, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
            mul_ite, mul_one, mul_zero]]
    exact (Finset.univ_sum_single a).symm
  rw [officialInner_eq_sum]
  conv_rhs => rw [hdecomp, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [(fderiv ℝ q x).map_smul, smul_eq_mul]

/-! ### The pointwise local energy identity (parabolic Caccioppoli integrand) -/

/-- **Pointwise local energy identity.**  Along a partial classical solution,
at every time `t ∈ [0,T)` and point `x`,

`2⟨u, ∂ₜu⟩ = −(u·∇)|u|² + νΔ(|u|²) − 2ν|∇u|² − 2(u·∇)p + 2⟨u,f⟩`,

where `Δ(|u|²)` and `(u·∇)|u|²` are the repository's coordinate scalar
Laplacian and directional derivative of the energy density `|u|²`, and
`|∇u|² = ∑ᵢ |∂ᵢu|²`.  This is the velocity analogue of
`LocalEnstrophyBalance.local_enstrophy_balance`, with the vortex-stretching
term replaced by the pressure term: the momentum equation tested with `u`,
then `fderiv_normSq_apply` (transport integrand), `scalarLaplacian_normSq`
(pointwise Bochner), and `officialInner_fderiv_basis` (pressure slot).

This is exactly the parabolic Caccioppoli integrand: multiplied by a cutoff
`φ²` and integrated by parts over a parabolic cylinder it yields the local
energy inequality that drives Moser/De Giorgi iteration.  The dissipative
term `−2ν|∇u|²` is sign-definite for `ν ≥ 0`; the transport term
`−(u·∇)|u|²` is a divergence (by incompressibility) and contributes only
cutoff remainders. -/
theorem local_energy_balance
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t < T) (x : Space) :
    2 * officialInner (sol.velocity t x) (timeDerivative sol.velocity t x) =
      - fderiv ℝ (fun y => officialEuclideanNorm (sol.velocity t y) ^ 2) x
          (sol.velocity t x)
      + ν * (∑ i : Fin 3,
          fderiv ℝ (fun z =>
            fderiv ℝ (fun y => officialEuclideanNorm (sol.velocity t y) ^ 2) z
              (basisVector i)) x (basisVector i))
      - 2 * ν * (∑ i : Fin 3,
          officialEuclideanNorm (fderiv ℝ (sol.velocity t) x (basisVector i)) ^ 2)
      - 2 * fderiv ℝ (sol.pressure t) x (sol.velocity t x)
      + 2 * officialInner (sol.velocity t x) (f t x) := by
  have hCD : ContDiff ℝ ∞ (sol.velocity t) := velocity_slice_contDiff sol ht0 htT
  have hdiffAll : ∀ y : Space, DifferentiableAt ℝ (sol.velocity t) y :=
    fun y => (hCD.differentiable (by norm_num)).differentiableAt
  have hdiff2 : DifferentiableAt ℝ (fderiv ℝ (sol.velocity t)) x :=
    ((hCD.fderiv_right (m := ∞) (by norm_num)).differentiable
      (by norm_num)).differentiableAt
  -- The momentum equation at `(t,x)`, tested against `u t x`.
  have hpd := sol.equation t ht0 htT x
  have h2 := congrArg (fun v : Space =>
    2 * officialInner (sol.velocity t x) v) hpd
  simp only [officialInner_add_right, officialInner_sub_right,
    officialInner_smul_right] at h2
  -- Identify the convection, Laplacian, and pressure-gradient slots with
  -- their scalar-identity counterparts.
  have hconv : convection sol.velocity t x =
      fderiv ℝ (sol.velocity t) x (sol.velocity t x) := rfl
  have hlap : laplacian sol.velocity t x =
      ∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (sol.velocity t) z (basisVector i)) x
          (basisVector i) := rfl
  have hgrad : officialInner (sol.velocity t x) (pressureGradient sol.pressure t x) =
      fderiv ℝ (sol.pressure t) x (sol.velocity t x) :=
    officialInner_fderiv_basis _ _ _
  rw [hconv, hlap, hgrad] at h2
  -- Transport integrand identity and pointwise Bochner identity.
  have htransport :
      fderiv ℝ (fun y => officialEuclideanNorm (sol.velocity t y) ^ 2) x
          (sol.velocity t x) =
      2 * officialInner (sol.velocity t x)
        (fderiv ℝ (sol.velocity t) x (sol.velocity t x)) :=
    fderiv_normSq_apply (sol.velocity t) x (sol.velocity t x) (hdiffAll x)
  have hbochner := scalarLaplacian_normSq (sol.velocity t) x hdiffAll hdiff2
  linear_combination h2 + htransport - ν * hbochner

/-! ### The De Giorgi–Moser numeric iteration engine -/

/-- **Rescaled superlinear step.**  For the rescaled majorant
`B k = C · b^{k+2} · A k`, the recurrence `A (k+1) ≤ C · b^k · (A k)²`
upgrades to the clean quadratic form `B (k+1) ≤ (B k)²`: the rescaling
exponent `k+2` is chosen precisely so that `b^{2k+3} ≤ b^{2k+4}` absorbs
the geometric factor `b^k`. -/
theorem deGiorgiMoser_rescaled_sq
    {A : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) {C b : ℝ} (hC : 1 ≤ C) (hb : 1 ≤ b)
    (hrec : ∀ k, A (k + 1) ≤ C * b ^ k * (A k) ^ 2) (k : ℕ) :
    C * b ^ (k + 1 + 2) * A (k + 1) ≤ (C * b ^ (k + 2) * A k) ^ 2 := by
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hb0 : (0 : ℝ) ≤ b := zero_le_one.trans hb
  have hstep := mul_le_mul_of_nonneg_left (hrec k)
    (mul_nonneg hC0 (pow_nonneg hb0 (k + 1 + 2)))
  have hpow : b ^ (k + 1 + 2) * b ^ k ≤ b ^ (k + 2) * b ^ (k + 2) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hb (by omega)
  calc C * b ^ (k + 1 + 2) * A (k + 1)
      ≤ C * b ^ (k + 1 + 2) * (C * b ^ k * (A k) ^ 2) := hstep
    _ = (C ^ 2 * (A k) ^ 2) * (b ^ (k + 1 + 2) * b ^ k) := by ring
    _ ≤ (C ^ 2 * (A k) ^ 2) * (b ^ (k + 2) * b ^ (k + 2)) :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (pow_nonneg hC0 2) (pow_nonneg (hA k) 2))
    _ = (C * b ^ (k + 2) * A k) ^ 2 := by ring

/-- **Rescaled geometric decay.**  Under the smallness condition
`C · b² · A 0 ≤ 1/2`, the rescaled majorant satisfies
`B k ≤ (1/2)^{k+1}`: induction on `B (k+1) ≤ (B k)²`, using
`((1/2)^{k+1})² = (1/2)^{2k+2} ≤ (1/2)^{k+2}` (the base `1/2 < 1` shrinks
larger powers). -/
theorem deGiorgiMoser_rescaled_le
    {A : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) {C b : ℝ} (hC : 1 ≤ C) (hb : 1 ≤ b)
    (hrec : ∀ k, A (k + 1) ≤ C * b ^ k * (A k) ^ 2)
    (h0 : C * b ^ 2 * A 0 ≤ 1 / 2) :
    ∀ k, C * b ^ (k + 2) * A k ≤ (1 / 2) ^ (k + 1) := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
      have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
      have hb0 : (0 : ℝ) ≤ b := zero_le_one.trans hb
      have hsq := deGiorgiMoser_rescaled_sq hA hC hb hrec k
      have hsq2 : (C * b ^ (k + 2) * A k) ^ 2 ≤ ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (mul_nonneg hC0 (pow_nonneg hb0 _)) (hA k)) ih 2
      have hdecay : ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 ≤ (1 / 2) ^ (k + 1 + 1) := by
        rw [pow_two, ← pow_add]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      exact (hsq.trans hsq2).trans hdecay

/-- **Explicit geometric majorant.**  Since `C · b^{k+2} ≥ 1`, the rescaled
decay delivers `A k ≤ (1/2)^{k+1}` outright. -/
theorem deGiorgiMoser_le_geometric
    {A : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) {C b : ℝ} (hC : 1 ≤ C) (hb : 1 ≤ b)
    (hrec : ∀ k, A (k + 1) ≤ C * b ^ k * (A k) ^ 2)
    (h0 : C * b ^ 2 * A 0 ≤ 1 / 2) (k : ℕ) :
    A k ≤ (1 / 2) ^ (k + 1) := by
  have hB := deGiorgiMoser_rescaled_le hA hC hb hrec h0 k
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hb1 : (1 : ℝ) ≤ b ^ (k + 2) := by
    simpa using pow_le_pow_right₀ hb (Nat.zero_le (k + 2))
  have h1 : (1 : ℝ) ≤ C * b ^ (k + 2) := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ C * b ^ (k + 2) :=
        mul_le_mul hC hb1 zero_le_one hC0
  calc A k = 1 * A k := (one_mul _).symm
    _ ≤ (C * b ^ (k + 2)) * A k := mul_le_mul_of_nonneg_right h1 (hA k)
    _ ≤ (1 / 2) ^ (k + 1) := hB

/-- **The De Giorgi–Moser iteration engine.**  A nonnegative sequence
satisfying the superlinear geometric recurrence
`A (k+1) ≤ C · b^k · (A k)²` with `C, b ≥ 1` and starting below the
smallness threshold `C · b² · A 0 ≤ 1/2` converges to `0`.

This is the closing step of the parabolic Moser and De Giorgi arguments:
there `A k` is the `L^{2κ^k}`-type energy on the `k`-th shrunken parabolic
cylinder (Moser) or the `k`-th level-set energy (De Giorgi); the exponent
`2` is the quadratic gain, and `b^k` prices the cylinder shrinkage.  The
smallness hypothesis is supplied in applications by the Caccioppoli
inequality applied to the first cylinder. -/
theorem deGiorgiMoser_tendsto_zero
    {A : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) {C b : ℝ} (hC : 1 ≤ C) (hb : 1 ≤ b)
    (hrec : ∀ k, A (k + 1) ≤ C * b ^ k * (A k) ^ 2)
    (h0 : C * b ^ 2 * A 0 ≤ 1 / 2) :
    Tendsto A atTop (nhds 0) := by
  have hgeom : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) atTop (nhds 0) := by
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)).mul_const (1 / 2 : ℝ)
    rw [zero_mul] at h2
    have heq : (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) =
        fun k => (1 / 2 : ℝ) ^ k * (1 / 2) :=
      funext fun k => pow_succ _ _
    rw [heq]
    exact h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom
    (fun k => hA k) (fun k => deGiorgiMoser_le_geometric hA hC hb hrec h0 k)

/-- **Threshold passage.**  The iterated energies pass below any positive
threshold: the form in which the De Giorgi argument consumes
`deGiorgiMoser_tendsto_zero` (the limit level is reached because every
positive overshoot is eventually excluded). -/
theorem deGiorgiMoser_eventually_lt
    {A : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) {C b : ℝ} (hC : 1 ≤ C) (hb : 1 ≤ b)
    (hrec : ∀ k, A (k + 1) ≤ C * b ^ k * (A k) ^ 2)
    (h0 : C * b ^ 2 * A 0 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → A k < ε := by
  have ht := deGiorgiMoser_tendsto_zero hA hC hb hrec h0
  have hev : ∀ᶠ k in atTop, A k < ε := ht.eventually (Iio_mem_nhds hε)
  exact eventually_atTop.1 hev

end Navier.Analysis.ParabolicCaccioppoli
