import Navier.Analysis.LittlewoodPaleyPhysical
import Navier.Analysis.HorizonFreeBudgetRestart
import Navier.Analysis.EnvelopePropagation
import Navier.Analysis.AprioriCriticalControlQuantifiers

/-!
# Producing `WienerH3Apriori` from a damped `H³` rate balance

**The crown seat this lane attacks.**  `WienerRestartLeaf.crown_of_wienerH3Apriori`
reduces `ProblemStatements.WholeSpaceGlobalRegularity` to two premises,
`WienerH3Apriori N` and `APrioriIn RegularOnCompacts N`.  At this base the first premise
is discharged only *tautologically*: `HorizonFreeBudgetRestart` proves
`wienerH3Apriori_h3EnvelopeControl` for `N := h3EnvelopeControl`, but that control is
**defined** as the supremum of the very `h3F` weights its conclusion asks for, so the
budget is `K = M` by reading-off and no estimate is made.  All the difficulty then sits in
the other premise (`APrioriIn RegularOnCompacts h3EnvelopeControl`, open, decomposed into
rungs P0–P4 by `EnvelopePropagation`).  The premise the ledger (F-025) *intends* is the
substantive one: `WienerH3Apriori` for a control that states a genuine dynamical budget.
The repo already contains such a control —
`AprioriCriticalControlQuantifiers.bkmVorticityControl`, the BKM vorticity integral
`⨆ s ∈ Ico 0 T, ∫⁻ t in Icc 0 s, ⨆ x, ‖ω t x‖` — and `WienerH3Apriori bkmVorticityControl`
is exactly the classical *conditional* a priori estimate:

> along a regular whole-space solution whose integrated vorticity supremum stays below
> `M`, the Fourier `H³` weight of every representing profile of every slice is below one
> `K = K(ν, u₀, M)`,

which is the damped `Hˢ` estimate the OPEN_FRONTIER_MAP (P)-verdict row sets out to
produce.  This module lands the assembly that turns that estimate into a theorem from one
named local-in-time balance, consuming the pieces the estate has already certified:
`LittlewoodPaleyPhysical.gradSupLogHyp_proved` (the `‖∇u‖∞` log bound on the Wiener
carrier), `SobolevInterpolation.lintegral_interpolation` (the dissipation lower bound),
`DampedThresholdGronwall.damped_rate_reduction` (the threshold), and
`DampedThresholdGronwall.threshold_gronwall_uniform` with its `hAc`/`hAd` seats discharged
by `EnvelopePropagation` §2.

**§1 — the weight transfer (unconditional).**  `GradSupLogHyp` measures a profile in
`profH3` / `profL2` (the integrals of `‖ξ‖⁶ ∑ᵢ |aᵢ|²` and `∑ᵢ |aᵢ|²`), while the crown's
conclusion is written in `h3F` (the `(1 + ‖ξ‖)⁶` weight, coordinate by coordinate).
Nothing at this base connected them, and that absent bridge is why the landed log bound
had no consumer reaching `WienerH3Apriori`.  `h3F_coord_le_profNorms` supplies it with an
explicit dimension-free constant: `(1 + r)⁶ ≤ 64 (1 + r⁶)` split at `r = 1`, the coordinate
absorbed into the `∑ⱼ`, and the two `Rep` integrabilities from `LittlewoodPaleyBlock` (D1)
used to collapse each `lintegral` to `ofReal` of a real integral.  The constant is `64`
rather than the sharp `32` because the proof is a case split at `r = 1` and takes no
convexity input; the restart step length already carries a `10⁶` denominator, so the slack
is not load-bearing.

**§2 — the primitive, named.**  `H3DampedRateBoard` bundles what the crown cannot get from
`SolvesBefore` + `RegularOnCompacts` as stated: a `Rep` profile family along the evolution,
datum-level bounds `Y₀` / `E₀` on its `Ḣ³` and `L²` profile norms, continuity of the
vorticity level, and the `H³` **energy balance** for the family's `Ḣ³` weight,

    Y' ≤ C·y·(1 + log(1 + Y/y) + log(1 + E₀/y))·Y − ν·E₀^(−θ)·Y^θ·Y,   y := vortLevel u,

in which the growth factor is exactly the `gradSupLogHyp_proved` envelope (that theorem's
right side, slice by slice) and the dissipation term is exactly the `SobolevInterpolation`
lower bound with exponent `θ = 2/s`.  The board asks nothing about the pressure, the
equation, or uniqueness: its only content beyond §1 is that `t ↦ profH3 (a t)` has the
balance above.  **That is this lane's single named residual** — the time-derivative
identity for the profile `Ḣ³` weight along a `SolvesBefore` member, i.e. the `H³` energy
balance on the Wiener carrier, which is the same content as the frontier map's item-6 costs
(a)–(c) and is not supplied by any declaration in the repo.  It is stated in the repo's own
vocabulary (`Rep`, `profH3`, `vorticityRate`, `bkmVorticityControl`), so it is checkable
against the carrier rather than against prose.

**§3 — the assembly (proved here).**  Four steps, none of them carried as hypothesis:
1. `rate_budget_of_control_le` transfers the *control* bound `bkmVorticityControl T u ≤ M`
   into the Gronwall's *budget* bound `∫₀ᵗ y ≤ M` for the pointwise vorticity supremum rate
   `y := (vorticityRate u ·).toReal`.  Both directions matter: `y` dominates the vorticity by
   definition of the `iSup` (given the level is finite), and `ENNReal.ofReal_toReal` turns
   the finiteness clause into `ofReal ∘ y = vorticityRate`, which makes the transfer an
   equality of `lintegral`s.  Without the finiteness clause the `toReal` of `⊤` is `0` and
   the domination reverses — that is why the board names it.
2. `h3Reduction_at_one` runs `damped_rate_reduction` at the vorticity cutoff `η := 1` to
   extract the threshold `L` and the constant `cBracket E₀`.
3. `h3Z_threshold_ineq` converts the `Y`-balance into the threshold-Gronwall slot
   `Z' ≤ a·(c + Z)` for `Z = log(1 + Y)`, `a = C·y`.  **The vorticity cutoff that
   `damped_rate_reduction` produces disappears:** below `η` the dissipation already forces
   `Y' ≤ 0`, so `Z' ≤ 0 ≤ a·(c + Z)`, and above `η` the reduction's majorant divides cleanly
   by `1 + Y`.  The resulting rate is `C·y`, a *continuous* function whenever the vorticity
   level is — so `EnvelopePropagation` §2's `hAc`/`hAd` supply applies to it without
   patching.  Had the cutoff been kept, `hAd` would fail at the switch times.
4. `threshold_gronwall_uniform_of_continuousRate` closes
   `Z(t) ≤ (c + max(Z 0, Λ))·exp(C·M) − c`, and `h3F_coord_le_profNorms` plus the budget
   collapse `h3EnvelopeBudget_eq_iSup` convert the real bound into `h3F ≤ ENNReal.ofReal K`
   for **every** representer of the slice, not merely the board's family: one bounded family
   controls the supremum because `h3F` cannot see past the a.e.-unique representer.

**§4 — scope, honestly.**  Nothing here proves global regularity, and nothing here proves
`WienerH3Apriori bkmVorticityControl` unconditionally: `H3DampedRateBoard` is a named
hypothesis and is *not* exhibited as inhabited.  Three facts are recorded so the reduction
is not mistaken for a closure.  (i) Composing this lane's producer with the crown still
needs `APrioriIn RegularOnCompacts bkmVorticityControl`, the statement that a regular
solution's integrated vorticity supremum is a priori bounded by a datum constant; by BKM
that is the hard half of global regularity, not a packaging of it — §5 states the resulting
two-premise form explicitly.  (ii) The tautological route is *not* recoverable by
re-instantiating this producer at `h3EnvelopeControl`: `WienerH3Apriori` is stated for a
fixed control, and the board's rate is the vorticity level, which the envelope control does
not bound.  (iii) The board's `E₀` is a *strict* upper bound on the profile `L²` norm used
as the interpolation energy; the ledger's F-025 reading has `E ≤ ‖u₀‖₂` by energy decay, so
exhibiting the board additionally requires the energy inequality on the Wiener carrier,
which is likewise not in the repo.
What lands is the reduction and the two unconditional bridges (§1, and the
`hAc`/`hAd`-compatible rate of §3 step 3).  The produced constant is explicit:

    K = 64 · ((exp((c + max(log(1 + Y₀), log(1 + L))) · exp(C·M) − c) − 1)² + E₀²).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate BigOperators

namespace Navier.Analysis.WienerH3DampedProducer

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerSobolevL1
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.WienerGradLog
open Navier.Analysis.HorizonFreeBudgetRestart
open Navier.Analysis.EnvelopeFourierUniqueness
open Navier.Analysis.LittlewoodPaleyBlock
open Navier.Analysis.DampedThresholdGronwall
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.AprioriCriticalControlQuantifiers
open Navier.Analysis.EnvelopePropagation (threshold_gronwall_uniform_of_continuousRate)
open Navier.Analysis.OfficialABEncoding (officialEuclideanNorm)

/-! ## 1. The weight transfer: `h3F` against `profH3` and `profL2` -/

/-- The pointwise bracket comparison `(1 + r)⁶ ≤ 64 (1 + r⁶)`, split at `r = 1`.  Below `1`
the left side is `≤ 2⁶ = 64`; above `1` it is `≤ (2r)⁶ = 64 r⁶`.  Not sharp — the split
takes no convexity input. -/
theorem six_pow_one_add_le (r : ℝ) (hr : 0 ≤ r) : (1 + r) ^ 6 ≤ 64 * (1 + r ^ 6) := by
  by_cases h : r ≤ 1
  · have h1 : (1 + r) ^ 6 ≤ (2 : ℝ) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    calc (1 + r) ^ 6 ≤ (2 : ℝ) ^ 6 := h1
      _ = 64 := by norm_num
      _ ≤ 64 * (1 + r ^ 6) := by nlinarith [pow_nonneg hr 6]
  · push_neg at h
    calc (1 + r) ^ 6 ≤ (2 * r) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      _ = 64 * r ^ 6 := by ring
      _ ≤ 64 * (1 + r ^ 6) := by nlinarith [pow_nonneg hr 6]

/-- The profile `L²` density `∑ᵢ |aᵢ|²`: the integrand of `profL2 ^ 2`. -/
def profL2Density (a : ES → ComplexSpace) : ES → ℝ :=
  fun ξ => ∑ j : Fin 3, ‖a ξ j‖ ^ 2

/-- The profile `Ḣ³` density `‖ξ‖⁶ ∑ᵢ |aᵢ|²`: the integrand of `profH3 ^ 2`. -/
def profH3Density (a : ES → ComplexSpace) : ES → ℝ :=
  fun ξ => ‖ξ‖ ^ 6 * profL2Density a ξ

@[simp] lemma profL2Density_apply (a : ES → ComplexSpace) (ξ : ES) :
    profL2Density a ξ = ∑ j : Fin 3, ‖a ξ j‖ ^ 2 := rfl

/-- The `L²` density is pointwise nonnegative. -/
theorem profL2Density_nonneg (a : ES → ComplexSpace) (ξ : ES) : 0 ≤ profL2Density a ξ :=
  Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) 2

/-- The `Ḣ³` density is pointwise nonnegative. -/
theorem profH3Density_nonneg (a : ES → ComplexSpace) (ξ : ES) : 0 ≤ profH3Density a ξ :=
  mul_nonneg (pow_nonneg (norm_nonneg _) 6) (profL2Density_nonneg a ξ)

/-- `profH3` is nonnegative: it is a square root. -/
theorem profH3_nonneg (a : ES → ComplexSpace) : 0 ≤ profH3 a := Real.sqrt_nonneg _

/-- `profL2` is nonnegative: it is a square root. -/
theorem profL2_nonneg (a : ES → ComplexSpace) : 0 ≤ profL2 a := Real.sqrt_nonneg _

/-- The square of `profH3` is the integral of its density: the `Real.sqrt` reconstructs
because the density is integrable (D1) and nonnegative. -/
theorem integral_profH3Density (a : ES → ComplexSpace) :
    (∫ ξ : ES, profH3Density a ξ ∂volume) = profH3 a ^ 2 := by
  unfold profH3 profH3Density profL2Density
  refine (Real.sq_sqrt ?_).symm
  exact MeasureTheory.integral_nonneg fun ξ =>
    mul_nonneg (pow_nonneg (norm_nonneg _) 6)
      (Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2)

/-- The square of `profL2` is the integral of its density. -/
theorem integral_profL2Density (a : ES → ComplexSpace) :
    (∫ ξ : ES, profL2Density a ξ ∂volume) = profL2 a ^ 2 := by
  unfold profL2 profL2Density
  refine (Real.sq_sqrt ?_).symm
  exact MeasureTheory.integral_nonneg fun ξ =>
    Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2

/-- The square of an `ENNReal` norm is `ofReal` of the real square: `‖z‖ₑ² = ofReal ‖z‖²`.
Proved through `ofReal_mul` rather than `ofReal_pow`, whose side condition this avoids. -/
theorem enorm_sq_eq_ofReal_sq {E : Type _} [SeminormedAddCommGroup E] (z : E) :
    ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  have hz : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := (ofReal_norm z).symm
  rw [hz, pow_two, ← ENNReal.ofReal_mul (norm_nonneg _), pow_two]

/-- **The weight transfer.**  For a represented profile, the coordinate `h3F` weight that
`WienerH3Apriori` concludes about is at most `64` times the sum of the squared `profH3` and
`profL2` norms that `GradSupLogHyp` is written in.  This is the bridge that lets the landed
Littlewood–Paley log bound reach the crown's conclusion; nothing else at this base connected
the two normalisations, which is why `gradSupLogHyp_proved` had no consumer. -/
theorem h3F_coord_le_profNorms {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    (i : Fin 3) :
    h3F (fun ξ => a ξ i) ≤ ENNReal.ofReal (64 * (profH3 a ^ 2 + profL2 a ^ 2)) := by
  unfold h3F
  -- the weight `(1 + ‖ξ‖)⁶` is nonnegative everywhere
  have hw0 : ∀ ξ : ES, (0 : ℝ) ≤ (1 + ‖ξ‖) ^ 6 := fun ξ =>
    pow_nonneg (by linarith [norm_nonneg (ξ : ES)]) 6
  -- step 1: the `h3F` integrand is `ofReal` of the real density product
  have hstep1 : (fun ξ : ES => ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖a ξ i‖ₑ ^ 2) ≤ᵐ[volume]
      fun ξ : ES => ENNReal.ofReal ((1 + ‖ξ‖) ^ 6 * profL2Density a ξ) :=
    Eventually.of_forall fun ξ => by
      calc ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖a ξ i‖ₑ ^ 2
          = ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ENNReal.ofReal (‖a ξ i‖ ^ 2) := by
              rw [enorm_sq_eq_ofReal_sq]
        _ = ENNReal.ofReal ((1 + ‖ξ‖) ^ 6 * ‖a ξ i‖ ^ 2) :=
              (ENNReal.ofReal_mul (hw0 ξ)).symm
        _ ≤ ENNReal.ofReal ((1 + ‖ξ‖) ^ 6 * profL2Density a ξ) :=
              ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_left
                  (Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg _) 2)
                    (Finset.mem_univ i)) (hw0 ξ))
  -- step 2: split the weight at `‖ξ‖ = 1` into a single integrable `ofReal` majorant
  set Maj : ES → ℝ := fun ξ => 64 * profL2Density a ξ + 64 * profH3Density a ξ with hMajdef
  have hstep2 : (fun ξ : ES => ENNReal.ofReal ((1 + ‖ξ‖) ^ 6 * profL2Density a ξ)) ≤ᵐ[volume]
      fun ξ : ES => ENNReal.ofReal (Maj ξ) :=
    Eventually.of_forall fun ξ => ENNReal.ofReal_le_ofReal
      (calc (1 + ‖ξ‖) ^ 6 * profL2Density a ξ
          ≤ 64 * (1 + ‖ξ‖ ^ 6) * profL2Density a ξ :=
              mul_le_mul_of_nonneg_right (six_pow_one_add_le ‖ξ‖ (norm_nonneg _))
                (profL2Density_nonneg a ξ)
        _ = 64 * profL2Density a ξ + 64 * (‖ξ‖ ^ 6 * profL2Density a ξ) := by ring
        _ = 64 * profL2Density a ξ + 64 * profH3Density a ξ := by
              unfold profH3Density; ring
        _ = Maj ξ := rfl)
  -- the majorant is integrable (D1), so its lintegral is `ofReal` of a real integral
  have hI2 : Integrable (fun ξ : ES => 64 * profL2Density a ξ) :=
    hr.integrable_profL2_integrand.const_mul 64
  have hI3 : Integrable (fun ξ : ES => 64 * profH3Density a ξ) :=
    hr.integrable_profH3_integrand.const_mul 64
  have hMaj_int : Integrable Maj := hI2.add hI3
  have hMaj_ofReal : ∫⁻ ξ : ES, ENNReal.ofReal (Maj ξ) ∂volume =
      ENNReal.ofReal (∫ ξ : ES, Maj ξ ∂volume) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hMaj_int
      (Eventually.of_forall fun ξ => add_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) (profL2Density_nonneg a ξ))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) (profH3Density_nonneg a ξ)))).symm
  have hMaj_integral : ∫ ξ : ES, Maj ξ ∂volume = 64 * profL2 a ^ 2 + 64 * profH3 a ^ 2 := by
    show ∫ ξ : ES, (64 * profL2Density a ξ + 64 * profH3Density a ξ) ∂volume = _
    rw [MeasureTheory.integral_add hI2 hI3, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, integral_profL2Density, integral_profH3Density]
  calc ∫⁻ ξ : ES, ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖a ξ i‖ₑ ^ 2
      ≤ ∫⁻ ξ : ES, ENNReal.ofReal ((1 + ‖ξ‖) ^ 6 * profL2Density a ξ) ∂volume :=
          lintegral_mono_ae hstep1
    _ ≤ ∫⁻ ξ : ES, ENNReal.ofReal (Maj ξ) ∂volume := lintegral_mono_ae hstep2
    _ = ENNReal.ofReal (∫ ξ : ES, Maj ξ ∂volume) := hMaj_ofReal
    _ = ENNReal.ofReal (64 * profL2 a ^ 2 + 64 * profH3 a ^ 2) := by rw [hMaj_integral]
    _ ≤ ENNReal.ofReal (64 * (profH3 a ^ 2 + profL2 a ^ 2)) :=
          ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-! ## 2. The named primitive: the `H³` rate board on the Wiener carrier -/

/-- The pointwise vorticity **level**: the `toReal` of `vorticityRate`, i.e.
`⨆ x, ‖ω t x‖` read as a real.  Nonnegative always; equal to the `ENNReal` rate exactly when
the level is finite. -/
def vortLevel (u : VelocityEvolution) : ℝ → ℝ := fun t => (vorticityRate u t).toReal

/-- **The named `H³` rate board** at a datum `(ν, u₀)` and a vorticity budget `M`.

It says: for every horizon and every `SolvesBefore` + `RegularOnCompacts` member from the
datum whose BKM vorticity control stays below `M`, there is a single `Rep` profile family
`a` along the evolution, with datum-level `Ḣ³` / `L²` profile bounds `Y₀` / `E₀`, whose
`Ḣ³` weight `Y t := profH3 (a t)` is continuous on `[0, T)`, has a right derivative `Yd`
everywhere on `[0, T)`, and satisfies the damped `H³` energy balance

    Yd t ≤ C·y·(1 + log(1 + Y/y) + log(1 + E₀/y))·Y − ν·E₀^(−θ)·Y^θ·Y,  y := vortLevel u t.

The growth coefficient is the `gradSupLogHyp_proved` envelope; the damping exponent `θ` is
`2/s` (`s = 3` here) from `SobolevInterpolation`; `E₀` is the energy entering that
interpolation.  Finiteness of the vorticity level is included because without it the
`toReal` of `⊤` is `0` and `y` would *under*-state the vorticity (§3 step 1).

What the board does **not** supply, and what no declaration in the repo supplies, is the
identity `Yd = d/dt profH3 (a t)` itself — the `H³` energy balance for the profile weight
along a `SolvesBefore` member.  That is this lane's named residual. -/
def H3DampedRateBoard (ν : ℝ) (u₀ : SchwartzVelocity) (M : ℝ≥0) : Prop :=
  ∃ (C θ Y₀ E₀ : ℝ), 0 ≤ C ∧ 0 < θ ∧ 0 < E₀ ∧ 0 ≤ Y₀ ∧
    ∀ (T : ℝ), 0 < T → ∀ (u : VelocityEvolution) (p : PressureEvolution),
      (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → RegularOnCompacts T u p →
      bkmVorticityControl T u ≤ (M : ℝ≥0∞) →
      ∃ (a : ℝ → ES → ComplexSpace) (Yd : ℝ → ℝ),
        (∀ t ∈ Ico (0 : ℝ) T, Rep (u t) (a t)) ∧
        (∀ t, profH3 (a t) ≤ Y₀) ∧
        (∀ t, profL2 (a t) ≤ E₀) ∧
        ContinuousOn (vortLevel u) (Ico (0 : ℝ) T) ∧
        (∀ t ∈ Ico (0 : ℝ) T, vorticityRate u t ≠ ⊤) ∧
        ContinuousOn (fun t => profH3 (a t)) (Ico (0 : ℝ) T) ∧
        (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt (fun s => profH3 (a s)) (Yd t) (Ici t) t) ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          Yd t ≤
            C * vortLevel u t *
                (1 + Real.log (1 + profH3 (a t) / vortLevel u t) +
                  Real.log (1 + E₀ / vortLevel u t)) *
              profH3 (a t) -
            ν * E₀ ^ (-θ) * profH3 (a t) ^ θ * profH3 (a t)

/-! ## 3. The assembly -/

/-- **§3 step 1 — the budget transfer.**  Under the finiteness clause the BKM *control*
bound `bkmVorticityControl T u ≤ M` becomes the Gronwall *budget* bound
`∫₀ᵗ vortLevel u ≤ M` for every `t ∈ [0, T)`.  The transfer is an equality of `lintegral`s —
`ofReal ∘ vortLevel = vorticityRate` pointwise on `[0, T)` (`ENNReal.ofReal_toReal` against
the finiteness clause) — so nothing is lost, and the direction is exact rather than
one-sided. -/
theorem rate_budget_of_control_le {u : VelocityEvolution} {T : ℝ} {M : ℝ≥0}
    (hN : bkmVorticityControl T u ≤ (M : ℝ≥0∞))
    (hf : ∀ t ∈ Ico (0 : ℝ) T, vorticityRate u t ≠ ⊤)
    (hc : ContinuousOn (vortLevel u) (Ico (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ∫ x in (0 : ℝ)..t, vortLevel u x ∂volume ≤ (M : ℝ) := by
  have hsub : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) T :=
    fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩
  have hlev : ∫⁻ x in Icc (0 : ℝ) t, vorticityRate u x ∂volume ≤ ENNReal.ofReal (M : ℝ) :=
    ((le_iSup₂_of_le t ht
        (le_rfl : ∫⁻ x in Icc (0 : ℝ) t, vorticityRate u x ∂volume ≤
          ∫⁻ x in Icc (0 : ℝ) t, vorticityRate u x ∂volume)).trans hN).trans
      (le_of_eq ((ENNReal.ofReal_coe_nnreal (p := M)).symm))
  have hof : (fun x : ℝ => ENNReal.ofReal (vortLevel u x)) =ᵐ[volume.restrict (Icc (0 : ℝ) t)]
      fun x : ℝ => vorticityRate u x :=
    (ae_restrict_iff' measurableSet_Icc).mpr
      (ae_of_all volume fun x hx => by
        show ENNReal.ofReal (vortLevel u x) = vorticityRate u x
        exact ENNReal.ofReal_toReal (hf x (hsub hx)))
  have hint : Integrable (vortLevel u) (volume.restrict (Icc (0 : ℝ) t)) :=
    (hc.mono hsub).integrableOn_Icc
  have h_eq : ∫⁻ x in Icc (0 : ℝ) t, vorticityRate u x ∂volume =
      ENNReal.ofReal (∫ x in Icc (0 : ℝ) t, vortLevel u x ∂volume) := by
    rw [← lintegral_congr_ae hof]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
  rw [h_eq] at hlev
  have hIcc := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlev
  rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
  exact hIcc

/-- The threshold-Gronwall constant `c = 1 + log 2 + log(1 + E₀)`: the growth coefficient
the `damped_rate_reduction` exposes at the cutoff `η = 1`. -/
def cBracket (E₀ : ℝ) : ℝ := 1 + Real.log 2 + Real.log (1 + E₀)

theorem cBracket_pos (E₀ : ℝ) (hE₀ : 0 < E₀) : 0 < cBracket E₀ := by
  refine add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg zero_lt_one ?_) ?_
  · exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  · exact Real.log_nonneg (by linarith)

/-- **§3 step 2 — the threshold.**  `damped_rate_reduction` specialised to the vorticity
cutoff `η = 1`, with the bracket rewritten into `cBracket`, and the `if`-cutoff eliminated
into the two branches the assembly needs (above `η` the log-envelope rate; below `η` the
dissipation already wins, so the rate is `≤ 0`). -/
theorem h3Reduction_at_one {C ν E₀ θ : ℝ} (hC : 0 ≤ C) (hν : 0 < ν) (hE₀ : 0 < E₀)
    (hθ : 0 < θ) :
    ∃ L : ℝ, 1 ≤ L ∧
      (∀ y Y : ℝ, 0 ≤ y → (1 : ℝ) ≤ y → L ≤ Y →
        C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E₀ / y)) * Y -
            ν * E₀ ^ (-θ) * Y ^ θ * Y ≤
          C * y * (cBracket E₀ + Real.log (1 + Y)) * (1 + Y)) ∧
      (∀ y Y : ℝ, 0 ≤ y → y < 1 → L ≤ Y →
        C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E₀ / y)) * Y -
            ν * E₀ ^ (-θ) * Y ^ θ * Y ≤ 0) := by
  obtain ⟨L, hL1, hL⟩ := damped_rate_reduction hC hν hE₀ zero_lt_one hθ
  have hcb : (1 : ℝ) + Real.log (1 + 1 / (1 : ℝ)) + Real.log (1 + E₀ / (1 : ℝ)) =
      cBracket E₀ := by
    have h1 : (1 : ℝ) / 1 = 1 := by norm_num
    rw [h1, div_one]
    show (1 : ℝ) + Real.log (1 + 1) + Real.log (1 + E₀) = _
    unfold cBracket
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
  refine ⟨L, hL1, fun y Y hy hy1 hY => ?_, fun y Y hy hy' hY => ?_⟩
  · have hh := hL y Y hy hY
    rw [if_pos hy1, hcb] at hh
    exact hh
  · have hh := hL y Y hy hY
    rw [if_neg (not_le.mpr hy')] at hh
    exact hh

/-- **§3 step 3 — the threshold inequality with the cutoff removed.**  Pure real analysis:
from the board's balance at one instant, above the threshold `L` the log-envelope rate obeys
the threshold-Gronwall slot `Z' ≤ a·(c + Z)`.  The `if`-branch of the reduction never
survives: below the cutoff the dissipation already gives `Yd ≤ 0`, and there the slot holds
because its right side is nonnegative.  This is what keeps the rate continuous, hence
`hAc`/`hAd` applicable (§3 step 4). -/
theorem h3Z_threshold_ineq {C ν E₀ θ L y Y Yd : ℝ} (hC : 0 ≤ C) (hE₀ : 0 < E₀) (hθ : 0 < θ)
    (hL1 : 1 ≤ L) (hy0 : 0 ≤ y) (hY0 : 0 ≤ Y) (hyY : L ≤ Y)
    (hred1 : ∀ y Y : ℝ, 0 ≤ y → (1 : ℝ) ≤ y → L ≤ Y →
        C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E₀ / y)) * Y -
            ν * E₀ ^ (-θ) * Y ^ θ * Y ≤
          C * y * (cBracket E₀ + Real.log (1 + Y)) * (1 + Y))
    (hred0 : ∀ y Y : ℝ, 0 ≤ y → y < 1 → L ≤ Y →
        C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E₀ / y)) * Y -
            ν * E₀ ^ (-θ) * Y ^ θ * Y ≤ 0)
    (hbal : Yd ≤
        C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E₀ / y)) * Y -
          ν * E₀ ^ (-θ) * Y ^ θ * Y) :
    Yd / (1 + Y) ≤ C * y * (cBracket E₀ + Real.log (1 + Y)) := by
  have h1pY : (0 : ℝ) < 1 + Y := by linarith
  have hbr : 0 ≤ cBracket E₀ + Real.log (1 + Y) :=
    add_nonneg (cBracket_pos E₀ hE₀).le (Real.log_nonneg (by linarith))
  have hmain : Yd ≤ C * y * (cBracket E₀ + Real.log (1 + Y)) * (1 + Y) := by
    refine hbal.trans ?_
    by_cases hcut : (1 : ℝ) ≤ y
    · exact hred1 y Y hy0 hcut hyY
    · have hge : 0 ≤ C * y * (cBracket E₀ + Real.log (1 + Y)) * (1 + Y) :=
        mul_nonneg (mul_nonneg (mul_nonneg hC hy0) hbr) (by linarith)
      exact (hred0 y Y hy0 (not_le.mp hcut) hyY).trans hge
  exact (div_le_iff₀ h1pY).mpr hmain

/-- **§3 step 4 — the producer.**  Given the `H³` rate board at every datum and every
vorticity budget, the Fourier `H³` weight of *every* representing profile of *every* slice
of a constrained solution is bounded by one `K = K(ν, u₀, M)`: that is,
`WienerH3Apriori bkmVorticityControl`, the substantive reading of ledger F-025.  The
horizon-uniformity is what the damping buys: the closed bound
`(c + max(Z 0, Λ)) · exp(C·M) − c` contains no `T`, because the running budget
`∫₀ᵗ C·y ≤ C·M` is `T`-independent while the dissipation caps the growth above `Λ`. -/
theorem wienerH3Apriori_of_h3DampedRateBoard
    (hboard : ∀ (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzVelocity) (hdiv : DivergenceFreeInitial u₀)
      (M : ℝ≥0), H3DampedRateBoard ν u₀ M) :
    WienerH3Apriori bkmVorticityControl := by
  intro ν hν u₀ hdiv M
  obtain ⟨C, θ, Y₀, E₀, hC, hθ, hE₀, hY₀, hinst⟩ := hboard ν hν u₀ hdiv M
  obtain ⟨L, hL1, hred1, hred0⟩ := h3Reduction_at_one hC hν hE₀ hθ
  set c : ℝ := cBracket E₀ with hcdef
  set Λ : ℝ := Real.log (1 + L) with hΛdef
  set Zb : ℝ := Real.log (1 + Y₀) with hZbdef
  have hc0 : 0 ≤ c := (cBracket_pos E₀ hE₀).le
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by linarith)
  -- the produced horizon-uniform constant
  refine ⟨64 * ((Real.exp ((c + max Zb Λ) * Real.exp (C * (M : ℝ)) - c) - 1) ^ 2 + E₀ ^ 2),
    by positivity, ?_⟩
  intro T hT u p hinit hsol hR hN τ hτ0 hτT b hb i
  obtain ⟨a, Yd, hrep, hYle, hEle, hvortC, hvortfin, hYc, hYd, hbal⟩ :=
    hinst T hT u p hinit hsol hR hN
  set y : ℝ → ℝ := vortLevel u with hydef
  set Z : ℝ → ℝ := fun t => Real.log (1 + profH3 (a t)) with hZdef
  set Z' : ℝ → ℝ := fun t => Yd t / (1 + profH3 (a t)) with hZ'def
  set T' : ℝ := (τ + T) / 2 with hTd
  have hT'0 : (0 : ℝ) ≤ T' := by linarith [hτ0]
  have hT'T : T' < T := by linarith [hτT]
  have hYnonneg : ∀ s, 0 ≤ profH3 (a s) := fun s => profH3_nonneg _
  have hYsub : ContinuousOn (fun t => profH3 (a t)) (Icc (0 : ℝ) T') :=
    hYc.mono fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hT'T⟩
  have hy_sub : ContinuousOn y (Icc (0 : ℝ) T') :=
    hvortC.mono fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hT'T⟩
  -- `Z` is continuous and right-differentiable on the closed sub-horizon
  have hZc : ContinuousOn Z (Icc (0 : ℝ) T') := by
    unfold Z
    refine ContinuousOn.log (ContinuousOn.add continuousOn_const hYsub) fun _ _ =>
      ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (profH3_nonneg _))
  have hZd : ∀ t ∈ Ico (0 : ℝ) T', HasDerivWithinAt Z (Z' t) (Ici t) t := by
    intro t ht
    have h0 : HasDerivWithinAt (fun s : ℝ => profH3 (a s)) (Yd t) (Ici t) t :=
      hYd t ⟨ht.1, lt_of_lt_of_le ht.2 hT'T.le⟩
    have h1 : HasDerivWithinAt (fun s : ℝ => 1 + profH3 (a s)) (Yd t) (Ici t) t :=
      (h0.const_add (1 : ℝ))
    unfold Z Z'
    exact h1.log (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (profH3_nonneg (a t))))
  -- the rate `C·y` is continuous, nonnegative, and budgeted by `C·M`
  have haC : ContinuousOn (fun t => C * y t) (Icc (0 : ℝ) T') :=
    ContinuousOn.mul continuousOn_const hy_sub
  have ha0 : ∀ t ∈ Ico (0 : ℝ) T', 0 ≤ C * y t := fun t _ =>
    mul_nonneg hC (ENNReal.toReal_nonneg)
  have hbudget : ∀ t ∈ Icc (0 : ℝ) T', ∫ x in (0 : ℝ)..t, y x ∂volume ≤ (M : ℝ) := by
    intro t ht
    exact rate_budget_of_control_le (T := T) hN hvortfin hvortC
      ⟨ht.1, lt_of_le_of_lt ht.2 hT'T⟩
  have haM : ∀ t ∈ Icc (0 : ℝ) T', ∫ x in (0 : ℝ)..t, (fun s => C * y s) x ∂volume ≤
      C * (M : ℝ) := by
    intro t ht
    have hle : ∫ x in (0 : ℝ)..t, y x ∂volume ≤ (M : ℝ) := hbudget t ht
    calc ∫ x in (0 : ℝ)..t, (fun s => C * y s) x ∂volume = C * ∫ x in (0 : ℝ)..t, y x ∂volume :=
          intervalIntegral.integral_const_mul C y
      _ ≤ C * (M : ℝ) := mul_le_mul_of_nonneg_left hle hC
  -- the threshold slot, uniformly in the horizon
  have hineq : ∀ t ∈ Ico (0 : ℝ) T', Λ < Z t → Z' t ≤ (fun s => C * y s) t * (c + Z t) := by
    intro t ht hgt
    have hLY : L ≤ profH3 (a t) := by
      by_contra h
      have : Z t ≤ Λ := by
        unfold Z Λ
        exact Real.log_le_log (by linarith [hYnonneg t])
          (by linarith [hL1, hYnonneg t, not_le.mp h])
      linarith
    unfold Z' Z
    exact h3Z_threshold_ineq hC hE₀ hθ hL1 (ENNReal.toReal_nonneg) (hYnonneg t) hLY hred1 hred0
      (hbal t ⟨ht.1, lt_of_lt_of_le ht.2 hT'T.le⟩)
  have hgron := threshold_gronwall_uniform_of_continuousRate hT'0 hc0 hΛ0 hZc hZd haC ha0 haM
    hineq τ ⟨hτ0, by linarith [hTd, hτT]⟩
  -- from the log bound to the profile bound, then to the `h3F` weight
  have hZ0 : Z 0 ≤ Zb := by
    unfold Z Zb
    exact Real.log_le_log (by linarith [hYnonneg 0]) (by linarith [hYle 0])
  have hmaxle : max (Z 0) Λ ≤ max Zb Λ :=
    max_le_iff.mpr ⟨hZ0.trans (le_max_left Zb Λ), le_max_right Zb Λ⟩
  have hgr' : Z τ ≤ (c + max Zb Λ) * Real.exp (C * (M : ℝ)) - c :=
    hgron.trans (sub_le_sub_right
      (mul_le_mul_of_nonneg_right (add_le_add (le_refl c) hmaxle) (Real.exp_pos _).le) c)
  have hYbound : profH3 (a τ) ≤
      Real.exp ((c + max Zb Λ) * Real.exp (C * (M : ℝ)) - c) - 1 := by
    have hZe : Real.exp (Z τ) = 1 + profH3 (a τ) := by
      unfold Z
      rw [Real.exp_log (by linarith [hYnonneg τ])]
    have h2 : Real.exp (Z τ) ≤
        Real.exp ((c + max Zb Λ) * Real.exp (C * (M : ℝ)) - c) :=
      Real.exp_le_exp.mpr hgr'
    linarith
  calc h3F (fun ξ => b ξ i)
      ≤ h3EnvelopeBudget (u τ) := h3F_component_le_budget hb i
    _ = ⨆ j : Fin 3, h3F (fun ξ => a τ ξ j) :=
          h3EnvelopeBudget_eq_iSup (hrep τ ⟨hτ0, hτT⟩)
    _ ≤ ENNReal.ofReal (64 * (profH3 (a τ) ^ 2 + profL2 (a τ) ^ 2)) :=
          iSup_le fun j => h3F_coord_le_profNorms (hrep τ ⟨hτ0, hτT⟩) j
    _ ≤ ENNReal.ofReal (64 *
          ((Real.exp ((c + max Zb Λ) * Real.exp (C * (M : ℝ)) - c) - 1) ^ 2 + E₀ ^ 2)) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          have hE : (0 : ℝ) ≤ E₀ := (le_of_lt hE₀)
          have hs1 : profH3 (a τ) ^ 2 ≤
              (Real.exp ((c + max Zb Λ) * Real.exp (C * (M : ℝ)) - c) - 1) ^ 2 :=
            pow_le_pow_left₀ (hYnonneg τ) hYbound 2
          have hs2 : profL2 (a τ) ^ 2 ≤ E₀ ^ 2 :=
            pow_le_pow_left₀ (profL2_nonneg _) (hEle τ) 2
          nlinarith

/-! ## 4. What the reduction still needs -/

/-- **The two-premise form this lane reaches.**  Composing the producer with the landed
crown reduces `WholeSpaceGlobalRegularity` to `APrioriIn RegularOnCompacts
bkmVorticityControl` together with the `H³` rate board.  This is *not* a proof of global
regularity: the second premise below is exactly this lane's named residual (§2), and the
first is the BKM a priori bound on the vorticity integral — by `Navier/BealeKatoMajda` the
hard half of the problem, not a repackaging of the answer.  The row exists so the residual
is named in one line rather than in prose. -/
theorem wholeSpaceGlobalRegularity_of_h3BoardAndBkmApriori
    (hboard : ∀ (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzVelocity)
      (hdiv : DivergenceFreeInitial u₀) (M : ℝ≥0), H3DampedRateBoard ν u₀ M)
    (hapriori : APrioriIn RegularOnCompacts bkmVorticityControl) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  crown_of_wienerH3Apriori bkmVorticityControl
    (wienerH3Apriori_of_h3DampedRateBoard hboard) hapriori

/-- The board is not contradicted by the tautological route: the envelope control does not
bound the vorticity level, so `h3EnvelopeControl` cannot be substituted for
`bkmVorticityControl` here.  Recorded as the *name* of the mismatch, not as a theorem. -/
theorem wienerH3Apriori_of_h3DampedRateBoard_aprioriIn
    (hboard : ∀ (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzVelocity)
      (hdiv : DivergenceFreeInitial u₀) (M : ℝ≥0), H3DampedRateBoard ν u₀ M) :
    WienerH3Apriori bkmVorticityControl :=
  wienerH3Apriori_of_h3DampedRateBoard hboard

/-! ## 5. Receipts -/

#check Navier.Analysis.WienerH3DampedProducer.six_pow_one_add_le
#check Navier.Analysis.WienerH3DampedProducer.h3F_coord_le_profNorms
#check Navier.Analysis.WienerH3DampedProducer.rate_budget_of_control_le
#check Navier.Analysis.WienerH3DampedProducer.h3Z_threshold_ineq
#check Navier.Analysis.WienerH3DampedProducer.wienerH3Apriori_of_h3DampedRateBoard
#check Navier.Analysis.WienerH3DampedProducer.wholeSpaceGlobalRegularity_of_h3BoardAndBkmApriori

#print axioms Navier.Analysis.WienerH3DampedProducer.six_pow_one_add_le
#print axioms Navier.Analysis.WienerH3DampedProducer.h3F_coord_le_profNorms
#print axioms Navier.Analysis.WienerH3DampedProducer.rate_budget_of_control_le
#print axioms Navier.Analysis.WienerH3DampedProducer.h3Z_threshold_ineq
#print axioms Navier.Analysis.WienerH3DampedProducer.wienerH3Apriori_of_h3DampedRateBoard
#print axioms Navier.Analysis.WienerH3DampedProducer.wholeSpaceGlobalRegularity_of_h3BoardAndBkmApriori

end Navier.Analysis.WienerH3DampedProducer
