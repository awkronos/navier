import Navier.Analysis.QuantumVortexWinding

/-!
# Zero-set unitVortex phase lift

NSQM-0926 wave-2 lane N2. Base 58a59257.

The wave-1 lane m-a (`MadelungSpinorDecoder.lean`) kernel-falsified the
nonvanishing-amplitude spinor lift of `rotationalDatum` and recorded the
exact residual: rotation can enter only through component ZEROS — the
unitVortex regime of closed non-exact forms off the zero set. This file
constructs that route in the plane (`ψ : ℂ → ℂ`, `Navier` units ħ/m = 1,
consuming `QuantumVortexRegularity.density/current/velocity` and
`QuantumVortexWinding.vortexPhase` machinery):

1. **Vortex-complement domain.** `vortexZeroSet`, `vortexComplement`,
   `hasIsolatedVortexZeros`, `normalizedVortexField`.
2. **Measurable lift ACROSS the zero set — CLOSED.** `madelungPhaseLift ψ`
   is the everywhere-defined real function `Complex.arg ∘ ψ`; it is
   measurable for measurable ψ, it exponentiates exactly to
   `normalizedVortexField ψ` on the complement, the exception set is the
   zero set itself (`liftException_subset_zeroSet`), and for `unitVortex`
   the lift holds almost everywhere across the core
   (`unitVortex_phaseLift_eventually_ae`). So the Madelung phase of a
   vortex-type field DOES extend across its zeros — in the measurable
   category.
3. **Pinned circulation witness — CLOSED.** `vortexCirculant` is the
   Euclidean pairing of the decoded Madelung velocity with the CCW
   tangent; `vortexCirculant_unitVortex_on_loop` pins its value to
   exactly `1` pointwise on the unit circle and
   `unitVortex_circulation_eq_integral_vortexCirculant` restates the
   wave-1 `unitVortex_velocity_circulation = 2π` as the integral of this
   geometric density.
4. **Differentiable lift across the zero set — FALSIFIED with a pinned
   witness.** `unitVortex_no_differentiable_phaseLift` (and its
   corollary `unitVortex_no_phaseLift_continuous_at_core`): no real
   phase differentiable on the whole punctured plane exponentiates to
   the normalized `unitVortex` field. Witness: restricting a putative
   lift to the unit circle `vortexPhase 1` yields a differentiable
   PERIODIC real lift of the charge-1 loop, contradicting wave-1's
   `no_differentiable_periodic_phaseLift_of_nonzero`; equivalently the
   loop has trivial U(1) holonomy (`exp(2πi·1) = 1`) yet no real lift —
   the `trivial_holonomy_without_real_lift` pattern (mirrored in reality
   at `Reality/Physics/MadelungHolonomy.lean:65`, which imports navier
   and therefore cannot be imported back; the obstruction is restated
   minimally here through the wave-1 Winding file).
5. **The general mechanism — CONDITIONAL, named hypotheses in the
   signature.** `circulation_eq_zero_of_phaseLift`: for any `C^∞` field
   `ψ` admitting a single-valued differentiable phase lift on its vortex
   complement, the Madelung-velocity circulation around every zero-free
   circle vanishes. The unitVortex instance has circulation `2π ≠ 0`,
   which is the same obstruction as §4 uniformly in `ψ` (wave-3: close
   the proof by the quotient-rule derivative identity, and replace the
   complement-differentiability hypothesis by real-analyticity where
   possible).

Status vocabulary: CLOSED = strict kernel axioms (receipts at file
tail); the only `sorry`s sit at honest WIP blockers named in a comment
line directly above each.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric
open scoped Interval

namespace Navier.Analysis

open Navier.Analysis.QuantumVortexRegularity
open Navier.Analysis.QuantumVortexWinding

/-! ## 1. The vortex-complement domain -/

/-- The vortex zero locus of a complex field. -/
def vortexZeroSet (ψ : ℂ → ℂ) : Set ℂ := ψ ⁻¹' {0}

/-- The domain on which the Madelung phase is physically defined. -/
def vortexComplement (ψ : ℂ → ℂ) : Set ℂ := (vortexZeroSet ψ)ᶜ

/-- Every zero is isolated: the regime of point vortices (the
`unitVortex` core and the finite-vortex configurations). -/
def hasIsolatedVortexZeros (ψ : ℂ → ℂ) : Prop :=
  ∀ z ∈ vortexZeroSet ψ, ∃ r > (0 : ℝ), ∀ w ∈ ball z r, w ∈ vortexZeroSet ψ → w = z

theorem mem_vortexComplement {ψ : ℂ → ℂ} {z : ℂ} :
    z ∈ vortexComplement ψ ↔ ψ z ≠ 0 := by
  simp [vortexComplement, vortexZeroSet, Set.mem_compl_iff, Set.mem_singleton_iff]

/-- The U(1)-valued phase map off the zero set (totalized division; at a
zero the value is `0`, which is why the lift equation is asserted only
on the complement). -/
noncomputable def normalizedVortexField (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ψ z / ‖ψ z‖

/-- On the complement the normalized field is unit-modulus. -/
theorem normalizedVortexField_norm_one {ψ : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ vortexComplement ψ) : ‖normalizedVortexField ψ z‖ = 1 := by
  have h : ψ z ≠ 0 := mem_vortexComplement.mp hz
  simp only [normalizedVortexField]
  rw [norm_div]
  have h2 : ‖(‖ψ z‖ : ℂ)‖ = ‖ψ z‖ := by simp
  rw [h2, div_self (norm_ne_zero_iff.mpr h)]

theorem normalizedVortexField_ne_zero {ψ : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ vortexComplement ψ) : normalizedVortexField ψ z ≠ 0 := by
  have h : ψ z ≠ 0 := mem_vortexComplement.mp hz
  simp only [normalizedVortexField]
  exact div_ne_zero h (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h))

/-! ## 2. The measurable lift ACROSS the zero set — CLOSED -/

/-- The global real phase lift: `Complex.arg` composed with the field.
It is defined at every point of the plane, INCLUDING the zeros
(`arg 0 = 0` by totalization), which is exactly the "lift off the zero
set" extension in the measurable category. -/
noncomputable def madelungPhaseLift (ψ : ℂ → ℂ) : ℂ → ℝ :=
  fun z => Complex.arg (ψ z)

/-- On the vortex complement the lift exponentiates exactly to the
normalized field. This is the lift equation, not a definitional tag. -/
theorem madelungPhaseLift_exponentiates (ψ : ℂ → ℂ) (z : ℂ)
    (hz : z ∈ vortexComplement ψ) :
    Complex.exp (madelungPhaseLift ψ z * Complex.I) = normalizedVortexField ψ z := by
  have hne : ψ z ≠ 0 := mem_vortexComplement.mp hz
  have hn : (‖ψ z‖ : ℂ) ≠ 0 := by simpa using norm_ne_zero_iff.mpr hne
  simp only [madelungPhaseLift, normalizedVortexField]
  rw [eq_div_iff hn, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I (ψ z)

/-- The lift is measurable for every measurable field: the zero set is
invisible to the lift. In particular the unit vortex (`ψ = id`) has a
measurable real phase across its core. -/
theorem madelungPhaseLift_measurable {ψ : ℂ → ℂ} (hψ : Measurable ψ) :
    Measurable (madelungPhaseLift ψ) :=
  Complex.measurable_arg.comp hψ

/-- The `unitVortex` zero set is exactly the core `{0}`. -/
theorem unitVortex_vortexZeroSet : vortexZeroSet unitVortex = ({0} : Set ℂ) := by
  ext z
  simp [vortexZeroSet, unitVortex]

/-- The `unitVortex` has an isolated zero. -/
theorem unitVortex_hasIsolatedVortexZeros : hasIsolatedVortexZeros unitVortex := by
  show ∀ z, z ∈ vortexZeroSet unitVortex →
    ∃ r > (0 : ℝ), ∀ w ∈ ball z r, w ∈ vortexZeroSet unitVortex → w = z
  intro z hz
  rw [unitVortex_vortexZeroSet, mem_singleton_iff] at hz
  subst hz
  exact ⟨1, by norm_num, fun _ _ hw => hw⟩

/-- The exception set of the lift equation is contained in the zero set:
outside it the lift holds everywhere pointwise. -/
theorem liftException_subset_zeroSet {ψ : ℂ → ℂ} :
    {z : ℂ | Complex.exp (madelungPhaseLift ψ z * Complex.I) ≠
        normalizedVortexField ψ z} ⊆ vortexZeroSet ψ := by
  intro z hz
  by_contra h
  exact hz (madelungPhaseLift_exponentiates ψ z h)

/-- For `unitVortex` the lift equation holds `volume`-almost everywhere
ACROSS the zero set: measurable lift + null exceptional fibre
(`Set.Countable.ae_notMem` under the `NullSingletonClass volume`
instance for the planar measure; the exception-set containment is
`liftException_subset_zeroSet`). -/
theorem unitVortex_phaseLift_eventually_ae :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Complex.exp (madelungPhaseLift unitVortex z * Complex.I) =
        normalizedVortexField unitVortex z := by
  have hzc : (vortexZeroSet unitVortex).Countable := by
    rw [unitVortex_vortexZeroSet]; exact Set.countable_singleton 0
  filter_upwards [hzc.ae_notMem volume] with z hz
  exact madelungPhaseLift_exponentiates unitVortex z (by
    rw [mem_vortexComplement]; exact hz)

/-! ## 3. Pinned circulation witness — the density the obstruction sees -/

/-- The circulation density: the decoded Madelung velocity paired with
the counter-clockwise tangent `I · z` at `z` (the Euclidean integrand of
wave-1 `unitVortex_velocity_circulation`). -/
noncomputable def vortexCirculant (ψ : ℂ → ℂ) (z : ℂ) : ℝ :=
  inner ℝ (velocity ψ z) (Complex.I * z)

/-- Pointwise witness pin: on the unit circle the `unitVortex` velocity
IS the CCW tangent, so the circulation density is exactly `1`. -/
theorem vortexCirculant_unitVortex_on_loop (θ : ℝ) :
    vortexCirculant unitVortex (vortexPhase (1 : ℤ) θ) = 1 := by
  have ht : vortexPhaseDerivative (1 : ℤ) θ = Complex.I * vortexPhase (1 : ℤ) θ := by
    simp [vortexPhaseDerivative]
  rw [vortexCirculant, unitVortex_velocity_on_phase_loop, ← ht,
    real_inner_self_eq_norm_sq, ht]
  have hn : ‖Complex.I * vortexPhase (1 : ℤ) θ‖ = 1 := by
    rw [norm_mul]
    simp [norm_vortexPhase]
  rw [hn]
  norm_num

/-- The wave-1 exact circulation `2π` restated as the integral of the
geometric circulation density over the charge-1 loop. -/
theorem unitVortex_circulation_eq_integral_vortexCirculant :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        vortexCirculant unitVortex (vortexPhase (1 : ℤ) θ)) = 2 * Real.pi := by
  convert unitVortex_velocity_circulation with θ
  have ht : vortexPhaseDerivative (1 : ℤ) θ = Complex.I * vortexPhase (1 : ℤ) θ := by
    simp [vortexPhaseDerivative]
  show inner ℝ (velocity unitVortex (vortexPhase (1 : ℤ) θ))
      (Complex.I * vortexPhase (1 : ℤ) θ) = _
  rw [← ht, Complex.inner]
  simp [mul_comm]

/-! ## 4. Differentiable lift across the zero set — FALSIFIED -/

/-- The headline negative: no real phase differentiable on the vortex
complement of `unitVortex` (the whole punctured plane) exponentiates to
its normalized field everywhere off the core. Proof: restrict to the
unit circle `vortexPhase 1`; the pullback is a differentiable periodic
real lift of the charge-1 loop, contradicting wave-1
`no_differentiable_periodic_phaseLift_of_nonzero` (whose own proof runs
through `hasDerivAt_phaseLift_eq_charge`: a lift's derivative is
pointwise the integer charge, so periodicity forces charge `0`). This is
the circulation-quantization obstruction with the pinned witness of §3:
density `1` on the loop, total circulation `2π ≠ 0`. -/
theorem unitVortex_no_differentiable_phaseLift :
    ¬ ∃ Θ : ℂ → ℝ, (∀ z ∈ vortexComplement unitVortex, DifferentiableAt ℝ Θ z) ∧
      ∀ z ∈ vortexComplement unitVortex,
        Complex.exp (Θ z * Complex.I) = normalizedVortexField unitVortex z := by
  rintro ⟨Θ, hdiff, hlift⟩
  refine no_differentiable_periodic_phaseLift_of_nonzero (1 : ℤ) (by norm_num)
    ⟨fun θ => Θ (vortexPhase (1 : ℤ) θ), ?_, ?_, ?_⟩
  · intro θ
    exact DifferentiableAt.comp θ
      (hdiff _ (mem_vortexComplement.mpr (vortexPhase_ne_zero (1 : ℤ) θ)))
      (hasDerivAt_vortexPhase (1 : ℤ) θ).differentiableAt
  · intro θ
    have hz : vortexPhase (1 : ℤ) θ ∈ vortexComplement unitVortex :=
      mem_vortexComplement.mpr (vortexPhase_ne_zero (1 : ℤ) θ)
    have hnorm : normalizedVortexField unitVortex (vortexPhase (1 : ℤ) θ) =
        vortexPhase (1 : ℤ) θ := by
      simp [normalizedVortexField, unitVortex, norm_vortexPhase]
    rw [← hnorm]
    exact hlift _ hz
  · show Θ (vortexPhase (1 : ℤ) (2 * Real.pi)) = Θ (vortexPhase (1 : ℤ) 0)
    rw [show (2 : ℝ) * Real.pi = (0 : ℝ) + 2 * Real.pi by ring,
      vortexPhase_two_pi_periodic (1 : ℤ) 0]

/-- Corollary (the physically-read form): a lift that is continuous AT
THE CORE and differentiable off it is in particular a complement-
differentiable lift, so it does not exist either. Lifting the
continuity-at-core hypothesis off differentiability (a continuous-but-
nowhere-differentiable candidate) needs the §5 FTC mechanism and is the
recorded wave-3 residual. -/
theorem unitVortex_no_phaseLift_continuous_at_core :
    ¬ ∃ Θ : ℂ → ℝ, Continuous Θ ∧
      (∀ z ∈ vortexComplement unitVortex, DifferentiableAt ℝ Θ z) ∧
      ∀ z ∈ vortexComplement unitVortex,
        Complex.exp (Θ z * Complex.I) = normalizedVortexField unitVortex z := by
  rintro ⟨Θ, _, hdiff, hlift⟩
  exact unitVortex_no_differentiable_phaseLift ⟨Θ, hdiff, hlift⟩

/-! ## 5. The general conditional mechanism -/

/-- CONDITIONAL headline (named hypotheses in the signature; see
`#check @circulation_eq_zero_of_phaseLift`): if a `C^∞` field `ψ`
admits a single-valued real phase differentiable on all of its vortex
complement and exponentiating to the normalized field there, then the
Madelung-velocity circulation around every circle missing the zero set
vanishes. `unitVortex` with `z₀ = 0`, `ρ = 1` has circulation `2π`
(§3), so the hypothesis fails for it — the §4 refutation is one
instance of this uniform statement.
WIP blocker (chunk 3): the pointwise identity
`deriv (Θ ∘ γ) θ = ⟪velocity ψ (γ θ), γ' θ⟫_ℝ` for `γ θ = z₀ + ρ·e^{iθ}`,
obtained by differentiating the lift equation `exp(Θ·I) = ψ/‖ψ‖` along
`γ` via the quotient rule (`HasDerivAt.div`), `ContDiffAt.norm` for the
denominator, `HasFDerivAt.comp_hasDerivAt` for the numerator, the
conj/normSq inversion `Complex.inv_def`, and
`inner_velocity_eq_im_fderiv_div`; then
`intervalIntegral.integral_eq_sub_of_hasDerivAt` plus periodicity of
`γ`. -/
theorem circulation_eq_zero_of_phaseLift {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ⊤ ψ)
    {Θ : ℂ → ℝ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcomp : ∀ θ : ℝ, z₀ + (ρ : ℂ) * vortexPhase (1 : ℤ) θ ∈ vortexComplement ψ)
    (hdiff : ∀ z ∈ vortexComplement ψ, DifferentiableAt ℝ Θ z)
    (hlift : ∀ z ∈ vortexComplement ψ,
      Complex.exp (Θ z * Complex.I) = normalizedVortexField ψ z) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
        inner ℝ (velocity ψ (z₀ + (ρ : ℂ) * vortexPhase (1 : ℤ) θ))
          (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ)) = 0 := by
  -- WIP: see the blocker list in the docstring above; every ingredient
  -- except the quotient-rule derivative identity is probe-verified to
  -- exist in this build.
  sorry

/-! ## 6. Receipts (raw `#print axioms`, strict tier) -/

#print axioms madelungPhaseLift_exponentiates
#print axioms madelungPhaseLift_measurable
#print axioms unitVortex_vortexZeroSet
#print axioms unitVortex_hasIsolatedVortexZeros
#print axioms liftException_subset_zeroSet
#print axioms normalizedVortexField_norm_one
#print axioms normalizedVortexField_ne_zero
#print axioms mem_vortexComplement
#print axioms unitVortex_phaseLift_eventually_ae
#print axioms vortexCirculant_unitVortex_on_loop
#print axioms unitVortex_circulation_eq_integral_vortexCirculant
#print axioms unitVortex_no_differentiable_phaseLift
#print axioms unitVortex_no_phaseLift_continuous_at_core

end Navier.Analysis
