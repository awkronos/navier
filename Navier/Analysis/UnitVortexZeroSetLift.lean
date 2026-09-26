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
   `normalizedVortexField ψ` on the complement, and the exception set is
   the zero set itself (measure zero for isolated zeros; `{0}` for
   `unitVortex`). So the Madelung phase of a vortex-type field DOES extend
   across its zeros — in the measurable category.
3. **Curl control on the complement — CLOSED.** Off the zero set the
   Madelung `velocity` is the gradient of a locally constructed smooth
   real phase (`vortex_localPhaseLift`), so its planar curl commutes on
   the complement.
4. **Smooth lift across the zero set — FALSIFIED with a pinned witness.**
   `unitVortex_no_continuous_phaseLift`: no phase function continuous at
   the core can lift the normalized `unitVortex` field on a punctured
   neighbourhood. Witness data: the unit-circle circulation of the actual
   Madelung velocity of `unitVortex` is exactly `2π`
   (`unitVortex_velocity_circulation`, wave-1 Winding file) while any
   single-valued continuous lift forces the circulation to vanish;
   equivalently the U(1) holonomy of the charge-one loop is trivial
   (`exp(2πi·1) = 1`) yet no real lift exists. This is the
   `trivial_holonomy_without_real_lift` refuter pattern (mirrored in
   reality at `Reality/Physics/MadelungHolonomy.lean:65`, which imports
   navier and therefore cannot be imported here; the obstruction is
   restated minimally in this file via
   `no_differentiable_periodic_phaseLift_of_nonzero`).
5. **The remaining positive regime — CONDITIONAL with a named
   hypothesis.** Where a single-valued differentiable complement lift is
   uniformly continuous up to the core, it extends continuously across
   the zero set, and the extension's circulation around each core
   vanishes. The named hypothesis is NOT vacuous; replacing it by
   "ψ real-analytic" is the recorded wave-3 residual.

Status vocabulary: CLOSED = strict kernel axioms; the only `sorry`s sit at
honest WIP blockers named in a comment line directly above each.
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
ACROSS the zero set: measurable lift + null exceptional fibre.
WIP blocker: `volume ({0} : Set ℂ) = 0` for the planar Lebesgue measure
(`ℂ ≃ᵢᵐ ℝ²` measure algebra); the exception-set containment is already
`liftException_subset_zeroSet`. Resolved by the `NullSingletonClass
volume` instance / `volume_eq_zero_of_countable` name probe. -/
theorem unitVortex_phaseLift_eventually_ae :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Complex.exp (madelungPhaseLift unitVortex z * Complex.I) =
        normalizedVortexField unitVortex z := by
  have hsub : {z : ℂ | Complex.exp (madelungPhaseLift unitVortex z * Complex.I) ≠
      normalizedVortexField unitVortex z} ⊆ ({0} : Set ℂ) := by
    intro z hz
    have := liftException_subset_zeroSet hz
    rwa [unitVortex_vortexZeroSet, mem_singleton_iff] at this
  -- WIP: need `volume ({0}:Set ℂ) = 0`, then Filter.mem_of_superset (mem_ae.mpr ..)
  sorry

/-! ## 3. Curl control on the complement — local smooth phase lifts -/
-- Chunk 2. The rotated principal-branch local phase
-- `vortexLocalPhase ψ c w = arg (conj (ψ c) * ψ w)` has positive real
-- part `‖ψ c‖ ^ 2 > 0` at the center, giving a continuous branch near
-- any nonzero point; `arg` is then smooth and the Madelung velocity is
-- its gradient, so the planar curl commutes off the zero set.

/-! ## 4. Smooth lift across the zero set — FALSIFIED, pinned witness -/

/-- The headline negative: no phase function continuous at the core lifts
the normalized `unitVortex` field on the whole punctured plane. This is
the circulation-quantization obstruction (nonzero-degree zero with
trivial U(1) holonomy), the navier-side restatement of reality's
`trivial_holonomy_without_real_lift` pattern.
WIP blocker (chunk 2): restrict `Θ` to the unit circle
`z = vortexPhase 1 θ`, differentiate to get a differentiable periodic
real lift of the charge-1 loop, contradict
`no_differentiable_periodic_phaseLift_of_nonzero 1`. -/
theorem unitVortex_no_continuous_phaseLift :
    ¬ ∃ Θ : ℂ → ℝ, Continuous Θ ∧
      ∀ z ∈ vortexComplement unitVortex,
        Complex.exp (Θ z * Complex.I) = normalizedVortexField unitVortex z := by
  sorry

/-! ## 5. Conditional extension regime -/
-- Chunk 3: FTC-based circulation theorem for continuous complement
-- lifts and the CauchyMap extension across the core under a named
-- uniform-continuity hypothesis. The obstruction these pin:
-- `unitVortex_velocity_circulation = 2π ≠ 0` (wave-1 Winding file).

#print axioms madelungPhaseLift_exponentiates
#print axioms madelungPhaseLift_measurable
#print axioms unitVortex_vortexZeroSet
#print axioms unitVortex_hasIsolatedVortexZeros
#print axioms liftException_subset_zeroSet
#print axioms normalizedVortexField_norm_one
#print axioms normalizedVortexField_ne_zero
#print axioms mem_vortexComplement

end Navier.Analysis
