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
   signature (kernel-strict proof).** `circulation_eq_zero_of_phaseLift`:
   for any `C^∞` field `ψ` admitting a single-valued differentiable
   phase lift on its vortex complement, the Madelung-velocity
   circulation around every circle missing the zero set vanishes. The
   unitVortex instance has circulation `2π ≠ 0` (§3), so its lift
   hypotheses fail — the §4 refutation is one instance of this uniform
   obstruction (wave-3: replace the complement-differentiability
   hypothesis by real-analytic data where possible, and classify the
   per-lift zero loci).

6. **Reduction — section 4 falls out of section 5 — CLOSED** (wave-3 lane
   N2b). `unitVortex_no_differentiable_phaseLift_of_circulation` derives the
   section-4 refutations from the section-5 uniform obstruction plus the
   section-3 pinned circulation alone, consuming none of wave-1's
   periodic-lift lemma; `hcomp_of_isolated_ball` produces the section-5
   `hcomp` hypothesis from the isolation-radius data of
   `hasIsolatedVortexZeros` for every `ρ` below the isolation bound.

Status vocabulary: CLOSED = strict kernel axioms (receipts at file
tail); CONDITIONAL = same strict receipts, with the unresolved
hypotheses named explicitly in the signature. There is no `sorry` in
this file.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric
open scoped Interval ContDiff

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

/-- Chain rule for the exponential of an imaginary real-phase curve; the
exact idiom of wave-1 `hasDerivAt_phaseLift_eq_charge`, isolated. -/
private theorem exp_phaseCurve_hasDerivAt {α : ℝ → ℝ} {θ : ℝ}
    (hα : DifferentiableAt ℝ α θ) :
    HasDerivAt (fun s => Complex.exp (↑(α s) * Complex.I))
      (Complex.exp (↑(α θ) * Complex.I) * (↑(deriv α θ) * Complex.I)) θ := by
  have he := (Complex.hasDerivAt_exp (↑(α θ) * Complex.I)).scomp θ
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt θ hα.hasDerivAt).mul_const Complex.I)
  simpa [Function.comp_def, smul_eq_mul, mul_comm] using he

/-- CONDITIONAL headline (named hypotheses in the signature; see
`#check @circulation_eq_zero_of_phaseLift`): if a `C^∞` field `ψ`
admits a single-valued real phase differentiable on all of its vortex
complement and exponentiating to the normalized field there, then the
Madelung-velocity circulation around every circle missing the zero set
vanishes. `unitVortex` with `z₀ = 0`, `ρ = 1` has circulation `2π`
(§3), so the hypotheses fail for it — the §4 refutation is one instance
of this uniform statement. Proof: differentiate the lift equation along
the circle; multiplying by the inverse `‖ψ‖/ψ` of the lift value
collapses the product-rule expansion to the logarithmic derivative
`ψ'/ψ` plus the single purely real term
`↑(deriv (‖ψ ∘ γ‖⁻¹) θ · ‖ψ ∘ γ θ‖)`, whose imaginary part vanishes;
`inner_velocity_eq_im_fderiv_div` then rewrites the integrand as
`deriv (Θ ∘ γ)`, and the interval FTC plus periodicity of `γ`
finishes. -/
theorem circulation_eq_zero_of_phaseLift {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    {Θ : ℂ → ℝ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcomp : ∀ θ : ℝ, z₀ + (ρ : ℂ) * vortexPhase (1 : ℤ) θ ∈ vortexComplement ψ)
    (hdiff : ∀ z ∈ vortexComplement ψ, DifferentiableAt ℝ Θ z)
    (hlift : ∀ z ∈ vortexComplement ψ,
      Complex.exp (Θ z * Complex.I) = normalizedVortexField ψ z) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
        inner ℝ (velocity ψ (z₀ + (ρ : ℂ) * vortexPhase (1 : ℤ) θ))
          (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ)) = 0 := by
  let γ : ℝ → ℂ := fun s => z₀ + (ρ : ℂ) * vortexPhase (1 : ℤ) s
  have hvpd (s : ℝ) :
      HasDerivAt γ (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) s)) s := by
    have h1 := (hasDerivAt_vortexPhase (1 : ℤ) s).const_mul (ρ : ℂ)
    have h2 := (hasDerivAt_const s z₀).add h1
    refine h2.congr_deriv ?_
    simp [vortexPhaseDerivative, zero_add, mul_comm, mul_left_comm]
  have hγ (s : ℝ) : DifferentiableAt ℝ γ s := (hvpd s).differentiableAt
  set gfn : ℝ → ℝ := fun θ =>
    inner ℝ (velocity ψ (γ θ)) (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ))
    with hgfn
  -- Pointwise derivative identity: deriv (Θ ∘ γ) θ = gfn θ.
  have hpoint (θ : ℝ) : HasDerivAt (fun s => Θ (γ s)) (gfn θ) θ := by
    have hz : γ θ ∈ vortexComplement ψ := hcomp θ
    have hne : ψ (γ θ) ≠ 0 := mem_vortexComplement.mp hz
    have hψfa : HasFDerivAt (𝕜 := ℝ) ψ (fderiv ℝ ψ (γ θ)) (γ θ) :=
      (hψ.contDiffAt.differentiableAt (by simp)).hasFDerivAt
    have hnum : HasDerivAt (fun s => ψ (γ s))
        (fderiv ℝ ψ (γ θ) (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ))) θ :=
      hψfa.comp_hasDerivAt θ (hvpd θ)
    -- denominator of the normalized field along the curve
    have hnd : DifferentiableAt ℝ (fun w : ℂ => ‖ψ w‖) (γ θ) := by
      have hc : DifferentiableAt ℝ ψ (γ θ) := hψ.contDiffAt.differentiableAt (by simp)
      have hnz : DifferentiableAt ℝ (fun z : ℂ => ‖z‖) (ψ (γ θ)) :=
        (contDiffAt_norm ℝ (n := ∞) hne).differentiableAt (by simp)
      exact DifferentiableAt.comp (γ θ) hnz hc
    have hden : HasDerivAt (fun s : ℝ => ‖ψ (γ s)‖)
        (deriv (fun s : ℝ => ‖ψ (γ s)‖) θ) θ :=
      (hnd.comp θ (hγ θ)).hasDerivAt
    have hr' : (‖ψ (γ θ)‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hne
    have hinv : HasDerivAt (fun s : ℝ => ((‖ψ (γ s)‖ : ℝ)⁻¹ : ℝ))
        (deriv (fun s : ℝ => (‖ψ (γ s)‖ : ℝ)⁻¹) θ) θ :=
      ((hden.inv (by simpa using hr')).differentiableAt).hasDerivAt
    have hcinv : HasDerivAt (fun s : ℝ => (((‖ψ (γ s)‖ : ℝ)⁻¹ : ℝ) : ℂ))
        (((deriv (fun s : ℝ => (‖ψ (γ s)‖ : ℝ)⁻¹) θ : ℝ) : ℂ)) θ :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt θ hinv
    have hmul : HasDerivAt (fun s : ℝ =>
        ψ (γ s) * (((‖ψ (γ s)‖ : ℝ)⁻¹ : ℝ) : ℂ))
        (fderiv ℝ ψ (γ θ) (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ))
          * ((‖ψ (γ θ)‖ : ℝ)⁻¹ : ℂ)
          + ψ (γ θ) * ((deriv (fun s : ℝ => (‖ψ (γ s)‖ : ℝ)⁻¹) θ : ℝ) : ℂ)) θ :=
      ((hnum.mul hcinv).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv
        (by simp [Complex.ofReal_inv])
    have hpsiF : (fun s : ℝ => normalizedVortexField ψ (γ s)) =
        fun s => ψ (γ s) * (((‖ψ (γ s)‖ : ℝ)⁻¹ : ℝ) : ℂ) := by
      funext s
      simp [normalizedVortexField, div_eq_mul_inv]
    have hpsi : HasDerivAt (fun s : ℝ => normalizedVortexField ψ (γ s))
        (fderiv ℝ ψ (γ θ) (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ))
          * ((‖ψ (γ θ)‖ : ℝ)⁻¹ : ℂ)
          + ψ (γ θ) * ((deriv (fun s : ℝ => (‖ψ (γ s)‖ : ℝ)⁻¹) θ : ℝ) : ℂ)) θ := by
      rw [hpsiF]; exact hmul
    -- exp side and uniqueness of the derivative along the curve
    have hα : DifferentiableAt ℝ (fun s => Θ (γ s)) θ :=
      DifferentiableAt.comp θ (hdiff _ hz) (hγ θ)
    have hexp : HasDerivAt (fun s => Complex.exp (↑(Θ (γ s)) * Complex.I))
        (Complex.exp (↑(Θ (γ θ)) * Complex.I)
          * (↑(deriv (fun s => Θ (γ s)) θ) * Complex.I)) θ :=
      exp_phaseCurve_hasDerivAt hα
    have hee : Filter.EventuallyEq (nhds θ)
        (fun s => normalizedVortexField ψ (γ s))
        (fun s => Complex.exp (↑(Θ (γ s)) * Complex.I)) :=
      Filter.Eventually.of_forall fun s => (hlift (γ s) (hcomp s)).symm
    have he1 : deriv (fun s : ℝ => normalizedVortexField ψ (γ s)) θ =
        Complex.exp (↑(Θ (γ θ)) * Complex.I)
          * (↑(deriv (fun s => Θ (γ s)) θ) * Complex.I) :=
      (hexp.congr_of_eventuallyEq hee).deriv
    have he2 := hpsi.deriv
    have hD := he1.symm.trans he2
    have hEexp : Complex.exp (↑(Θ (γ θ)) * Complex.I) =
        ψ (γ θ) * ((‖ψ (γ θ)‖ : ℝ)⁻¹ : ℂ) := by
      have h1 : normalizedVortexField ψ (γ θ) =
          ψ (γ θ) * ((‖ψ (γ θ)‖ : ℝ)⁻¹ : ℂ) := by
        simp [normalizedVortexField, div_eq_mul_inv]
      rw [← h1, hlift (γ θ) hz]
    -- Multiply the differentiated lift equation by `exp⁻¹ = ‖ψ‖ · ψ⁻¹`
    -- (from `hEexp`).  The derivative of the real factor `‖ψ ∘ γ‖⁻¹` then
    -- appears only as the REAL quantity `deriv (‖ψ ∘ γ‖⁻¹) θ · ‖ψ γθ‖`,
    -- so no explicit inverse-derivative formula is needed: the imaginary
    -- part kills it.
    have hmain : (↑(deriv (fun s => Θ (γ s)) θ) : ℂ) * Complex.I =
        fderiv ℝ ψ (γ θ) (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ))
          * (ψ (γ θ))⁻¹
          + ↑(deriv (fun s : ℝ => (‖ψ (γ s)‖ : ℝ)⁻¹) θ * ‖ψ (γ θ)‖) := by
      have hnE : Complex.exp (↑(Θ (γ θ)) * Complex.I) ≠ 0 :=
        Complex.exp_ne_zero _
      have h3 : (Complex.exp (↑(Θ (γ θ)) * Complex.I))⁻¹ =
          (‖ψ (γ θ)‖ : ℂ) * (ψ (γ θ))⁻¹ := by
        rw [hEexp]
        field_simp [hne]
      have h := congrArg (fun w : ℂ =>
          w * (Complex.exp (↑(Θ (γ θ)) * Complex.I))⁻¹) hD
      rw [h3, hEexp] at h
      field_simp [hne, hr', hnE] at h ⊢
      rw [h]
      simp only [mul_comm, mul_assoc, Complex.ofReal_mul]
    have him : deriv (fun s => Θ (γ s)) θ =
        (fderiv ℝ ψ (γ θ) (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ))
          / ψ (γ θ)).im := by
      have h := congrArg Complex.im hmain
      simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero] at h
      simpa [div_eq_mul_inv] using h
    have heq' : deriv (fun s => Θ (γ s)) θ = gfn θ := by
      rw [him]
      exact (inner_velocity_eq_im_fderiv_div ψ (γ θ)
        (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ))).symm
    exact hα.hasDerivAt.congr_deriv heq'
  -- Continuity of the integrand, hence interval integrability.
  have hgc : Continuous gfn := by
    have h1 : Continuous (fun θ => velocity ψ (γ θ)) := by
      refine continuous_iff_continuousAt.mpr fun θ => ?_
      have hz : γ θ ∈ vortexComplement ψ := hcomp θ
      exact ContinuousAt.comp
        ((velocity_smoothAt_of_nonzero hψ (mem_vortexComplement.mp hz)).continuousAt)
        ((hγ θ).continuousAt)
    have hv : Continuous fun θ : ℝ => vortexPhase (1 : ℤ) θ := by
      refine continuous_iff_continuousAt.mpr fun θ =>
        ((hasDerivAt_vortexPhase (1 : ℤ) θ).differentiableAt).continuousAt
    have h2 : Continuous fun θ : ℝ =>
        (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ) : ℂ) :=
      (hv.const_mul (ρ : ℂ)).const_mul Complex.I
    have hconj : Continuous fun θ => (starRingEnd ℂ (velocity ψ (γ θ)) : ℂ) :=
      Complex.conjCLE.continuous.comp h1
    have h3 : gfn = fun θ =>
        ((Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ))
          * starRingEnd ℂ (velocity ψ (γ θ))).re := by
      funext θ
      show inner ℝ (velocity ψ (γ θ))
          (Complex.I * ((ρ : ℂ) * vortexPhase (1 : ℤ) θ)) = _
      rw [Complex.inner]
    rw [h3]
    exact Complex.reCLM.continuous.comp (h2.mul hconj)
  have hI : IntervalIntegrable gfn MeasureTheory.volume 0 (2 * Real.pi) :=
    (hgc.continuousOn).intervalIntegrable
  have hper : γ (2 * Real.pi) = γ 0 := by
    show z₀ + (ρ : ℂ) * vortexPhase (1 : ℤ) (2 * Real.pi) = _
    rw [show (2 : ℝ) * Real.pi = (0 : ℝ) + 2 * Real.pi by ring,
      vortexPhase_two_pi_periodic (1 : ℤ) 0]
  have hFTC : ∫ θ in (0 : ℝ)..(2 * Real.pi), gfn θ =
      (fun s => Θ (γ s)) (2 * Real.pi) - (fun s => Θ (γ s)) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (by intro θ _hθ; exact hpoint θ) hI
  have hzero : (fun s => Θ (γ s)) (2 * Real.pi) - (fun s => Θ (γ s)) 0 = 0 := by
    show Θ (γ (2 * Real.pi)) - Θ (γ 0) = 0
    rw [hper]
    exact sub_self _
  exact hFTC.trans hzero

/-! ## 6. Reduction: section 4 falls out of section 5 (wave-3 item 1) -/

/-- **The uniform-obstruction reduction.** The section-4 headline negative is
derived from the general section-5 mechanism plus the section-3 pinned
circulation ALONE: assuming a complement-differentiable phase lift `Θ` for
`unitVortex`, §5 at `ψ := unitVortex`, `z₀ := 0`, `ρ := 1` forces the
circulation integral around the unit circle to vanish, while §3 pins the very
same integral at `2 * Real.pi ≠ 0`. Wave-1's periodic-lift lemma
`no_differentiable_periodic_phaseLift_of_nonzero` is not consumed here: the
trichotomy (§2 CLOSED / §4 FALSIFIED / §5 CONDITIONAL) is one theorem with a
witness, not three independent artifacts. -/
theorem unitVortex_no_differentiable_phaseLift_of_circulation :
    ¬ ∃ Θ : ℂ → ℝ, (∀ z ∈ vortexComplement unitVortex, DifferentiableAt ℝ Θ z) ∧
      ∀ z ∈ vortexComplement unitVortex,
        Complex.exp (Θ z * Complex.I) = normalizedVortexField unitVortex z := by
  rintro ⟨Θ, hdiff, hlift⟩
  have hcomp : ∀ θ : ℝ,
      (0 : ℂ) + ((1 : ℝ) : ℂ) * vortexPhase (1 : ℤ) θ ∈ vortexComplement unitVortex := by
    intro θ
    simp [mem_vortexComplement, unitVortex, zero_add, vortexPhase_ne_zero]
  have hz0 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      inner ℝ (velocity unitVortex (0 + ((1 : ℝ) : ℂ) * vortexPhase (1 : ℤ) θ))
        (Complex.I * (((1 : ℝ) : ℂ) * vortexPhase (1 : ℤ) θ))) = 0 :=
    circulation_eq_zero_of_phaseLift (ψ := unitVortex) (Θ := Θ) (z₀ := (0 : ℂ)) (ρ := (1 : ℝ))
      unitVortex_smooth (by norm_num : (0 : ℝ) < 1) hcomp hdiff hlift
  have hpi : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      inner ℝ (velocity unitVortex (0 + ((1 : ℝ) : ℂ) * vortexPhase (1 : ℤ) θ))
        (Complex.I * (((1 : ℝ) : ℂ) * vortexPhase (1 : ℤ) θ)))
      = ∫ θ in (0 : ℝ)..(2 * Real.pi),
        vortexCirculant unitVortex (vortexPhase (1 : ℤ) θ) := by
    congr 1
    funext θ
    show inner ℝ (velocity unitVortex (0 + ((1 : ℝ) : ℂ) * vortexPhase (1 : ℤ) θ))
        (Complex.I * (((1 : ℝ) : ℂ) * vortexPhase (1 : ℤ) θ)) = _
    simp [vortexCirculant, zero_add, one_mul]
  rw [hpi, unitVortex_circulation_eq_integral_vortexCirculant] at hz0
  exact ne_of_gt Real.two_pi_pos hz0

/-- The physically-read corollary follows through §5 as well: a lift
continuous on the whole plane (hence on the complement, differentiably) does
not exist — same contradiction, same single mechanism. -/
theorem unitVortex_no_phaseLift_continuous_at_core_of_circulation :
    ¬ ∃ Θ : ℂ → ℝ, Continuous Θ ∧
      (∀ z ∈ vortexComplement unitVortex, DifferentiableAt ℝ Θ z) ∧
      ∀ z ∈ vortexComplement unitVortex,
        Complex.exp (Θ z * Complex.I) = normalizedVortexField unitVortex z := by
  rintro ⟨Θ, _, hdiff, hlift⟩
  exact unitVortex_no_differentiable_phaseLift_of_circulation ⟨Θ, hdiff, hlift⟩

/-- **Section-5 hypothesis producer (item 4, narrow form).** Inside the
isolation radius of an isolated vortex zero, EVERY circle centered at that
zero misses the zero set — so `circulation_eq_zero_of_phaseLift`'s `hcomp` is
DERIVED from the isolation data of `hasIsolatedVortexZeros` (its matrix body,
spelled in the signature), not assumed, for every `ρ ∈ (0, r)`. The global
almost-all-`ρ` statement over the whole plane needs the discrete-intersect-
compact finiteness route and is recorded for wave-4. -/
theorem hcomp_of_isolated_ball {ψ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hiso : ∀ w ∈ ball z₀ r, w ∈ vortexZeroSet ψ → w = z₀)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    ∀ θ : ℝ, z₀ + (ρ : ℂ) * vortexPhase (1 : ℤ) θ ∈ vortexComplement ψ := by
  intro θ
  have hnw : ‖(ρ : ℂ) * vortexPhase (1 : ℤ) θ‖ = ρ := by
    have hc : ‖(ρ : ℂ)‖ = ρ := by
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq (le_of_lt hρ)]
    rw [norm_mul, hc, norm_vortexPhase, mul_one]
  have hw : z₀ + (ρ : ℂ) * vortexPhase (1 : ℤ) θ ∈ ball z₀ r := by
    rw [mem_ball, dist_eq_norm]
    rw [show z₀ + (ρ : ℂ) * vortexPhase (1 : ℤ) θ - z₀
        = (ρ : ℂ) * vortexPhase (1 : ℤ) θ from by abel]
    rw [hnw]
    exact hρr
  by_contra h
  rw [mem_vortexComplement, not_ne_iff] at h
  have hm : z₀ + (ρ : ℂ) * vortexPhase (1 : ℤ) θ ∈ vortexZeroSet ψ := by
    simpa [vortexZeroSet] using h
  have heq := hiso _ hw hm
  have hu : (ρ : ℂ) * vortexPhase (1 : ℤ) θ = 0 := by
    have h' := congrArg (fun x : ℂ => x - z₀) heq
    simpa using h'
  rcases mul_eq_zero.mp hu with hρ0 | hv0
  · exact (ne_of_gt hρ) (Complex.ofReal_eq_zero.mp hρ0)
  · exact vortexPhase_ne_zero (1 : ℤ) θ hv0

/-! ## 7. Receipts (raw `#print axioms`, strict tier) -/

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
#print axioms circulation_eq_zero_of_phaseLift
#print axioms unitVortex_no_differentiable_phaseLift_of_circulation
#print axioms unitVortex_no_phaseLift_continuous_at_core_of_circulation
#print axioms hcomp_of_isolated_ball

end Navier.Analysis
