import Navier.Analysis.ConstructedForceExtension
import Navier.Construction.R3.CompactEnergy

/-!
# Finite energy of the selected compact candidate

The selected Euclidean candidate exposes one compact spatial support for its
velocity and one for its force at every physical time.  That is enough for the
ordinary whole-space energy estimate on `0 ≤ t < 1`; compact support of the
force at negative times is not needed.
-/

noncomputable section

open Set MeasureTheory Function
open scoped ContDiff Topology

namespace Navier.Analysis.SelectedCandidateEnergy

open Navier.Construction.ProblemStatement
open Navier.Construction.R3CompactCandidate
open Navier.ConstructionR3.CompactEnergy

private abbrev ESpace := Navier.Construction.ProblemStatement.Space
private abbrev EVelocityField := Navier.Construction.ProblemStatement.VelocityField

/-- A continuous force with one compact spatial support on the physical unit
time slab has a uniform squared `L²` bound there. -/
theorem exists_uniform_force_l2sq_bound {f : EVelocityField} {K : Set ESpace}
    (hK : IsCompact K) (hf : Continuous f)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∉ K, f (t, x) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      Integrable (fun x : ESpace => ‖f (t, x)‖ ^ 2) volume ∧
        (∫ x : ESpace, ‖f (t, x)‖ ^ 2 ∂volume) ≤ C := by
  have hcompact (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasCompactSupport (fun x : ESpace => ‖f (t, x)‖ ^ 2) := by
    apply HasCompactSupport.intro hK
    intro x hx
    simp only [hsupp t ht x hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Integrable (fun x : ESpace => ‖f (t, x)‖ ^ 2) volume := by
    have hslice : Continuous (fun x : ESpace => f (t, x)) :=
      hf.comp (continuous_const.prodMk continuous_id)
    exact (hslice.norm.pow 2).integrable_of_hasCompactSupport (hcompact t ht)
  have hcontinuous :
      ContinuousOn (fun t : ℝ => ∫ x : ESpace, ‖f (t, x)‖ ^ 2 ∂volume)
        (Icc (0 : ℝ) 1) := by
    apply continuousOn_integral_of_compact_support hK
    · exact (hf.norm.pow 2).continuousOn
    · intro t x ht hx
      simp only [hsupp t ht x hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  obtain ⟨C, hC, hbound⟩ :=
    (isCompact_Icc.image_of_continuousOn hcontinuous).isBounded.exists_pos_norm_le
  refine ⟨C, hC.le, ?_⟩
  intro t ht
  refine ⟨hint t ht, ?_⟩
  have hnorm := hbound _ ⟨t, ht, rfl⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)

/-- The compact-candidate carrier itself implies ordinary uniform finite
energy for its velocity once the already-constructed force is known to be
globally smooth.  All integrals use Lebesgue volume on `ℝ³`. -/
theorem uniform_finite_energy_of_properties {u : EVelocityField}
    {p : Navier.Construction.ProblemStatement.PressureField}
    {f : EVelocityField} (h : Properties u p f) (hf : ContDiff ℝ ∞ f) :
    Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u := by
  obtain ⟨Ku, hKu, huoutside⟩ := h.velocity_support
  obtain ⟨Kf, hKf, hfoutside⟩ := h.force_support
  have husupp : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : ESpace => u (t, x)) ⊆ Ku := by
    intro t ht
    apply closure_minimal _ hKu.isClosed
    intro x hx
    by_contra hxK
    exact hx (huoutside t ht x hxK)
  obtain ⟨C, hC, hforce⟩ := exists_uniform_force_l2sq_bound hKf hf.continuous
    (fun t ht x hx => hfoutside t ht.1 x hx)
  refine ⟨(1 / 2 : ℝ) * (C * Real.exp 1),
    mul_nonneg (by norm_num) (mul_nonneg hC (Real.exp_pos _).le), ?_⟩
  intro t ht
  have hsub : Navier.ConstructionR3.Comparison.slab 0 t ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 ht.2⟩, hz.2⟩
  have huT := h.velocity_smooth.mono hsub
  have hpT := h.pressure_smooth.mono hsub
  have hsuppT : ∀ r ∈ Icc (0 : ℝ) t,
      tsupport (fun x : ESpace => u (r, x)) ⊆ Ku := by
    intro r hr
    exact husupp r ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hzero : l2Sq u 0 = 0 := by
    simp [l2Sq, h.zero_initial_velocity]
  have hbound : l2Sq u t ≤ C * Real.exp 1 := by
    apply Navier.ConstructionR3.ScalarEnergyBound.forced_gronwall_uniform
      ht.1 ht.2.le hC
      (l2Sq_continuousOn hKu huT hsuppT) hzero
      (fun r hr => energy_hasDerivAt hKu huT hsuppT hr) _ t ⟨ht.1, le_rfl⟩
    intro r hr
    have hrT : r ∈ Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
    have hr1 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, hr.2.trans ht.2⟩
    have hrf := hforce r ⟨hr.1.le, hr1.2.le⟩
    have hrate := energy_rate_le
      (Navier.Construction.PeriodicUniqueness.spatial_smooth huT hrT)
      (Navier.Construction.PeriodicUniqueness.spatial_smooth hpT hrT)
      (hf.continuous.comp (continuous_const.prodMk continuous_id))
      (slice_compact hKu (hsuppT r hrT)) hrf.1
      (h.divergence_free r ⟨hr.1.le, hr1.2⟩) (h.navier_stokes r hr1)
    exact hrate.trans (add_le_add_right hrf.2 _)
  refine ⟨integrable_norm_sq
    (Navier.Construction.PeriodicUniqueness.spatial_smooth huT ⟨ht.1, le_rfl⟩).continuous
    (slice_compact hKu (husupp t ht)), ?_⟩
  exact mul_le_mul_of_nonneg_left hbound (by norm_num)

/-- The exact selected velocity, pressure, and compact force inhabit the
finite-energy conclusion; this is not a separate abstract candidate. -/
theorem selected_compact_candidate_with_energy :
    ∃ u : EVelocityField,
      ∃ p : Navier.Construction.ProblemStatement.PressureField,
      ∃ f : EVelocityField,
      Properties u p f ∧ ContDiff ℝ ∞ f ∧
        Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u := by
  obtain ⟨u, p, f, hcandidate, hf⟩ :=
    Navier.Analysis.ConstructedForceExtension.selected_compact_candidate_contDiff
  exact ⟨u, p, f, hcandidate, hf,
    uniform_finite_energy_of_properties hcandidate hf⟩

#print axioms exists_uniform_force_l2sq_bound
#print axioms uniform_finite_energy_of_properties
#print axioms selected_compact_candidate_with_energy

end Navier.Analysis.SelectedCandidateEnergy
