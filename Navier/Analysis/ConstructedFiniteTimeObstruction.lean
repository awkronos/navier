import Navier.Analysis.SelectedCandidateEnergy
import Navier.Construction.R3FiniteEnergyComparison

/-!
# Sharp finite-time consequences of the selected compact candidate

The comparison theorem identifies the selected velocity with every smooth
finite-energy competitor on each closed slab before time one.  Independently,
the candidate's unbounded speed and fixed compact spatial support rule out even
a continuous extension through time one: continuity on the compact support
cylinder would force a uniform bound there.

These are consequences of the constructed fields.  No extension, uniqueness,
or breakdown statement is included as a hypothesis.
-/

noncomputable section

namespace Navier.Analysis.ConstructedFiniteTimeObstruction

open Set
open scoped ContDiff
open Navier.Construction.ProblemStatement
open Navier.Construction.ComparatorBridge

private abbrev ESpace := Navier.Construction.ProblemStatement.Space
private abbrev EVelocityField := Navier.Construction.ProblemStatement.VelocityField
private abbrev EPressureField := Navier.Construction.ProblemStatement.PressureField

/-- An extension agreeing with an unbounded compactly supported candidate
cannot be uniformly bounded on the candidate's closed support cylinder through
time one.  This is the quantitative core of terminal nonextension. -/
theorem not_bounded_extension_on_support
    {u f : EVelocityField} {p : EPressureField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f)
    {K : Set ESpace}
    (hsupport : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0)
    {v : EVelocityField}
    (hvbound : ∃ M : ℝ, ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ K, ‖v z‖ ≤ M) :
    ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x)) := by
  intro heq
  obtain ⟨M, hM⟩ := hvbound
  have hpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨t, x, ht, _, hlarge⟩ := h.speed_unbounded (max M 1) hpos 1 zero_lt_one
  have hx : x ∈ K := by
    by_contra hxK
    rw [hsupport t ⟨ht.1.le, ht.2⟩ x hxK, norm_zero] at hlarge
    exact (not_lt_of_ge hpos.le) hlarge
  have hb := hM (t, x) ⟨⟨ht.1.le, ht.2.le⟩, hx⟩
  rw [← heq t ⟨ht.1.le, ht.2⟩ x] at hb
  exact (not_lt_of_ge (hb.trans (le_max_left M 1))) hlarge

/-- Even continuity only on the compact region occupied by the candidate is
incompatible with an extension through the singular time that agrees at all
presingular times. -/
theorem not_continuous_extension_on_support
    {u f : EVelocityField} {p : EPressureField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupport : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0)
    {v : EVelocityField} (hv : ContinuousOn v (Icc (0 : ℝ) 1 ×ˢ K)) :
    ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x)) := by
  apply not_bounded_extension_on_support h hsupport
  exact (isCompact_Icc.prod hK).exists_bound_of_continuousOn hv

/-- No competitor can remain smooth before time one, continuous through time
one on the candidate's support, and finite-energy on every individual compact
presingular slab while solving the same equation from the same initial data.
The energy bound may depend on the slab endpoint and need not remain uniform as
the endpoint tends to one. -/
theorem compact_candidate_excludes_locally_finite_energy_continuation
    {u f : EVelocityField} {p : EPressureField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupport : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0)
    {v : EVelocityField} {q : EPressureField}
    (hv : ContDiffOn ℝ ∞ v preSingularDomain)
    (hq : ContDiffOn ℝ ∞ q preSingularDomain)
    (hvterminal : ContinuousOn v (Icc (0 : ℝ) 1 ×ˢ K))
    (henergy : ∀ T ∈ Ico (0 : ℝ) 1,
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, spatialDivergence v t x = 0)
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, navierStokesResidual v q t x = f (t, x))
    (hvzero : ∀ x, v (0, x) = 0) : False := by
  apply not_continuous_extension_on_support h hK hsupport hvterminal
  intro t ht x
  have hsub : Navier.ConstructionR3.Comparison.slab 0 t ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt ht.2⟩, hz.2⟩
  have heq := compact_candidate_unique_on_Icc h ht.2
    (hv.mono hsub) (hq.mono hsub) (henergy t ht)
    (fun r hr => hdv r ⟨hr.1, hr.2.trans ht.2⟩)
    (fun r hr => hNSv r ⟨hr.1, hr.2.trans ht.2⟩)
    hvzero
  exact heq t ⟨ht.1, le_rfl⟩ x

/-- Every compact candidate exposes a particular compact support on which no
continuous terminal extension can agree with it before time one. -/
theorem exists_support_with_no_continuous_extension
    {u f : EVelocityField} {p : EPressureField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f) :
    ∃ K : Set ESpace, IsCompact K ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0) ∧
      ∀ v : EVelocityField, ContinuousOn v (Icc (0 : ℝ) 1 ×ˢ K) →
        ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x)) := by
  obtain ⟨K, hK, hsupport⟩ := h.velocity_support
  exact ⟨K, hK, hsupport, fun _ hv =>
    not_continuous_extension_on_support h hK hsupport hv⟩

/-- The selected fields simultaneously carry finite energy, terminal
nonextension, and finite-slab uniqueness.  Keeping these consequences on one
existential witness records that they concern the same constructed flow. -/
theorem selected_candidate_finite_time_profile :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField, ∃ K : Set ESpace,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ f ∧
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      IsCompact K ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0) ∧
      (∀ v : EVelocityField, ContinuousOn v (Icc (0 : ℝ) 1 ×ˢ K) →
        ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x))) ∧
      ∀ T : ℝ, T < 1 → ∀ v : EVelocityField, ∀ q : EPressureField,
        ContDiffOn ℝ ∞ v (Navier.ConstructionR3.Comparison.slab 0 T) →
        ContDiffOn ℝ ∞ q (Navier.ConstructionR3.Comparison.slab 0 T) →
        Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v →
        (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0) →
        (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, navierStokesResidual v q t x = f (t, x)) →
        (∀ x, v (0, x) = 0) →
        ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  obtain ⟨u, p, f, h, hf, henergy⟩ :=
    Navier.Analysis.SelectedCandidateEnergy.selected_compact_candidate_with_energy
  obtain ⟨K, hK, hsupport⟩ := h.velocity_support
  refine ⟨u, p, f, K, h, hf, henergy, hK, hsupport,
    fun _ hv => not_continuous_extension_on_support h hK hsupport hv, ?_⟩
  intro T hT v q hv hq hev hdv hNSv hvzero
  exact compact_candidate_unique_on_Icc h hT hv hq hev hdv hNSv hvzero

/-- The exact selected construction has a globally smooth force and a velocity
that admits no continuous extension through time one even on its own fixed
compact spatial support. -/
theorem selected_candidate_no_continuous_extension :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField, ∃ K : Set ESpace,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ f ∧
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      IsCompact K ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0) ∧
      ∀ v : EVelocityField, ContinuousOn v (Icc (0 : ℝ) 1 ×ˢ K) →
        ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x)) := by
  obtain ⟨u, p, f, K, h, hf, henergy, hK, hsupport, hno, _⟩ :=
    selected_candidate_finite_time_profile
  exact ⟨u, p, f, K, h, hf, henergy, hK, hsupport, hno⟩

/-- On every finite presingular slab, the selected velocity is the unique
smooth finite-energy flow with the selected force and zero initial data. -/
theorem selected_candidate_unique_on_every_presingular_slab :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧ ContDiff ℝ ∞ f ∧
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      ∀ T : ℝ, T < 1 → ∀ v : EVelocityField, ∀ q : EPressureField,
        ContDiffOn ℝ ∞ v (Navier.ConstructionR3.Comparison.slab 0 T) →
        ContDiffOn ℝ ∞ q (Navier.ConstructionR3.Comparison.slab 0 T) →
        Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v →
        (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0) →
        (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, navierStokesResidual v q t x = f (t, x)) →
        (∀ x, v (0, x) = 0) →
        ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  obtain ⟨u, p, f, _, h, hf, henergy, _, _, _, hunique⟩ :=
    selected_candidate_finite_time_profile
  exact ⟨u, p, f, h, hf, henergy, hunique⟩

/-- The selected actual candidate excludes the locally finite-energy
continuation class: presingular smoothness and a separate finite-energy bound
on every compact slab still cannot coexist with continuity through time one on
the compact region occupied by the flow. -/
theorem selected_candidate_excludes_locally_finite_energy_continuation :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField, ∃ K : Set ESpace,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ f ∧
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      IsCompact K ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0) ∧
      ¬ ∃ v : EVelocityField, ∃ q : EPressureField,
        ContDiffOn ℝ ∞ v preSingularDomain ∧
        ContDiffOn ℝ ∞ q preSingularDomain ∧
        ContinuousOn v (Icc (0 : ℝ) 1 ×ˢ K) ∧
        (∀ T ∈ Ico (0 : ℝ) 1,
          Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, spatialDivergence v t x = 0) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, navierStokesResidual v q t x = f (t, x)) ∧
        ∀ x, v (0, x) = 0 := by
  obtain ⟨u, p, f, K, h, hf, henergy, hK, hsupport, _, _⟩ :=
    selected_candidate_finite_time_profile
  refine ⟨u, p, f, K, h, hf, henergy, hK, hsupport, ?_⟩
  rintro ⟨v, q, hv, hq, hvterminal, hlocalEnergy, hdv, hNSv, hvzero⟩
  exact compact_candidate_excludes_locally_finite_energy_continuation
    h hK hsupport hv hq hvterminal hlocalEnergy hdv hNSv hvzero

end Navier.Analysis.ConstructedFiniteTimeObstruction

#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.not_bounded_extension_on_support
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.not_continuous_extension_on_support
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_excludes_locally_finite_energy_continuation
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_no_continuous_extension
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_unique_on_every_presingular_slab
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_excludes_locally_finite_energy_continuation

#check Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile
#check Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_excludes_locally_finite_energy_continuation
