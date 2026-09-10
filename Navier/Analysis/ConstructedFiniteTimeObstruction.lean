import Navier.Analysis.SelectedCandidateEnergy
import Navier.Construction.R3FiniteEnergyComparison
import Navier.Analysis.QuantumVortexRegularity

/-!
# Sharp finite-time consequences of the selected compact candidate

The comparison theorem identifies the selected velocity with every smooth
finite-energy competitor on each closed slab before time one.  Independently,
the candidate's unbounded speed and fixed compact spatial support rule out even
a continuous extension through time one: continuity on the compact support
cylinder would force a uniform bound there.

These are consequences of the constructed fields.  No extension, uniqueness,
or breakdown statement is included as a hypothesis. The Madelung obstruction
uses actual spatial Frechet derivatives and uniform nonvanishing; it asserts
no wavefunction lift and no quantum evolution equation.
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

/-- Speed blowup excludes a bound even on the half-open support cylinder.
Both terminal nonextension and regular-decoder obstructions consume this lemma. -/
theorem not_bounded_on_presingular_support
    {u f : EVelocityField} {p : EPressureField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f)
    {K : Set ESpace}
    (hsupport : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0)
    : ¬ (∃ M : ℝ, ∀ z ∈ Ico (0 : ℝ) 1 ×ˢ K, ‖u z‖ ≤ M) := by
  intro hvbound
  obtain ⟨M, hM⟩ := hvbound
  have hpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨t, x, ht, _, hlarge⟩ := h.speed_unbounded (max M 1) hpos 1 zero_lt_one
  have hx : x ∈ K := by
    by_contra hxK
    rw [hsupport t ⟨ht.1.le, ht.2⟩ x hxK, norm_zero] at hlarge
    exact (not_lt_of_ge hpos.le) hlarge
  have hb := hM (t, x) ⟨⟨ht.1.le, ht.2⟩, hx⟩
  exact (not_lt_of_ge (hb.trans (le_max_left M 1))) hlarge

/-- The extension consequence reuses the presingular boundedness obstruction. -/
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
  apply not_bounded_on_presingular_support h hsupport
  refine ⟨M, ?_⟩
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  rw [heq t ht x]
  exact hM (t, x) ⟨⟨ht.1, ht.2.le⟩, hx⟩

/-- A scalar Madelung representation on the support cannot have both a
uniform positive amplitude floor and uniformly bounded spatial derivative.
The pairing is the coordinate-free current formula, with `κ = hbar / mass`.
Spatial differentiability is explicit so totalized `fderiv` is not used as
a substitute for a derivative. No Schrödinger equation is assumed. -/
theorem compact_candidate_no_regular_madelung_lift
    {u f : EVelocityField} {p : EPressureField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f)
    {K : Set ESpace}
    (hsupport : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0)
    (ψ : ℝ → ESpace → ℂ) (κ c M : ℝ) (hc : 0 < c)
    (_hψ : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ K, DifferentiableAt ℝ (ψ t) x)
    (hfloor : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ K, c ≤ ‖ψ t x‖)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ K, ‖fderiv ℝ (ψ t) x‖ ≤ M) :
    ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ K, ∀ d : ESpace,
      inner ℝ (u (t, x)) d = κ * (fderiv ℝ (ψ t) x d / ψ t x).im) := by
  intro hdecode
  apply not_bounded_on_presingular_support h hsupport
  refine ⟨|κ| * M / c, ?_⟩
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  have hnonzero : ψ t x ≠ 0 := norm_pos_iff.mp (hc.trans_le (hfloor t ht x hx))
  have hM : 0 ≤ M := (norm_nonneg _).trans (hderiv t ht x hx)
  have hbound := Navier.Analysis.QuantumVortexRegularity.norm_le_of_madelung_pairing
    (u := u (t, x)) (ψ := ψ t x) (D := fderiv ℝ (ψ t) x) (κ := κ)
    hnonzero (hdecode t ht x hx)
  exact hbound.trans (div_le_div₀
    (mul_nonneg (abs_nonneg κ) hM)
    (mul_le_mul_of_nonneg_left (hderiv t ht x hx) (abs_nonneg κ))
    hc (hfloor t ht x hx))

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

/-- Every smooth same-force competitor with finite energy on each individual
compact presingular slab agrees pointwise with the candidate before time one.
The energy bound may depend on the slab endpoint and need not remain uniform as
the endpoint tends to one. -/
theorem compact_candidate_agrees_with_locally_finite_energy_competitor
    {u f : EVelocityField} {p : EPressureField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f)
    {v : EVelocityField} {q : EPressureField}
    (hv : ContDiffOn ℝ ∞ v preSingularDomain)
    (hq : ContDiffOn ℝ ∞ q preSingularDomain)
    (henergy : ∀ T ∈ Ico (0 : ℝ) 1,
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, spatialDivergence v t x = 0)
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, navierStokesResidual v q t x = f (t, x))
    (hvzero : ∀ x, v (0, x) = 0) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x) := by
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

/-- In the normalized unit-viscosity, deadline-one problem, the candidate's
full pointwise speed blowup transfers to every smooth
same-force competitor having finite energy separately on each compact
presingular slab.  No continuity or boundedness at time one is assumed. -/
theorem compact_candidate_transfers_speed_unbounded
    {u f : EVelocityField} {p : EPressureField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f)
    {v : EVelocityField} {q : EPressureField}
    (hv : ContDiffOn ℝ ∞ v preSingularDomain)
    (hq : ContDiffOn ℝ ∞ q preSingularDomain)
    (henergy : ∀ T ∈ Ico (0 : ℝ) 1,
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, spatialDivergence v t x = 0)
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, navierStokesResidual v q t x = f (t, x))
    (hvzero : ∀ x, v (0, x) = 0) : SpeedUnboundedAtOne v := by
  have hagree := compact_candidate_agrees_with_locally_finite_energy_competitor
    h hv hq henergy hdv hNSv hvzero
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := h.speed_unbounded M hM δ hδ
  exact ⟨t, x, ht, hnear, by rwa [hagree t ⟨ht.1.le, ht.2⟩ x] at hlarge⟩

/-- In the normalized unit-viscosity, deadline-one problem, the force of a
compact blowup candidate cannot vanish identically during physical presingular
time.  Otherwise the smooth zero flow would be a locally-finite-energy
same-force competitor and would inherit impossible speed blowup. -/
theorem compact_candidate_force_nonzero_before_one
    {u f : EVelocityField} {p : EPressureField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : ESpace, f (t, x) ≠ 0 := by
  by_contra hzero
  have hfzero : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : ESpace, f (t, x) = 0 := by
    intro t ht x
    by_contra hne
    exact hzero ⟨t, ht, x, hne⟩
  apply zero_velocity_not_unbounded
  apply compact_candidate_transfers_speed_unbounded h
    (v := fun _ => 0) (q := fun _ => 0)
    contDiff_const.contDiffOn contDiff_const.contDiffOn
  · intro T hT
    refine ⟨0, le_rfl, ?_⟩
    intro t ht
    constructor
    · simp [Navier.ConstructionR3.ProblemStatement.SquareIntegrableAtTime]
    · simp [Navier.ConstructionR3.ProblemStatement.kineticEnergy]
  · intro t ht
    intro x
    simp [Navier.Construction.ProblemStatement.spatialDivergence,
      Navier.Construction.ProblemStatement.spatialDerivative]
  · intro t ht x
    exact (zero_residual t x).trans (hfzero t ht x).symm
  · intro x
    rfl

/-- No competitor can remain smooth before time one, continuous through time
one on the candidate's support, and finite-energy on every individual compact
presingular slab while solving the same equation from the same initial data. -/
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
  exact compact_candidate_agrees_with_locally_finite_energy_competitor
    h hv hq henergy hdv hNSv hvzero

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

/-- The actual selected force exposes one compact spatial support and one
finite upper endpoint for its support on physical time.  Global smoothness and
the selected velocity's presingular finite energy are retained on the same
witness. -/
theorem selected_force_has_compact_physical_support :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField,
      ∃ K : Set ESpace, ∃ T : ℝ,
        Navier.Construction.R3CompactCandidate.Properties u p f ∧
        ContDiff ℝ ∞ f ∧
        Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
        IsCompact K ∧ 0 ≤ T ∧
        Navier.Construction.CompactSpatialForceDecay.SupportedIn K f ∧
        ∀ t : ℝ, T ≤ t → ∀ x : ESpace, f (t, x) = 0 := by
  obtain ⟨u, p, f, h, hf, henergy⟩ :=
    Navier.Analysis.SelectedCandidateEnergy.selected_compact_candidate_with_energy
  obtain ⟨K, hK, hspace⟩ := h.force_support
  obtain ⟨T, hT, htime⟩ := h.force_time_support
  exact ⟨u, p, f, K, T, h, hf, henergy, hK, hT, hspace, htime⟩

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

/-- The selected forced finite-energy profile itself excludes a uniformly
regular scalar Madelung lift. This instantiates the obstruction with the
constructed witness, rather than assuming a blowup candidate exists. -/
theorem selected_candidate_no_regular_madelung_lift :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField, ∃ K : Set ESpace,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ f ∧
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      IsCompact K ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0) ∧
      ∀ (ψ : ℝ → ESpace → ℂ) (κ c M : ℝ), 0 < c →
        (∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ K, DifferentiableAt ℝ (ψ t) x) →
        (∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ K, c ≤ ‖ψ t x‖) →
        (∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ K, ‖fderiv ℝ (ψ t) x‖ ≤ M) →
        ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ K, ∀ d : ESpace,
          inner ℝ (u (t, x)) d = κ * (fderiv ℝ (ψ t) x d / ψ t x).im) := by
  obtain ⟨u, p, f, K, h, hf, henergy, hK, hsupport, _⟩ :=
    selected_candidate_no_continuous_extension
  exact ⟨u, p, f, K, h, hf, henergy, hK, hsupport,
    fun ψ κ c M hc hψ hfloor hderiv =>
      compact_candidate_no_regular_madelung_lift h hsupport ψ κ c M hc hψ hfloor hderiv⟩

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

/-- In the normalized unit-viscosity, deadline-one problem, every
presingular-smooth, locally finite-energy solution of the selected forced
equation from rest must develop the same pointwise speed blowup at time one.
This conclusion requires neither a terminal trace nor one energy bound uniform
in the slab endpoint. -/
theorem selected_candidate_forces_speed_blowup_in_every_smooth_competitor :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ f ∧
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      ∀ v : EVelocityField, ∀ q : EPressureField,
        ContDiffOn ℝ ∞ v preSingularDomain →
        ContDiffOn ℝ ∞ q preSingularDomain →
        (∀ T ∈ Ico (0 : ℝ) 1,
          Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v) →
        (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, spatialDivergence v t x = 0) →
        (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, navierStokesResidual v q t x = f (t, x)) →
        (∀ x, v (0, x) = 0) → SpeedUnboundedAtOne v := by
  obtain ⟨u, p, f, _, h, hf, henergy, _, _, _, _⟩ :=
    selected_candidate_finite_time_profile
  refine ⟨u, p, f, h, hf, henergy, ?_⟩
  intro v q hv hq hlocalEnergy hdv hNSv hvzero
  exact compact_candidate_transfers_speed_unbounded
    h hv hq hlocalEnergy hdv hNSv hvzero

/-- In the normalized unit-viscosity, deadline-one problem, the selected
globally smooth compact force is genuinely nonzero at some physical point
before the singular time.  Thus the constructed endpoint is formally
separated from the unforced equation. -/
theorem selected_force_nonzero_before_one :
    ∃ u : EVelocityField, ∃ p : EPressureField, ∃ f : EVelocityField,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ f ∧
      Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : ESpace, f (t, x) ≠ 0 := by
  obtain ⟨u, p, f, _, h, hf, henergy, _, _, _, _⟩ :=
    selected_candidate_finite_time_profile
  exact ⟨u, p, f, h, hf, henergy, compact_candidate_force_nonzero_before_one h⟩

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
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.not_bounded_on_presingular_support
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_no_regular_madelung_lift
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_no_regular_madelung_lift
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.not_continuous_extension_on_support
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_agrees_with_locally_finite_energy_competitor
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_transfers_speed_unbounded
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_force_nonzero_before_one
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.compact_candidate_excludes_locally_finite_energy_continuation
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_force_has_compact_physical_support
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_no_continuous_extension
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_unique_on_every_presingular_slab
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_forces_speed_blowup_in_every_smooth_competitor
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_force_nonzero_before_one
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_excludes_locally_finite_energy_continuation

#check Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile
#check Navier.Analysis.ConstructedFiniteTimeObstruction.selected_force_has_compact_physical_support
#check Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_forces_speed_blowup_in_every_smooth_competitor
#check Navier.Analysis.ConstructedFiniteTimeObstruction.selected_force_nonzero_before_one
#check Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_excludes_locally_finite_energy_continuation
