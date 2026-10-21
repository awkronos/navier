import Navier.Analysis.RegularRestart
import Navier.Analysis.PressureAgree

/-!
# Item 6 of the R-route: local existence from an H³ restart-slice datum

`docs/OPEN_FRONTIER_MAP.md` row A records the ITEM-6 FEASIBILITY AUDIT: every clause of
the class `R = RegularOnCompacts` is attainable in principle from `H³` data, but three
hazards stand between the audit and a proof.  This module is the item-6 interface and
decomposition: it names the datum class a producer must consume, names the piece class
it must return, PROVES the structural halves the audit calls "a separate lemma", and
states the three analytic premises with the consumer that turns them into
`RegularRestart.DatumHorizonIndependentRestartR` — hence into the crown.

**(a) The fixed point for non-Wiener data.**  The repository's Wiener/Lei–Lin local
theory consumes all Fourier moments, while `H³ ∩ L²` data gives weighted-`L¹` moments
`∫ |ξ|^α |û| dξ` only for `α < 3/2` (split at `|ξ| = 1`: the low part is finite for
`α > −3/2` from `û ∈ L²`, the high part for `2α − 6 < −3`, i.e. `α < 3/2`, from the
`|ξ|³ û ∈ L²` weight; `α = 3` is reached by neither).  So none of those carriers can be
fed by an `H³` slice.  This module therefore states `H3SliceLocalExistence` — a
datum-uniform lifespan `L = L(ν, K)` producing a `RestartPiece` — as a NAMED premise,
and proves the two facts that make it the right premise: `h3SliceDatum_of_R` (every
slice of an `R`-solution below its horizon is an admissible datum, so the premise is
demanded of exactly the objects the restart ladder presents) and
`RestartPiece.of_solvesBefore` (every existing start-smooth local solution in `R`
inhabits `RestartPiece`, so the premise is a genuine weakening at `t = 0`, not an
uninhabitable contract).

**(b) Joint `C^∞` on `[T₀, T₀ + L)` from `H³` data.**  `SolvesFrom` asks for smoothness
AT the strip start, which `H³` data does not give; the piece is smooth only in the
interior.  The audit prescribes combining uniqueness with interior parabolic smoothing,
"the latter a separate bootstrap".  This module proves the separate lemma in the shape
the bootstrap needs: `strip_of_restart_piece` glues an `R`-solution on `[T₀, T)` to a
piece that is smooth only on the OPEN slab `(0, L) × ℝ³` and returns a full `SolvesFrom`
strip together with `RegularOnCompactsFrom` on `[T₀, T₀ + L)` and the normalized strip
pressure.  Smoothness at the strip start is supplied by the `R`-solution (which is
smooth at `T₀` because `T₀ < T`); smoothness across the cut at `T` comes from the
agreement, which makes the strip equal to the single shifted piece on all of
`(T₀, T₀ + L)`; the energy clause normalized at `T₀` comes from the piece; the uniform
`R`-bound up to `T₀` from `RegularOnCompacts` at the midpoint of `[T₀, T]`.  Its only
analytic input is the named agreement, and `pressure_agree_of_piece` proves the pressure
half of that agreement from the velocity half — so the open content of hazard (b) is
exactly one field, `RestartAgreement`.  The leaf `timeDerivative_shift_open` is the
calculus fact this forces: `RestartPaste.timeDerivative_shift` requires the restarted
field to be smooth on the CLOSED slab `[0, δ)`, which an `H³` restart piece does not
have.

**(c) The Riesz-transform pressure for non-Wiener fields.**  This module attacks (c) by
typing the obligation into the producer's return contract rather than assuming it:
`RestartPiece` requires `PresSlice` and `PresL2` bounds on the produced pressure (via
`rslice`) and its normalization (`pres0`), so `H3SliceLocalExistence` can only be
discharged by a producer that constructs `p` with `∇p ∈ H¹` and `p − c ∈ L²`.  The
pointwise representation `p = Σᵢⱼ RᵢRⱼ(uᵢuⱼ)` for non-Wiener fields is NOT proved here;
the repository's `Analysis.SingularIntegralPrelims` / `Analysis.PressureL2Riesz` layer
(p² Calderón–Zygmund for the double-Riesz multiplier, transported to the estate `L²`
carrier) is the carrier such a producer would consume, and `RestartPiece.rslice` names
what has to come out of it.

Nothing here widens `RegularOnCompacts`: it is consumed exactly as the `R`-restart leaf
states it, in accordance with the recorded recommendation "no further extension of `R`
before item 6 is built".
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal

namespace Navier.Analysis.H3RestartSlice

open Navier Navier.Breakdown
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.RestartPaste
open Navier.Analysis.RegularRestart
open Navier.Analysis.PressureAgree

/-! ## The datum class -/

/-- **An `H³` restart-slice datum with bound `K`.**  Exactly the content of one `R`
slice that a local-existence producer can be handed at a restart time: the
`Ḣ¹ ∩ Ḣ² ∩ Ḣ³` integral bound, the Serrin-type pointwise bound on the field and its
first derivatives, square-integrability of the energy, and incompressibility.  It
carries NO pressure: producing `p` with `∇p ∈ H¹` and `p − c ∈ L²` from `v` is hazard
(c), and belongs to what `H3SliceLocalExistence` must deliver. -/
structure H3SliceDatum (K : ℝ) (v : VelocityField) : Prop where
  energy : Integrable (fun x : Space => ‖v x‖ ^ 2)
  reg : RegSlice K v
  sup : SupSlice K v
  div : ∀ x : Space, staticDivergence v x = 0

/-- **Satisfiability guard (datum class nonempty).**  The zero field is an `H³` slice
datum with bound `0`, so `H3SliceLocalExistence` is not asked of an empty class — the
pole-(a) guard of `Navier.Problem` transported to the slice interface. -/
theorem h3SliceDatum_zero : H3SliceDatum 0 (fun _ : Space => (0 : Space)) where
  energy := by simp
  reg := by
    intro i j l
    refine ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩
  sup := ⟨fun _x => by simp, fun _x _i => by simp⟩
  div := fun _x => by simp [staticDivergence]

/-- **The `R`-slices a restart actually presents are admissible data.**  Every time
slice strictly below the horizon of a solution in `R` is an `H³` slice datum: the
`RegSlice`/`SupSlice` halves from the class bound at that time, the energy half from
the solution's finite-energy field, incompressibility from its equation bundle.  So the
restart ladder never hands the producer anything outside `H3SliceDatum`, and hazard (a)
is the only obstruction to closing the leaf. -/
theorem h3SliceDatum_of_R {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore ν T u p) (hR : RegularOnCompacts T u p)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) : ∃ K : ℝ, H3SliceDatum K (u t) := by
  obtain ⟨K, hK⟩ := hR t htT
  obtain ⟨hreg, _, _, hsup, _⟩ := hK t ⟨ht, le_rfl⟩
  exact ⟨K, ⟨hsol.finite_energy t ht htT, hreg, hsup,
    fun x => (divergence_eq_staticDivergence u t x).symm.trans
      (hsol.classical.2.2.1 t ht htT x)⟩⟩

/-! ## The piece class -/

/-- **A restart piece of length `L` driven by the datum `v` at its own start time.**
This is the return type item 6 must produce: a classical strip on `[0, L)` whose joint
spacetime smoothness is asked ONLY on the open slab `(0, L) × ℝ³` — the hazard-(b)
point being that `H³` data does not make the piece smooth at `t = 0` — together with
the `R`-bounds on the open sub-intervals (`rslice`), the normalized pressure (`pres0`)
and the energy inequality normalized at the piece's own start.
`strip_of_restart_piece` shows this is precisely enough to build an `R`-strip, the
missing start smoothness being supplied by the solution being restarted. -/
structure RestartPiece (ν L : ℝ) (v : VelocityField) (vel : ℝ → VelocityField)
    (pres : ℝ → PressureField) : Prop where
  Lpos : 0 < L
  init : vel 0 = v
  smooth_vel : ContDiffOn ℝ ∞ (fun z : ℝ × Space => vel z.1 z.2)
    (Set.Ioo (0 : ℝ) L ×ˢ (Set.univ : Set Space))
  smooth_pres : ContDiffOn ℝ ∞ (fun z : ℝ × Space => pres z.1 z.2)
    (Set.Ioo (0 : ℝ) L ×ˢ (Set.univ : Set Space))
  incompressible : ∀ t : ℝ, 0 ≤ t → t < L → ∀ x : Space, divergence vel t x = 0
  equation : ∀ t : ℝ, 0 < t → t < L → ∀ x : Space,
    timeDerivative vel t x + convection vel t x =
      ν • laplacian vel t x - pressureGradient pres t x
  finite_energy : ∀ t : ℝ, 0 ≤ t → t < L → Integrable (fun x : Space => ‖vel t x‖ ^ 2)
  energy_le_start : ∀ t : ℝ, 0 ≤ t → t < L →
    kineticEnergy vel t ≤ kineticEnergy vel 0
  rslice : ∀ T' : ℝ, T' < L → ∃ K : ℝ, ∀ t ∈ Set.Ioc (0 : ℝ) T',
    RegSlice K (vel t) ∧ PresSlice K (pres t) ∧ TimeSlice K vel t ∧
      SupSlice K (vel t) ∧ PresL2 K (pres t)
  pres0 : ∀ t : ℝ, 0 ≤ t → t < L → pres t 0 = 0

/-- Restricting a piece to a shorter lifespan is again a piece.  The consumer needs
this because its strip length `T - T₀ + h` is bounded by, not equal to, the lifespan
the producer supplies. -/
theorem RestartPiece.mono {ν L L' : ℝ} {v : VelocityField} {vel : ℝ → VelocityField}
    {pres : ℝ → PressureField} (hp : RestartPiece ν L v vel pres) (hL'L : L' ≤ L)
    (hL'0 : 0 < L') : RestartPiece ν L' v vel pres := by
  obtain ⟨hpos, hinit, hsv, hsp, hinc, heq, hfe, hel, hrsl, hp0⟩ := hp
  refine ⟨hL'0, hinit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hsv.mono (Set.prod_mono (Set.Ioo_subset_Ioo le_rfl hL'L) (Set.Subset.refl _))
  · exact hsp.mono (Set.prod_mono (Set.Ioo_subset_Ioo le_rfl hL'L) (Set.Subset.refl _))
  · exact fun t ht1 ht2 => hinc t ht1 (lt_of_lt_of_le ht2 hL'L)
  · exact fun t ht1 ht2 => heq t ht1 (lt_of_lt_of_le ht2 hL'L)
  · exact fun t ht1 ht2 => hfe t ht1 (lt_of_lt_of_le ht2 hL'L)
  · exact fun t ht1 ht2 => hel t ht1 (lt_of_lt_of_le ht2 hL'L)
  · exact fun T' hT' => hrsl T' (lt_of_lt_of_le hT' hL'L)
  · exact fun t ht1 ht2 => hp0 t ht1 (lt_of_lt_of_le ht2 hL'L)

/-- **Satisfiability guard (piece class inhabited).**  Every `SolvesBefore` solution of
positive length that lies in `R` with normalized pressure is a `RestartPiece` driven by
its own initial slice: the piece contract asks for strictly less at `t = 0` than
`SolvesBefore` does.  So `H3SliceLocalExistence` is a weakening of the repository's
local-existence leaf at the slice level — not an incompatible, hence vacuously true,
strengthening. -/
theorem RestartPiece.of_solvesBefore {ν L : ℝ} (_hν : 0 < ν) {v : VelocityEvolution}
    {q : PressureEvolution} (hL : 0 < L) (hsol : SolvesBefore ν L v q)
    (hR : RegularOnCompacts L v q) (hqn : PressureNormalizedBefore L q) :
    RestartPiece ν L (v 0) v q where
  Lpos := hL
  init := rfl
  smooth_vel := hsol.classical.1.mono
    (Set.prod_mono Set.Ioo_subset_Ico_self (Set.Subset.refl _))
  smooth_pres := hsol.classical.2.1.mono
    (Set.prod_mono Set.Ioo_subset_Ico_self (Set.Subset.refl _))
  incompressible := hsol.classical.2.2.1
  equation := fun t ht1 ht2 x => by
    have e := hsol.classical.2.2.2 t ht1.le ht2 x
    rw [show zeroForce t x = (0 : Space) from rfl, add_zero] at e
    exact e
  finite_energy := hsol.finite_energy
  energy_le_start := fun t ht1 ht2 => hsol.energy_le_initial t ht1 ht2
  rslice := fun T' hT' => by
    obtain ⟨K, hK⟩ := hR T' hT'
    exact ⟨K, fun t ht => hK t ⟨ht.1.le, ht.2⟩⟩
  pres0 := hqn

/-! ## Slice-transport leaves

Every term the strip interface mentions is a function of the slice alone, so a slice
equality transports it, possibly across times.  These are the public twins of the
private leaves of `RestartPaste`, stated for two (possibly different) times. -/

/-- Divergence sees only the slice. -/
theorem divergence_slice_congr {u v : VelocityEvolution} {t s : ℝ} (h : u t = v s)
    (x : Space) : divergence u t x = divergence v s x := by
  show ∑ i : Fin 3, fderiv ℝ (u t) x (basisVector i) i =
      ∑ i : Fin 3, fderiv ℝ (v s) x (basisVector i) i
  rw [h]

/-- The convective term sees only the slice. -/
theorem convection_slice_congr {u v : VelocityEvolution} {t s : ℝ} (h : u t = v s)
    (x : Space) : convection u t x = convection v s x := by
  show fderiv ℝ (u t) x (u t x) = fderiv ℝ (v s) x (v s x)
  rw [h]

/-- The Laplacian sees only the slice. -/
theorem laplacian_slice_congr {u v : VelocityEvolution} {t s : ℝ} (h : u t = v s)
    (x : Space) : laplacian u t x = laplacian v s x := by
  unfold laplacian
  rw [h]

/-- The pressure gradient sees only the pressure slice. -/
theorem pressureGradient_slice_congr {p q : PressureEvolution} {t s : ℝ} (h : p t = q s)
    (x : Space) : pressureGradient p t x = pressureGradient q s x := by
  unfold pressureGradient
  rw [h]

/-- The kinetic energy sees only the slice. -/
theorem kineticEnergy_slice_congr {u v : VelocityEvolution} {t s : ℝ} (h : u t = v s) :
    kineticEnergy u t = kineticEnergy v s := by
  unfold kineticEnergy
  rw [h]

/-- **Interior translation of the half-line time derivative.**  The same identity as
`RestartPaste.timeDerivative_shift`, for a field smooth only on the OPEN slab
`(0, δ) × ℝ³`: at a strictly interior time both sides are ordinary Fréchet derivatives,
so the closed-slab hypothesis of the paste lemma is not needed.  This is the calculus
leaf hazard (b) forces on an `H³` restart piece, whose smoothness at its own start time
is exactly what is not known. -/
theorem timeDerivative_shift_open (v : VelocityEvolution) (δ T₀ t : ℝ) (x : Space)
    (ht : 0 < t)
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)
      (Set.Ioo (0 : ℝ) δ ×ˢ (Set.univ : Set Space)))
    (hs : t - T₀ ∈ Set.Ioo (0 : ℝ) δ) :
    timeDerivative (fun s : ℝ => v (s - T₀)) t x = timeDerivative v (t - T₀) x := by
  have hopen : Set.Ioo (0 : ℝ) δ ×ˢ (Set.univ : Set Space) ∈ 𝓝 ⟨t - T₀, x⟩ :=
    (IsOpen.prod isOpen_Ioo isOpen_univ).mem_nhds ⟨⟨hs.1, hs.2⟩, Set.mem_univ x⟩
  have hF : DifferentiableAt ℝ (fun z : ℝ × Space => v z.1 z.2) ⟨t - T₀, x⟩ :=
    ((hv ⟨t - T₀, x⟩ ⟨⟨hs.1, hs.2⟩, Set.mem_univ x⟩).differentiableWithinAt
      (by simp)).differentiableAt hopen
  have hc : DifferentiableAt ℝ (fun u : ℝ => (u, x)) (t - T₀) :=
    DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const x)
  have hg : DifferentiableAt ℝ (fun u : ℝ => v u x) (t - T₀) := by
    show DifferentiableAt ℝ
      ((fun w : ℝ × Space => v w.1 w.2) ∘ (fun u : ℝ => (u, x))) (t - T₀)
    exact hF.comp (t - T₀) hc
  have hphi : DifferentiableAt ℝ (fun r : ℝ => r - T₀) t :=
    differentiableAt_id.sub (differentiableAt_const T₀)
  have hnt : Set.Ici (0 : ℝ) ∈ 𝓝 t :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ht)) Set.Ioi_subset_Ici_self
  have hns : Set.Ici (0 : ℝ) ∈ 𝓝 (t - T₀) :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hs.1)) Set.Ioi_subset_Ici_self
  have hgc : fderiv ℝ (fun u : ℝ => v u x) (t - T₀) =
      fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) ⟨t - T₀, x⟩ ∘SL
        fderiv ℝ (fun u : ℝ => (u, x)) (t - T₀) := by
    show fderiv ℝ
        ((fun w : ℝ × Space => v w.1 w.2) ∘ (fun u : ℝ => (u, x))) (t - T₀) = _
    exact fderiv_comp (t - T₀) hF hc
  have hcv : fderiv ℝ (fun u : ℝ => (u, x)) (t - T₀) =
      (ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Space) :=
    ((hasFDerivAt_id (t - T₀)).prodMk (hasFDerivAt_const x (t - T₀))).fderiv
  have hfphi : fderiv ℝ (fun r : ℝ => r - T₀) t = ContinuousLinearMap.id ℝ ℝ := by
    rw [fderiv_sub_const]
    simp
  have hL : fderivWithin ℝ (fun r : ℝ => v (r - T₀) x) (Set.Ici 0) t 1 =
      fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) ⟨t - T₀, x⟩ (1, 0) := by
    show fderivWithin ℝ ((fun u : ℝ => v u x) ∘ (fun r : ℝ => r - T₀)) (Set.Ici 0) t 1 = _
    rw [fderivWithin_of_mem_nhds hnt, fderiv_comp t hg hphi, hfphi, hgc, hcv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply]
  have hR : fderivWithin ℝ (fun r : ℝ => v r x) (Set.Ici 0) (t - T₀) 1 =
      fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) ⟨t - T₀, x⟩ (1, 0) := by
    show fderivWithin ℝ
        ((fun z : ℝ × Space => v z.1 z.2) ∘ (fun u : ℝ => (u, x))) (Set.Ici 0) (t - T₀) 1 = _
    rw [fderivWithin_of_mem_nhds hns, fderiv_comp (t - T₀) hF hc, hcv]
    simp
  exact hL.trans hR.symm

/-- Right translation of a piece smooth on the open slab: smoothness on
`(0, δ) × ℝ³` transports to smoothness on `(T₀, T₀ + δ) × ℝ³`.  The open twin of
`RestartPaste.contDiffOn_shift`; it is enough because the strip start `T₀` itself is
covered by the restarted solution, not by the piece. -/
theorem contDiffOn_shift_open {T₀ δ : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ × Space → E}
    (hF : ContDiffOn ℝ ∞ F (Set.Ioo (0 : ℝ) δ ×ˢ (Set.univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => F (z.1 - T₀, z.2))
      (Set.Ioo T₀ (T₀ + δ) ×ˢ (Set.univ : Set Space)) := by
  refine hF.comp (((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn) ?_
  rintro ⟨a, b⟩ ⟨⟨ha1, ha2⟩, -⟩
  exact ⟨⟨sub_pos.mpr ha1, sub_lt_iff_lt_add'.mpr ha2⟩, Set.mem_univ _⟩

/-! ## Set-upgrade leaves for the paste

The strip lives on `Ico T₀ (T₀ + L) ×ˢ univ`, while the restarted solution is smooth
only on `Ico 0 T ×ˢ univ` and the shifted piece only on `Ioo T₀ (T₀ + L) ×ˢ univ`.  At
a point of the strip the three sets agree locally — below the cut for the solution,
strictly above the start for the piece — which is what the two leaves below package. -/

/-- Below the cut `t = T`, smoothness within `Ico 0 T ×ˢ univ` is smoothness within the
strip `Ico T₀ (T₀ + L) ×ˢ univ`. -/
theorem contDiffWithinAt_strip_of_below {T₀ T L : ℝ} (hT₀ : 0 ≤ T₀)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × Space → F}
    (hf : ContDiffOn ℝ ∞ f (Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set Space))) (z : ℝ × Space)
    (hz : z ∈ Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)) (hzT : z.1 < T) :
    ContDiffWithinAt ℝ ∞ f (Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)) z :=
  (hf z ⟨⟨le_trans hT₀ hz.1.1, hzT⟩, hz.2⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin.mpr ⟨Set.Iio T ×ˢ (Set.univ : Set Space),
      IsOpen.prod isOpen_Iio isOpen_univ, ⟨Set.mem_Iio.mpr hzT, Set.mem_univ _⟩,
      fun ⟨_, b⟩ ⟨⟨ha, _⟩, ⟨⟨h1, _⟩, _⟩⟩ =>
        ⟨⟨le_trans hT₀ h1, Set.mem_Iio.mp ha⟩, Set.mem_univ b⟩⟩)

/-- Strictly above the strip start, smoothness within `Ioo T₀ (T₀ + L) ×ˢ univ` is
smoothness within the closed strip `Ico T₀ (T₀ + L) ×ˢ univ`. -/
theorem contDiffWithinAt_strip_of_above {T₀ L : ℝ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × Space → F}
    (hf : ContDiffOn ℝ ∞ f (Set.Ioo T₀ (T₀ + L) ×ˢ (Set.univ : Set Space))) (z : ℝ × Space)
    (hz : z ∈ Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)) (hT₀z : T₀ < z.1) :
    ContDiffWithinAt ℝ ∞ f (Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)) z :=
  (hf z ⟨⟨hT₀z, hz.1.2⟩, hz.2⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin.mpr ⟨Set.Ioi T₀ ×ˢ (Set.univ : Set Space),
      IsOpen.prod isOpen_Ioi isOpen_univ, ⟨Set.mem_Ioi.mpr hT₀z, Set.mem_univ _⟩,
      fun ⟨_, b⟩ ⟨⟨ha, _⟩, ⟨⟨_, hlt⟩, _⟩⟩ =>
        ⟨⟨Set.mem_Ioi.mp ha, hlt⟩, Set.mem_univ b⟩⟩)

/-- **The strip `C^∞` half of the paste (`smoothOnOpen_of_unique_extension`).**  A
field that is the restarted solution below the cut `T` and the shifted piece above the
start `T₀` is smooth on the closed strip, provided the two agree on the open overlap.
The case split is `z.1 < T` / `T ≤ z.1`: below the cut the solution's own smoothness
applies (no agreement needed, so the strip start `T₀`, where `H³` data gives nothing, is
covered); at and above the cut the shifted piece is smooth in the neighbourhood
`Ioi T₀`, and there the paste *is* the piece — which is where the open-interval
agreement is used. -/
theorem contDiffOn_paste {T₀ T L : ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u vel w : ℝ → Space → F}
    (hT₀ : 0 ≤ T₀) (hT₀T : T₀ < T)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2)
      (Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set Space)))
    (hvs : ContDiffOn ℝ ∞ (fun z : ℝ × Space => vel (z.1 - T₀) z.2)
      (Set.Ioo T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)))
    (hw_below : ∀ s : ℝ, s < T → w s = u s)
    (hw_above : ∀ s : ℝ, T₀ < s → w s = vel (s - T₀)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => w z.1 z.2)
      (Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)) := by
  intro z hz
  rcases lt_or_ge z.1 T with htT | htT
  · have hb : Filter.EventuallyEq
      (𝓝[Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)] z)
      (fun zz : ℝ × Space => w zz.1 zz.2) (fun zz : ℝ × Space => u zz.1 zz.2) :=
      eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds ((IsOpen.prod isOpen_Iio isOpen_univ).mem_nhds
          ⟨Set.mem_Iio.mpr htT, Set.mem_univ z.2⟩))
        fun z' hz' => congrFun (hw_below z'.1 (Set.mem_Iio.mp hz'.1)) z'.2
    exact (contDiffWithinAt_strip_of_below hT₀ hu z hz htT).congr_of_eventuallyEq_of_mem hb hz
  · have hT₀z : T₀ < z.1 := lt_of_lt_of_le hT₀T htT
    have hb : Filter.EventuallyEq
      (𝓝[Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)] z)
      (fun zz : ℝ × Space => w zz.1 zz.2) (fun zz : ℝ × Space => vel (zz.1 - T₀) zz.2) :=
      eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds ((IsOpen.prod isOpen_Ioi isOpen_univ).mem_nhds
          ⟨Set.mem_Ioi.mpr hT₀z, Set.mem_univ z.2⟩))
        fun z' hz' => congrFun (hw_above z'.1 (Set.mem_Ioi.mp hz'.1)) z'.2
    exact (contDiffWithinAt_strip_of_above hvs z hz hT₀z).congr_of_eventuallyEq_of_mem hb hz

/-! ## Hazard (b): the glue -/

/-- **`smoothOnOpen_of_unique_extension`: the separate lemma of the audit.**
Let `u` be a solution in `R` on `[0, T)` and let `(vel, pres)` be a restart piece of
length `L ≥ T - T₀` driven by the slice `u T₀`, smooth only on the open slab.  If the
piece agrees with `u` on the OPEN overlap `(T₀, T)` in velocity and pressure, then the
pasted strip is a `SolvesFrom ν T₀ L` strip, carries `RegularOnCompactsFrom` on
`[T₀, T₀ + L)`, and has normalized pressure on the whole strip.

This is the whole structural content of hazard (b), and it is proved, not assumed.  The
`SolvesFrom` clause `energy_le_start` — which `RestartPaste`'s module header records as
genuinely unavailable from the datum-level inequality `E(t) ≤ E(0)` — is discharged here
through the agreement, which rewrites every strip slice strictly above `T₀` to the
shifted piece and thereby normalizes the inequality at the strip start.  The agreement
is asked only on the open interval: at `T₀` itself the piece identity `vel 0 = u T₀` is
already part of the piece contract, and everything the strip needs at `T₀` comes from
the restarted solution. -/
theorem strip_of_restart_piece {ν T T₀ L : ℝ} (_hν : 0 < ν) (hT₀ : 0 ≤ T₀) (hT₀T : T₀ < T)
    (_hTL : T ≤ T₀ + L) {u : VelocityEvolution} {p : PressureEvolution}
    {vel : ℝ → VelocityField} {pres : ℝ → PressureField}
    (hsol : SolvesBefore ν T u p) (hR : RegularOnCompacts T u p)
    (hpiece : RestartPiece ν L (u T₀) vel pres)
    (hagree : ∀ t : ℝ, T₀ < t → t < T → u t = vel (t - T₀))
    (hagreep : ∀ t : ℝ, T₀ < t → t < T → p t = pres (t - T₀))
    (hpn : PressureNormalizedBefore T p) :
    SolvesFrom ν T₀ L (fun t : ℝ => if t < T then u t else fun x => vel (t - T₀) x)
      (fun t : ℝ => if t < T then p t else fun x => pres (t - T₀) x) ∧
      RegularOnCompactsFrom T₀ L
        (fun t : ℝ => if t < T then u t else fun x => vel (t - T₀) x)
        (fun t : ℝ => if t < T then p t else fun x => pres (t - T₀) x) ∧
        (∀ t : ℝ, T₀ ≤ t → t < T₀ + L →
          (fun t : ℝ => if t < T then p t else fun x => pres (t - T₀) x) t 0 = 0) := by
  obtain ⟨hu, hp, hinc, heq⟩ := hsol.classical
  have hfe := hsol.finite_energy
  obtain ⟨hLpos, hinit, hpsv, hpsp, pinc, peq, pfe, pel, prs, pp0⟩ := hpiece
  set w : VelocityEvolution := fun t => if t < T then u t else fun x => vel (t - T₀) x
    with hwdef
  set q : PressureEvolution := fun t => if t < T then p t else fun x => pres (t - T₀) x
    with hqdef
  -- the paste is the u-side strictly below the cut, unconditionally
  have hw_below : ∀ s : ℝ, s < T → w s = u s := fun s hs => if_pos hs
  have hq_below : ∀ s : ℝ, s < T → q s = p s := fun s hs => if_pos hs
  -- and equals the shifted piece strictly above the strip start: below the cut this IS
  -- the (open) agreement, above it the second branch of the paste
  have hw_above : ∀ s : ℝ, T₀ < s → w s = vel (s - T₀) := by
    intro s hs
    rcases lt_or_ge s T with hsT | hsT
    · exact (hw_below s hsT).trans (hagree s hs hsT)
    · exact if_neg (by linarith : ¬(s < T))
  have hq_above : ∀ s : ℝ, T₀ < s → q s = pres (s - T₀) := by
    intro s hs
    rcases lt_or_ge s T with hsT | hsT
    · exact (hq_below s hsT).trans (hagreep s hs hsT)
    · exact if_neg (by linarith : ¬(s < T))
  -- shifted piece smoothness on the open part of the strip
  have hvs : ContDiffOn ℝ ∞ (fun z : ℝ × Space => vel (z.1 - T₀) z.2)
      (Set.Ioo T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)) :=
    contDiffOn_shift_open (T₀ := T₀) (δ := L)
      (F := fun z : ℝ × Space => vel z.1 z.2) hpsv
  have hps : ContDiffOn ℝ ∞ (fun z : ℝ × Space => pres (z.1 - T₀) z.2)
      (Set.Ioo T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)) :=
    contDiffOn_shift_open (T₀ := T₀) (δ := L)
      (F := fun z : ℝ × Space => pres z.1 z.2) hpsp
  -- time derivative of the strip: the u-side below the cut, the piece-side above the start
  have htd_below : ∀ t : ℝ, t < T → ∀ x : Space,
      timeDerivative w t x = timeDerivative u t x := by
    intro t htT x
    have hev : ∀ᶠ s in 𝓝 t, w s = u s :=
      Filter.eventually_of_mem (Iio_mem_nhds htT) fun s hs => hw_below s hs
    exact timeDerivative_congr_nhds hev x
  have htd_above : ∀ t : ℝ, T₀ < t → t < T₀ + L → ∀ x : Space,
      timeDerivative w t x = timeDerivative vel (t - T₀) x := by
    intro t ht1 ht2 x
    have hev : ∀ᶠ s in 𝓝 t, w s = (fun r : ℝ => vel (r - T₀)) s :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht1) fun s hs => hw_above s hs
    refine ((timeDerivative_congr_nhds hev x).trans ?_)
    exact timeDerivative_shift_open vel L T₀ t x (lt_of_le_of_lt hT₀ ht1) hpsv
      ⟨sub_pos.mpr ht1, sub_lt_iff_lt_add'.mpr ht2⟩
  /- ### Joint smoothness -/
  have hvel_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Space => w z.1 z.2)
      (Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)) :=
    contDiffOn_paste (T₀ := T₀) (T := T) (L := L) (u := u) (vel := vel) (w := w)
      hT₀ hT₀T hu hvs hw_below hw_above
  have hpres_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)
      (Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)) :=
    contDiffOn_paste (T₀ := T₀) (T := T) (L := L) (u := p) (vel := pres) (w := q)
      hT₀ hT₀T hp hps hq_below hq_above
  /- ### Incompressibility -/
  have hinc' : ∀ t : ℝ, T₀ ≤ t → t < T₀ + L → ∀ x : Space, divergence w t x = 0 := by
    intro t ht1 ht2 x
    rcases lt_or_ge t T with htT | htT
    · rw [divergence_slice_congr (hw_below t htT) x]
      exact hinc t (hT₀.trans ht1) htT x
    · have hT₀t : T₀ < t := lt_of_lt_of_le hT₀T htT
      rw [divergence_slice_congr (hw_above t hT₀t) x]
      exact pinc (t - T₀) (sub_nonneg.mpr ht1) (sub_lt_iff_lt_add'.mpr ht2) x
  /- ### The equation on the open slab -/
  have heq' : ∀ t : ℝ, T₀ < t → t < T₀ + L → ∀ x : Space,
      timeDerivative w t x + convection w t x =
        ν • laplacian w t x - pressureGradient q t x := by
    intro t ht1 ht2 x
    rcases lt_or_ge t T with htT | htT
    · have e1 := heq t (hT₀.trans ht1.le) htT x
      rw [show zeroForce t x = (0 : Space) from rfl, add_zero] at e1
      rw [htd_below t htT x, convection_slice_congr (hw_below t htT) x,
        laplacian_slice_congr (hw_below t htT) x,
        pressureGradient_slice_congr (hq_below t htT) x]
      exact e1
    · have hT₀t : T₀ < t := ht1
      have e2 := peq (t - T₀) (sub_pos.mpr hT₀t) (sub_lt_iff_lt_add'.mpr ht2) x
      rw [← htd_above t hT₀t ht2 x, ← convection_slice_congr (hw_above t hT₀t) x,
        ← laplacian_slice_congr (hw_above t hT₀t) x,
        ← pressureGradient_slice_congr (hq_above t hT₀t) x] at e2
      exact e2
  /- ### Finite energy -/
  have hfe' : ∀ t : ℝ, T₀ ≤ t → t < T₀ + L → Integrable (fun x : Space => ‖w t x‖ ^ 2) := by
    intro t ht1 ht2
    rcases lt_or_ge t T with htT | htT
    · have hf : (fun x : Space => ‖w t x‖ ^ 2) = (fun x : Space => ‖u t x‖ ^ 2) := by
        funext x
        exact congrArg (fun y : Space => ‖y‖ ^ 2) (congrFun (hw_below t htT) x)
      rw [hf]
      exact hfe t (hT₀.trans ht1) htT
    · have hT₀t : T₀ < t := lt_of_lt_of_le hT₀T htT
      have hf : (fun x : Space => ‖w t x‖ ^ 2) =
          (fun x : Space => ‖vel (t - T₀) x‖ ^ 2) := by
        funext x
        exact congrArg (fun y : Space => ‖y‖ ^ 2) (congrFun (hw_above t hT₀t) x)
      rw [hf]
      exact pfe (t - T₀) (sub_nonneg.mpr ht1) (sub_lt_iff_lt_add'.mpr ht2)
  /- ### Energy normalized at the strip start -/
  have hel' : ∀ t : ℝ, T₀ ≤ t → t < T₀ + L → kineticEnergy w t ≤ kineticEnergy w T₀ := by
    intro t ht1 ht2
    by_cases h : t = T₀
    · rw [h]
    · have hlt : T₀ < t := lt_of_le_of_ne ht1 (Ne.symm h)
      calc kineticEnergy w t
          = kineticEnergy vel (t - T₀) := kineticEnergy_slice_congr (hw_above t hlt)
        _ ≤ kineticEnergy vel 0 :=
            pel (t - T₀) (sub_nonneg.mpr hlt.le) (sub_lt_iff_lt_add'.mpr ht2)
        _ = kineticEnergy u T₀ := kineticEnergy_slice_congr hinit
        _ = kineticEnergy w T₀ := kineticEnergy_slice_congr ((hw_below T₀ hT₀T).symm)
  /- ### The `R` bounds on the strip -/
  have hRF : RegularOnCompactsFrom T₀ L w q := by
    intro T' hT'
    set m : ℝ := (T₀ + T) / 2 with hm
    have hmT : m < T := by rw [hm]; linarith
    have hT₀m : T₀ < m := by rw [hm]; linarith
    obtain ⟨K₁, hK₁⟩ := hR m hmT
    obtain ⟨K₂, hK₂⟩ := prs (T' - T₀) (sub_lt_iff_lt_add'.mpr hT')
    refine ⟨max K₁ K₂, fun t ht => ?_⟩
    rcases le_or_gt t m with htm | htm
    · have htT : t < T := lt_of_le_of_lt htm hmT
      obtain ⟨a1, a2, a3, a4, a5⟩ := hK₁ t ⟨hT₀.trans ht.1, htm⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hw_below t htT]; exact a1.mono (le_max_left _ _)
      · rw [hq_below t htT]; exact a2.mono (le_max_left _ _)
      · refine (TimeSlice.mono ?_ (le_max_left _ _))
        simp only [TimeSlice, htd_below t htT]
        exact a3
      · rw [hw_below t htT]; exact a4.mono (le_max_left _ _)
      · rw [hq_below t htT]; exact a5.mono (le_max_left _ _)
    · have hT₀t : T₀ < t := lt_trans hT₀m htm
      have htL : t < T₀ + L := lt_of_le_of_lt ht.2 hT'
      obtain ⟨a1, a2, a3, a4, a5⟩ :=
        hK₂ (t - T₀) ⟨sub_pos.mpr hT₀t, sub_le_sub_right ht.2 T₀⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hw_above t hT₀t]; exact a1.mono (le_max_right _ _)
      · rw [hq_above t hT₀t]; exact a2.mono (le_max_right _ _)
      · refine (TimeSlice.mono ?_ (le_max_right _ _))
        simp only [TimeSlice, htd_above t hT₀t htL]
        exact a3
      · rw [hw_above t hT₀t]; exact a4.mono (le_max_right _ _)
      · rw [hq_above t hT₀t]; exact a5.mono (le_max_right _ _)
  /- ### Normalized strip pressure -/
  have hqn : ∀ t : ℝ, T₀ ≤ t → t < T₀ + L → q t 0 = 0 := by
    intro t ht1 ht2
    rcases lt_or_ge t T with htT | htT
    · rw [hq_below t htT]; exact hpn t (hT₀.trans ht1) htT
    · have hT₀t : T₀ < t := lt_of_lt_of_le hT₀T htT
      rw [hq_above t hT₀t]
      exact pp0 (t - T₀) (sub_nonneg.mpr ht1) (sub_lt_iff_lt_add'.mpr ht2)
  exact ⟨⟨hvel_smooth, hpres_smooth, hinc', heq', hfe', hel'⟩, hRF, hqn⟩

/-- **The pressure half of the agreement is a consequence, not a premise.**  Given the
velocity agreement on the open overlap `(T₀, T)`, the two pressures have the same
gradient at every interior time — the two equations share `∂ₜ u`, `(u·∇)u` and `Δu`
once the agreement is transported through `timeDerivative_shift_open` — and both are
normalized at the origin, so the slices are equal (`eq_of_gradient_eq`).  Together with
`strip_of_restart_piece` this reduces hazard (b)'s analytic input to the single field
named in `RestartAgreement`.  Unlike `PressureAgree.pressure_agree`, this needs no
`SolvesFrom` strip and therefore no right-continuity argument at `T₀`: it holds for the
piece itself on the open interval. -/
theorem pressure_agree_of_piece {ν T T₀ L : ℝ} (hT₀ : 0 ≤ T₀) (_hT₀T : T₀ < T)
    (hTL : T ≤ T₀ + L) {u : VelocityEvolution} {p : PressureEvolution}
    {vel : ℝ → VelocityField} {pres : ℝ → PressureField}
    (hsol : SolvesBefore ν T u p) (hpn : PressureNormalizedBefore T p)
    (hpiece : RestartPiece ν L (u T₀) vel pres)
    (hagree : ∀ t : ℝ, T₀ < t → t < T → u t = vel (t - T₀)) :
    ∀ t : ℝ, T₀ < t → t < T → p t = pres (t - T₀) := by
  obtain ⟨-, hp, -, heq⟩ := hsol.classical
  obtain ⟨-, -, hpsv, hpsp, -, peq, -, -, -, pp0⟩ := hpiece
  intro t ht1 ht2
  have hut : u t = vel (t - T₀) := hagree t ht1 ht2
  have hs : t - T₀ ∈ Set.Ioo (0 : ℝ) L :=
    ⟨sub_pos.mpr ht1, lt_of_lt_of_le (sub_lt_sub_right ht2 T₀)
      (sub_le_iff_le_add'.mpr hTL)⟩
  have hev : ∀ᶠ s in 𝓝 t, u s = (fun r : ℝ => vel (r - T₀)) s :=
    Filter.eventually_of_mem (Ioo_mem_nhds ht1 ht2) fun s hs' => hagree s hs'.1 hs'.2
  have hpg : ∀ x : Space, pressureGradient p t x = pressureGradient pres (t - T₀) x := by
    intro x
    have htd : timeDerivative u t x = timeDerivative vel (t - T₀) x :=
      (timeDerivative_congr_nhds hev x).trans
        (timeDerivative_shift_open vel L T₀ t x (lt_of_le_of_lt hT₀ ht1) hpsv hs)
    have hc : convection u t x = convection vel (t - T₀) x := convection_slice_congr hut x
    have hl : laplacian u t x = laplacian vel (t - T₀) x := laplacian_slice_congr hut x
    have e1 := heq t (hT₀.trans ht1.le) ht2 x
    have e2 := peq (t - T₀) hs.1 hs.2 x
    rw [show zeroForce t x = (0 : Space) from rfl, add_zero] at e1
    have this : ν • laplacian u t x - pressureGradient p t x =
        ν • laplacian vel (t - T₀) x - pressureGradient pres (t - T₀) x := by
      rw [← e1, ← e2, htd, hc]
    rw [hl] at this
    exact sub_right_injective this
  exact eq_of_gradient_eq (differentiable_slice hp ⟨hT₀.trans ht1.le, ht2⟩)
    (differentiable_slice hpsp hs)
    (fun x i => congrFun (hpg x) i)
    ((hpn t (hT₀.trans ht1.le) ht2).trans (pp0 (t - T₀) hs.1.le hs.2).symm)

/-! ## The three named premises of item 6 -/

/-- **Hazard (a), named.**  Local existence for `H³` slice data, with a lifespan
`L = L(ν, K)` depending only on the viscosity and the datum bound — the
datum-uniformity that makes the restart horizon-independent.  The return type is
`RestartPiece`, so a discharge of this premise must also produce the pressure bounds
(hazard (c)) and must be smooth on the open slab (interior parabolic smoothing, the
analytic half of hazard (b)).  NOT proved here: no carrier in the repository feeds an
`H³` slice into a fixed point (see the module header's moment count). -/
def H3SliceLocalExistence : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ, ∃ L : ℝ, 0 < L ∧
    ∀ v : VelocityField, H3SliceDatum K v →
      ∃ vel : ℝ → VelocityField, ∃ pres : ℝ → PressureField, RestartPiece ν L v vel pres

/-- **Hazard (b)'s single remaining analytic field, named.**  A restart piece driven by
the slice `u T₀` of a solution in `R` is the continuation of that solution on the open
overlap `(T₀, T)`.  This is the interior-start twin of
`RegularUniqueness.uniqueness_R`, and it is exactly the transfer the existing uniqueness
theorems cannot perform: their admissible class `SolClass` demands joint smoothness at
the initial time (`SmoothVelocityBefore`), which an `H³` restart piece does not have —
that is precisely what `RestartPiece.smooth_vel` weakens.  The pressure half is NOT part
of this premise: `pressure_agree_of_piece` derives it, and the value at `T₀` itself is
already fixed by `RestartPiece.init`. -/
def RestartAgreement : Prop :=
  ∀ ν T T₀ L : ℝ, 0 < ν → 0 ≤ T₀ → T₀ < T → T ≤ T₀ + L →
    ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      ∀ vel : ℝ → VelocityField, ∀ pres : ℝ → PressureField,
        SolvesBefore ν T u p → RegularOnCompacts T u p →
          RestartPiece ν L (u T₀) vel pres → PressureNormalizedBefore T p →
          ∀ t : ℝ, T₀ < t → t < T → u t = vel (t - T₀)

/-- **The physical-space twin of `WienerRestartLeaf.WienerH3Apriori`, named.**  The
critical quantity `N` bounds the `H³` slice datum of every `R`-solution under budget
`M`, uniformly along the life interval.  `h3SliceDatum_of_R` shows the shape of the
conclusion is the right one; what is not available in the repository is the `N`-uniform
`K` on the whole of `[0, T)`, as opposed to the per-compact-subinterval `K` that `R`
alone gives. -/
def H3SliceControl (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ M : ℝ≥0, ∃ K : ℝ, ∀ T : ℝ, 0 < T →
    ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      SolvesBefore ν T u p → RegularOnCompacts T u p → N T u ≤ (M : ℝ≥0∞) →
      ∀ t : ℝ, 0 ≤ t → t < T → H3SliceDatum K (u t)

/-! ## The consumer -/

/-- **Item 6 discharges the `R`-restart leaf.**  From the three named premises,
`DatumHorizonIndependentRestartR N`: the a priori slice control gives a bound `K`
uniform along the life interval, the datum-uniform lifespan gives `L = L(ν, K)`, the
restart step is `h := L / 2` and `T₀ := max (T - h) 0`, so the strip length
`T - T₀ + h ≤ 2h = L` fits inside the piece; the velocity agreement comes from
`RestartAgreement`, the pressure agreement from `pressure_agree_of_piece`, and the strip
itself — with its `SolvesFrom` bundle, its `R` bounds and its normalized pressure — from
`strip_of_restart_piece`.  The arithmetic of `h`, `T₀` and the strip length mirrors
`WienerRestartLeaf.datumRestartR_of_wienerH3Apriori`, with the Wiener constant replaced
by the `H³` lifespan; the leaf's two agreement fields are discharged by the paste's own
`if_pos`, exactly as there. -/
theorem datumRestartR_of_h3Slice (N : CriticalQuantity) (hExist : H3SliceLocalExistence)
    (hAgr : RestartAgreement) (hCtl : H3SliceControl N) :
    DatumHorizonIndependentRestartR N := by
  intro ν hν u₀ hdiv M
  obtain ⟨K, hK⟩ := hCtl ν hν M
  obtain ⟨L, hL, hex⟩ := hExist ν hν K
  set h : ℝ := L / 2 with hhdef
  have hh : 0 < h := by linarith
  have hh2 : h + h = L := by rw [hhdef]; ring
  refine ⟨h, hh, fun T hT u p hu0 hu hRu hpn hN => ?_⟩
  set T₀ : ℝ := max (T - h) 0 with hT₀def
  have hT₀0 : 0 ≤ T₀ := le_max_right _ _
  have hT₀T : T₀ < T := max_lt (by linarith) hT
  have hTh₀ : T - h ≤ T₀ := le_max_left _ _
  obtain ⟨vel, pres, hpiece⟩ := hex (u T₀) (hK T hT u p hu hRu hN T₀ hT₀0 hT₀T)
  set L' : ℝ := T - T₀ + h with hL'def
  have hL'0 : 0 < L' := by rw [hL'def]; linarith
  have hL'L : L' ≤ L := by linarith
  have hpiece' : RestartPiece ν L' (u T₀) vel pres := hpiece.mono hL'L hL'0
  have hsum : T₀ + L' = T + h := by rw [hL'def]; ring
  have hTL' : T ≤ T₀ + L' := by linarith
  have hagreeV : ∀ t : ℝ, T₀ < t → t < T → u t = vel (t - T₀) :=
    hAgr ν T T₀ L' hν hT₀0 hT₀T hTL' u p vel pres hu hRu hpiece' hpn
  have hagreeP : ∀ t : ℝ, T₀ < t → t < T → p t = pres (t - T₀) :=
    pressure_agree_of_piece hT₀0 hT₀T hTL' hu hpn hpiece' hagreeV
  obtain ⟨hSF, hRF, hqn⟩ :=
    strip_of_restart_piece hν hT₀0 hT₀T hTL' hu hRu hpiece' hagreeV hagreeP hpn
  refine ⟨T₀, hT₀0, hT₀T, (fun t : ℝ => if t < T then u t else fun x => vel (t - T₀) x),
    (fun t : ℝ => if t < T then p t else fun x => pres (t - T₀) x),
    fun t _ ht => (if_pos ht).symm, fun t _ ht => (if_pos ht).symm, hSF, hRF, ?_⟩
  intro t ht1 ht2
  rw [← hsum] at ht2
  exact hqn t ht1 ht2

/-- **The crown from item 6's three named premises and the `R` a priori leaf.**  Local
existence lands in `R` through the `H³` restart-slice route, so the reduction of
Fefferman's statement A to the two `R`-leaves is complete modulo exactly
`H3SliceLocalExistence`, `RestartAgreement` and `H3SliceControl`. -/
theorem crown_of_h3Slice (N : CriticalQuantity) (hExist : H3SliceLocalExistence)
    (hAgr : RestartAgreement) (hCtl : H3SliceControl N)
    (hapriori : APrioriIn RegularOnCompacts N) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_R_restart_apriori N
    (datumRestartR_of_h3Slice N hExist hAgr hCtl) hapriori

end Navier.Analysis.H3RestartSlice

set_option pp.fullNames true in
#check @Navier.Analysis.H3RestartSlice.H3SliceLocalExistence
set_option pp.fullNames true in
#check @Navier.Analysis.H3RestartSlice.RestartAgreement
set_option pp.fullNames true in
#check @Navier.Analysis.H3RestartSlice.H3SliceControl
set_option pp.fullNames true in
#print axioms Navier.Analysis.H3RestartSlice.h3SliceDatum_zero
set_option pp.fullNames true in
#print axioms Navier.Analysis.H3RestartSlice.h3SliceDatum_of_R
set_option pp.fullNames true in
#print axioms Navier.Analysis.H3RestartSlice.RestartPiece.of_solvesBefore
set_option pp.fullNames true in
#print axioms Navier.Analysis.H3RestartSlice.timeDerivative_shift_open
set_option pp.fullNames true in
#print axioms Navier.Analysis.H3RestartSlice.contDiffOn_paste
set_option pp.fullNames true in
#print axioms Navier.Analysis.H3RestartSlice.strip_of_restart_piece
set_option pp.fullNames true in
#print axioms Navier.Analysis.H3RestartSlice.pressure_agree_of_piece
set_option pp.fullNames true in
#print axioms Navier.Analysis.H3RestartSlice.datumRestartR_of_h3Slice
set_option pp.fullNames true in
#print axioms Navier.Analysis.H3RestartSlice.crown_of_h3Slice
