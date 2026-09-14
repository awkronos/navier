/-
Original work, lane L6b2, 2026-09-14.
-/
import Navier.Analysis.BKMVorticityIntegralDivergence
import Navier.Analysis.BiotSavartVelocityRecovery
import Navier.Analysis.BiotSavartNearBounds
import Navier.Analysis.GronwallAffine

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff BigOperators Matrix Pointwise
open Navier Navier.Analysis.Vorticity Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.BKMForcedBreakdownNecessity
open Navier.Analysis.BKMVorticityIntegralDivergence
open Navier.Construction.ProblemStatement
open Navier.Construction.R3CompactCandidate
open Navier.Analysis.BiotSavartVelocityRecovery
open Navier.Analysis.GronwallAffine

/-!
# The Grönwall control pair for the selected profile: exact reduction,
# carrier facts, and the Biot--Savart form of the named residual

`Navier.Analysis.BKMVorticityIntegralDivergence` consumes, for the selected
profile `u` of the constructed field, an exactly-named Grönwall control pair:
`∃ Y Y',` continuous on `Ico 0 1`, differentiable on `Ioo 0 1` with
derivative `Y'`, strictly positive, satisfying `Y' t ≤ V u t * Y t`, and
dominating the velocity `‖uncurry u t x‖ ≤ Y t`. The pair is the named
residual. This module does three things with it.

* **Exact reduction.** `gronwall_pair_iff_velocity_bound`: the pair exists if
  and only if the single pointwise estimate `GronwallVelocityBound u` holds:

      ∃ C > 0, ∀ t ∈ Ico 0 1, ∀ x, ‖uncurry u t x‖ ≤ C * exp(∫₀ᵗ V u).

  The forward direction is the estate's own affine Grönwall step
  (`GronwallAffine.gronwall_affine_apriori` with forcing zero); the reverse
  direction reads the exponential back off the integral of `V`.
* **Carrier fact (routing note 1, refuted).** `no_uniform_sup_bound`: no
  selected-profile competitor has a spatially and temporally uniform bound on
  `[0, 1)`, so no constant pair can exist. The blowup is genuinely a sup-norm
  velocity blowup, up to the attained `√3` carrier comparison.
* **Biot--Savart reduction.** `velocity_le_V`: for every selected-profile
  competitor there is `C > 0` with `‖uncurry u t x‖ ≤ C * V u t` on
  `[0, 1)` — the whole-space recovery integral over the compactly supported
  smooth slice, truncated to a ball by the support of the slice itself.
  Combined with the scalar *vorticity-rate estimate* `VorticityRateBound u`
  this gives `GronwallVelocityBound u`, hence the pair:
  `gronwall_pair_of_rate_bound`.

WHAT THIS MODULE DOES NOT PROVE: the vorticity-rate estimate
`∃ C₂ ≥ 0, ∀ t ∈ Ico 0 1, V u t ≤ C₂ * exp(∫₀ᵗ V u)` for the selected
profile. That is the exact residual named here. By
`gronwall_pair_iff_velocity_bound` and `velocity_le_V` it is, over the
constructed-field machinery, a strictly *scalar* estimate on the peak-vorticity
profile `V`. Everything here is a fact about the constructed *forced* profile
(a `R3CompactCandidate.Properties` competitor), not about unforced
Navier--Stokes.
-/

namespace Navier.Analysis.BKMProfileGronwallPair

private abbrev ESpace := Navier.Construction.ProblemStatement.Space
private abbrev EVelocityField := Navier.Construction.ProblemStatement.VelocityField

private def toPiCLM : ESpace →L[ℝ] Navier.Space where
  toFun := fun y => (y : Navier.Space)
  map_add' := by intro a b; rfl
  map_smul' := by intro c x; rfl
  cont := by fun_prop

private def fromPiCLM : Navier.Space →L[ℝ] ESpace where
  toFun := fun x => WithLp.toLp 2 x
  map_add' := by intro a b; rfl
  map_smul' := by intro c x; rfl
  cont := by fun_prop

private theorem toPiCLM_apply (y : ESpace) : toPiCLM y = (y : Navier.Space) := rfl

private theorem toPiCLM_fromPiCLM (x : Navier.Space) : toPiCLM (fromPiCLM x) = x := rfl

/-! ## 1. The pair, the single estimate, and their equivalence. -/

/-- The exact residual proposition of
`Navier.Analysis.BKMVorticityIntegralDivergence`: a Grönwall control pair for
`u`, formulated verbatim as the five-conjunct bundle the downstream
divergence theorems consume. -/
def GronwallPair (u : EVelocityField) : Prop :=
  ∃ (Y Y' : ℝ → ℝ), ContinuousOn Y (Ico (0 : ℝ) 1) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Y (Y' t) t) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, 0 < Y t) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, Y' t ≤ V u t * Y t) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Navier.Space, ‖uncurry u t x‖ ≤ Y t)

/-- The single pointwise Grönwall estimate `(†)`: the selected profile's
velocity is dominated by the exponential of its own vorticity integral, up to
one multiplicative constant. -/
def GronwallVelocityBound (u : EVelocityField) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Navier.Space,
    ‖uncurry u t x‖ ≤ C * Real.exp (∫ s in (0 : ℝ)..t, V u s)

/-- The scalar vorticity-rate estimate: the peak vorticity profile is bounded
by the exponential of its own running integral, up to one multiplicative
constant. This is the exact residual of the decomposition. -/
def VorticityRateBound (u : EVelocityField) : Prop :=
  ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ t ∈ Ico (0 : ℝ) 1,
    V u t ≤ C₂ * Real.exp (∫ s in (0 : ℝ)..t, V u s)

/-- The running integral of `V` is continuous on `[0, 1)` whenever `V` is:
the moving bound of the interval integral is continuous on each compact
window, and the windows are cofinal in the neighbourhood filter of every
point of `Ico 0 1`. -/
private theorem integral_V_continuousOn {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, V u s) (Ico (0 : ℝ) 1) := by
  intro t₀ ht₀
  set b : ℝ := (t₀ + 1) / 2 with hb
  have htb : t₀ < b := by rw [hb]; linarith [ht₀.2]
  have hb₁ : b < 1 := by rw [hb]; linarith [ht₀.2]
  have hb₀ : (0 : ℝ) ≤ b := by rw [hb]; linarith [ht₀.1]
  have hV : ContinuousOn (V u) (Icc (0 : ℝ) b) :=
    (V_continuousOn hu hK hsupp).mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hb₁⟩
  have hint : IntegrableOn (V u) (Icc (0 : ℝ) b) volume :=
    hV.integrableOn_compact isCompact_Icc
  have hpc : ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, V u s) (Icc (0 : ℝ) b) := by
    have hprim := intervalIntegral.continuousOn_primitive_interval
      (a := (0 : ℝ)) (b := b) (f := V u) (μ := volume)
      (by rw [Set.uIcc_of_le hb₀]; exact hint)
    rwa [Set.uIcc_of_le hb₀] at hprim
  show Tendsto (fun x => ∫ s in (0 : ℝ)..x, V u s) (𝓝[Ico (0 : ℝ) 1] t₀) (𝓝 _)
  refine Tendsto.mono_left (hpc.continuousWithinAt ⟨ht₀.1, le_of_lt htb⟩) ?_
  rw [nhdsWithin, nhdsWithin]
  refine le_inf_iff.mpr ⟨inf_le_left, le_principal_iff.mpr (mem_nhdsWithin.mpr
    ⟨Iio b, isOpen_Iio, htb, fun z hz => ⟨hz.2.1, le_of_lt hz.1⟩⟩)⟩

/-- The fundamental theorem for the running integral of `V` at every interior
time: the derivative is `V u t`. -/
private theorem integral_V_hasDerivAt {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, V u s) (V u t) t := by
  have hV : ContinuousOn (V u) (Icc (0 : ℝ) t) :=
    (V_continuousOn hu hK hsupp).mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hint : IntervalIntegrable (V u) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht.1.le]
    exact hV
  have hVoo : ContinuousOn (V u) (Ioo (0 : ℝ) 1) :=
    (V_continuousOn hu hK hsupp).mono Set.Ioo_subset_Ico_self
  have hnhd : Ioo (0 : ℝ) 1 ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have hat : ContinuousAt (V u) t := hVoo.continuousAt hnhd
  have hsmaf : StronglyMeasurableAtFilter (V u) (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hVoo t ht
  exact intervalIntegral.integral_hasDerivAt_right hint hsmaf hat

/-- **Pair `(†)` direction one.** A Grönwall control pair for `u` yields the
single velocity estimate. The affine Grönwall step at zero forcing gives
`Y t ≤ Y 0 * exp(∫₀ᵗ V)` on each window `[0, t]`, and the pair's own
domination field transfers it to the velocity. -/
theorem velocity_gronwall_bound_of_pair {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {Y Y' : ℝ → ℝ}
    (hYcont : ContinuousOn Y (Ico (0 : ℝ) 1))
    (hYder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Y (Y' t) t)
    (hYpos : ∀ t ∈ Ico (0 : ℝ) 1, 0 < Y t)
    (hYgron : ∀ t ∈ Ioo (0 : ℝ) 1, Y' t ≤ V u t * Y t)
    (hYdom : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Navier.Space, ‖uncurry u t x‖ ≤ Y t) :
    GronwallVelocityBound u := by
  refine ⟨Y 0, hYpos 0 ⟨le_refl 0, by linarith⟩, fun t ht x => ?_⟩
  refine (hYdom t ht x).trans ?_
  have hT : (0 : ℝ) ≤ t := ht.1
  have h := gronwall_affine_apriori (a := V u) (b := fun _ => 0) (T := t) hT
    ((V_continuousOn hu hK hsupp).mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩)
    continuousOn_const
    (fun s hs => V_nonneg hu hK hsupp ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩)
    (fun s _ => le_refl 0)
    (hYcont.mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩)
    (fun s hs => hYder s ⟨hs.1, hs.2.trans ht.2⟩)
    (fun s hs => (hYgron s ⟨hs.1, hs.2.trans ht.2⟩).trans_eq ((add_zero _).symm))
    t ⟨hT, le_refl t⟩
  rw [intervalIntegral.integral_const] at h
  simpa using h

/-- **Pair `(†)` direction two.** The single velocity estimate constructs the
Grönwall control pair: `Y := C · exp(∫₀ᵗ V)` is continuous and differentiable
by the fundamental theorem, strictly positive, satisfies the differential
inequality with equality (`Y' = V · Y`), and dominates the velocity by the
estimate itself. -/
theorem velocity_gronwall_pair_of_bound {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    (hb : GronwallVelocityBound u) : GronwallPair u := by
  obtain ⟨C, hC, hle⟩ := hb
  set Y : ℝ → ℝ := fun t => C * Real.exp (∫ s in (0 : ℝ)..t, V u s) with hY
  refine ⟨Y, fun t => V u t * Y t, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((integral_V_continuousOn hu hK hsupp).rexp)).const_mul C
  · intro t ht
    have hd : HasDerivAt Y (C * (Real.exp (∫ s in (0 : ℝ)..t, V u s) * V u t)) t := by
      have hexp := ((integral_V_hasDerivAt hu hK hsupp ht).exp).const_mul C
      convert hexp using 1
    have he : C * (Real.exp (∫ s in (0 : ℝ)..t, V u s) * V u t) = V u t * Y t := by
      show C * (Real.exp (∫ s in (0 : ℝ)..t, V u s) * V u t) =
        V u t * (C * Real.exp (∫ s in (0 : ℝ)..t, V u s))
      ring
    show HasDerivAt Y (V u t * Y t) t
    rw [← he]
    exact hd
  · intro t ht
    rw [hY]
    exact mul_pos hC (Real.exp_pos _)
  · intro t ht
    exact le_refl _
  · intro t ht x
    exact hle t ht x

/-- **The exact reduction.** For the constructed field's machinery the named
residual — the Grönwall control pair — is equivalent to the single pointwise
estimate `(†)`. -/
theorem gronwall_pair_iff_velocity_bound {u p f : _} (h : Properties u p f) :
    GronwallPair u ↔ GronwallVelocityBound u := by
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  exact ⟨fun hp => by
      obtain ⟨Y, Y', hYcont, hYder, hYpos, hYgron, hYdom⟩ := hp
      exact velocity_gronwall_bound_of_pair h.velocity_smooth hK hsupp
        hYcont hYder hYpos hYgron hYdom,
    fun hb => velocity_gronwall_pair_of_bound h.velocity_smooth hK hsupp hb⟩

/-! ## 2. Routing note 1: no uniform sup bound, no constant pair. -/

private theorem norm_Euclidean_cast (z : ESpace) :
    ‖z‖ ≤ Real.sqrt 3 * ‖(z : Navier.Space)‖ := by
  have h : officialEuclideanNorm (z : Navier.Space) = ‖z‖ := by
    simp [officialEuclideanNorm, officialEuclideanPoint, EuclideanSpace.norm_eq]
  rw [← h]
  exact officialEuclideanNorm_le (z : Navier.Space)

/-- **The blowup is sup-norm.** No selected-profile competitor admits a
uniform bound on the velocity over `[0, 1) × ESpace` in the Euclidean carrier,
nor over `[0, 1) × Navier.Space` in the uncurried carrier. In particular the
Grönwall pair cannot be taken constant: a constant pair would dominate the
velocity uniformly, contradicting `speed_unbounded`. This is
`unbounded_speed_excludes_uniform_bound` plus the attained `√3` carrier
comparison. -/
theorem no_uniform_sup_bound_Euclidean {u p f : _} (h : Properties u p f) :
    ¬ ∃ C : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : ESpace, ‖u (t, x)‖ ≤ C :=
  unbounded_speed_excludes_uniform_bound h.speed_unbounded

/-- The uncurried form of `no_uniform_sup_bound_Euclidean`: the negation of
the domination field of a *constant* Grönwall pair. -/
theorem no_uniform_sup_bound {u p f : _} (h : Properties u p f) :
    ¬ ∃ C : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Navier.Space, ‖uncurry u t x‖ ≤ C := by
  rintro ⟨C, hC⟩
  refine no_uniform_sup_bound_Euclidean h ⟨Real.sqrt 3 * C, fun t ht y => ?_⟩
  have hcast : uncurry u t (y : Navier.Space) = (u (t, y) : Navier.Space) := by
    simp [uncurry]
  calc ‖u (t, y)‖ ≤ Real.sqrt 3 * ‖(u (t, y) : Navier.Space)‖ :=
      norm_Euclidean_cast (u (t, y))
    _ = Real.sqrt 3 * ‖uncurry u t (y : Navier.Space)‖ := by rw [hcast]
    _ ≤ Real.sqrt 3 * C := mul_le_mul_of_nonneg_left (hC t ht _) (Real.sqrt_nonneg 3)

/-! ## 3. The Biot--Savart comparison `‖uncurry u t x‖ ≤ C · V u t`. -/

/-- The `L^∞`-carrier cross-product estimate `‖a ⨯₃ b‖ ≤ 2 ‖a‖ ‖b‖`. -/
private theorem norm_le_two_norm_mul_norm_cross (a b : Navier.Space) :
    ‖a ⨯₃ b‖ ≤ 2 * ‖a‖ * ‖b‖ := by
  have hpq : ∀ j k : Fin 3, ‖a j * b k‖ ≤ ‖a‖ * ‖b‖ := fun j k =>
    (norm_mul _ _).le.trans
      (mul_le_mul (norm_le_pi_norm a j) (norm_le_pi_norm b k)
        (norm_nonneg _) (norm_nonneg _))
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  fin_cases i
  · show ‖a 1 * b 2 - a 2 * b 1‖ ≤ 2 * ‖a‖ * ‖b‖
    exact (norm_sub_le _ _).trans (by linarith [hpq 1 2, hpq 2 1])
  · show ‖a 2 * b 0 - a 0 * b 2‖ ≤ 2 * ‖a‖ * ‖b‖
    exact (norm_sub_le _ _).trans (by linarith [hpq 2 0, hpq 0 2])
  · show ‖a 0 * b 1 - a 1 * b 0‖ ≤ 2 * ‖a‖ * ‖b‖
    exact (norm_sub_le _ _).trans (by linarith [hpq 0 1, hpq 1 0])

private theorem norm_bsVectorKernel (z : Navier.Space) :
    ‖bsVectorKernel z‖ = bsKernelScalar z * ‖z‖ := by
  rw [bsVectorKernel, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (bsKernelScalar_nonneg z)]

private theorem hasCompactSupport_uncurry_slice {u : EVelocityField}
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    HasCompactSupport (uncurry u t) :=
  HasCompactSupport.intro (hK.image toPiCLM.continuous)
    fun x hx => by
      have hxK : ⇑fromPiCLM x ∉ K := by
        intro hK'
        exact hx ⟨_, hK', rfl⟩
      exact congrArg (fun v : ESpace => (v : Navier.Space)) (hsupp t ht _ hxK)

/-- The compactly supported smooth time-slice of the selected profile, as a
Schwartz velocity. -/
private def sliceSchwartz {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : SchwartzVelocity :=
  (hasCompactSupport_uncurry_slice hK hsupp ht).toSchwartzMap
    (uncurry_slice_contDiff hu ht)

private theorem sliceSchwartz_coe {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ⇑(sliceSchwartz hu hK hsupp ht) = uncurry u t := rfl

private theorem sliceSchwartz_divFree {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : ESpace, spatialDivergence u t x = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    DivergenceFreeInitial (sliceSchwartz hu hK hsupp ht) := by
  intro x
  show staticDivergence (uncurry u t) x = 0
  rw [staticDivergence_uncurry_slice hu ht x]
  exact hdiv t ht _

/-- The static curl of a `C^∞` field is continuous. -/
private theorem continuous_staticCurl {w : Navier.Space → Navier.Space}
    (hw : ContDiff ℝ ∞ w) : Continuous fun y : Navier.Space => staticCurl w y := by
  have hkey : (fun y : Navier.Space => staticCurl w y) =
      fun y => ∑ i : Fin 3, basisVector i ⨯₃ fderiv ℝ w y (basisVector i) := rfl
  rw [hkey]
  refine continuous_finsetSum (f := fun i : Fin 3 => fun y =>
      basisVector i ⨯₃ fderiv ℝ w y (basisVector i)) Finset.univ fun i _ => ?_
  have hD : Continuous (fun y : Navier.Space => fderiv ℝ w y (basisVector i)) :=
    (hw.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hcross : Continuous (fun v : Navier.Space => basisVector i ⨯₃ v) :=
    (LinearMap.toContinuousLinearMap (crossProduct (basisVector i))).continuous
  exact hcross.comp hD

/-- The curl-cross-kernel recovery integrand is measurable. -/
private theorem measurable_curl_cross_kernel {w : Navier.Space → Navier.Space}
    (hw : ContDiff ℝ ∞ w) (x : Navier.Space) :
    Measurable (fun z : Navier.Space => staticCurl w (x - z) ⨯₃ bsVectorKernel z) := by
  have hsubc : Continuous (fun z : Navier.Space => x - z) :=
    continuous_const.sub continuous_id
  have hcu : Measurable (fun z : Navier.Space => staticCurl w (x - z)) :=
    (continuous_staticCurl hw).measurable.comp hsubc.measurable
  have hker : Measurable bsVectorKernel := by
    refine measurable_pi_iff.mpr fun j => ?_
    have key : (fun z : Navier.Space => bsVectorKernel z j) =
        fun z : Navier.Space => bsKernelScalar z * z j := by
      funext z
      rw [bsVectorKernel, Pi.smul_apply, smul_eq_mul]
    rw [key]
    exact measurable_bsKernelScalar.mul (continuous_apply j).measurable
  have hcu_j := measurable_pi_iff.mp hcu
  have hker_j := measurable_pi_iff.mp hker
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · show Measurable (fun z : Navier.Space => staticCurl w (x - z) 1 * bsVectorKernel z 2 -
        staticCurl w (x - z) 2 * bsVectorKernel z 1)
    exact ((hcu_j 1).mul (hker_j 2)).sub ((hcu_j 2).mul (hker_j 1))
  · show Measurable (fun z : Navier.Space => staticCurl w (x - z) 2 * bsVectorKernel z 0 -
        staticCurl w (x - z) 0 * bsVectorKernel z 2)
    exact ((hcu_j 2).mul (hker_j 0)).sub ((hcu_j 0).mul (hker_j 2))
  · show Measurable (fun z : Navier.Space => staticCurl w (x - z) 0 * bsVectorKernel z 1 -
        staticCurl w (x - z) 1 * bsVectorKernel z 0)
    exact ((hcu_j 0).mul (hker_j 1)).sub ((hcu_j 1).mul (hker_j 0))

/-- The pointwise comparison `‖a ⨯₃ b‖ ≤ 2 ‖a‖ ‖b‖` plus the `V` profile
bound the recovery integrand: for `t ∈ Ico 0 1` and every `z`,
`‖staticCurl (uncurry u t) (x - z) ⨯₃ bsVectorKernel z‖ ≤
2 * V u t * (‖z‖ * bsKernelScalar z)`. -/
private theorem integrand_le {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x z : Navier.Space) :
    ‖staticCurl (uncurry u t) (x - z) ⨯₃ bsVectorKernel z‖ ≤
      2 * V u t * (‖z‖ * bsKernelScalar z) := by
  have hcurl : ‖staticCurl (uncurry u t) (x - z)‖ ≤ V u t := by
    refine (norm_le_officialEuclideanNorm _).trans
      (vort_le_V hu hK hsupp ht (x - z))
  calc ‖staticCurl (uncurry u t) (x - z) ⨯₃ bsVectorKernel z‖
      ≤ 2 * ‖staticCurl (uncurry u t) (x - z)‖ * ‖bsVectorKernel z‖ :=
        norm_le_two_norm_mul_norm_cross _ _
    _ = 2 * ‖staticCurl (uncurry u t) (x - z)‖ * (bsKernelScalar z * ‖z‖) := by
        rw [norm_bsVectorKernel]
    _ ≤ 2 * V u t * (bsKernelScalar z * ‖z‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcurl zero_le_two)
          (mul_nonneg (bsKernelScalar_nonneg z) (norm_nonneg _))
    _ = 2 * V u t * (‖z‖ * bsKernelScalar z) := by ring

/-- **Ball truncation of the recovery integral.** For `x` in the uncurried
compact support of the slice, bounded by `bound`, the recovery integrand
vanishes outside `Metric.ball 0 (2 * bound + 1)`; truncating there and applying
the `L¹`-majorant `2 * V u t * (‖z‖ * bsKernelScalar z)` gives a linear-in-`V`
pointwise velocity bound. -/
private theorem velocity_ball_le {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {K : Set ESpace} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, ∀ y, y ∉ K → u (t, y) = 0)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : ESpace, spatialDivergence u t x = 0)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x : Navier.Space) (bound : ℝ)
    (hbnd : ∀ y ∈ ⇑toPiCLM '' K, ‖y‖ ≤ bound)
    (hx : x ∈ ⇑toPiCLM '' K) :
    ‖uncurry u t x‖ ≤
      2 * V u t * (2 * (volume (Metric.ball (0 : Navier.Space) 1)).toReal / Real.pi *
        (2 * bound + 1)) := by
  classical
  set ρ : ℝ := 2 * bound + 1 with hρdef
  have hx0 : ‖(x : Navier.Space)‖ ≤ bound := hbnd x hx
  have hρ : (0 : ℝ) < ρ := by rw [hρdef]; linarith [norm_nonneg x]
  -- off the ball of radius `ρ` the curl vanishes: `x - z` leaves the support.
  have hzero : ∀ z : Navier.Space, z ∉ Metric.ball (0 : Navier.Space) ρ →
      staticCurl (uncurry u t) (x - z) = 0 := by
    intro z hz
    show vorticity (uncurry u) t (x - z) = 0
    refine vort_zero_outside_support hK hsupp ht ?_
    intro hy
    have htri : ‖z‖ ≤ ‖x - z‖ + ‖x‖ :=
      calc ‖z‖ = ‖(z - x) + x‖ := by congr 1; abel
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ = ‖x - z‖ + ‖x‖ := by rw [norm_sub_rev]
    have hgt : ρ ≤ ‖z‖ := by
      rw [Metric.mem_ball] at hz
      rw [dist_eq_norm, sub_zero] at hz
      exact not_lt.mp hz
    linarith [hbnd (x - z) hy, htri, hx0, hgt, hρdef]
  have hrec : uncurry u t x = ∫ z : Navier.Space,
      staticCurl (uncurry u t) (x - z) ⨯₃ bsVectorKernel z := by
    have h := integral_staticCurl_cross_bsVectorKernel
      (sliceSchwartz hu hK hsupp ht) (sliceSchwartz_divFree hu hK hsupp hdiv ht) x
    rw [sliceSchwartz_coe hu hK hsupp ht] at h
    exact h.symm
  have hm : Measurable (fun z : Navier.Space =>
      staticCurl (uncurry u t) (x - z) ⨯₃ bsVectorKernel z) :=
    measurable_curl_cross_kernel (uncurry_slice_contDiff hu ht) x
  set G : Navier.Space → ℝ :=
    fun z => ‖staticCurl (uncurry u t) (x - z) ⨯₃ bsVectorKernel z‖ with hGdef
  have hGmeas : Measurable G := hm.norm
  have hstep2 : (∫⁻ z : Navier.Space, ENNReal.ofReal (G z) ∂volume) =
      ∫⁻ z in Metric.ball (0 : Navier.Space) ρ, ENNReal.ofReal (G z) ∂volume := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr_ae (ae_of_all volume fun z => ?_)
    rw [hGdef]
    by_cases hzb : z ∈ Metric.ball (0 : Navier.Space) ρ
    · simp only [Set.indicator_apply, ite_eq_left hzb]
    · simp only [Set.indicator_apply, ite_eq_right hzb]
      rw [hzero z hzb]
      simp
  have hstep3 : (∫⁻ z in Metric.ball (0 : Navier.Space) ρ, ENNReal.ofReal (G z) ∂volume) ≤
      ENNReal.ofReal (2 * V u t) *
        (ENNReal.ofReal (2 * ρ / Real.pi) * volume (Metric.ball (0 : Navier.Space) 1)) := by
    have hmono : (∫⁻ z in Metric.ball (0 : Navier.Space) ρ, ENNReal.ofReal (G z) ∂volume) ≤
        (∫⁻ z in Metric.ball (0 : Navier.Space) ρ,
          ENNReal.ofReal (2 * V u t * (‖z‖ * bsKernelScalar z)) ∂volume) := by
      refine MeasureTheory.lintegral_mono fun z => ?_
      rw [hGdef]
      exact ENNReal.ofReal_le_ofReal (integrand_le hu hK hsupp ht x z)
    refine hmono.trans ?_
    simp_rw [ENNReal.ofReal_mul (mul_nonneg zero_le_two (V_nonneg hu hK hsupp ht))]
    have hfpm : Measurable fun a : Navier.Space =>
        ENNReal.ofReal (‖a‖ * bsKernelScalar a) :=
      ENNReal.measurable_ofReal.comp
        (continuous_norm.measurable.mul measurable_bsKernelScalar)
    rw [MeasureTheory.lintegral_const_mul (r := ENNReal.ofReal (2 * V u t)) (hf := hfpm)]
    have hN := lintegral_norm_mul_bsKernelScalar_ball_le hρ
    gcongr
  have hMne : (ENNReal.ofReal (2 * V u t) *
      (ENNReal.ofReal (2 * ρ / Real.pi) * volume (Metric.ball (0 : Navier.Space) 1))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ball_lt_top (μ := volume) (x := (0 : Navier.Space)) (r := 1)).ne)
  have hLne : (∫⁻ z in Metric.ball (0 : Navier.Space) ρ, ENNReal.ofReal (G z) ∂volume) ≠ ⊤ :=
    ne_top_of_le_ne_top hMne hstep3
  calc ‖uncurry u t x‖
      = ‖∫ z : Navier.Space, staticCurl (uncurry u t) (x - z) ⨯₃ bsVectorKernel z ∂volume‖ :=
        by rw [hrec]
    _ ≤ ∫ z : Navier.Space, G z ∂volume := by
        rw [hGdef]; exact norm_integral_le_integral_norm _
    _ = (∫⁻ z : Navier.Space, ENNReal.ofReal (G z) ∂volume).toReal := by
        rw [← hGdef]
        exact integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun z => norm_nonneg _) hGmeas.aestronglyMeasurable
    _ = (∫⁻ z in Metric.ball (0 : Navier.Space) ρ, ENNReal.ofReal (G z) ∂volume).toReal := by
        rw [hstep2]
    _ ≤ (ENNReal.ofReal (2 * V u t) *
        (ENNReal.ofReal (2 * ρ / Real.pi) * volume (Metric.ball (0 : Navier.Space) 1))).toReal :=
        (ENNReal.toReal_le_toReal hLne hMne).mpr hstep3
    _ ≤ 2 * V u t * (2 * (volume (Metric.ball (0 : Navier.Space) 1)).toReal / Real.pi *
        (2 * bound + 1)) := by
        refine le_of_eq ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (mul_nonneg zero_le_two (V_nonneg hu hK hsupp ht)),
          ENNReal.toReal_ofReal (by positivity), hρdef]
        ring

/-- **The Biot--Savart comparison.** For every selected-profile competitor
there is `C > 0` with `‖uncurry u t x‖ ≤ C * V u t` on `[0, 1)`: the velocity
is recovered from its own vorticity by the whole-space Biot--Savart integral,
the support of the slice truncates it to a fixed ball, and the kernel's
cancellation mass on that ball is `O(1)`. -/
theorem velocity_le_V {u p f : _} (h : Properties u p f) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Navier.Space,
      ‖uncurry u t x‖ ≤ C * V u t := by
  classical
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  set K' : Set Navier.Space := ⇑toPiCLM '' K with hK'def
  have hK'c : IsCompact K' := hK.image toPiCLM.continuous
  by_cases hempty : K' = ∅
  · refine ⟨1, by norm_num, fun t ht x => ?_⟩
    have hzero : uncurry u t x = 0 := by
      refine congrArg (fun v : ESpace => (v : Navier.Space)) (hsupp t ht _ ?_)
      intro hK'
      have hxK' : x ∈ K' := ⟨_, hK', rfl⟩
      rw [hempty] at hxK'
      exact (Set.mem_empty_iff_false x).mp hxK'
    rw [hzero, norm_zero]
    exact mul_nonneg (by norm_num) (V_nonneg h.velocity_smooth hK hsupp ht)
  · obtain ⟨x₀, hx₀, hmax⟩ := hK'c.exists_isMaxOn
      (Set.nonempty_iff_ne_empty.mpr hempty) continuous_norm.continuousOn
    have hmax' : ∀ y ∈ K', ‖y‖ ≤ ‖x₀‖ := isMaxOn_iff.mp hmax
    set C : ℝ := 2 * (2 * (volume (Metric.ball (0 : Navier.Space) 1)).toReal / Real.pi *
      (2 * ‖x₀‖ + 1)) with hCdef
    have hCpos : 0 < C := by
      refine mul_pos (by norm_num) (mul_pos ?_ ?_)
      · have hv : 0 < (volume (Metric.ball (0 : Navier.Space) 1)).toReal :=
          ENNReal.toReal_pos
            (Metric.measure_ball_pos volume (0 : Navier.Space) (by norm_num : (0 : ℝ) < 1)).ne'
            (measure_ball_lt_top (μ := volume) (x := (0 : Navier.Space)) (r := 1)).ne
        exact div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hv) Real.pi_pos
      · have h1 : (0 : ℝ) ≤ ‖(x₀ : Navier.Space)‖ := norm_nonneg _
        linarith
    refine ⟨C, hCpos, fun t ht x => ?_⟩
    by_cases hx : x ∈ K'
    · rw [hCdef]
      exact (velocity_ball_le h.velocity_smooth hK hsupp h.divergence_free ht x ‖x₀‖
        hmax' hx).trans_eq (by ring)
    · have hxK : ⇑fromPiCLM x ∉ K := by
        intro hK'
        exact hx (by rw [hK'def]; exact ⟨_, hK', rfl⟩)
      have hzero : uncurry u t x = 0 := by
        refine congrArg (fun v : ESpace => (v : Navier.Space)) (hsupp t ht _ hxK)
      rw [hzero, norm_zero]
      exact mul_nonneg (le_of_lt hCpos) (V_nonneg h.velocity_smooth hK hsupp ht)

/-! ## 4. The named residual: the scalar vorticity-rate estimate. -/

/-- **The residual is one scalar inequality away.** The velocity-rate
comparison `velocity_le_V` plus the scalar estimate `VorticityRateBound u`
gives the single Grönwall velocity estimate `(†)`. -/
theorem gronwall_velocity_bound_of_rate_bound {u p f : _} (h : Properties u p f)
    (hr : VorticityRateBound u) : GronwallVelocityBound u := by
  obtain ⟨C₁, hC₁, hle₁⟩ := velocity_le_V h
  obtain ⟨C₂, hC₂, hle₂⟩ := hr
  refine ⟨C₁ * max C₂ 1, mul_pos hC₁ (lt_of_lt_of_le zero_lt_one (le_max_right _ _)),
    fun t ht x => ?_⟩
  calc ‖uncurry u t x‖ ≤ C₁ * V u t := hle₁ t ht x
    _ ≤ C₁ * (max C₂ 1 * Real.exp (∫ s in (0 : ℝ)..t, V u s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₁)
        exact (hle₂ t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.exp_pos _).le)
    _ = C₁ * max C₂ 1 * Real.exp (∫ s in (0 : ℝ)..t, V u s) := by ring

/-- **The named residual, constructed form.** A Grönwall control pair for the
selected profile is obtained exactly when the scalar vorticity-rate estimate
holds; the construction reads the pair off the rate bound via `(†)`. -/
theorem gronwall_pair_of_rate_bound {u p f : _} (h : Properties u p f)
    (hr : VorticityRateBound u) : GronwallPair u := by
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  exact velocity_gronwall_pair_of_bound h.velocity_smooth hK hsupp
    (gronwall_velocity_bound_of_rate_bound h hr)

/-! ## 5. Conditional forms of the crown. -/

/-- The BKM vorticity-integral divergence, under the constructed Grönwall
control pair. -/
theorem vorticity_integral_divergence_of_gronwall_pair {u p f : _}
    (h : Properties u p f) (hp : GronwallPair u) :
    ¬ ∃ B : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, V u s ≤ B := by
  obtain ⟨Y, Y', hYcont, hYder, hYpos, hYgron, hYdom⟩ := hp
  exact vorticity_integral_divergence h hYcont hYder hYpos hYgron hYdom

/-- The `lintegral` crown form, under the constructed Grönwall control pair. -/
theorem lintegral_vorticity_integral_divergence_of_gronwall_pair {u p f : _}
    (h : Properties u p f) (hp : GronwallPair u) :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (V u t) = ⊤ := by
  obtain ⟨Y, Y', hYcont, hYder, hYpos, hYgron, hYdom⟩ := hp
  exact lintegral_vorticity_integral_divergence h hYcont hYder hYpos hYgron hYdom

/-- The crown under the single velocity estimate `(†)`. -/
theorem vorticity_integral_divergence_of_velocity_bound {u p f : _}
    (h : Properties u p f) (hb : GronwallVelocityBound u) :
    ¬ ∃ B : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, V u s ≤ B :=
  vorticity_integral_divergence_of_gronwall_pair h
    ((gronwall_pair_iff_velocity_bound h).mpr hb)

/-- The `lintegral` crown under the single velocity estimate `(†)`. -/
theorem lintegral_vorticity_integral_divergence_of_velocity_bound {u p f : _}
    (h : Properties u p f) (hb : GronwallVelocityBound u) :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (V u t) = ⊤ :=
  lintegral_vorticity_integral_divergence_of_gronwall_pair h
    ((gronwall_pair_iff_velocity_bound h).mpr hb)

/-- The crown under the scalar vorticity-rate estimate: the exact named
residual, one scalar inequality from completion. -/
theorem vorticity_integral_divergence_of_rate_bound {u p f : _}
    (h : Properties u p f) (hr : VorticityRateBound u) :
    ¬ ∃ B : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, V u s ≤ B :=
  vorticity_integral_divergence_of_velocity_bound h
    (gronwall_velocity_bound_of_rate_bound h hr)

/-- The `lintegral` crown under the scalar vorticity-rate estimate. -/
theorem lintegral_vorticity_integral_divergence_of_rate_bound {u p f : _}
    (h : Properties u p f) (hr : VorticityRateBound u) :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (V u t) = ⊤ :=
  lintegral_vorticity_integral_divergence_of_velocity_bound h
    (gronwall_velocity_bound_of_rate_bound h hr)

end Navier.Analysis.BKMProfileGronwallPair

#check @Navier.Analysis.BKMProfileGronwallPair.gronwall_pair_iff_velocity_bound
#print axioms Navier.Analysis.BKMProfileGronwallPair.gronwall_pair_iff_velocity_bound
#check @Navier.Analysis.BKMProfileGronwallPair.no_uniform_sup_bound
#print axioms Navier.Analysis.BKMProfileGronwallPair.no_uniform_sup_bound
#check @Navier.Analysis.BKMProfileGronwallPair.velocity_le_V
#print axioms Navier.Analysis.BKMProfileGronwallPair.velocity_le_V
#check @Navier.Analysis.BKMProfileGronwallPair.gronwall_pair_of_rate_bound
#print axioms Navier.Analysis.BKMProfileGronwallPair.gronwall_pair_of_rate_bound
#check @Navier.Analysis.BKMProfileGronwallPair.vorticity_integral_divergence_of_gronwall_pair
#print axioms Navier.Analysis.BKMProfileGronwallPair.vorticity_integral_divergence_of_gronwall_pair
#check @Navier.Analysis.BKMProfileGronwallPair.lintegral_vorticity_integral_divergence_of_rate_bound
#print axioms Navier.Analysis.BKMProfileGronwallPair.lintegral_vorticity_integral_divergence_of_rate_bound
