import Navier.Analysis.FourierBridge
import Navier.Analysis.EnergyNormBridge
import Navier.Analysis.EnergyPointwiseBalance
import Navier.Breakdown.MaximalNonextension
import Navier.Breakdown.CompactFutureForce
import Navier.Construction.ComparatorR3Bridge
import Navier.Construction.R3CompactCandidate

/-!
# Euclidean-coordinate transport for the whole-space PDE

The explicit singular construction is most naturally stated on
`EuclideanSpace ℝ (Fin 3)`, while the repository's official endpoint uses the
same three coordinates equipped with the product norm.  This file transports
fields and every differential operator through the canonical continuous
linear equivalence.  The operator comparison is proved from the chain rule;
it is not stored as an equivalence hypothesis.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff Topology

namespace Navier.Analysis.EuclideanPDETransport

open MeasureTheory
open Navier
open Navier.Analysis.FourierBridge
open Navier.Analysis.EnergyNormBridge
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.EnergyPointwiseBalance
open Navier.Breakdown

/-- The Euclidean normed version of the repository's three-coordinate space. -/
abbrev ESpace := EuclideanSpace ℝ (Fin 3)

abbrev EVelocityField := (ℝ × ESpace) → ESpace
abbrev EPressureField := (ℝ × ESpace) → ℝ

def eSpacetimeBefore (T : ℝ) : Set (ℝ × ESpace) :=
  Set.Ico 0 T ×ˢ Set.univ

def eFutureDomain : Set (ℝ × ESpace) :=
  Set.Ici 0 ×ˢ Set.univ

/-- Coordinate identity from the Euclidean norm to the endpoint's product norm. -/
def toNative : ESpace ≃L[ℝ] Space := EuclideanSpace.equiv (Fin 3) ℝ

/-- Coordinate identity from the endpoint's product norm to the Euclidean norm. -/
def toEuclidean : Space ≃L[ℝ] ESpace := toNative.symm

@[simp] theorem toNative_apply (x : ESpace) (i : Fin 3) : toNative x i = x i := rfl
@[simp] theorem toEuclidean_apply (x : Space) (i : Fin 3) : toEuclidean x i = x i := rfl

@[simp] theorem toNative_toEuclidean (x : Space) :
    toNative (toEuclidean x) = x := toNative.apply_symm_apply x

@[simp] theorem toEuclidean_toNative (x : ESpace) :
    toEuclidean (toNative x) = x := toNative.symm_apply_apply x

/-- Euclidean coordinate vector corresponding to `basisVector`. -/
def eBasisVector (i : Fin 3) : ESpace := EuclideanSpace.single i 1

@[simp] theorem toNative_eBasisVector (i : Fin 3) :
    toNative (eBasisVector i) = basisVector i := by
  ext j
  simp [eBasisVector, basisVector, Pi.single_apply, eq_comm]

@[simp] theorem toEuclidean_basisVector (i : Fin 3) :
    toEuclidean (basisVector i) = eBasisVector i := by
  apply toNative.injective
  rw [toNative_toEuclidean, toNative_eBasisVector]

/-- Change only the normed presentation of a spacetime point. -/
def spacetimeToEuclidean : ℝ × Space → ℝ × ESpace :=
  fun z => (z.1, toEuclidean z.2)

theorem spacetimeToEuclidean_contDiff : ContDiff ℝ ∞ spacetimeToEuclidean := by
  exact contDiff_fst.prodMk (toEuclidean.contDiff.comp contDiff_snd)

/-- Transport a Euclidean velocity to the repository's official carrier. -/
def nativeVelocity (u : EVelocityField) : VelocityEvolution :=
  fun t x => toNative (u (t, toEuclidean x))

/-- Transport a Euclidean scalar pressure without changing its values. -/
def nativePressure (p : EPressureField) : PressureEvolution :=
  fun t x => p (t, toEuclidean x)

/-- Transport a Euclidean force to the repository's official carrier. -/
def nativeForce (f : EVelocityField) : ForceField :=
  fun t x => toNative (f (t, toEuclidean x))

/-- Inverse coordinate transport for a native velocity. -/
def euclideanVelocity (u : VelocityEvolution) : EVelocityField :=
  fun z => toEuclidean (u z.1 (toNative z.2))

/-- Inverse coordinate transport for a native pressure. -/
def euclideanPressure (p : PressureEvolution) : EPressureField :=
  fun z => p z.1 (toNative z.2)

@[simp] theorem nativeVelocity_euclideanVelocity (u : VelocityEvolution) :
    nativeVelocity (euclideanVelocity u) = u := by
  funext t x
  simp [nativeVelocity, euclideanVelocity]

@[simp] theorem nativePressure_euclideanPressure (p : PressureEvolution) :
    nativePressure (euclideanPressure p) = p := by
  funext t x
  simp [nativePressure, euclideanPressure]

@[simp] theorem euclideanVelocity_nativeVelocity (u : EVelocityField) :
    euclideanVelocity (nativeVelocity u) = u := by
  funext z
  simp [nativeVelocity, euclideanVelocity]

@[simp] theorem euclideanPressure_nativePressure (p : EPressureField) :
    euclideanPressure (nativePressure p) = p := by
  funext z
  simp [nativePressure, euclideanPressure]

/-- Ordinary Euclidean time derivative, used at interior times. -/
def eTimeDerivative (u : EVelocityField) (t : ℝ) (x : ESpace) : ESpace :=
  fderiv ℝ (fun s : ℝ => u (s, x)) t 1

/-- Euclidean spatial derivative with time fixed. -/
def eSpatialDerivative (u : EVelocityField) (t : ℝ) (x : ESpace) :
    ESpace →L[ℝ] ESpace :=
  fderiv ℝ (fun y : ESpace => u (t, y)) x

def eConvection (u : EVelocityField) (t : ℝ) (x : ESpace) : ESpace :=
  eSpatialDerivative u t x (u (t, x))

def eDivergence (u : EVelocityField) (t : ℝ) (x : ESpace) : ℝ :=
  ∑ i : Fin 3, eSpatialDerivative u t x (eBasisVector i) i

def ePressureGradient (p : EPressureField) (t : ℝ) (x : ESpace) : ESpace :=
  ∑ i : Fin 3,
    (fderiv ℝ (fun y : ESpace => p (t, y)) x (eBasisVector i)) • eBasisVector i

def eLaplacian (u : EVelocityField) (t : ℝ) (x : ESpace) : ESpace :=
  ∑ i : Fin 3,
    fderiv ℝ (fun y : ESpace => eSpatialDerivative u t y (eBasisVector i)) x
      (eBasisVector i)

theorem nativeVelocity_value (u : EVelocityField) (t : ℝ) (x : ESpace) :
    nativeVelocity u t (toNative x) = toNative (u (t, x)) := by simp [nativeVelocity]

theorem nativePressure_value (p : EPressureField) (t : ℝ) (x : ESpace) :
    nativePressure p t (toNative x) = p (t, x) := by simp [nativePressure]

theorem nativeForce_value (f : EVelocityField) (t : ℝ) (x : ESpace) :
    nativeForce f t (toNative x) = toNative (f (t, x)) := by simp [nativeForce]

/-- Chain-rule identity for the first spatial derivative. -/
theorem spatialDerivative_nativeVelocity
    (u : EVelocityField) {t : ℝ} {x : ESpace}
    (hu : DifferentiableAt ℝ (fun y : ESpace => u (t, y)) x) :
    spatialDerivative (nativeVelocity u) t (toNative x) =
      toNative.toContinuousLinearMap.comp
        ((eSpatialDerivative u t x).comp toEuclidean.toContinuousLinearMap) := by
  have hin := hu.hasFDerivAt.comp (toNative x) toEuclidean.hasFDerivAt
  have hout := toNative.hasFDerivAt.comp (toNative x) hin
  change fderiv ℝ (fun y : Space => toNative (u (t, toEuclidean y))) (toNative x) = _
  simpa [eSpatialDerivative, Function.comp_def] using hout.fderiv

theorem convection_nativeVelocity
    (u : EVelocityField) {t : ℝ} {x : ESpace}
    (hu : DifferentiableAt ℝ (fun y : ESpace => u (t, y)) x) :
    convection (nativeVelocity u) t (toNative x) =
      toNative (eConvection u t x) := by
  rw [convection, spatialDerivative_nativeVelocity u hu]
  simp [nativeVelocity_value, eConvection, ContinuousLinearMap.comp_apply]

theorem divergence_nativeVelocity
    (u : EVelocityField) {t : ℝ} {x : ESpace}
    (hu : DifferentiableAt ℝ (fun y : ESpace => u (t, y)) x) :
    divergence (nativeVelocity u) t (toNative x) = eDivergence u t x := by
  rw [divergence, eDivergence, spatialDerivative_nativeVelocity u hu]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.comp_apply]
  change toNative ((eSpatialDerivative u t x) (toEuclidean (basisVector i))) i = _
  rw [toEuclidean_basisVector]
  exact toNative_apply _ i

theorem pressureGradient_nativePressure
    (p : EPressureField) {t : ℝ} {x : ESpace}
    (hp : DifferentiableAt ℝ (fun y : ESpace => p (t, y)) x) :
    pressureGradient (nativePressure p) t (toNative x) =
      toNative (ePressureGradient p t x) := by
  unfold pressureGradient ePressureGradient nativePressure
  have hcomp := hp.hasFDerivAt.comp (toNative x) toEuclidean.hasFDerivAt
  have hfd : fderiv ℝ (fun y : Space => p (t, toEuclidean y)) (toNative x) =
      (fderiv ℝ (fun y : ESpace => p (t, y)) x).comp
        toEuclidean.toContinuousLinearMap := by
    simpa [Function.comp_def] using hcomp.fderiv
  rw [hfd]
  ext j
  rw [ContinuousLinearMap.comp_apply]
  change (fderiv ℝ (fun y : ESpace => p (t, y)) x)
      (toEuclidean (basisVector j)) = _
  rw [toEuclidean_basisVector]
  simp [eBasisVector, Pi.single_apply]

/-- Chain-rule identity for the second spatial operator. -/
theorem laplacian_nativeVelocity
    (u : EVelocityField) {t : ℝ} {x : ESpace}
    (hu : ContDiff ℝ ∞ (fun y : ESpace => u (t, y))) :
    laplacian (nativeVelocity u) t (toNative x) = toNative (eLaplacian u t x) := by
  unfold laplacian eLaplacian
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfirst :
      (fun y : Space => fderiv ℝ (nativeVelocity u t) y (basisVector i)) =
        fun y : Space => toNative
          (eSpatialDerivative u t (toEuclidean y) (eBasisVector i)) := by
    funext y
    have h := congrArg (fun L : Space →L[ℝ] Space => L (basisVector i))
      (spatialDerivative_nativeVelocity u
        ((hu.differentiable (by norm_num)) (toEuclidean y)))
    simpa [spatialDerivative, ContinuousLinearMap.comp_apply] using h
  rw [hfirst]
  have hD : ContDiff ℝ 1
      (fun y : ESpace => eSpatialDerivative u t y (eBasisVector i)) := by
    exact (hu.fderiv_right (m := 1)
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le).clm_apply contDiff_const
  have hin := (hD.differentiable (by norm_num) x).hasFDerivAt.comp
    (toNative x) toEuclidean.hasFDerivAt
  have hout := toNative.hasFDerivAt.comp (toNative x) hin
  have hfd :
      fderiv ℝ
          (fun y : Space => toNative
            (eSpatialDerivative u t (toEuclidean y) (eBasisVector i)))
          (toNative x) =
        toNative.toContinuousLinearMap.comp
          ((fderiv ℝ (fun y : ESpace => eSpatialDerivative u t y (eBasisVector i)) x).comp
            toEuclidean.toContinuousLinearMap) := by
    simpa [Function.comp_def] using hout.fderiv
  rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    show toEuclidean.toContinuousLinearMap (basisVector i) = eBasisVector i from
      toEuclidean_basisVector i]
  rfl

theorem timeDerivative_nativeVelocity_of_pos
    (u : EVelocityField) {t : ℝ} (ht : 0 < t) (x : ESpace)
    (hu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t) :
    timeDerivative (nativeVelocity u) t (toNative x) =
      toNative (eTimeDerivative u t x) := by
  unfold timeDerivative eTimeDerivative
  rw [fderivWithin_of_mem_nhds (Ici_mem_nhds ht)]
  have hout := toNative.hasFDerivAt.comp t hu.hasFDerivAt
  have hfd :
      fderiv ℝ (fun s : ℝ => nativeVelocity u s (toNative x)) t =
        toNative.toContinuousLinearMap.comp
          (fderiv ℝ (fun s : ℝ => u (s, x)) t) := by
    simpa [nativeVelocity, Function.comp_def] using hout.fderiv
  rw [hfd, ContinuousLinearMap.comp_apply]
  rfl

theorem nativeVelocity_smoothBefore {T : ℝ} {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u (eSpacetimeBefore T)) :
    SmoothVelocityBefore T (nativeVelocity u) := by
  have hm : Set.MapsTo spacetimeToEuclidean (spacetimeBefore T)
      (eSpacetimeBefore T) := by
    intro z hz
    exact ⟨hz.1, Set.mem_univ _⟩
  have hi := hu.comp spacetimeToEuclidean_contDiff.contDiffOn hm
  have ho := toNative.contDiff.comp_contDiffOn hi
  simpa [SmoothVelocityBefore, spacetimeBefore, nativeVelocity,
    spacetimeToEuclidean, Function.comp_def] using ho

theorem nativePressure_smoothBefore {T : ℝ} {p : EPressureField}
    (hp : ContDiffOn ℝ ∞ p (eSpacetimeBefore T)) :
    SmoothPressureBefore T (nativePressure p) := by
  have hm : Set.MapsTo spacetimeToEuclidean (spacetimeBefore T)
      (eSpacetimeBefore T) := by
    intro z hz
    exact ⟨hz.1, Set.mem_univ _⟩
  have hi := hp.comp spacetimeToEuclidean_contDiff.contDiffOn hm
  simpa [SmoothPressureBefore, spacetimeBefore, nativePressure,
    spacetimeToEuclidean, Function.comp_def] using hi

theorem nativeForce_smoothOnNonnegativeTime {f : EVelocityField}
    (hf : ContDiffOn ℝ ∞ f eFutureDomain) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => nativeForce f z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hm : Set.MapsTo spacetimeToEuclidean
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) eFutureDomain := by
    intro z hz
    exact ⟨hz.1, Set.mem_univ _⟩
  have hi := hf.comp spacetimeToEuclidean_contDiff.contDiffOn hm
  have ho := toNative.contDiff.comp_contDiffOn hi
  simpa [nativeForce, spacetimeToEuclidean, Function.comp_def] using ho

theorem nativeForce_supported {K : Set ESpace} {f : EVelocityField}
    (hf : ∀ t : ℝ, 0 ≤ t → ∀ x : ESpace, x ∉ K → f (t, x) = 0) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space, x ∉ toNative '' K → nativeForce f t x = 0 := by
  intro t ht x hx
  have hy : toEuclidean x ∉ K := by
    intro hmem
    apply hx
    exact ⟨toEuclidean x, hmem, toNative_toEuclidean x⟩
  simp [nativeForce, hf t ht (toEuclidean x) hy]

theorem nativeForce_compactSupport {K : Set ESpace} (hK : IsCompact K) :
    IsCompact (toNative '' K) := hK.image toNative.continuous

theorem nativeForce_futureTimeSupport {f : EVelocityField} {T : ℝ}
    (hf : ∀ t : ℝ, T ≤ t → ∀ x : ESpace, f (t, x) = 0) :
    ∀ t : ℝ, T ≤ t → ∀ x : Space, nativeForce f t x = 0 := by
  intro t ht x
  simp [nativeForce, hf t ht]

/-- Compact Euclidean space support and future-time support give the official
rapid-decay force predicate after coordinate transport. -/
theorem nativeForce_forcedDataRapidDecay
    {K : Set ESpace} {f : EVelocityField} {T : ℝ}
    (hf : ContDiffOn ℝ ∞ f eFutureDomain) (hK : IsCompact K)
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ x : ESpace, x ∉ K → f (t, x) = 0)
    (htime : ∀ t : ℝ, T ≤ t → ∀ x : ESpace, f (t, x) = 0) :
    ForcedDataRapidDecay (nativeForce f) := by
  apply Navier.Breakdown.CompactFutureForce.forcedDataRapidDecay_of_compactFutureSupport
    (S := toNative '' K) (T := T)
  · exact nativeForce_smoothOnNonnegativeTime hf
  · exact nativeForce_compactSupport hK
  · exact nativeForce_supported hs
  · exact nativeForce_futureTimeSupport htime

def spacetimeToNative : ℝ × ESpace → ℝ × Space :=
  fun z => (z.1, toNative z.2)

theorem spacetimeToNative_contDiff : ContDiff ℝ ∞ spacetimeToNative := by
  exact contDiff_fst.prodMk (toNative.contDiff.comp contDiff_snd)

theorem euclideanVelocity_smoothOnNonnegativeTime {u : VelocityEvolution}
    (hu : SmoothVelocityOnNonnegativeTime u) :
    ContDiffOn ℝ ∞ (euclideanVelocity u) eFutureDomain := by
  change ContDiffOn ℝ ∞ (fun z : ℝ × ESpace =>
    toEuclidean (u z.1 (toNative z.2))) eFutureDomain
  have hm : Set.MapsTo spacetimeToNative eFutureDomain
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro z hz
    exact ⟨hz.1, Set.mem_univ _⟩
  have hi := hu.comp spacetimeToNative_contDiff.contDiffOn hm
  have ho := toEuclidean.contDiff.comp_contDiffOn hi
  simpa [SmoothVelocityOnNonnegativeTime, euclideanVelocity,
    spacetimeToNative, Function.comp_def] using ho

theorem euclideanPressure_smoothOnNonnegativeTime {p : PressureEvolution}
    (hp : SmoothPressureOnNonnegativeTime p) :
    ContDiffOn ℝ ∞ (euclideanPressure p) eFutureDomain := by
  change ContDiffOn ℝ ∞ (fun z : ℝ × ESpace =>
    p z.1 (toNative z.2)) eFutureDomain
  have hm : Set.MapsTo spacetimeToNative eFutureDomain
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro z hz
    exact ⟨hz.1, Set.mem_univ _⟩
  have hi := hp.comp spacetimeToNative_contDiff.contDiffOn hm
  simpa [SmoothPressureOnNonnegativeTime, euclideanPressure,
    spacetimeToNative, Function.comp_def] using hi

theorem eFutureSpatialSlice_contDiff {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u eFutureDomain)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (fun x : ESpace => u (t, x)) := by
  have hm : Set.MapsTo (fun x : ESpace => (t, x)) Set.univ eFutureDomain := by
    intro x _
    exact ⟨ht, Set.mem_univ _⟩
  exact contDiffOn_univ.mp
    (hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn hm)

theorem eFuturePressureSlice_contDiff {p : EPressureField}
    (hp : ContDiffOn ℝ ∞ p eFutureDomain)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (fun x : ESpace => p (t, x)) := by
  have hm : Set.MapsTo (fun x : ESpace => (t, x)) Set.univ eFutureDomain := by
    intro x _
    exact ⟨ht, Set.mem_univ _⟩
  exact contDiffOn_univ.mp
    (hp.comp (contDiff_const.prodMk contDiff_id).contDiffOn hm)

theorem eFutureTimeSlice_differentiableAt {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u eFutureDomain)
    {t : ℝ} (ht : 0 < t) (x : ESpace) :
    DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t := by
  have hc : ContDiffAt ℝ ∞ u (t, x) := hu.contDiffAt
    (prod_mem_nhds (Ici_mem_nhds ht) Filter.univ_mem)
  exact (hc.differentiableAt (by simp)).comp t
    (hasFDerivAt_prodMk_left t x).differentiableAt

/-- The coordinate identity preserves the canonical Lebesgue volume. -/
theorem measurePreserving_toNative :
    MeasurePreserving toNative (volume : Measure ESpace) (volume : Measure Space) := by
  exact PiLp.volume_preserving_ofLp (Fin 3)

theorem integral_native_eq_euclidean (g : Space → ℝ) :
    (∫ x : Space, g x) = ∫ y : ESpace, g (toNative y) := by
  rw [← measurePreserving_toNative.integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding]

@[simp] theorem norm_toEuclidean (x : Space) :
    ‖toEuclidean x‖ = officialEuclideanNorm x := rfl

/-- Native sup-norm square integrability gives the Euclidean scalar `L²`
condition required by the finite-energy comparison solution. -/
theorem euclideanNorm_memLp_two_of_native
    (v : Space → Space) (hv : Continuous v)
    (hint : Integrable (fun x : Space => ‖v x‖ ^ 2)) :
    MemLp (fun y : ESpace => ‖toEuclidean (v (toNative y))‖) 2 := by
  have hoff : Integrable (fun x : Space => officialEuclideanNorm (v x) ^ 2) :=
    (integrable_norm_sq_iff_officialEuclideanNorm_sq v
      hv.aestronglyMeasurable).1 hint
  have htr : Integrable
      ((fun x : Space => officialEuclideanNorm (v x) ^ 2) ∘ toNative) :=
    (measurePreserving_toNative.integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding).2 hoff
  have hmeas : AEStronglyMeasurable
      (fun y : ESpace => ‖toEuclidean (v (toNative y))‖) :=
    (toEuclidean.continuous.comp (hv.comp toNative.continuous)).norm.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  simpa [Function.comp_def] using htr

/-- The global comparison energy integral is exactly the repository's
Euclidean-coordinate kinetic energy. -/
theorem euclideanEnergy_eq_kineticEnergy (v : VelocityEvolution) (t : ℝ) :
    (∫ y : ESpace, ‖toEuclidean (v t (toNative y))‖ ^ 2) = kineticEnergy v t := by
  rw [← integral_native_eq_euclidean
    (g := fun x : Space => ‖toEuclidean (v t x)‖ ^ 2)]
  unfold kineticEnergy
  apply integral_congr_ae
  filter_upwards with x
  rw [norm_toEuclidean, officialEuclideanNorm_sq_eq_sum_sq]

/-- The Euclidean finite-energy competitor bundle used by the whole-space
uniqueness argument.  Its fields coincide with `GlobalSolutionRn`: smoothness,
zero initial velocity, the actual PDE, `L²`, and a uniform energy bound. -/
structure EuclideanGlobalData
    (f v : EVelocityField) (p : EPressureField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ v eFutureDomain
  pressure_smooth : ContDiffOn ℝ ∞ p eFutureDomain
  initial_velocity : ∀ x : ESpace, v (0, x) = 0
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : ESpace, eDivergence v t x = 0
  equation : ∀ t : ℝ, 0 < t → ∀ x : ESpace,
    eTimeDerivative v t x + eConvection v t x =
      eLaplacian v t x - ePressureGradient p t x + f (t, x)
  integrable : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : ESpace => ‖v (t, x)‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t : ℝ, 0 ≤ t →
    (∫ x : ESpace, ‖v (t, x)‖ ^ 2) < E

/-- Every native global finite-energy competitor transports to the exact
Euclidean competitor bundle. -/
def IsClassicalSolution.toEuclideanGlobalData
    {f : EVelocityField} {v : VelocityEvolution} {p : PressureEvolution}
    (sol : IsClassicalSolution 1 (nativeForce f) (0 : SchwartzVelocity) v p) :
    EuclideanGlobalData f (euclideanVelocity v) (euclideanPressure p) where
  velocity_smooth := euclideanVelocity_smoothOnNonnegativeTime sol.velocity_smooth
  pressure_smooth := euclideanPressure_smoothOnNonnegativeTime sol.pressure_smooth
  initial_velocity := by
    intro x
    simp [euclideanVelocity, sol.initial_condition]
  divergence_free := by
    intro t ht x
    have hs := eFutureSpatialSlice_contDiff
      (euclideanVelocity_smoothOnNonnegativeTime sol.velocity_smooth) ht
    have hd := divergence_nativeVelocity (euclideanVelocity v)
      (x := x) (hs.differentiable (by simp) x)
    rw [nativeVelocity_euclideanVelocity] at hd
    exact hd.symm.trans (sol.incompressible t ht (toNative x))
  equation := by
    intro t ht x
    have hs := eFutureSpatialSlice_contDiff
      (euclideanVelocity_smoothOnNonnegativeTime sol.velocity_smooth) ht.le
    have hps := eFuturePressureSlice_contDiff
      (euclideanPressure_smoothOnNonnegativeTime sol.pressure_smooth) ht.le
    have htime := eFutureTimeSlice_differentiableAt
      (euclideanVelocity_smoothOnNonnegativeTime sol.velocity_smooth) ht x
    have ht' := timeDerivative_nativeVelocity_of_pos (euclideanVelocity v) ht x htime
    have hc := convection_nativeVelocity (euclideanVelocity v)
      (x := x) (hs.differentiable (by simp) x)
    have hl := laplacian_nativeVelocity (euclideanVelocity v) (x := x) hs
    have hp' := pressureGradient_nativePressure (euclideanPressure p) (x := x)
      (hps.differentiable (by simp) x)
    apply toNative.injective
    simp only [map_add, map_sub]
    rw [← ht', ← hc, ← hl, ← hp']
    rw [← nativeForce_value f t x]
    simpa using sol.equation t ht.le (toNative x)
  integrable := by
    intro t ht
    exact euclideanNorm_memLp_two_of_native (v t)
      (contDiff_spatialSlice_of_smoothVelocity v sol.velocity_smooth t ht).continuous
      (sol.finite_energy t ht)
  globally_bounded_energy := by
    obtain ⟨E, hE, hb⟩ := sol.uniformly_bounded_energy
    refine ⟨E, fun t ht => ?_⟩
    change (∫ x : ESpace, ‖toEuclidean (v t (toNative x))‖ ^ 2) < E
    rw [euclideanEnergy_eq_kineticEnergy]
    exact hb t ht

/-- Package the internal bridge record as the construction's exact
`GlobalSolutionRn` comparator. -/
def EuclideanGlobalData.toGlobalSolutionRn
    {f v : EVelocityField} {p : EPressureField}
    (h : EuclideanGlobalData f v p) :
    Navier.Construction.ComparatorBridge.GlobalSolutionRn f v p where
  velocity_smooth := h.velocity_smooth
  pressure_smooth := h.pressure_smooth
  initial_velocity := h.initial_velocity
  divergence_free := h.divergence_free
  navier_stokes := by
    intro t ht x
    change eTimeDerivative v t x + eConvection v t x - eLaplacian v t x +
      ePressureGradient p t x = f (t, x)
    rw [h.equation t ht x]
    abel
  integrable := h.integrable
  globally_bounded_energy := h.globally_bounded_energy

/-- Direct adapter used by the uniqueness contradiction: a native official
global solution becomes the construction's Euclidean finite-energy global
competitor. -/
def IsClassicalSolution.toGlobalSolutionRn
    {f : EVelocityField} {v : VelocityEvolution} {p : PressureEvolution}
    (sol : IsClassicalSolution 1 (nativeForce f) (0 : SchwartzVelocity) v p) :
    Navier.Construction.ComparatorBridge.GlobalSolutionRn f
      (euclideanVelocity v) (euclideanPressure p) :=
  EuclideanGlobalData.toGlobalSolutionRn
    (IsClassicalSolution.toEuclideanGlobalData sol)

theorem eSpatialSlice_contDiff {T : ℝ} {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u (eSpacetimeBefore T))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    ContDiff ℝ ∞ (fun x : ESpace => u (t, x)) := by
  have hm : Set.MapsTo (fun x : ESpace => (t, x)) Set.univ
      (eSpacetimeBefore T) := by
    intro x _
    exact ⟨⟨ht0, htT⟩, Set.mem_univ _⟩
  have h := hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn hm
  exact contDiffOn_univ.mp h

theorem ePressureSlice_contDiff {T : ℝ} {p : EPressureField}
    (hp : ContDiffOn ℝ ∞ p (eSpacetimeBefore T))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    ContDiff ℝ ∞ (fun x : ESpace => p (t, x)) := by
  have hm : Set.MapsTo (fun x : ESpace => (t, x)) Set.univ
      (eSpacetimeBefore T) := by
    intro x _
    exact ⟨⟨ht0, htT⟩, Set.mem_univ _⟩
  have h := hp.comp (contDiff_const.prodMk contDiff_id).contDiffOn hm
  exact contDiffOn_univ.mp h

theorem eTimeSlice_differentiableAt {T : ℝ} {u : EVelocityField}
    (hu : ContDiffOn ℝ ∞ u (eSpacetimeBefore T))
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : ESpace) :
    DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t := by
  have hc : ContDiffAt ℝ ∞ u (t, x) := hu.contDiffAt
    (prod_mem_nhds (Ico_mem_nhds ht0 htT) Filter.univ_mem)
  have hjoint : DifferentiableAt ℝ u (t, x) := hc.differentiableAt (by simp)
  exact hjoint.comp t (hasFDerivAt_prodMk_left t x).differentiableAt

/-- Actual Euclidean classical data needed to build a native partial solution.
The PDE is imposed at ordinary interior times.  The fields are identically zero
on a right neighborhood of the initial time, which supplies the native
one-sided equation at `t = 0`. -/
structure EuclideanPartialData
    (u : EVelocityField) (p : EPressureField) (f : EVelocityField) (T : ℝ) : Prop where
  terminalTime_pos : 0 < T
  velocity_smooth : ContDiffOn ℝ ∞ u (eSpacetimeBefore T)
  pressure_smooth : ContDiffOn ℝ ∞ p (eSpacetimeBefore T)
  initially_quiescent : ∃ ε : ℝ, 0 < ε ∧
    ∀ t : ℝ, 0 ≤ t → t < ε → ∀ x : ESpace,
      u (t, x) = 0 ∧ p (t, x) = 0 ∧ f (t, x) = 0
  divergence_free : ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : ESpace,
    eDivergence u t x = 0
  equation : ∀ t : ℝ, 0 < t → t < T → ∀ x : ESpace,
    eTimeDerivative u t x + eConvection u t x =
      eLaplacian u t x - ePressureGradient p t x + f (t, x)

/-- The actual compact candidate supplies all fields of the Euclidean partial
solution once its construction-level activation lemma provides the initial
quiescent interval. -/
def EuclideanPartialData.ofR3CompactCandidate
    {u : EVelocityField} {p : EPressureField} {f : EVelocityField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f)
    (hq : ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 0 ≤ t → t < ε → ∀ x : ESpace,
        u (t, x) = 0 ∧ p (t, x) = 0 ∧ f (t, x) = 0) :
    EuclideanPartialData u p f 1 where
  terminalTime_pos := zero_lt_one
  velocity_smooth := h.velocity_smooth
  pressure_smooth := h.pressure_smooth
  initially_quiescent := hq
  divergence_free := by
    intro t ht0 ht1 x
    exact h.divergence_free t ⟨ht0, ht1⟩ x
  equation := by
    intro t ht0 ht1 x
    have he := h.navier_stokes t ⟨ht0, ht1⟩ x
    change eTimeDerivative u t x + eConvection u t x - eLaplacian u t x +
      ePressureGradient p t x = f (t, x) at he
    rw [← he]
    abel

theorem R3CompactCandidate.nativeForce_forcedDataRapidDecay
    {u : EVelocityField} {p : EPressureField} {f : EVelocityField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f) :
    ForcedDataRapidDecay (nativeForce f) := by
  obtain ⟨K, hK, hs⟩ := h.force_support
  obtain ⟨T, _hT, htime⟩ := h.force_time_support
  exact Navier.Analysis.EuclideanPDETransport.nativeForce_forcedDataRapidDecay
    h.force_smooth hK hs htime

theorem timeDerivative_nativeVelocity_zero_of_initially_quiescent
    {u : EVelocityField} {ε : ℝ} (hε : 0 < ε)
    (hu : ∀ t : ℝ, 0 ≤ t → t < ε → ∀ x : ESpace, u (t, x) = 0)
    (x : Space) : timeDerivative (nativeVelocity u) 0 x = 0 := by
  have he : (fun s : ℝ => nativeVelocity u s x) =ᶠ[nhdsWithin 0 (Set.Ici 0)]
      (fun _ : ℝ => (0 : Space)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε)] with s hs0 hsε
    simp [nativeVelocity, hu s hs0 hsε]
  unfold timeDerivative
  rw [he.fderivWithin_eq_of_mem (Set.mem_Ici.mpr le_rfl)]
  simp

/-- The chain-rule transport of actual Euclidean data is a native
`PartialClassicalSolution` at viscosity one. -/
def EuclideanPartialData.toNativePartial
    {u : EVelocityField} {p : EPressureField} {f : EVelocityField} {T : ℝ}
    (h : EuclideanPartialData u p f T) :
    PartialClassicalSolution 1 (nativeForce f) (fun _ => 0) T where
  terminalTime_pos := h.terminalTime_pos
  velocity := nativeVelocity u
  pressure := nativePressure p
  velocity_smooth := nativeVelocity_smoothBefore h.velocity_smooth
  pressure_smooth := nativePressure_smoothBefore h.pressure_smooth
  initial_condition := by
    obtain ⟨ε, hε, hq⟩ := h.initially_quiescent
    funext x
    simp [nativeVelocity, hq 0 le_rfl hε]
  incompressible := by
    intro t ht0 htT x
    let y := toEuclidean x
    have hs := eSpatialSlice_contDiff h.velocity_smooth ht0 htT
    have hd := divergence_nativeVelocity u
      (x := y) (hs.differentiable (by simp) y)
    simpa [y] using hd.trans (h.divergence_free t ht0 htT y)
  equation := by
    intro t ht0 htT x
    by_cases ht : t = 0
    · subst t
      obtain ⟨ε, hε, hq⟩ := h.initially_quiescent
      have hu0 : nativeVelocity u 0 = fun _ => 0 := by
        funext y
        simp [nativeVelocity, hq 0 le_rfl hε]
      have hp0 : nativePressure p 0 = fun _ => 0 := by
        funext y
        simp [nativePressure, hq 0 le_rfl hε]
      have hf0 : nativeForce f 0 x = 0 := by
        simp [nativeForce, hq 0 le_rfl hε]
      have hdt := timeDerivative_nativeVelocity_zero_of_initially_quiescent hε
        (fun s hs0 hsε y => (hq s hs0 hsε y).1) x
      rw [hdt]
      unfold convection spatialDerivative laplacian pressureGradient
      rw [hu0, hp0, hf0]
      simp
      rfl
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
      let y := toEuclidean x
      have huS := eSpatialSlice_contDiff h.velocity_smooth ht0 htT
      have hpS := ePressureSlice_contDiff h.pressure_smooth ht0 htT
      have htime := eTimeSlice_differentiableAt h.velocity_smooth htpos htT y
      have heq := congrArg toNative (h.equation t htpos htT y)
      have ht' := timeDerivative_nativeVelocity_of_pos u htpos y htime
      have hc := convection_nativeVelocity u (x := y)
        (huS.differentiable (by simp) y)
      have hl := laplacian_nativeVelocity u (x := y)
        huS
      have hp' := pressureGradient_nativePressure p (x := y)
        (hpS.differentiable (by simp) y)
      have hxy : toNative y = x := by simp [y]
      rw [← hxy, ht', hc, hl, hp', nativeForce_value]
      simpa using heq

#print axioms spatialDerivative_nativeVelocity
#print axioms laplacian_nativeVelocity
#print axioms EuclideanPartialData.toNativePartial
#print axioms IsClassicalSolution.toGlobalSolutionRn
#print axioms nativeForce_forcedDataRapidDecay
#print axioms EuclideanPartialData.ofR3CompactCandidate
#print axioms R3CompactCandidate.nativeForce_forcedDataRapidDecay

end Navier.Analysis.EuclideanPDETransport
