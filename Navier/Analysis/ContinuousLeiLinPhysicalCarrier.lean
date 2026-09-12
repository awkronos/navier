import Navier.Analysis.ContinuousLeiLinSpace
import Navier.Analysis.ContinuousLeiLinTimeDuhamel
import Navier.Analysis.FourierMajorant
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fourier inversion of the whole-space carrier to physical space

The continuous Lei--Lin carrier lives on the frequency side: a trajectory
`w : ℝ → ES → ComplexSpace` with finite `X⁻¹/X¹` coordinate masses.  This
file builds the *physical* inversion map and certifies the three facts every
later `VelocityEvolution`/`PressureEvolution` consumption needs:

* `physicalCoord` — inverse Fourier transform, one coordinate at a time;
* `norm_physicalCoord_le` / `sum_norm_physicalCoord_le_coordinateX0Mass` —
  pointwise physical domination by the Wiener-slot mass `coordinateX0Mass`
  (the inversion bound `|û̌(x)| ≤ ∫ |û|` is unconditional: both sides of the
  Bochner-junk case are zero);
* `physicalCoord_fourierDatum` — **Schwartz initial agreement**: inverting
  the Fourier datum `fourierDatum u₀` of a `SchwartzVelocity` recovers the
  initial velocity pointwise, by `fourierInv_fourier_eq` on the Euclidean
  component (`FourierMajorant` carrier convention, `euclidComponent_apply`).

Finite energy is certified at the Schwartz datum level through the
Schwartz-space Plancherel identity `integral_norm_sq_fourier`:
`fourierDatum_energy_eq_physical` identifies the total frequency-side
`L²` mass of the datum with the physical initial energy
`∫ x, ∑ᵢ (u₀ x i)²` in the `Navier.kineticEnergy` density convention.

## What this file deliberately does NOT claim

* No fixed point: the admissible-ball completeness construction
  (`NOTES-ns.md` §NS4.1) is a separate obligation; this carrier consumes any
  trajectory, fixed or not.
* No `L²` isometry for non-Schwartz profiles: Mathlib carries no L² Fourier
  isometry (`l2Isometry` is absent at the pinned rev, measured by source
  grep); the energy identity here is the Schwartz-level one, which is the
  form the small-data and Fujita--Kato initial conditions need.
* No reality: `physicalCoord` of a Hermitian-symmetric profile is real, but
  the symmetry of the mild image is a pointwise-PDE obligation
  (`NOTES-ns.md` §NS4.3), not an inversion fact.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Navier.Analysis.ContinuousLeiLinPhysicalCarrier

open MeasureTheory Set SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap
open Navier
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.FourierMajorant

/-! ## The inversion map -/

/-- The physical-space inverse of one Fourier coordinate of a carrier
profile.  No integrability of `w` is required in the definition: the Bochner
integral defaults to `0` off `L¹`, and the domination lemma below is then
the `0 ≤ 0` case. -/
def physicalCoord (w : ES → ComplexSpace) (i : Fin 3) : ES → ℂ :=
  𝓕⁻ (fun ξ : ES => w ξ i)

/-- **Pointwise physical domination by the coordinate Wiener mass.**  Each
physical coordinate is bounded by the `L¹` mass of the corresponding
frequency coordinate: `|ûᵢ(x)| ≤ ∫ |ûᵢ|`. -/
theorem norm_physicalCoord_le (w : ES → ComplexSpace) (i : Fin 3) (x : ES) :
    ‖physicalCoord w i x‖ ≤ ∫ ξ : ES, ‖w ξ i‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- The full physical `ℓ¹` coordinate mass at a point is dominated by the
carrier's `coordinateX0Mass` — the exact Wiener-slot quantity that the
admissible-ball estimates control. -/
theorem sum_norm_physicalCoord_le_coordinateX0Mass (w : ES → ComplexSpace) (x : ES) :
    ∑ i : Fin 3, ‖physicalCoord w i x‖ ≤ coordinateX0Mass w := by
  unfold coordinateX0Mass
  refine Finset.sum_le_sum fun i _ => norm_physicalCoord_le w i x

/-! ## The Fourier-side initial datum and its pointwise agreement -/

/-- The Fourier-side initial datum of a Schwartz velocity: coordinate `i` is
`𝓕` of the Euclidean-real component `euclidComponent u₀ i`.  This is the
frequency-side image of the initial condition the admissible fixed point
must match. -/
def fourierDatum (u₀ : SchwartzVelocity) (ξ : ES) : ComplexSpace :=
  fun i => 𝓕 (euclidComponent u₀ i) ξ

/-- **Schwartz initial agreement.**  Fourier-inverting the datum recovers
the initial velocity pointwise: `𝓕⁻(𝓕(u₀ᵢ ∘ spaceProj)) x = (u₀ (spaceProj x) i : ℂ)`.
The proof is the `FourierMajorant` inversion pattern
(`FourierMajorant.lean:626`) specialized to the Euclidean carrier. -/
theorem physicalCoord_fourierDatum (u₀ : SchwartzVelocity) (i : Fin 3) (x : ES) :
    physicalCoord (fourierDatum u₀) i x = ((u₀ (spaceProj x) i : ℝ) : ℂ) := by
  unfold physicalCoord fourierDatum
  set g := euclidComponent u₀ i with hg
  have hfun : (fun ξ : ES => 𝓕 g ξ) = 𝓕 (⇑g) := by
    funext ξ
    simp only [SchwartzMap.fourier_coe]
  rw [hfun]
  have hinv : 𝓕⁻ (𝓕 (⇑g)) = (⇑g) :=
    g.continuous.fourierInv_fourier_eq g.integrable
      (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 g).integrable)
  rw [hinv, hg]
  exact euclidComponent_apply u₀ i x

/-- The inverted physical coordinate of the datum is pointwise the complex
Euclidean component, hence continuous (and in particular bounded). -/
theorem continuous_physicalCoord_fourierDatum (u₀ : SchwartzVelocity) (i : Fin 3) :
    Continuous (physicalCoord (fourierDatum u₀) i) := by
  have heq : physicalCoord (fourierDatum u₀) i = ⇑(euclidComponent u₀ i) := by
    funext x
    exact physicalCoord_fourierDatum u₀ i x
  rw [heq]
  exact (euclidComponent u₀ i).continuous

/-! ## Schwartz-level Plancherel energy of the datum -/

/-- The pointwise squared-norm identity carrying the Euclidean component's
energy from the Euclidean model `ES` back to `Space`. -/
theorem normSq_euclidComponent (u₀ : SchwartzVelocity) (i : Fin 3) (y : ES) :
    ‖euclidComponent u₀ i y‖ ^ 2 = (u₀ (spaceProj y) i) ^ 2 := by
  rw [euclidComponent_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Transport of the Euclidean-component `L²` energy to the standard `Space`
coordinates, via `integral_spaceProj`. -/
theorem integral_normSq_euclidComponent (u₀ : SchwartzVelocity) (i : Fin 3) :
    (∫ y : ES, ‖euclidComponent u₀ i y‖ ^ 2) = ∫ x : Space, (u₀ x i) ^ 2 := by
  rw [← integral_spaceProj (fun x : Space => (u₀ x i) ^ 2)]
  refine integral_congr_ae ?_
  filter_upwards with y
  exact normSq_euclidComponent u₀ i y

/-- **Plancherel energy of one datum coordinate.**  The frequency-side `L²`
mass of `fourierDatum u₀` equals the physical `L²` mass of the Euclidean
component, by Schwartz-space Plancherel `integral_norm_sq_fourier`. -/
theorem integral_normSq_fourierDatum (u₀ : SchwartzVelocity) (i : Fin 3) :
    (∫ ξ : ES, ‖fourierDatum u₀ ξ i‖ ^ 2) =
      ∫ x : Space, (u₀ x i) ^ 2 := by
  simp only [fourierDatum]
  rw [integral_norm_sq_fourier (euclidComponent u₀ i)]
  exact integral_normSq_euclidComponent u₀ i

/-- Each squared real component of a Schwartz velocity is `volume`-integrable
on `Space`: it is the `L²` norm energy of the `ℂ`-valued Schwartz component
`scalarComponent` (`SchwartzMap.memLp` + `MemLp.integrable_norm_pow`, with the
pointwise identification `⇑(scalarComponent u₀ i) x = ((u₀ x i : ℝ) : ℂ)` by
`rfl`, `Complex.norm_real`, `sq_abs`).  This is the side-condition consumed by
`integral_finsetSum` in the total energy identities below — this Mathlib rev
carries no unconditional `integral_sum` (measured by source grep). -/
theorem integrable_sq_component (u₀ : SchwartzVelocity) (i : Fin 3) :
    Integrable (fun x : Space => (u₀ x i) ^ 2) volume := by
  have h : Integrable (fun x : Space => ‖⇑(scalarComponent u₀ i) x‖ ^ 2) volume :=
    ((scalarComponent u₀ i).memLp 2 volume).integrable_norm_pow (by norm_num)
  refine h.congr (ae_of_all volume fun x => ?_)
  show ‖⇑(scalarComponent u₀ i) x‖ ^ 2 = (u₀ x i) ^ 2
  rw [show ⇑(scalarComponent u₀ i) x = ((u₀ x i : ℝ) : ℂ) from rfl,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The physical-side `L²` mass of one inverted datum coordinate equals the
transported Euclidean component energy: by pointwise agreement the inversion
is energy-neutral at the Schwartz datum. -/
theorem integral_normSq_physicalCoord_fourierDatum (u₀ : SchwartzVelocity) (i : Fin 3) :
    (∫ x : ES, ‖physicalCoord (fourierDatum u₀) i x‖ ^ 2) =
      ∫ x : Space, (u₀ x i) ^ 2 := by
  refine (integral_congr_ae ?_).trans (integral_normSq_euclidComponent u₀ i)
  filter_upwards with x
  rw [physicalCoord_fourierDatum, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    normSq_euclidComponent]

/-- **The total energy identity for the Fourier-side datum.**  The summed
frequency-side `L²` mass of `fourierDatum u₀` is exactly the initial
kinetic-energy density integral `∫ x, ∑ᵢ (u₀ x i)²` in the
`Navier.kineticEnergy` convention, and so is the summed physical-side mass of
its inversion.  This is the Plancherel input the small data and
Fujita--Kato initial-energy clauses consume. -/
theorem fourierDatum_energy_eq_physical (u₀ : SchwartzVelocity) :
    (∑ i : Fin 3, ∫ ξ : ES, ‖fourierDatum u₀ ξ i‖ ^ 2) =
      ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
  refine Eq.trans (Finset.sum_congr rfl fun i _ => integral_normSq_fourierDatum u₀ i) ?_
  exact (integral_finsetSum Finset.univ (fun i _ => integrable_sq_component u₀ i)).symm

/-- The same identity on the inverted physical coordinates. -/
theorem physicalCoord_fourierDatum_energy_eq_physical (u₀ : SchwartzVelocity) :
    (∑ i : Fin 3, ∫ x : ES, ‖physicalCoord (fourierDatum u₀) i x‖ ^ 2) =
      ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
  refine Eq.trans (Finset.sum_congr rfl fun i _ =>
    integral_normSq_physicalCoord_fourierDatum u₀ i) ?_
  exact (integral_finsetSum Finset.univ (fun i _ => integrable_sq_component u₀ i)).symm

end Navier.Analysis.ContinuousLeiLinPhysicalCarrier

#print axioms Navier.Analysis.ContinuousLeiLinPhysicalCarrier.norm_physicalCoord_le
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalCarrier.sum_norm_physicalCoord_le_coordinateX0Mass
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalCarrier.physicalCoord_fourierDatum
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalCarrier.continuous_physicalCoord_fourierDatum
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalCarrier.integral_normSq_physicalCoord_fourierDatum
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalCarrier.physicalCoord_fourierDatum_energy_eq_physical
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalCarrier.normSq_euclidComponent
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalCarrier.integral_normSq_euclidComponent
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalCarrier.integral_normSq_fourierDatum
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalCarrier.fourierDatum_energy_eq_physical
