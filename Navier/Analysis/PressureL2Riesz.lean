import Navier.Analysis.SingularIntegralPrelims
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The `L²` pressure bound on the estate's own carrier

`SingularIntegralPrelims` certifies the `p = 2` Calderón–Zygmund layer over
`EuclideanSpace ℝ (Fin 3)`, the carrier Plancherel requires (a real
inner-product structure).  The Navier–Stokes estate runs on
`Space = Fin 3 → ℝ`, which carries the sup norm and no inner product.  This
file performs the missing transport, so the `L²` pressure bound is available
where the PDE lives.

## Certified here (no sorry)

* `spaceToFourierL2` — the `L²` transport `L²(Space) → L²(EuclideanSpace)`
  along the volume-preserving coordinate identification
  (`PiLp.volume_preserving_ofLp`), an additive isometry
  (`norm_spaceToFourierL2`).
* `pressure_l2_bound_space` — **on `Space`**: if `P = Σᵢⱼ RᵢRⱼ(wᵢⱼ)` then
  `‖P‖₂ ≤ Σᵢⱼ ‖wᵢⱼ‖₂`.
* `exists_doubleRieszTransform_space` — the operator exists on `L²(Space)`,
  so the hypothesis bundle of `pressure_l2_bound_space` is inhabited.

## Scope

`p = 2` only, and the Calderón–Zygmund *representation*
`p = Σᵢⱼ RᵢRⱼ(uᵢuⱼ)` — the solution of the pressure Poisson equation
`-Δp = Σᵢⱼ ∂ᵢ∂ⱼ(uᵢuⱼ)` — remains a hypothesis, not a conclusion.  What was
Mathlib-absent (the `L²` operator bound) is now certified; what remains is the
representation.

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PressureL2Riesz

open MeasureTheory
open Navier.Analysis.SingularIntegralPrelims

/-- `L²` complex scalars over the estate's carrier `Space = Fin 3 → ℝ`. -/
abbrev L2Space := Lp ℂ 2 (volume : Measure Space)

/-- `L²` complex scalars over the Plancherel carrier. -/
abbrev L2Fourier := Lp (α := FourierSpace) ℂ 2

/-- The coordinate identification `EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)` is
volume preserving. -/
theorem measurePreserving_ofLp :
    MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ))
      (volume : Measure FourierSpace) (volume : Measure Space) :=
  PiLp.volume_preserving_ofLp (Fin 3)

/-- **The `L²` transport onto the Plancherel carrier.**  Composition with the
volume-preserving coordinate identification. -/
def spaceToFourierL2 : L2Space →+ L2Fourier :=
  MeasureTheory.Lp.compMeasurePreserving
    (@WithLp.ofLp 2 (Fin 3 → ℝ)) measurePreserving_ofLp

@[simp]
theorem norm_spaceToFourierL2 (g : L2Space) : ‖spaceToFourierL2 g‖ = ‖g‖ :=
  MeasureTheory.Lp.norm_compMeasurePreserving g measurePreserving_ofLp

theorem spaceToFourierL2_sum {ι : Type*} (s : Finset ι) (g : ι → L2Space) :
    spaceToFourierL2 (∑ k ∈ s, g k) = ∑ k ∈ s, spaceToFourierL2 (g k) :=
  map_sum spaceToFourierL2 g s

/-- **The double Riesz transform exists on `L²(Space)`.**  Transport the
`EuclideanSpace` construction back along the (bijective, volume-preserving)
coordinate identification.  This inhabits the hypothesis bundle of
`pressure_l2_bound_space`, so no consumer of that theorem is vacuously true. -/
theorem exists_doubleRieszTransform_space (i j : Fin 3) (f : L2Space) :
    ∃ g : L2Space,
      (∀ᵐ ξ : FourierSpace,
        (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ (spaceToFourierL2 g)) ξ
          = doubleRieszMultiplier i j ξ •
            (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ
              (spaceToFourierL2 f)) ξ) ∧ ‖g‖ ≤ ‖f‖ := by
  obtain ⟨G, hG, hnorm⟩ := exists_doubleRieszTransform i j (spaceToFourierL2 f)
  refine ⟨MeasureTheory.Lp.compMeasurePreserving (@WithLp.toLp 2 (Fin 3 → ℝ))
    (PiLp.volume_preserving_toLp (Fin 3)) G, ?_, ?_⟩
  · have hEq : spaceToFourierL2 (MeasureTheory.Lp.compMeasurePreserving
        (@WithLp.toLp 2 (Fin 3 → ℝ)) (PiLp.volume_preserving_toLp (Fin 3)) G) = G := by
      apply Subtype.ext
      rw [spaceToFourierL2, MeasureTheory.Lp.compMeasurePreserving_val,
        MeasureTheory.Lp.compMeasurePreserving_val,
        ← MeasureTheory.AEEqFun.compMeasurePreserving_comp]
      exact MeasureTheory.AEEqFun.compMeasurePreserving_id (G : FourierSpace →ₘ[volume] ℂ)
    rw [hEq]
    exact hG
  · rw [MeasureTheory.Lp.norm_compMeasurePreserving G
      (PiLp.volume_preserving_toLp (Fin 3))]
    simpa using hnorm

/-- **The `L²` pressure bound on `Space`.**  If the pressure decomposes as
`P = Σᵢⱼ RᵢRⱼ(wᵢⱼ)`, with `wᵢⱼ` the quadratic velocity products `uᵢuⱼ`, then

  `‖P‖₂ ≤ Σᵢⱼ ‖wᵢⱼ‖₂`.

This is the `p = 2` half of blocker (b) of
`ConditionalRegularity.prodiSerrin_interior_outerRegion_bounded`, stated on the
carrier the PDE actually uses.  The remaining half is the Calderón–Zygmund
*representation* itself, which is a hypothesis here. -/
theorem pressure_l2_bound_space
    (w R : Fin 3 → Fin 3 → L2Space) (P : L2Space)
    (hR : ∀ i j : Fin 3, ∀ᵐ ξ : FourierSpace,
      (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ
        (spaceToFourierL2 (R i j))) ξ
        = doubleRieszMultiplier i j ξ •
          (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ
            (spaceToFourierL2 (w i j))) ξ)
    (hP : P = ∑ i : Fin 3, ∑ j : Fin 3, R i j) :
    ‖P‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖w i j‖ := by
  rw [hP]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  have := doubleRiesz_l2_bound i j (spaceToFourierL2 (w i j))
    (spaceToFourierL2 (R i j)) (hR i j)
  simpa using this

end Navier.Analysis.PressureL2Riesz
