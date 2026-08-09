import Navier.Analysis.OfficialABEncoding

/-!
# Inherited versus official Euclidean kinetic energy

`Navier.Space` inherits the finite product supremum norm, whereas Fefferman's
energy clause uses the Euclidean norm on `R^3`.  This file squares the checked
point-norm comparison, transports integrability under an explicit strong
measurability hypothesis, compares the two kinetic-energy integrals, and
transports their uniform boundedness clauses.

The remaining representation step is to derive the slice measurability used
here from the official smooth spacetime solution predicate.  These norm
comparisons do not prove an energy identity or any a priori estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.EnergyNormBridge

open Navier
open Navier.Analysis.OfficialABEncoding

/-- Fefferman's Euclidean kinetic-energy integral at one time. -/
def officialKineticEnergy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, officialEuclideanNorm (u t x) ^ 2

theorem continuous_officialEuclideanNorm :
    Continuous officialEuclideanNorm := by
  unfold officialEuclideanNorm officialEuclideanPoint
  fun_prop

/-- The inherited squared norm is bounded by the official squared norm. -/
theorem norm_sq_le_officialEuclideanNorm_sq (x : Space) :
    ‖x‖ ^ 2 ≤ officialEuclideanNorm x ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg x) (norm_le_officialEuclideanNorm x) 2

/-- In dimension three, the official squared norm is at most three times the
inherited squared norm. -/
theorem officialEuclideanNorm_sq_le_three_mul_norm_sq (x : Space) :
    officialEuclideanNorm x ^ 2 ≤ 3 * ‖x‖ ^ 2 := by
  calc
    officialEuclideanNorm x ^ 2 ≤
        (Real.sqrt 3 * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (officialEuclideanNorm_nonneg x)
        (officialEuclideanNorm_le x) 2
    _ = 3 * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- For a strongly measurable spatial field, the inherited and official
squared energy densities are integrable simultaneously. -/
theorem integrable_norm_sq_iff_officialEuclideanNorm_sq
    (f : Space → Space) (hf : AEStronglyMeasurable f) :
    Integrable (fun x => ‖f x‖ ^ 2) ↔
      Integrable (fun x => officialEuclideanNorm (f x) ^ 2) := by
  have hnorm :
      AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) :=
    hf.norm.pow 2
  have hoff :
      AEStronglyMeasurable
        (fun x => officialEuclideanNorm (f x) ^ 2) :=
    (continuous_officialEuclideanNorm.comp_aestronglyMeasurable hf).pow 2
  constructor
  · intro h
    apply (h.const_mul (3 : ℝ)).mono' hoff
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact officialEuclideanNorm_sq_le_three_mul_norm_sq (f x)
  · intro h
    apply h.mono' hnorm
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_sq_le_officialEuclideanNorm_sq (f x)

/-- The Euclidean norm squared equals the component-wise sum of squares. -/
theorem officialEuclideanNorm_sq_eq_sum_sq (x : Space) :
    officialEuclideanNorm x ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  simp [officialEuclideanNorm, officialEuclideanPoint,
    EuclideanSpace.real_norm_sq_eq]

/-- The sup norm squared is bounded by the sum of squares. -/
theorem norm_sq_le_sum_sq (x : Space) : ‖x‖ ^ 2 ≤ ∑ i : Fin 3, x i ^ 2 := by
  calc
    ‖x‖ ^ 2 ≤ officialEuclideanNorm x ^ 2 := norm_sq_le_officialEuclideanNorm_sq x
    _ = ∑ i : Fin 3, x i ^ 2 := officialEuclideanNorm_sq_eq_sum_sq x

/-- The inherited kinetic energy is bounded by the official Euclidean one. -/
theorem kineticEnergy_le_officialKineticEnergy
    (u : VelocityEvolution) (t : ℝ)
    (hu : AEStronglyMeasurable (u t))
    (hoff : Integrable
      (fun x => officialEuclideanNorm (u t x) ^ 2)) :
    kineticEnergy u t ≤ officialKineticEnergy u t := by
  have hcur' : Integrable (fun x => ∑ i : Fin 3, (u t x i) ^ 2) := by
    have h_eq : (fun x : Space => officialEuclideanNorm (u t x) ^ 2) =
        (fun x : Space => ∑ i : Fin 3, (u t x i) ^ 2) := by
      ext x; simp [officialEuclideanNorm_sq_eq_sum_sq (u t x)]
    simpa [h_eq] using hoff
  unfold kineticEnergy officialKineticEnergy
  exact integral_mono hcur' hoff
    (fun x => by
      simp [officialEuclideanNorm_sq_eq_sum_sq (u t x)])

/-- The official kinetic energy is at most three times the inherited one. -/
theorem officialKineticEnergy_le_three_mul_kineticEnergy
    (u : VelocityEvolution) (t : ℝ)
    (hu : AEStronglyMeasurable (u t))
    (hcur : Integrable (fun x => ‖u t x‖ ^ 2)) :
    officialKineticEnergy u t ≤ 3 * kineticEnergy u t := by
  have hoff : Integrable
      (fun x => officialEuclideanNorm (u t x) ^ 2) :=
    (integrable_norm_sq_iff_officialEuclideanNorm_sq (u t) hu).1 hcur
  have hsum : Integrable (fun x => ∑ i : Fin 3, (u t x i) ^ 2) := by
    have h_eq : (fun x : Space => officialEuclideanNorm (u t x) ^ 2) =
        (fun x : Space => ∑ i : Fin 3, (u t x i) ^ 2) := by
      ext x; simp [officialEuclideanNorm_sq_eq_sum_sq (u t x)]
    simpa [h_eq] using hoff
  unfold kineticEnergy officialKineticEnergy
  calc
    (∫ x : Space, officialEuclideanNorm (u t x) ^ 2) ≤
        ∫ x : Space, 3 * ∑ i : Fin 3, (u t x i) ^ 2 :=
      integral_mono hoff (hsum.const_mul 3)
        (fun x => by
          rw [officialEuclideanNorm_sq_eq_sum_sq (u t x)]
          have hnn : (0 : ℝ) ≤ ∑ i : Fin 3, (u t x i) ^ 2 :=
            Finset.sum_nonneg fun i _ => sq_nonneg _
          linarith)
    _ = 3 * ∫ x : Space, ∑ i : Fin 3, (u t x i) ^ 2 := by
      rw [MeasureTheory.integral_const_mul]

/-- Under slice measurability and the existing integrability clause, uniform
boundedness of the inherited and official energies is equivalent.  The bound
changes by at most the fixed dimension factor three. -/
theorem uniformlyBoundedEnergy_iff_official
    (u : VelocityEvolution)
    (hmeas : ∀ t : ℝ, 0 ≤ t → AEStronglyMeasurable (u t))
    (hint : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun x => ‖u t x‖ ^ 2)) :
    (∃ E : ℝ, 0 < E ∧
      ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E) ↔
      ∃ E : ℝ, 0 < E ∧
        ∀ t : ℝ, 0 ≤ t → officialKineticEnergy u t < E := by
  constructor
  · rintro ⟨E, hE, hbound⟩
    refine ⟨3 * E, mul_pos (by norm_num) hE, ?_⟩
    intro t ht
    exact lt_of_le_of_lt
      (officialKineticEnergy_le_three_mul_kineticEnergy
        u t (hmeas t ht) (hint t ht))
      (mul_lt_mul_of_pos_left (hbound t ht) (by norm_num))
  · rintro ⟨E, hE, hbound⟩
    refine ⟨E, hE, ?_⟩
    intro t ht
    have hoff : Integrable
        (fun x => officialEuclideanNorm (u t x) ^ 2) :=
      (integrable_norm_sq_iff_officialEuclideanNorm_sq
        (u t) (hmeas t ht)).1 (hint t ht)
    exact lt_of_le_of_lt
      (kineticEnergy_le_officialKineticEnergy
        u t (hmeas t ht) hoff)
      (hbound t ht)

end Navier.Analysis.EnergyNormBridge
