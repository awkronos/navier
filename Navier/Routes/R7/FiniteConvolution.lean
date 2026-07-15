import Navier.Routes.R7.GeneratedSupport
import Navier.Analysis.ComplexLerayProjection

/-!
# Exact finite complex Fourier convection algebra

Fix the Fourier convention

`u(x) = ∑ₖ a(k) exp(I * k · x)`.

When the derivative falls on the second factor in `(u · ∇)u`, the ordered
pair `(k,l)` contributes `I * (l · a(k))` times `a(l)` at output `k+l`.
The dot product here is complex bilinear: it contains no conjugation.  This
file sums those contributions over an explicit finite support and then applies
the checked complex Leray symbol at the output frequency.

This is finite frequencywise algebra only.  It does not define an infinite
Fourier series, an amplitude ODE, a conjugate-symmetric real field, an energy
identity, shell summability, or cascade exclusion.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Routes.R7

open Navier.Analysis.ComplexLerayProjection

/-- Complex bilinear coordinate dot product, with no conjugation. -/
def complexBilinearDot (z w : ComplexSpace) : ℂ :=
  ∑ i, z i * w i

/-- Coordinatewise complexification of a real wavevector. -/
def complexifiedWave (k : Space) : ComplexSpace :=
  fun i => (k i : ℂ)

/-- Complex bilinear pairing of a real wavevector with a complex amplitude. -/
def complexWaveDot (k : Space) (z : ComplexSpace) : ℂ :=
  complexBilinearDot (complexifiedWave k) z

/-- The complex bilinear dot product is additive in its first input. -/
theorem complexBilinearDot_add_left (z₁ z₂ w : ComplexSpace) :
    complexBilinearDot (z₁ + z₂) w =
      complexBilinearDot z₁ w + complexBilinearDot z₂ w := by
  simp [complexBilinearDot, add_mul, Finset.sum_add_distrib]

/-- The complex bilinear dot product is additive in its second input. -/
theorem complexBilinearDot_add_right (z w₁ w₂ : ComplexSpace) :
    complexBilinearDot z (w₁ + w₂) =
      complexBilinearDot z w₁ + complexBilinearDot z w₂ := by
  simp [complexBilinearDot, mul_add, Finset.sum_add_distrib]

/-- The complex bilinear dot product is homogeneous in its first input. -/
theorem complexBilinearDot_smul_left
    (c : ℂ) (z w : ComplexSpace) :
    complexBilinearDot (c • z) w = c * complexBilinearDot z w := by
  simp [complexBilinearDot, Finset.mul_sum, mul_assoc]

/-- The complex bilinear dot product is homogeneous in its second input. -/
theorem complexBilinearDot_smul_right
    (c : ℂ) (z w : ComplexSpace) :
    complexBilinearDot z (c • w) = c * complexBilinearDot z w := by
  simp [complexBilinearDot, Finset.mul_sum, mul_left_comm]

/-- The wave-amplitude pairing is additive in the amplitude. -/
theorem complexWaveDot_add (k : Space) (z w : ComplexSpace) :
    complexWaveDot k (z + w) = complexWaveDot k z + complexWaveDot k w :=
  complexBilinearDot_add_right _ _ _

/-- The wave-amplitude pairing is complex homogeneous in the amplitude. -/
theorem complexWaveDot_smul (k : Space) (c : ℂ) (z : ComplexSpace) :
    complexWaveDot k (c • z) = c * complexWaveDot k z :=
  complexBilinearDot_smul_right _ _ _

/-- Ordered convection contribution.  `derivativeWave` is the frequency of
the differentiated (`advected`) factor, so the explicit derivative multiplier
is `Complex.I`. -/
def orderedConvectionCoefficient
    (derivativeWave : Space)
    (advecting advected : ComplexSpace) : ComplexSpace :=
  (Complex.I * complexWaveDot derivativeWave advecting) • advected

/-- The ordered contribution is additive in the advecting amplitude. -/
theorem orderedConvectionCoefficient_add_advecting
    (l : Space) (u v w : ComplexSpace) :
    orderedConvectionCoefficient l (u + v) w =
      orderedConvectionCoefficient l u w +
        orderedConvectionCoefficient l v w := by
  simp [orderedConvectionCoefficient, complexWaveDot_add, mul_add, add_smul]

/-- The ordered contribution is additive in the advected amplitude. -/
theorem orderedConvectionCoefficient_add_advected
    (l : Space) (u v w : ComplexSpace) :
    orderedConvectionCoefficient l u (v + w) =
      orderedConvectionCoefficient l u v +
        orderedConvectionCoefficient l u w := by
  simp [orderedConvectionCoefficient, smul_add]

/-- The ordered contribution is homogeneous in the advecting amplitude. -/
theorem orderedConvectionCoefficient_smul_advecting
    (l : Space) (c : ℂ) (u v : ComplexSpace) :
    orderedConvectionCoefficient l (c • u) v =
      c • orderedConvectionCoefficient l u v := by
  simp [orderedConvectionCoefficient, complexWaveDot_smul,
    smul_smul, mul_left_comm]

/-- The ordered contribution is homogeneous in the advected amplitude. -/
theorem orderedConvectionCoefficient_smul_advected
    (l : Space) (c : ℂ) (u v : ComplexSpace) :
    orderedConvectionCoefficient l u (c • v) =
      c • orderedConvectionCoefficient l u v := by
  simp [orderedConvectionCoefficient, smul_smul, mul_comm]

/-- Selection predicate for an ordered pair contributing to output `q`. -/
def PairSumsToOutput (k l q : Space) : Prop :=
  k + l = q

/-- Exact finite coefficient of `(u · ∇)u` at output frequency `q`, before
Leray projection, under the Fourier convention stated above. -/
def finiteConvectionCoefficient
    (support : Finset Space) (a : Space → ComplexSpace)
    (q : Space) : ComplexSpace := by
  classical
  exact
    ∑ k ∈ support, ∑ l ∈ support,
      if PairSumsToOutput k l q then
        orderedConvectionCoefficient l (a k) (a l)
      else 0

/-- The exact finite convection coefficient after frequencywise Leray
projection at its output frequency. -/
def projectedFiniteConvectionCoefficient
    (support : Finset Space) (a : Space → ComplexSpace)
    (q : Space) : ComplexSpace :=
  complexLeray q (finiteConvectionCoefficient support a q)

/-- Two occupied frequencies place their sum in the pairwise Minkowski sum. -/
theorem add_mem_pairwiseMinkowskiSum
    {support : Finset Space} {k l : Space}
    (hk : k ∈ support) (hl : l ∈ support) :
    k + l ∈ pairwiseMinkowskiSum support := by
  classical
  rw [pairwiseMinkowskiSum, Finset.mem_image]
  exact ⟨(k, l), by simpa using And.intro hk hl, rfl⟩

/-- The unprojected coefficient vanishes outside the exact pairwise
Minkowski support. -/
theorem finiteConvectionCoefficient_eq_zero_of_not_mem_pairwiseMinkowskiSum
    {support : Finset Space} {a : Space → ComplexSpace} {q : Space}
    (hq : q ∉ pairwiseMinkowskiSum support) :
    finiteConvectionCoefficient support a q = 0 := by
  classical
  unfold finiteConvectionCoefficient
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  have hne : ¬ PairSumsToOutput k l q := by
    intro hsum
    apply hq
    rw [← hsum]
    exact add_mem_pairwiseMinkowskiSum hk hl
  simp [hne]

/-- Leray projection preserves the zero coefficient outside the exact
pairwise Minkowski support. -/
theorem projectedFiniteConvectionCoefficient_eq_zero_of_not_mem_pairwiseMinkowskiSum
    {support : Finset Space} {a : Space → ComplexSpace} {q : Space}
    (hq : q ∉ pairwiseMinkowskiSum support) :
    projectedFiniteConvectionCoefficient support a q = 0 := by
  unfold projectedFiniteConvectionCoefficient
  rw [finiteConvectionCoefficient_eq_zero_of_not_mem_pairwiseMinkowskiSum hq]
  exact map_zero (complexLeray q)

/-- The projected finite coefficient has zero complex bilinear divergence at
its output frequency. -/
theorem projectedFiniteConvectionCoefficient_divergence
    (support : Finset Space) (a : Space → ComplexSpace) (q : Space) :
    complexWaveDot q (projectedFiniteConvectionCoefficient support a q) = 0 := by
  unfold projectedFiniteConvectionCoefficient
  simpa [complexWaveDot, complexBilinearDot, complexifiedWave] using
    complexLeray_transverse q (finiteConvectionCoefficient support a q)

/-- Applying the same frequencywise Leray projection again leaves the
projected finite coefficient unchanged. -/
theorem projectedFiniteConvectionCoefficient_already_projected
    (support : Finset Space) (a : Space → ComplexSpace) (q : Space) :
    complexLeray q (projectedFiniteConvectionCoefficient support a q) =
      projectedFiniteConvectionCoefficient support a q := by
  unfold projectedFiniteConvectionCoefficient
  exact complexLeray_idempotent q _

end Navier.Routes.R7
