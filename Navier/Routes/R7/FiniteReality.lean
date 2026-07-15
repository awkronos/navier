import Navier.Routes.R7.FiniteAmplitudeDynamics

/-!
# Reality compatibility of the finite Fourier-amplitude RHS

For the convention `u(x) = ∑ₖ a(k) exp(I * k · x)`, a real-valued field has
the amplitude relation

`a(-q) = conj(a(q))`.

This file proves that the exact finite viscous amplitude RHS respects this
relation whenever its finite support is centrally symmetric.  The crucial
ordered identity includes both sign changes: conjugation sends the derivative
factor `I` to `-I`, while the reindexing `(k,l) ↦ (-k,-l)` negates the
derivative wave.  Those signs cancel, so the ordered convection coefficient,
its finite convolution sum, Leray projection, viscosity term, and full RHS all
have the correct reality compatibility.

This remains finite frequencywise algebra.  It does not construct a real
Fourier series, solve a finite-dimensional ODE, establish consistency between
generations, or prove any infinite-support or cascade statement.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Routes.R7

open Navier.Analysis.ComplexLerayProjection

/-- Coordinatewise complex conjugation of a complex three-vector. -/
def coordinateConjugate (z : ComplexSpace) : ComplexSpace :=
  fun i => starRingEnd ℂ (z i)

/-- Exact Fourier reality condition `a(-q) = conj(a(q))`. -/
def AmplitudeReality (a : Space → ComplexSpace) : Prop :=
  ∀ q, a (-q) = coordinateConjugate (a q)

@[simp] theorem coordinateConjugate_apply (z : ComplexSpace) (i : Fin 3) :
    coordinateConjugate z i = starRingEnd ℂ (z i) :=
  rfl

/-- Coordinate conjugation fixes the zero vector. -/
@[simp] theorem coordinateConjugate_zero :
    coordinateConjugate 0 = 0 := by
  ext i
  simp [coordinateConjugate]

/-- Coordinate conjugation preserves addition. -/
theorem coordinateConjugate_add (z w : ComplexSpace) :
    coordinateConjugate (z + w) =
      coordinateConjugate z + coordinateConjugate w := by
  ext i
  simp [coordinateConjugate]

/-- Coordinate conjugation preserves additive negation. -/
theorem coordinateConjugate_neg (z : ComplexSpace) :
    coordinateConjugate (-z) = -coordinateConjugate z := by
  ext i
  simp [coordinateConjugate]

/-- Coordinate conjugation conjugates a complex scalar multiplier. -/
theorem coordinateConjugate_smul (c : ℂ) (z : ComplexSpace) :
    coordinateConjugate (c • z) =
      (starRingEnd ℂ c) • coordinateConjugate z := by
  ext i
  simp [coordinateConjugate]

/-- Coordinate conjugation is involutive. -/
@[simp] theorem coordinateConjugate_involutive (z : ComplexSpace) :
    coordinateConjugate (coordinateConjugate z) = z := by
  ext i
  simp [coordinateConjugate]

/-- The route-local conjugation is the checked complex-Leray conjugation. -/
theorem coordinateConjugate_eq_complexConjugate (z : ComplexSpace) :
    coordinateConjugate z = complexConjugate z :=
  rfl

/-- A real wavevector may be moved through coordinate conjugation in the
complex bilinear wave pairing. -/
theorem complexWaveDot_coordinateConjugate
    (q : Space) (z : ComplexSpace) :
    complexWaveDot q (coordinateConjugate z) =
      starRingEnd ℂ (complexWaveDot q z) := by
  simp [complexWaveDot, complexBilinearDot, complexifiedWave,
    coordinateConjugate, map_sum]

/-- The real normalized Leray symbol is even in its frequency. -/
theorem normalizedLeraySymbol_neg_frequency (q v : Space) :
    normalizedLeraySymbol (-q) v = normalizedLeraySymbol q v := by
  ext i
  simp [normalizedLeraySymbol, dotProduct]
  ring

/-- The complex Leray symbol is even in its real frequency. -/
theorem complexLeray_neg_frequency (q : Space) (z : ComplexSpace) :
    complexLeray (-q) z = complexLeray q z := by
  ext i
  simp [complexLeray, complexOfParts, normalizedLeraySymbol_neg_frequency]

/-- Negating the real frequency and conjugating the amplitude commute with
the complex Leray projection. -/
theorem complexLeray_neg_coordinateConjugate
    (q : Space) (z : ComplexSpace) :
    complexLeray (-q) (coordinateConjugate z) =
      coordinateConjugate (complexLeray q z) := by
  rw [complexLeray_neg_frequency,
    coordinateConjugate_eq_complexConjugate,
    complexLeray_conjugate]
  rfl

/-- The sign from conjugating the Fourier derivative factor is exactly
cancelled by negating the derivative frequency. -/
theorem orderedConvectionCoefficient_neg_coordinateConjugate
    (l : Space) (u v : ComplexSpace) :
    orderedConvectionCoefficient (-l)
        (coordinateConjugate u) (coordinateConjugate v) =
      coordinateConjugate (orderedConvectionCoefficient l u v) := by
  rw [orderedConvectionCoefficient, orderedConvectionCoefficient,
    complexWaveDot_neg_wave, complexWaveDot_coordinateConjugate,
    coordinateConjugate_smul]
  ext i
  simp

/-- Membership in a centrally symmetric support is invariant under negation. -/
theorem mem_support_neg_iff
    {support : Finset Space} (hS : CentrallySymmetricSupport support)
    (q : Space) :
    -q ∈ support ↔ q ∈ support := by
  constructor
  · intro hnq
    have h := hS (-q) hnq
    simpa using h
  · exact hS q

private def negPairEquiv : Space × Space ≃ Space × Space where
  toFun p := (-p.1, -p.2)
  invFun p := (-p.1, -p.2)
  left_inv p := by simp
  right_inv p := by simp

@[simp] private theorem negPairEquiv_apply (p : Space × Space) :
    negPairEquiv p = (-p.1, -p.2) :=
  rfl

private theorem mem_product_negPairEquiv_iff
    {support : Finset Space} (hS : CentrallySymmetricSupport support)
    (p : Space × Space) :
    p ∈ support ×ˢ support ↔ negPairEquiv p ∈ support ×ˢ support := by
  rw [Finset.mem_product, Finset.mem_product]
  change (p.1 ∈ support ∧ p.2 ∈ support) ↔
    (-p.1 ∈ support ∧ -p.2 ∈ support)
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨hS p.1 h₁, hS p.2 h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨(mem_support_neg_iff hS p.1).1 h₁,
      (mem_support_neg_iff hS p.2).1 h₂⟩

/-- Simultaneously negating an ordered pair reverses its selected output. -/
theorem pairSumsToOutput_neg_iff (k l q : Space) :
    PairSumsToOutput (-k) (-l) q ↔ PairSumsToOutput k l (-q) := by
  unfold PairSumsToOutput
  constructor
  · intro h
    calc
      k + l = -(-k + -l) := by abel
      _ = -q := by rw [h]
  · intro h
    calc
      -k + -l = -(k + l) := by abel
      _ = -(-q) := by rw [h]
      _ = q := by simp

private def finiteConvectionTerm
    (a : Space → ComplexSpace) (q : Space)
    (p : Space × Space) : ComplexSpace := by
  classical
  exact
    if PairSumsToOutput p.1 p.2 q then
      orderedConvectionCoefficient p.2 (a p.1) (a p.2)
    else 0

private theorem finiteConvectionCoefficient_eq_product_sum
    (support : Finset Space) (a : Space → ComplexSpace) (q : Space) :
    finiteConvectionCoefficient support a q =
      ∑ p ∈ support ×ˢ support, finiteConvectionTerm a q p := by
  classical
  unfold finiteConvectionCoefficient
  simpa [finiteConvectionTerm] using
    (Finset.sum_product' support support
      (fun k l =>
        if PairSumsToOutput k l q then
          orderedConvectionCoefficient l (a k) (a l)
        else 0)).symm

/-- Coordinate conjugation commutes with a finite vector sum. -/
theorem coordinateConjugate_sum
    {ι : Type*} (s : Finset ι) (f : ι → ComplexSpace) :
    coordinateConjugate (∑ x ∈ s, f x) =
      ∑ x ∈ s, coordinateConjugate (f x) := by
  ext i
  simp [coordinateConjugate, map_sum]

private theorem finiteConvectionTerm_neg_output
    {a : Space → ComplexSpace} (hreal : AmplitudeReality a)
    (q : Space) (p : Space × Space) :
    finiteConvectionTerm a (-q) p =
      coordinateConjugate (finiteConvectionTerm a q (negPairEquiv p)) := by
  classical
  by_cases hsum : PairSumsToOutput p.1 p.2 (-q)
  · have hsumNeg : PairSumsToOutput (-p.1) (-p.2) q :=
      (pairSumsToOutput_neg_iff p.1 p.2 q).2 hsum
    simp only [finiteConvectionTerm, negPairEquiv_apply,
      hsum, hsumNeg, if_true]
    rw [hreal p.1, hreal p.2,
      orderedConvectionCoefficient_neg_coordinateConjugate,
      coordinateConjugate_involutive]
  · have hsumNeg : ¬ PairSumsToOutput (-p.1) (-p.2) q := by
      intro h
      exact hsum ((pairSumsToOutput_neg_iff p.1 p.2 q).1 h)
    simp [finiteConvectionTerm, negPairEquiv_apply, hsum, hsumNeg]

/-- On a centrally symmetric support, the exact unprojected finite convection
coefficient at `-q` is the conjugate of the coefficient at `q`. -/
theorem finiteConvectionCoefficient_neg_output
    {support : Finset Space} {a : Space → ComplexSpace}
    (hS : CentrallySymmetricSupport support)
    (hreal : AmplitudeReality a) (q : Space) :
    finiteConvectionCoefficient support a (-q) =
      coordinateConjugate (finiteConvectionCoefficient support a q) := by
  classical
  rw [finiteConvectionCoefficient_eq_product_sum,
    finiteConvectionCoefficient_eq_product_sum,
    coordinateConjugate_sum]
  apply Finset.sum_equiv negPairEquiv
  · exact mem_product_negPairEquiv_iff hS
  · intro p hp
    exact finiteConvectionTerm_neg_output hreal q p

/-- Leray projection preserves the finite convolution reality identity. -/
theorem projectedFiniteConvectionCoefficient_neg_output
    {support : Finset Space} {a : Space → ComplexSpace}
    (hS : CentrallySymmetricSupport support)
    (hreal : AmplitudeReality a) (q : Space) :
    projectedFiniteConvectionCoefficient support a (-q) =
      coordinateConjugate
        (projectedFiniteConvectionCoefficient support a q) := by
  unfold projectedFiniteConvectionCoefficient
  rw [finiteConvectionCoefficient_neg_output hS hreal,
    complexLeray_neg_coordinateConjugate]

/-- Squared frequency is even. -/
@[simp] theorem squaredFrequency_neg (q : Space) :
    squaredFrequency (-q) = squaredFrequency q := by
  simp [squaredFrequency, dotProduct]

/-- The viscosity multiplier is even in frequency. -/
@[simp] theorem viscosityMultiplier_neg_frequency (ν : ℝ) (q : Space) :
    viscosityMultiplier ν (-q) = viscosityMultiplier ν q := by
  simp [viscosityMultiplier]

/-- The viscosity multiplier is real and hence fixed by conjugation. -/
@[simp] theorem viscosityMultiplier_conjugate (ν : ℝ) (q : Space) :
    starRingEnd ℂ (viscosityMultiplier ν q) = viscosityMultiplier ν q := by
  simp [viscosityMultiplier]

/-- The linear viscous RHS preserves amplitude reality. -/
theorem viscousLinearRHS_neg_output
    {ν : ℝ} {a : Space → ComplexSpace}
    (hreal : AmplitudeReality a) (q : Space) :
    viscousLinearRHS ν a (-q) =
      coordinateConjugate (viscousLinearRHS ν a q) := by
  rw [viscousLinearRHS, viscousLinearRHS,
    viscosityMultiplier_neg_frequency, hreal q,
    coordinateConjugate_smul, viscosityMultiplier_conjugate]

/-- The negative projected nonlinear RHS preserves amplitude reality on a
centrally symmetric finite support. -/
theorem finiteProjectedNonlinearRHS_neg_output
    {support : Finset Space} {a : Space → ComplexSpace}
    (hS : CentrallySymmetricSupport support)
    (hreal : AmplitudeReality a) (q : Space) :
    finiteProjectedNonlinearRHS support a (-q) =
      coordinateConjugate (finiteProjectedNonlinearRHS support a q) := by
  unfold finiteProjectedNonlinearRHS
  rw [projectedFiniteConvectionCoefficient_neg_output hS hreal]
  exact (coordinateConjugate_neg _).symm

/-- The full finite viscous amplitude RHS has the correct conjugation identity
at the negated output frequency. -/
theorem finiteAmplitudeRHS_neg_output
    {ν : ℝ} {support : Finset Space} {a : Space → ComplexSpace}
    (hS : CentrallySymmetricSupport support)
    (hreal : AmplitudeReality a) (q : Space) :
    finiteAmplitudeRHS ν support a (-q) =
      coordinateConjugate (finiteAmplitudeRHS ν support a q) := by
  unfold finiteAmplitudeRHS
  rw [viscousLinearRHS_neg_output hreal,
    finiteProjectedNonlinearRHS_neg_output hS hreal,
    coordinateConjugate_add]

/-- The full finite amplitude RHS preserves the exact Fourier reality
condition on every centrally symmetric finite support. -/
theorem finiteAmplitudeRHS_preserves_reality
    {ν : ℝ} {support : Finset Space} {a : Space → ComplexSpace}
    (hS : CentrallySymmetricSupport support)
    (hreal : AmplitudeReality a) :
    AmplitudeReality (finiteAmplitudeRHS ν support a) :=
  finiteAmplitudeRHS_neg_output hS hreal

/-- Every recursively generated R7 support is centrally symmetric, so its
finite amplitude RHS preserves the reality condition. -/
theorem generatedSupport_finiteAmplitudeRHS_preserves_reality
    {ν s : ℝ} {n : ℕ} {a : Space → ComplexSpace}
    (hreal : AmplitudeReality a) :
    AmplitudeReality (finiteAmplitudeRHS ν (generatedSupport s n) a) :=
  finiteAmplitudeRHS_preserves_reality
    (generatedSupport_centrallySymmetric s n) hreal

end Navier.Routes.R7
