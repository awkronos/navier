import Navier.Problem

/-!
# Algebraic Navier--Stokes scaling coordinates

This file formalizes only the scalar arithmetic behind the mixed-norm scaling
exponent

`1 - 3 / p - 2 / q`

and its critical line `2 / q + 3 / p = 1`.  It does **not** assert that any
Bochner, Lorentz, weak, endpoint, or mixed Lebesgue norm has been constructed
or proved to scale by this exponent; that analytic statement requires separate
measure-theoretic work.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Scaling

/-- The algebraic homogeneity exponent associated with a spatial `L^p` and
temporal `L^q` mixed norm under Navier--Stokes parabolic scaling. -/
def mixedNormExponent (p q : ℝ) : ℝ := 1 - 3 / p - 2 / q

/-- The Serrin critical-line equation in finite real exponent coordinates. -/
def CriticalLine (p q : ℝ) : Prop := 2 / q + 3 / p = 1

/-- Vanishing of the algebraic scaling exponent is exactly the critical-line
equation.  This is pure field arithmetic and carries no analytic norm claim. -/
theorem mixedNormExponent_eq_zero_iff (p q : ℝ) :
    mixedNormExponent p q = 0 ↔ CriticalLine p q := by
  simp only [mixedNormExponent, CriticalLine]
  constructor <;> intro h <;> linarith

/-- The canonical finite Serrin pair `(p,q) = (6,4)` lies on the critical
line. -/
theorem criticalLine_six_four : CriticalLine 6 4 := by
  norm_num [CriticalLine]

/-- The finite pair `(p,q) = (9,3)` is another exact point on the critical
line. -/
theorem criticalLine_nine_three : CriticalLine 9 3 := by
  norm_num [CriticalLine]

/-- Reciprocal exponent coordinates avoid pretending that `infinity` is a
real number: `spatialReciprocal = 1/p` and `timeReciprocal = 1/q`. -/
def ReciprocalCriticalLine (spatialReciprocal timeReciprocal : ℝ) : Prop :=
  3 * spatialReciprocal + 2 * timeReciprocal = 1

/-- The same homogeneity exponent written in reciprocal coordinates. -/
def reciprocalMixedNormExponent
    (spatialReciprocal timeReciprocal : ℝ) : ℝ :=
  1 - 3 * spatialReciprocal - 2 * timeReciprocal

/-- Vanishing in reciprocal coordinates is exactly the reciprocal critical
line. -/
theorem reciprocalMixedNormExponent_eq_zero_iff (a b : ℝ) :
    reciprocalMixedNormExponent a b = 0 ↔ ReciprocalCriticalLine a b := by
  simp only [reciprocalMixedNormExponent, ReciprocalCriticalLine]
  constructor <;> intro h <;> linarith

/-- The formal reciprocal coordinates for `(p,q) = (3,infinity)` are
`(1/3,0)`.  This theorem is arithmetic only; it does not construct `L^infinity`
or an endpoint mixed norm. -/
theorem reciprocalCriticalLine_three_infinity :
    ReciprocalCriticalLine (1 / 3) 0 := by
  norm_num [ReciprocalCriticalLine]

/-- The formal reciprocal coordinates for `(p,q) = (infinity,2)` are
`(0,1/2)`. -/
theorem reciprocalCriticalLine_infinity_two :
    ReciprocalCriticalLine 0 (1 / 2) := by
  norm_num [ReciprocalCriticalLine]

end Navier.Scaling
