import Navier.Analysis.CriticalMildDuhamelBochner
import Navier.Analysis.PeriodicQuotientBridge
import Navier.Construction.ParametricTorusInverse

/-!
# Fourier coefficients of native smooth periodic data

This module begins the faithful bridge from the official unit-periodic datum
to the weighted lattice carrier used by the critical mild theory.  The scalar
coefficient is an actual triple unit-cube integral with the convention
`exp (-2π i k · x)`.  Smoothness and periodicity give the anisotropic decay
needed for its weighted absolute summability.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped BigOperators ContDiff

namespace Navier.Analysis.PeriodicDatumFourierBridge

open Set
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Construction

abbrev ScalarSource := ParametricTorusInverse.Source

/-- Reassociate the external coordinate and the two planar coordinates with
the official three-dimensional physical-space carrier. -/
def pointToSpace (q : ParametricTorusInverse.Point) : Space :=
  ![q.1, q.2.1, q.2.2]

theorem pointToSpace_smooth : ContDiff ℝ ∞ pointToSpace := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_fst
  · exact contDiff_fst.comp contDiff_snd
  · exact contDiff_snd.comp contDiff_snd

/-- One scalar coordinate of an official real velocity datum, complexified
after the faithful reassociation of its three physical coordinates. -/
def nativeScalarSource (u₀ : VelocityField) (i : Fin 3) : ScalarSource :=
  fun q => (u₀ (pointToSpace q) i : ℂ)

theorem nativeScalarSource_smooth {u₀ : VelocityField}
    (hu₀ : ContDiff ℝ ∞ u₀) (i : Fin 3) :
    ContDiff ℝ ∞ (nativeScalarSource u₀ i) := by
  have hi : ContDiff ℝ ∞ (fun x => u₀ x i) := contDiff_pi.mp hu₀ i
  change ContDiff ℝ ∞
    (Complex.ofRealCLM ∘ (fun x => u₀ x i) ∘ pointToSpace)
  exact Complex.ofRealCLM.contDiff.comp (hi.comp pointToSpace_smooth)

theorem planeIntegerShift_mem_integerLattice (k : ℤ × ℤ) :
    (![0, (k.1 : ℝ), (k.2 : ℝ)] : Space) ∈
      PeriodicQuotientBridge.integerLattice := by
  intro i _
  fin_cases i
  · exact ⟨0, by simp⟩
  · exact ⟨k.1, by simp⟩
  · exact ⟨k.2, by simp⟩

/-- Period one in the external coordinate as well as the two torus coordinates
carried by `ParametricTorusInverse`. -/
def UnitPeriodic3 (f : ScalarSource) : Prop :=
  ParametricTorusInverse.Periodic f ∧
    ∀ z : ℝ, ∀ Y : TorusInverse.Plane, f (z + 1, Y) = f (z, Y)

theorem nativeScalarSource_periodic {u₀ : VelocityField}
    (hu₀ : SpatiallyPeriodicDatum u₀) (i : Fin 3) :
    UnitPeriodic3 (nativeScalarSource u₀ i) := by
  constructor
  · intro p Y k
    have hinvariant := PeriodicQuotientBridge.invariant_add_integerLattice
      hu₀ (planeIntegerShift_mem_integerLattice k) (pointToSpace (p, Y))
    apply congrArg (fun v : Space => (v i : ℂ))
    convert hinvariant using 1
    ext j
    fin_cases j <;> simp [pointToSpace]
  · intro z Y
    have hperiod := hu₀ (pointToSpace (z, Y)) (0 : Fin 3)
    have hspace : pointToSpace (z + 1, Y) =
        pointToSpace (z, Y) + basisVector 0 := by
      ext j
      fin_cases j <;> simp [pointToSpace, basisVector]
    change (u₀ (pointToSpace (z + 1, Y)) i : ℂ) =
      (u₀ (pointToSpace (z, Y)) i : ℂ)
    rw [hspace]
    exact congrArg (fun v : Space => (v i : ℂ)) hperiod

/-- The actual three-dimensional unit-period Fourier coefficient.  The first
lattice coordinate is the external parameter and the last two are the
two-dimensional coefficient already proved in `SmoothFourierData`. -/
def scalarCoefficient (f : ScalarSource) (k : LatticeMode) : ℂ :=
  SmoothFourierData.unitCoeff
    (fun z => ParametricTorusInverse.coefficient f z k.2) k.1

/-- The coefficient convention is the literal nested unit-cube integral. -/
theorem scalarCoefficient_eq_tripleIntegral (f : ScalarSource) (k : LatticeMode) :
    scalarCoefficient f k =
      ∫ z in (0 : ℝ)..1,
        fourier (-k.1) (z : UnitAddCircle) *
          (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
            SmoothFourierData.kernel k.2 (x, y) * f (z, (x, y))) := by
  rw [scalarCoefficient, SmoothFourierData.unitCoeff_eq_integral]
  simp only [ParametricTorusInverse.coefficient,
    SmoothFourierData.coefficient_eq_doubleIntegral, ParametricTorusInverse.slice]

def ParameterPeriodic (f : ScalarSource) : Prop :=
  ∀ z : ℝ, ∀ Y : TorusInverse.Plane, f (z + 1, Y) = f (z, Y)

theorem parameterPartial_parameterPeriodic {f : ScalarSource}
    (hp : ParameterPeriodic f) :
    ParameterPeriodic (ParametricTorusInverse.parameterPartial f) := by
  intro z Y
  have he : (fun q : ParametricTorusInverse.Point => f (q + (1, 0))) = f := by
    funext q
    change f (q.1 + 1, q.2 + 0) = f (q.1, q.2)
    simpa only [add_zero] using hp q.1 q.2
  have hd := congrArg (fun g : ScalarSource => fderiv ℝ g (z, Y)) he
  rw [fderiv_comp_add_right] at hd
  have happ := congrArg
    (fun L : ParametricTorusInverse.Point →L[ℝ] ℂ => L (1, 0)) hd
  simpa [ParametricTorusInverse.parameterPartial] using happ

theorem parameterJet_parameterPeriodic {f : ScalarSource}
    (hp : ParameterPeriodic f) (n : ℕ) :
    ParameterPeriodic (ParametricTorusInverse.parameterJet n f) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
      rw [ParametricTorusInverse.parameterJet, Function.iterate_succ_apply']
      exact parameterPartial_parameterPeriodic ih

theorem parameterJet_periodic3 {f : ScalarSource}
    (hp : UnitPeriodic3 f) (n : ℕ) :
    UnitPeriodic3 (ParametricTorusInverse.parameterJet n f) :=
  ⟨ParametricTorusInverse.parameterJet_periodic hp.1 n,
    parameterJet_parameterPeriodic hp.2 n⟩

/-- Repeated integration by parts in the first coordinate, with the exact
unit-period frequency `2π i k₁`. -/
theorem scalarCoefficient_parameterJet {f : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic3 f)
    {k : LatticeMode} (hk : k.1 ≠ 0) (n : ℕ) :
    scalarCoefficient f k =
      (TorusInverse.omega * (k.1 : ℂ))⁻¹ ^ n *
        scalarCoefficient (ParametricTorusInverse.parameterJet n f) k := by
  induction n with
  | zero => simp [ParametricTorusInverse.parameterJet]
  | succ n ih =>
      have hd : ∀ z, HasDerivAt
          (fun q => ParametricTorusInverse.coefficient
            (ParametricTorusInverse.parameterJet n f) q k.2)
          (ParametricTorusInverse.coefficient
            (ParametricTorusInverse.parameterJet (n + 1) f) z k.2) z := by
        intro z
        convert ParametricTorusInverse.coefficient_hasDerivAt
          (ParametricTorusInverse.parameterJet_smooth hf n) k.2 z using 1
        rw [ParametricTorusInverse.parameterJet, Function.iterate_succ_apply']
        simp [ParametricTorusInverse.parameterJet]
      have hboundary : ParametricTorusInverse.coefficient
          (ParametricTorusInverse.parameterJet n f) 1 k.2 =
          ParametricTorusInverse.coefficient
            (ParametricTorusInverse.parameterJet n f) 0 k.2 := by
        have hper := congrArg
          (fun g : TorusInverse.Plane → ℂ => SmoothFourierData.coefficient g k.2)
          (funext fun Y => (parameterJet_periodic3 hp n).2 0 Y)
        change SmoothFourierData.coefficient
            (fun Y => ParametricTorusInverse.parameterJet n f (1, Y)) k.2 =
          SmoothFourierData.coefficient
            (fun Y => ParametricTorusInverse.parameterJet n f (0, Y)) k.2
        simpa only [zero_add] using hper
      have hstep : SmoothFourierData.unitCoeff
          (fun q => ParametricTorusInverse.coefficient
            (ParametricTorusInverse.parameterJet n f) q k.2) k.1 =
          (TorusInverse.omega * (k.1 : ℂ))⁻¹ *
            SmoothFourierData.unitCoeff
              (fun q => ParametricTorusInverse.coefficient
                (ParametricTorusInverse.parameterJet (n + 1) f) q k.2) k.1 :=
        SmoothFourierData.unitCoeff_of_hasDerivAt hk hd
        ((ParametricTorusInverse.coefficient_smooth
          (ParametricTorusInverse.parameterJet_smooth hf (n + 1)) k.2).continuous)
        hboundary
      rw [ih, scalarCoefficient, hstep, pow_succ, mul_assoc]
      rfl

/-- Uniform plane-frequency decay for the coefficient after any fixed number
of derivatives in the first coordinate. -/
theorem exists_parameterJet_planeBound {f : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic3 f) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Icc (0 : ℝ) 1, ∀ k : LatticeMode,
      TorusInverse.weight k.2 ^ s *
        ‖ParametricTorusInverse.coefficient
          (ParametricTorusInverse.parameterJet r f) z k.2‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := ParametricTorusInverse.exists_uniform_coefficient_bound
    (ParametricTorusInverse.parameterJet_smooth hf r)
    (ParametricTorusInverse.parameterJet_periodic hp.1 r) s 0 1
  exact ⟨C, hC, fun z hz k => hb z hz k.2⟩

/-- The first-frequency moment of the three-dimensional coefficient is
controlled jointly with any chosen plane-frequency moment. -/
theorem exists_scalarCoefficient_mixedBound {f : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic3 f) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : LatticeMode, k.1 ≠ 0 →
      |(k.1 : ℝ)| ^ r * TorusInverse.weight k.2 ^ s *
        ‖scalarCoefficient f k‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_parameterJet_planeBound hf hp r s
  refine ⟨C, hC, ?_⟩
  intro k hk
  have hunit : ‖scalarCoefficient (ParametricTorusInverse.parameterJet r f) k‖ ≤
      C / TorusInverse.weight k.2 ^ s := by
    change ‖SmoothFourierData.unitCoeff
      (fun z => ParametricTorusInverse.coefficient
        (ParametricTorusInverse.parameterJet r f) z k.2) k.1‖ ≤ _
    apply SmoothFourierData.unitCoeff_norm_le
    intro z hz
    exact (le_div_iff₀ (pow_pos (TorusInverse.weight_pos k.2) s)).2
      (by simpa [mul_comm] using hbound z hz k)
  rw [scalarCoefficient_parameterJet hf hp hk r, norm_mul, norm_pow]
  have hω : 1 ≤ ‖TorusInverse.omega‖ := SmoothFourierData.norm_omega_ge_one
  have hki : 0 < |(k.1 : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have hfactor : |(k.1 : ℝ)| ^ r *
      ‖(TorusInverse.omega * (k.1 : ℂ))⁻¹‖ ^ r ≤ 1 := by
    rw [norm_inv, norm_mul, Complex.norm_intCast, mul_inv_rev, mul_pow]
    calc
      |(k.1 : ℝ)| ^ r *
          (|(k.1 : ℝ)|⁻¹ ^ r * ‖TorusInverse.omega‖⁻¹ ^ r) =
          ‖TorusInverse.omega‖⁻¹ ^ r := by
            rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hki.ne', one_pow, one_mul]
      _ ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (norm_nonneg _))
        (inv_le_one_of_one_le₀ hω)
  have hplane : TorusInverse.weight k.2 ^ s *
      ‖scalarCoefficient (ParametricTorusInverse.parameterJet r f) k‖ ≤ C := by
    simpa [mul_comm] using
      (le_div_iff₀ (pow_pos (TorusInverse.weight_pos k.2) s)).1 hunit
  calc
    |(k.1 : ℝ)| ^ r * TorusInverse.weight k.2 ^ s *
          (‖(TorusInverse.omega * (k.1 : ℂ))⁻¹‖ ^ r *
            ‖scalarCoefficient (ParametricTorusInverse.parameterJet r f) k‖)
        = (|(k.1 : ℝ)| ^ r *
            ‖(TorusInverse.omega * (k.1 : ℂ))⁻¹‖ ^ r) *
            (TorusInverse.weight k.2 ^ s *
              ‖scalarCoefficient (ParametricTorusInverse.parameterJet r f) k‖) := by ring
    _ ≤ 1 * C := mul_le_mul hfactor hplane
      (mul_nonneg (pow_nonneg (TorusInverse.weight_pos k.2).le s) (norm_nonneg _))
      zero_le_one
    _ = C := one_mul C

/-- A version of the decay estimate that is uniform across the zero slice of
the first lattice coordinate.  The exponents `3` and `5` leave exactly the
summable losses `2` and `4` after paying for the critical lattice weight. -/
theorem exists_scalarCoefficient_productBound {f : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic3 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : LatticeMode,
      (1 + |(k.1 : ℝ)|) ^ 3 * TorusInverse.weight k.2 ^ 5 *
        ‖scalarCoefficient f k‖ ≤ C := by
  obtain ⟨C₀, hC₀, hzero⟩ := exists_parameterJet_planeBound hf hp 0 5
  obtain ⟨C₁, hC₁, hnonzero⟩ := exists_scalarCoefficient_mixedBound hf hp 3 5
  refine ⟨max C₀ (8 * C₁), hC₀.trans (le_max_left _ _), ?_⟩
  intro k
  by_cases hk : k.1 = 0
  · have hunit : ‖scalarCoefficient f k‖ ≤
        C₀ / TorusInverse.weight k.2 ^ 5 := by
      change ‖SmoothFourierData.unitCoeff
        (fun z => ParametricTorusInverse.coefficient f z k.2) k.1‖ ≤ _
      apply SmoothFourierData.unitCoeff_norm_le
      intro z hz
      exact (le_div_iff₀ (pow_pos (TorusInverse.weight_pos k.2) 5)).2
        (by simpa [ParametricTorusInverse.parameterJet, mul_comm] using hzero z hz k)
    have hplane : TorusInverse.weight k.2 ^ 5 * ‖scalarCoefficient f k‖ ≤ C₀ := by
      simpa [mul_comm] using
        (le_div_iff₀ (pow_pos (TorusInverse.weight_pos k.2) 5)).1 hunit
    rw [hk]
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, one_mul]
    exact hplane.trans (le_max_left _ _)
  · have habs : (1 : ℝ) ≤ |(k.1 : ℝ)| := by
      have hn : 1 ≤ k.1.natAbs :=
        (Nat.one_le_iff_ne_zero).2 ((Int.natAbs_ne_zero).2 hk)
      calc
        (1 : ℝ) ≤ (k.1.natAbs : ℝ) := by exact_mod_cast hn
        _ = |(k.1 : ℝ)| := by
          rw [← Int.cast_abs]
          exact congrArg (fun z : ℤ => (z : ℝ))
            (Int.natCast_natAbs k.1)
    have hone : 1 + |(k.1 : ℝ)| ≤ 2 * |(k.1 : ℝ)| := by linarith
    have hpow : (1 + |(k.1 : ℝ)|) ^ 3 ≤ 8 * |(k.1 : ℝ)| ^ 3 := by
      calc
        (1 + |(k.1 : ℝ)|) ^ 3 ≤ (2 * |(k.1 : ℝ)|) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hone 3
        _ = 8 * |(k.1 : ℝ)| ^ 3 := by ring
    calc
      (1 + |(k.1 : ℝ)|) ^ 3 * TorusInverse.weight k.2 ^ 5 *
          ‖scalarCoefficient f k‖ ≤
        (8 * |(k.1 : ℝ)| ^ 3) * TorusInverse.weight k.2 ^ 5 *
          ‖scalarCoefficient f k‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpow
                (pow_nonneg (TorusInverse.weight_pos k.2).le 5))
              (norm_nonneg _)
      _ = 8 * (|(k.1 : ℝ)| ^ 3 * TorusInverse.weight k.2 ^ 5 *
          ‖scalarCoefficient f k‖) := by ring
      _ ≤ 8 * C₁ := mul_le_mul_of_nonneg_left (hnonzero k hk) (by norm_num)
      _ ≤ max C₀ (8 * C₁) := le_max_right _ _

/-- The Hermitian Euclidean norm is bounded by the sum of the three coordinate
norms.  This elementary finite-dimensional estimate is kept local so the data
bridge does not import the continuous-frequency integration layer. -/
theorem complexEuclideanNorm_le_coordinateSum (z : ComplexSpace) :
    complexEuclideanNorm z ≤ ∑ i : Fin 3, ‖z i‖ := by
  unfold complexEuclideanNorm complexEuclideanPoint
  have hz : z = ∑ i : Fin 3, Pi.single i (z i) := by
    ext i
    simp
  conv_lhs => rw [hz, WithLp.toLp_sum]
  refine le_trans (norm_sum_le (Finset.univ)
    (fun i => WithLp.toLp 2 (Pi.single i (z i)))) ?_
  simp

/-- The critical Euclidean lattice weight is paid for by one factor from the
external integer and one factor from the two-dimensional torus weight. -/
theorem latticeModeWeight_le_productWeight (k : LatticeMode) :
    latticeModeWeight k ≤
      (1 + |(k.1 : ℝ)|) * TorusInverse.weight k.2 := by
  have hnorm := complexEuclideanNorm_le_coordinateSum
    (complexOfReal (latticeFrequency k))
  have hcoordinate : ‖complexFrequency (latticeFrequency k)‖ ≤
      |(k.1 : ℝ)| + |(k.2.1 : ℝ)| + |(k.2.2 : ℝ)| := by
    simpa [complexFrequency, latticeFrequency, complexOfReal, complexOfParts,
      complexEuclideanNorm, Complex.norm_real, Real.norm_eq_abs,
      Fin.sum_univ_succ, add_assoc] using hnorm
  unfold latticeModeWeight TorusInverse.weight
  calc
    1 + ‖complexFrequency (latticeFrequency k)‖ ≤
        1 + (|(k.1 : ℝ)| + |(k.2.1 : ℝ)| + |(k.2.2 : ℝ)|) :=
      by linarith
    _ ≤ (1 + |(k.1 : ℝ)|) *
        (1 + |(k.2.1 : ℝ)| + |(k.2.2 : ℝ)|) := by
      nlinarith [abs_nonneg (k.1 : ℝ), abs_nonneg (k.2.1 : ℝ),
        abs_nonneg (k.2.2 : ℝ)]

/-- The separable lattice tail left after the derivative loss is summable. -/
theorem summable_productWeightTail : Summable (fun k : LatticeMode =>
    ((1 + |(k.1 : ℝ)|) ^ 2)⁻¹ *
      (TorusInverse.weight k.2 ^ 4)⁻¹) := by
  exact SmoothFourierData.summable_integer_weight_inv_two.mul_of_nonneg
    SmoothFourierData.summable_weight_inv_four
    (fun _ => inv_nonneg.mpr (pow_nonneg (by positivity) 2))
    (fun _ => inv_nonneg.mpr (pow_nonneg (TorusInverse.weight_pos _).le 4))

/-- Every smooth unit-periodic scalar datum has the exact weighted `ℓ¹`
coefficient summability required by the critical mild lattice layer. -/
theorem summable_weighted_scalarCoefficient {f : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic3 f) :
    Summable (fun k : LatticeMode =>
      latticeModeWeight k * ‖scalarCoefficient f k‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_scalarCoefficient_productBound hf hp
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight k)) (norm_nonneg _)) _
    (summable_productWeightTail.mul_left C)
  intro k
  have hdenom : 0 <
      (1 + |(k.1 : ℝ)|) ^ 2 * TorusInverse.weight k.2 ^ 4 :=
    mul_pos (pow_pos (by positivity) 2)
      (pow_pos (TorusInverse.weight_pos k.2) 4)
  have hquot : latticeModeWeight k * ‖scalarCoefficient f k‖ ≤
      C / ((1 + |(k.1 : ℝ)|) ^ 2 * TorusInverse.weight k.2 ^ 4) := by
    apply (le_div_iff₀ hdenom).2
    calc
      (latticeModeWeight k * ‖scalarCoefficient f k‖) *
          ((1 + |(k.1 : ℝ)|) ^ 2 * TorusInverse.weight k.2 ^ 4) ≤
        (((1 + |(k.1 : ℝ)|) * TorusInverse.weight k.2) *
          ‖scalarCoefficient f k‖) *
          ((1 + |(k.1 : ℝ)|) ^ 2 * TorusInverse.weight k.2 ^ 4) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (latticeModeWeight_le_productWeight k)
                (norm_nonneg _)) hdenom.le
      _ = (1 + |(k.1 : ℝ)|) ^ 3 * TorusInverse.weight k.2 ^ 5 *
          ‖scalarCoefficient f k‖ := by ring
      _ ≤ C := hbound k
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm] using hquot

/-- The actual vector Fourier coefficient of an official velocity datum, with
the same `exp (-2π i k · x)` convention in every component. -/
def nativeCoefficient (u₀ : VelocityField) (k : LatticeMode) : ComplexSpace :=
  fun i => scalarCoefficient (nativeScalarSource u₀ i) k

@[simp] theorem nativeCoefficient_apply (u₀ : VelocityField)
    (k : LatticeMode) (i : Fin 3) :
    nativeCoefficient u₀ k i = scalarCoefficient (nativeScalarSource u₀ i) k :=
  rfl

/-- The official smooth periodic datum is an actual consumer of the Fourier
decay bridge: its coefficient sequence satisfies the critical mild layer's
weighted `ℓ¹` contract. -/
theorem periodicInitialDatum_latticeWeightedL1 {u₀ : VelocityField}
    (hu₀ : PeriodicInitialDatum u₀) :
    LatticeWeightedL1 (nativeCoefficient u₀) := by
  have hcoordinate (i : Fin 3) : Summable (fun k : LatticeMode =>
      latticeModeWeight k * ‖scalarCoefficient (nativeScalarSource u₀ i) k‖) :=
    summable_weighted_scalarCoefficient
      (nativeScalarSource_smooth hu₀.1 i)
      (nativeScalarSource_periodic hu₀.2.2 i)
  have hmajor : Summable (fun k : LatticeMode =>
      ∑ i : Fin 3,
        latticeModeWeight k * ‖scalarCoefficient (nativeScalarSource u₀ i) k‖) := by
    simpa [Fin.sum_univ_succ] using
      (hcoordinate (0 : Fin 3)).add
        ((hcoordinate (1 : Fin 3)).add (hcoordinate (2 : Fin 3)))
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight k)) (norm_nonneg _)) _ hmajor
  intro k
  calc
    latticeModeWeight k * complexEuclideanNorm (nativeCoefficient u₀ k) ≤
        latticeModeWeight k * ∑ i : Fin 3, ‖nativeCoefficient u₀ k i‖ :=
      mul_le_mul_of_nonneg_left
        (complexEuclideanNorm_le_coordinateSum (nativeCoefficient u₀ k))
        (zero_le_one.trans (one_le_latticeModeWeight k))
    _ = ∑ i : Fin 3,
        latticeModeWeight k * ‖scalarCoefficient (nativeScalarSource u₀ i) k‖ := by
      rw [Finset.mul_sum]
      rfl

end Navier.Analysis.PeriodicDatumFourierBridge
