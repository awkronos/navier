import Navier.Analysis.HorizonFreeBudgetRestart
import Navier.Analysis.WienerReality
import Navier.Analysis.WienerDatumSmooth
import Navier.Analysis.ContinuousLeiLinPressurePhysical
import Navier.Analysis.LittlewoodPaleyBlock
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# L¹ Fourier-inversion uniqueness for the `Rep`/`physOf` carrier, and the
# `h3EnvelopeControl` non-top exhibit

This module closes the *named* open boundary recorded in the header of
`Navier.Analysis.HorizonFreeBudgetRestart` (§Nondegeneracy): the `< ⊤`
exhibit for the envelope control was blocked on the a.e.-uniqueness of the
Wiener profile recovered by the repo's pointwise `𝓕⁻` route
(`physOf`-injectivity on representers).

**Theorem 1 (uniqueness core).**  `ae_eq_zero_of_fourierInv_eq_zero`: an
`L¹` frequency profile whose pointwise inverse Fourier field vanishes
*everywhere* vanishes almost everywhere.  The proof is the measure-determining
test-function route: Mathlib's `ae_eq_zero_of_integral_contDiff_smul_eq_zero`
against smooth compactly supported real tests, where each test integral is
swapped by the repo's own `L¹`-level self-adjointness of `𝓕⁻`
(`integral_fourierInv_pairing`, `ContinuousLeiLinPressurePhysical`) and
returned by Fourier inversion on the Schwartz representative of the test.  No
`𝓕`/`𝓕'` distribution duality and no Schwartz–Schwartz integral is needed —
the boundary note's "no directly applicable form" obstruction was about the
wrong pairing, not about the carrier.

**Theorem 2 (`physOf`-injectivity).**  `rep_component_ae_eq`: two
representers `Rep v a`, `Rep v b` of the same slice agree a.e., component by
component (bundled: `rep_ae_eq`).  `WDatum.sym` makes each `𝓕⁻ (a·i)`
real-valued pointwise (`fourierInv_conj`); the `Rep.eq` fields then pin the
(real) values against each other on `range euclidPoint`,
`euclidPoint_surjective` lifts them to all of `ES`, and Theorem 1 applied to
`a·i − b·i` finishes.

**Theorem 3 (budget collapse).**  `h3EnvelopeBudget_eq_iSup`: for a
representable slice, the envelope budget — the supremum over *all*
representers — is exactly the weight `⨆ i, h3F (a·i)` of any *fixed*
representer `a`.  Its `≤` half is precisely Theorem 2.

**Theorem 4 (the exhibit).**  `exists_h3EnvelopeControl_lt_top` and the
strengthened sandwich `exists_h3EnvelopeControl_pos_lt_top`, witnessed by the
concrete transverse, Hermitian, compactly supported frequency profile `prof`
(§4): `a(ξ) = 1_{‖ξ‖<2} · (iξ₂, −iξ₁, 0)` (repository coordinate order),
whose physical field `u = fun _ => physOf prof` has
`0 < h3EnvelopeControl 1 u < ⊤`.
Caveat carried here, in the style of `bkmVorticityControl_nondegenerate`:
the witness lives at the FUNCTIONAL level; it is not asserted to be a
`SolvesBefore` member.

With the exhibit landed, `crown_from_envelopeApriori` leaves the whole-space
crown on its single hard premise `APrioriIn RegularOnCompacts
h3EnvelopeControl`; the `≢⊤` audit flag is discharged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate BigOperators SchwartzMap

namespace Navier.Analysis.EnvelopeFourierUniqueness

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.WienerSobolevL1
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerReality
open Navier.Analysis.WienerDatumSmooth
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.HorizonFreeBudgetRestart
open Navier.Analysis.LittlewoodPaleyBlock (euclidPoint_surjective)

/-! ## 1. The inversion core -/

/-- Pointwise subtraction of `𝓕⁻` at the bare-function level (the `L1C`
version `fourierInv_sub` transports through `Integrable.coeFn_toL1`; this
form avoids the class machinery entirely). -/
theorem fourierInv_sub_apply {f g : ES → ℂ} (hf : Integrable f) (hg : Integrable g)
    (x : ES) : 𝓕⁻ (fun ξ => f ξ - g ξ) x = 𝓕⁻ f x - 𝓕⁻ g x := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, Real.fourierInv_eq,
    ← integral_sub (integrable_fourierChar_smul hf x) (integrable_fourierChar_smul hg x)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_sub]

/-- A smooth compactly supported real test function, as a Schwartz map:
`(fun x => (g x : ℂ)) ∈ 𝓢(ES, ℂ)` with pointwise value `(g x : ℂ)` — the
packaging of `FourierL2Agree` (`hsupp.comp_left Complex.ofReal_zero`). -/
private def toSchwartzOfReal {g : ES → ℝ} (hg : HasCompactSupport g)
    (hC : ContDiff ℝ ∞ g) : 𝓢(ES, ℂ) :=
  (hg.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hC)

private theorem coe_toSchwartzOfReal {g : ES → ℝ} (hg : HasCompactSupport g)
    (hC : ContDiff ℝ ∞ g) (x : ES) : toSchwartzOfReal hg hC x = (g x : ℂ) := rfl

/-- **The L¹ Fourier-inversion uniqueness core.**  An integrable frequency
profile whose pointwise inverse Fourier field vanishes everywhere is itself
vanishing almost everywhere. -/
theorem ae_eq_zero_of_fourierInv_eq_zero {f : ES → ℂ} (hf : Integrable f)
    (h₀ : ∀ x : ES, 𝓕⁻ f x = 0) : f =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable ?_
  intro g gC gS
  set φ : 𝓢(ES, ℂ) := toSchwartzOfReal gS gC with hφ
  have hfi : Integrable (𝓕 ⇑φ) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 φ).integrable
  have hinv : 𝓕⁻ (𝓕 ⇑φ) = ⇑φ :=
    Continuous.fourierInv_fourier_eq φ.continuous φ.integrable hfi
  calc ∫ x, g x • f x = ∫ x, φ x • f x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hφ, coe_toSchwartzOfReal, Complex.real_smul, smul_eq_mul]
    _ = ∫ x, 𝓕⁻ (𝓕 ⇑φ) x • f x :=
        congrArg (fun F : ES → ℂ => ∫ x, F x • f x) hinv.symm
    _ = ∫ ξ, 𝓕 ⇑φ ξ • 𝓕⁻ f ξ :=
        ContinuousLeiLinPressurePhysical.integral_fourierInv_pairing (𝓕 ⇑φ) f hfi hf
    _ = 0 := by simp [h₀]

/-! ## 2. `physOf`-injectivity on representers -/

/-- Reality of the recovered field: a `WDatum` profile's inverse Fourier
transform is real-valued at every point (`WDatum.sym` + the repo's
`conj_fourierInv`). -/
theorem fourierInv_conj {a : ES → ComplexSpace} (hd : WDatum a) (i : Fin 3) (y : ES) :
    conj (𝓕⁻ (fun ξ => a ξ i) y) = 𝓕⁻ (fun ξ => a ξ i) y := by
  rw [conj_fourierInv]
  refine fourierInv_congr ?_ y
  filter_upwards [hd.sym i] with ξ hξ
  show conj (a (-ξ) i) = a ξ i
  rw [hξ, Complex.conj_conj]

/-- **`physOf`-injectivity on representers.**  Two representers of the same
velocity slice agree almost everywhere, component by component.  This is the
lemma whose absence the `HorizonFreeBudgetRestart` header recorded as the
named boundary for the `≢⊤` exhibit. -/
theorem rep_component_ae_eq {v : VelocityField} {a b : ES → ComplexSpace}
    (ha : Rep v a) (hb : Rep v b) (i : Fin 3) :
    (fun ξ => a ξ i) =ᵐ[volume] (fun ξ => b ξ i) := by
  have har : Integrable (fun ξ => a ξ i) := ha.datum.integrable i
  have hbr : Integrable (fun ξ => b ξ i) := hb.datum.integrable i
  have hz : ((fun ξ => a ξ i) - fun ξ => b ξ i) =ᵐ[volume] 0 :=
    ae_eq_zero_of_fourierInv_eq_zero (har.sub hbr) (by
      intro y
      obtain ⟨x, rfl⟩ := euclidPoint_surjective y
      have hra : conj (𝓕⁻ (fun ξ => a ξ i) (euclidPoint x)) =
          𝓕⁻ (fun ξ => a ξ i) (euclidPoint x) := fourierInv_conj ha.datum i _
      have hrb : conj (𝓕⁻ (fun ξ => b ξ i) (euclidPoint x)) =
          𝓕⁻ (fun ξ => b ξ i) (euclidPoint x) := fourierInv_conj hb.datum i _
      -- the physical values agree; `physOf` reads them off the real parts:
      have hre : (𝓕⁻ (fun ξ => a ξ i) (euclidPoint x)).re =
          (𝓕⁻ (fun ξ => b ξ i) (euclidPoint x)).re := by
        have h : (physOf a x) i = (physOf b x) i :=
          congrFun ((ha.eq x).symm.trans (hb.eq x)) i
        have h1 : (physOf a x) i =
            -(1 / (2 * Real.pi)) * (𝓕⁻ (fun ξ => a ξ i) (euclidPoint x)).re := rfl
        have h2 : (physOf b x) i =
            -(1 / (2 * Real.pi)) * (𝓕⁻ (fun ξ => b ξ i) (euclidPoint x)).re := rfl
        rw [h1, h2] at h
        have hc : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 := by
          have hπ : (0 : ℝ) < 1 / (2 * Real.pi) :=
            div_pos zero_lt_one (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
          linarith
        exact mul_left_cancel₀ hc h
      -- both values are real (`fourierInv_conj`), equal in real parts:
      have hai : (𝓕⁻ (fun ξ => a ξ i) (euclidPoint x)).im = 0 := by
        have h := congrArg Complex.im hra
        rw [Complex.conj_im] at h
        linarith
      have hbi : (𝓕⁻ (fun ξ => b ξ i) (euclidPoint x)).im = 0 := by
        have h := congrArg Complex.im hrb
        rw [Complex.conj_im] at h
        linarith
      have hex : 𝓕⁻ (fun ξ => a ξ i) (euclidPoint x) =
          𝓕⁻ (fun ξ => b ξ i) (euclidPoint x) :=
        Complex.ext hre (by rw [hai, hbi])
      show 𝓕⁻ (fun ξ => a ξ i - b ξ i) (euclidPoint x) = 0
      rw [fourierInv_sub_apply har hbr _, hex, sub_self])
  filter_upwards [hz] with ξ hξ
  exact sub_eq_zero.mp hξ

/-- The bundled form: two representers agree a.e. as `ES → ComplexSpace`. -/
theorem rep_ae_eq {v : VelocityField} {a b : ES → ComplexSpace}
    (ha : Rep v a) (hb : Rep v b) : a =ᵐ[volume] b := by
  have h0 := rep_component_ae_eq ha hb 0
  have h1 := rep_component_ae_eq ha hb 1
  have h2 := rep_component_ae_eq ha hb 2
  filter_upwards [h0, h1, h2] with ξ e0 e1 e2
  refine funext (fun i => by
    fin_cases i
    · exact e0
    · exact e1
    · exact e2)

/-! ## 3. The budget collapses to any one representer -/

/-- **Budget collapse.**  For a representable slice, the envelope budget —
the supremum over *all* representers — is the weight `⨆ i, h3F (a·i)` of any
single representer `a`.  The `≤` half consumes `rep_component_ae_eq`:
`h3F` cannot see a representer other than the a.e.-unique one. -/
theorem h3EnvelopeBudget_eq_iSup {v : VelocityField} {a : ES → ComplexSpace}
    (ha : Rep v a) : h3EnvelopeBudget v = ⨆ i : Fin 3, h3F (fun ξ => a ξ i) := by
  refine le_antisymm ?_ ?_
  · refine (h3EnvelopeBudget_le_iff ⟨a, ha⟩).mpr ?_
    intro b hb i
    refine le_trans ?_ (le_iSup (fun j => h3F (fun ξ => a ξ j)) i)
    rw [h3F_congr (rep_component_ae_eq hb ha i)]
  · exact iSup_le fun i => h3F_component_le_budget ha i

/-! ## 4. The exhibit: a transverse bump profile -/

/-- The exhibit profile `a(ξ) = 1_{‖ξ‖<2} · (iξ₂, −iξ₁, 0)`: a transverse,
Hermitian, bounded, compactly supported frequency profile. -/
def prof : ES → ComplexSpace :=
  (Metric.ball (0 : ES) (2 : ℝ)).indicator fun η =>
    ![Complex.I * (η 1 : ℂ), -Complex.I * (η 0 : ℂ), 0]

theorem prof_in {ξ : ES} (h : ξ ∈ Metric.ball (0 : ES) (2 : ℝ)) :
    prof ξ = ![Complex.I * (ξ 1 : ℂ), -Complex.I * (ξ 0 : ℂ), 0] := by
  rw [prof, Set.indicator_of_mem h]

theorem prof_notIn {ξ : ES} (h : ξ ∉ Metric.ball (0 : ES) (2 : ℝ)) : prof ξ = 0 := by
  rw [prof, Set.indicator_of_notMem h]

/-- The ball `Metric.ball (0 : ES) 2` is membership-even (`‖-ξ‖ = ‖ξ‖`). -/
private theorem mem_ball_neg {ξ : ES} :
    ξ ∈ Metric.ball (0 : ES) (2 : ℝ) ↔ -ξ ∈ Metric.ball (0 : ES) (2 : ℝ) := by
  constructor <;> intro h <;>
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero, norm_neg] using h

/-- `prof` is measurable (indicator of a continuous vector function over a
measurable ball). -/
theorem measurable_prof : Measurable prof := by
  refine Measurable.indicator ?_ measurableSet_ball
  refine measurable_pi_iff.2 fun i => by
    classical
    fin_cases i
    · show Measurable fun ξ : ES => Complex.I * (↑(ξ 1) : ℂ)
      have hc : Continuous (fun ξ : ES => (ξ 1 : ℝ)) := PiLp.continuous_apply 2 _ 1
      refine measurable_const.mul ?_
      exact Complex.measurable_ofReal.comp hc.measurable
    · show Measurable fun ξ : ES => -Complex.I * (↑(ξ 0) : ℂ)
      have hc : Continuous (fun ξ : ES => (ξ 0 : ℝ)) := PiLp.continuous_apply 2 _ 0
      refine measurable_const.mul ?_
      exact Complex.measurable_ofReal.comp hc.measurable
    · exact measurable_const

/-- On the ball, the sup norm of the (unpacked) profile is at most `‖ξ‖`. -/
theorem norm_prof_le {ξ : ES} (h : ξ ∈ Metric.ball (0 : ES) (2 : ℝ)) :
    ‖prof ξ‖ ≤ ‖ξ‖ := by
  rw [prof_in h]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => by
    fin_cases j
    · show ‖Complex.I * (↑(ξ 1) : ℂ)‖ ≤ ‖ξ‖
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, EuclideanSpace.norm_eq]
      refine Real.le_sqrt_of_sq_le ?_
      have hsum : ∀ i ∈ Finset.univ, 0 ≤ ‖ξ.ofLp i‖ ^ 2 := fun i _ => sq_nonneg _
      exact Finset.single_le_sum hsum (Finset.mem_univ (1 : Fin 3))
    · show ‖(-Complex.I) * (↑(ξ 0) : ℂ)‖ ≤ ‖ξ‖
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
        EuclideanSpace.norm_eq]
      refine Real.le_sqrt_of_sq_le ?_
      have hsum : ∀ i ∈ Finset.univ, 0 ≤ ‖ξ.ofLp i‖ ^ 2 := fun i _ => sq_nonneg _
      exact Finset.single_le_sum hsum (Finset.mem_univ (0 : Fin 3))
    · show ‖(0 : ℂ)‖ ≤ ‖ξ‖
      rw [norm_zero]
      exact norm_nonneg _

theorem bdd_prof :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ ξ ∂(volume : Measure ES), ∀ i, ‖prof ξ i‖ ≤ A := by
  refine ⟨2, (by norm_num : (0 : ℝ) ≤ 2), Eventually.of_forall fun ξ i => ?_⟩
  by_cases h : ξ ∈ Metric.ball (0 : ES) (2 : ℝ)
  · have hlt : ‖ξ‖ < 2 := by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using h
    calc ‖prof ξ i‖ ≤ ‖prof ξ‖ := norm_le_pi_norm (prof ξ) i
      _ ≤ ‖ξ‖ := norm_prof_le h
      _ ≤ 2 := le_of_lt hlt
  · rw [prof_notIn h, Pi.zero_apply, norm_zero]
    linarith

/-- The `ℝ≥0∞`-valued norm is `ENNReal.ofReal` of the real norm (every
seminormed group: `‖x‖ₑ = ↑‖x‖₊` by `rfl`, `ENNReal.coe_nnreal_eq`). -/
private theorem enorm_ofReal_norm {E : Type*} [SeminormedAddCommGroup E] (x : E) :
    ‖x‖ₑ = ENNReal.ofReal ‖x‖ :=
  ENNReal.coe_nnreal_eq ‖x‖₊

/-- `prof` is a `WDatum`: measurable, with all moments finite, and Hermitian
(`prof (-ξ) i = conj (prof ξ i)` pointwise). -/
theorem wdatum_prof : WDatum prof := by
  refine ⟨measurable_prof, ?_, ?_⟩
  · intro n
    have hp : ∀ ξ : ES, ENNReal.ofReal (‖ξ‖ ^ n) * ‖prof ξ‖ₑ ≤
        (Metric.ball (0 : ES) (2 : ℝ)).indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (n + 1))) ξ := by
      intro ξ
      by_cases h : ξ ∈ Metric.ball (0 : ES) (2 : ℝ)
      · have hlt : ‖ξ‖ < 2 := by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using h
        rw [Set.indicator_of_mem h]
        rw [enorm_ofReal_norm]
        refine le_trans (mul_le_mul' (b := ENNReal.ofReal (‖ξ‖ ^ n))
          (d := ENNReal.ofReal (2 : ℝ)) le_rfl
          (ENNReal.ofReal_le_ofReal ((norm_prof_le h).trans (le_of_lt hlt)))) ?_
        rw [← ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) n), pow_succ]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hlt) n)
            (by norm_num : (0 : ℝ) ≤ 2))
      · rw [Set.indicator_of_notMem h, prof_notIn h]
        simp
    have hbound : (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖prof ξ‖ₑ) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) * volume (Metric.ball (0 : ES) (2 : ℝ)) := by
      refine le_trans (lintegral_mono hp) (le_of_eq ?_)
      exact lintegral_indicator_const measurableSet_ball
        (ENNReal.ofReal ((2 : ℝ) ^ (n + 1)))
    exact ne_of_lt (lt_of_le_of_lt hbound (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) measure_ball_lt_top))
  · intro i
    refine Eventually.of_forall fun ξ => by
      by_cases h : ξ ∈ Metric.ball (0 : ES) (2 : ℝ)
      · rw [prof_in (mem_ball_neg.mp h), prof_in h]
        fin_cases i
        · show Complex.I * (↑((-ξ) 1) : ℂ) = conj (Complex.I * (↑(ξ 1) : ℂ))
          rw [PiLp.neg_apply, Complex.ofReal_neg, mul_neg, ← Complex.star_def,
            star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
            neg_mul]
        · show -Complex.I * (↑((-ξ) 0) : ℂ) = conj (-Complex.I * (↑(ξ 0) : ℂ))
          rw [PiLp.neg_apply, Complex.ofReal_neg, neg_mul_neg, ← Complex.star_def,
            star_mul', star_neg, Complex.star_def, Complex.conj_I, neg_neg,
            Complex.conj_ofReal]
        · simp
      · rw [prof_notIn (fun hB => h (mem_ball_neg.mpr hB)), prof_notIn h]
        simp

/-- `prof` is transverse: `∑ i, (ξ i : ℂ) * prof ξ i = 0` pointwise. -/
theorem div_prof : ∀ᵐ ξ ∂(volume : Measure ES),
    ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * prof ξ i = 0 :=
  Eventually.of_forall fun ξ => by
    by_cases h : ξ ∈ Metric.ball (0 : ES) (2 : ℝ)
    · rw [Fin.sum_univ_three, prof_in h]
      have hvec : (![Complex.I * (ξ 1 : ℂ), -Complex.I * (ξ 0 : ℂ), 0] : ComplexSpace)
          0 = Complex.I * (ξ 1 : ℂ) := rfl
      have hvec' : (![Complex.I * (ξ 1 : ℂ), -Complex.I * (ξ 0 : ℂ), 0] : ComplexSpace)
          1 = -Complex.I * (ξ 0 : ℂ) := rfl
      have hvec'' : (![Complex.I * (ξ 1 : ℂ), -Complex.I * (ξ 0 : ℂ), 0] : ComplexSpace)
          2 = 0 := rfl
      rw [hvec, hvec', hvec'']
      ring
    · rw [Fin.sum_univ_three, prof_notIn h]
      simp

/-- **The exhibit representer.** `prof` represents the constant slice
`physOf prof`: datum, boundedness, transversality and the tautological
`eq` field. -/
theorem rep_prof : Rep (physOf prof) prof :=
  ⟨wdatum_prof, bdd_prof, div_prof, fun _ => rfl⟩

/-- The weighted `H³` component energy of `prof` is finite uniformly in the
component: each `h3F (prof·i) ≤ ENNReal.ofReal 2916 * volume (ball 0 2)`. -/
theorem h3F_prof_le (i : Fin 3) :
    h3F (fun ξ => prof ξ i) ≤
      ENNReal.ofReal (2916 : ℝ) * volume (Metric.ball (0 : ES) (2 : ℝ)) := by
  unfold h3F
  have hp : ∀ ξ : ES, ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖prof ξ i‖ₑ ^ 2 ≤
      (Metric.ball (0 : ES) (2 : ℝ)).indicator (fun _ => ENNReal.ofReal (2916 : ℝ)) ξ := by
    intro ξ
    by_cases h : ξ ∈ Metric.ball (0 : ES) (2 : ℝ)
    · have hlt : ‖ξ‖ < 2 := by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using h
      have hcoord : ‖prof ξ i‖ ≤ ‖ξ‖ :=
        (norm_le_pi_norm (prof ξ) i).trans (norm_prof_le h)
      have h729 : ((1 + ‖ξ‖ : ℝ) ^ 6) ≤ 729 := by
        have hb : (1 + ‖ξ‖ : ℝ) ≤ 3 := by linarith [norm_nonneg ξ]
        calc (1 + ‖ξ‖) ^ 6 ≤ (3 : ℝ) ^ 6 :=
          pow_le_pow_left₀ (by linarith [norm_nonneg ξ]) hb 6
          _ = 729 := by norm_num
      have hsq : ‖prof ξ i‖ₑ ^ 2 ≤ ENNReal.ofReal (4 : ℝ) := by
        rw [enorm_ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
        refine ENNReal.ofReal_le_ofReal ?_
        exact (pow_le_pow_left₀ (norm_nonneg _) (hcoord.trans (le_of_lt hlt)) 2).trans
          (by norm_num : ((2 : ℝ) ^ 2 : ℝ) ≤ 4)
      rw [Set.indicator_of_mem h]
      calc ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖prof ξ i‖ₑ ^ 2
          ≤ ENNReal.ofReal 729 * ENNReal.ofReal 4 :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal h729) hsq
        _ = ENNReal.ofReal (2916 : ℝ) := by
            rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (729 : ℝ))]
            norm_num
    · rw [Set.indicator_of_notMem h, prof_notIn h]
      simp
  refine le_trans (lintegral_mono hp) (le_of_eq ?_)
  exact lintegral_indicator_const measurableSet_ball (ENNReal.ofReal (2916 : ℝ))

/-- The `i = 0` component weight is strictly positive: its integrand's
support contains the open set `ball(0,2) ∩ {ξ | ξ.1 ≠ 0}`. -/
theorem h3F_prof_0_pos : 0 < h3F (fun ξ => prof ξ 0) := by
  unfold h3F
  have hcont : Continuous fun ξ : ES => (1 + ‖ξ‖ : ℝ) ^ 6 :=
    (continuous_const.add continuous_norm).pow 6
  have hm1 : Measurable fun ξ => ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) :=
    ENNReal.continuous_ofReal.measurable.comp hcont.measurable
  have hm2 : Measurable fun ξ => ‖prof ξ 0‖ₑ ^ 2 := by
    have h0 : Measurable fun ξ : ES => prof ξ 0 :=
      (measurable_pi_apply (0 : Fin 3)).comp measurable_prof
    have hn : Measurable fun x : ℂ => ‖x‖ₑ := continuous_enorm.measurable
    have hq : Measurable fun ξ : ES => ‖prof ξ 0‖ₑ := hn.comp h0
    exact (ENNReal.continuous_pow 2).measurable.comp hq
  show 0 < ∫⁻ (ξ : ES), ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖prof ξ 0‖ₑ ^ 2
  have hmeas :
      Measurable fun ξ : ES => ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖prof ξ 0‖ₑ ^ 2 :=
    hm1.mul hm2
  rw [lintegral_pos_iff_support hmeas]
  set s : Set ES := Metric.ball (0 : ES) (2 : ℝ) ∩ {ξ | (ξ 1 : ℝ) ≠ 0}
  have hξ : ‖(euclidPoint (![0, 1, 0] : Space) : ES)‖ < 2 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ i : Fin 3, ‖(euclidPoint (![0, 1, 0] : Space)) i‖ ^ 2 = (1 : ℝ) := by
      rw [Fin.sum_univ_three]
      have h0 : (euclidPoint (![0, 1, 0] : Space)) 0 = (0 : ℝ) := rfl
      have h1 : (euclidPoint (![0, 1, 0] : Space)) 1 = (1 : ℝ) := rfl
      have h2 : (euclidPoint (![0, 1, 0] : Space)) 2 = (0 : ℝ) := rfl
      rw [h0, h1, h2]
      norm_num
    rw [hsum]
    norm_num
  have hc : Continuous (fun ξ : ES => (ξ 1 : ℝ)) := PiLp.continuous_apply 2 _ 1
  have hco : IsOpen {ξ : ES | (ξ 1 : ℝ) ≠ 0} := by
    have hset : {ξ : ES | (ξ 1 : ℝ) ≠ 0} =
        (fun ξ : ES => (ξ 1 : ℝ)) ⁻¹' (Set.Iio 0 ∪ Set.Ioi 0) := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_Ioi]
      exact ⟨lt_or_gt_of_ne, fun h => h.elim ne_of_lt ne_of_gt⟩
    rw [hset]
    exact hc.isOpen_preimage _ ((isOpen_Iio' 0).union (isOpen_Ioi' 0))
  have ho : IsOpen s := IsOpen.inter Metric.isOpen_ball hco
  have hn : s.Nonempty := by
    refine ⟨euclidPoint (![0, 1, 0] : Space), ?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hξ
    · exact one_ne_zero
  refine lt_of_lt_of_le (ho.measure_pos (μ := (volume : Measure ES)) hn) (measure_mono ?_)
  intro ξ hξ
  obtain ⟨hball, hcoord⟩ := hξ
  rw [Function.mem_support]
  show ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖prof ξ 0‖ₑ ^ 2 ≠ 0
  have hvec : (![Complex.I * (ξ 1 : ℂ), -Complex.I * (ξ 0 : ℂ), 0] : ComplexSpace)
      0 = Complex.I * (ξ 1 : ℂ) := rfl
  rw [prof_in hball, hvec]
  intro hz
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) h1
  · have he : ‖Complex.I * (ξ 1 : ℂ)‖ₑ = 0 := by
      rw [pow_two] at h2
      exact (mul_eq_zero.mp h2).elim id id
    rw [enorm_ofReal_norm, ENNReal.ofReal_eq_zero] at he
    have hz0 : Complex.I * (ξ 1 : ℂ) = 0 := norm_eq_zero.mp (le_antisymm he (norm_nonneg _))
    rcases mul_eq_zero.mp hz0 with hi | hc
    · exact absurd hi Complex.I_ne_zero
    · exact hcoord (Complex.ofReal_eq_zero.mp hc)

/-- The exhibit slice's envelope budget is finite. -/
theorem h3EnvelopeBudget_physOf_lt_top : h3EnvelopeBudget (physOf prof) < ⊤ := by
  rw [h3EnvelopeBudget_eq_iSup rep_prof]
  refine lt_of_le_of_lt (iSup_le fun i => h3F_prof_le i) ?_
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
    measure_ball_lt_top

/-- **The `≢⊤` exhibit that the `HorizonFreeBudgetRestart` header recorded as
the named missing piece.** There is a horizon and a (constant) velocity
evolution whose envelope control is finite. -/
theorem exists_h3EnvelopeControl_lt_top :
    ∃ (T : ℝ) (u : VelocityEvolution), h3EnvelopeControl T u < ⊤ := by
  refine ⟨1, fun _ => physOf prof, ?_⟩
  exact lt_of_le_of_lt (iSup₂_le fun _ _ => le_rfl) h3EnvelopeBudget_physOf_lt_top

/-- **The strengthened exhibit:** the control of `fun _ => physOf prof` at
horizon `1` is strictly between `0` and `⊤` — the ⊤-guard never misfires,
and the profile is genuinely nonzero.  As in
`bkmVorticityControl_nondegenerate`, this lives at the functional level; it
is not asserted that the witness is a `SolvesBefore` member. -/
theorem exists_h3EnvelopeControl_pos_lt_top :
    ∃ (T : ℝ) (u : VelocityEvolution), 0 < h3EnvelopeControl T u ∧
      h3EnvelopeControl T u < ⊤ := by
  refine ⟨1, fun _ => physOf prof, ?_, ?_⟩
  · have hp : 0 < h3EnvelopeBudget (physOf prof) := by
      rw [h3EnvelopeBudget_eq_iSup rep_prof]
      exact lt_of_lt_of_le h3F_prof_0_pos
        (le_iSup (fun i => h3F (fun ξ => prof ξ i)) (0 : Fin 3))
    exact lt_of_lt_of_le hp
      (le_iSup₂_of_le (0 : ℝ) (by norm_num : (0 : ℝ) ∈ Ico (0 : ℝ) 1) le_rfl)
  · exact lt_of_le_of_lt (iSup₂_le fun _ _ => le_rfl) h3EnvelopeBudget_physOf_lt_top

end Navier.Analysis.EnvelopeFourierUniqueness

set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopeFourierUniqueness.rep_component_ae_eq
set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopeFourierUniqueness.exists_h3EnvelopeControl_pos_lt_top
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeFourierUniqueness.ae_eq_zero_of_fourierInv_eq_zero
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeFourierUniqueness.rep_component_ae_eq
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeFourierUniqueness.rep_ae_eq
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeFourierUniqueness.h3EnvelopeBudget_eq_iSup
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeFourierUniqueness.exists_h3EnvelopeControl_lt_top
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeFourierUniqueness.exists_h3EnvelopeControl_pos_lt_top
