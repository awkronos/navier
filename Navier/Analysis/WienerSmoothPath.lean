import Navier.Analysis.WienerL1Carrier
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Smooth Fourier paths and joint smoothness of their inverse Fourier fields

A `SmoothFourierPath T` is a family `D k α t ∈ L¹(ℝ³; ℂ)` indexed by a time
order `k`, a spatial multi-index `α` and a time `t`, with

* `D k (α + eⱼ) t = ξⱼ · D k α t` (almost everywhere), and
* `t ↦ D k α t` differentiable within `[0, T)` in `L¹` with derivative
  `D (k+1) α t`.

`D 0 0` is the Fourier coefficient path; `D k α` is `ξ^α ∂ₜᵏ` of it.  The main
theorem `contDiffOn_phys` proves that the inverse Fourier field
`(t, x) ↦ 𝓕⁻(D 0 0 t)(x)` is `C^∞` jointly on `[0, T) × ℝ³`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace ContDiff

namespace Navier.Analysis.WienerSmoothPath

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerL1Carrier

/-- The coordinate multi-index increment. -/
abbrev ej (j : Fin 3) : Fin 3 → ℕ := Pi.single j 1

/-- A smooth Fourier path on `[0, T)`. -/
structure SmoothFourierPath (T : ℝ) where
  D : ℕ → (Fin 3 → ℕ) → ℝ → L1C
  mul : ∀ (k : ℕ) (α : Fin 3 → ℕ) (j : Fin 3) (t : ℝ),
    ⇑(D k (α + ej j) t) =ᵐ[volume] fun ξ : ES => ((ξ j : ℝ) : ℂ) * D k α t ξ
  deriv : ∀ (k : ℕ) (α : Fin 3 → ℕ), ∀ t ∈ Ico (0 : ℝ) T,
    HasDerivWithinAt (D k α) (D (k + 1) α t) (Ico (0 : ℝ) T) t

namespace SmoothFourierPath

variable {T : ℝ} (P : SmoothFourierPath T)

/-- Shift in time order. -/
def shiftT : SmoothFourierPath T where
  D k α := P.D (k + 1) α
  mul k α j t := P.mul (k + 1) α j t
  deriv k α t ht := P.deriv (k + 1) α t ht

/-- Shift in the `j`-th spatial index. -/
def shiftX (j : Fin 3) : SmoothFourierPath T where
  D k α := P.D k (α + ej j)
  mul k α i t := by
    have h := P.mul k (α + ej j) i t
    rwa [show α + ej j + ej i = α + ej i + ej j by abel] at h
  deriv k α t ht := P.deriv k (α + ej j) t ht

/-- The inverse Fourier field of the path. -/
def phys (z : ℝ × ES) : ℂ := 𝓕⁻ (⇑(P.D 0 0 z.1)) z.2

end SmoothFourierPath

/-! ## Elementary bounds for the inverse Fourier transform on `L¹` -/

theorem norm_fourierInv_le (f : L1C) (x : ES) : ‖𝓕⁻ (⇑f) x‖ ≤ ‖f‖ := by
  rw [Real.fourierInv_eq, L1.norm_eq_integral_norm]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext ξ
  rw [Circle.norm_smul]

theorem integrable_fourierChar_smul {f : ES → ℂ} (hf : Integrable f) (x : ES) :
    Integrable (fun v : ES => 𝐞 ⟪v, x⟫ • f v) := by
  refine hf.norm.mono' ?_ (Eventually.of_forall fun v => by rw [Circle.norm_smul])
  exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).aestronglyMeasurable).smul
    hf.1

theorem fourierInv_sub (f g : L1C) (x : ES) :
    𝓕⁻ (⇑(f - g)) x = 𝓕⁻ (⇑f) x - 𝓕⁻ (⇑g) x := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, Real.fourierInv_eq,
    ← integral_sub (integrable_fourierChar_smul (L1.integrable_coeFn f) x)
      (integrable_fourierChar_smul (L1.integrable_coeFn g) x)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub f g] with v h
  rw [h, Pi.sub_apply, smul_sub]

theorem fourierInv_congr {f : ES → ℂ} {g : ES → ℂ} (h : f =ᵐ[volume] g) (x : ES) :
    𝓕⁻ f x = 𝓕⁻ g x := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  refine integral_congr_ae ?_
  filter_upwards [h] with v hv
  rw [hv]

/-- Continuity of the inverse Fourier transform of an integrable profile. -/
theorem continuous_fourierInv {f : ES → ℂ} (hf : Integrable f) : Continuous (𝓕⁻ f) := by
  have h : 𝓕⁻ f = fun x => ∫ v, 𝐞 ⟪v, x⟫ • f v := funext fun x => Real.fourierInv_eq f x
  rw [h]
  refine continuous_of_dominated
    (fun x => (integrable_fourierChar_smul hf x).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun v => by rw [Circle.norm_smul]) hf.norm ?_
  exact Eventually.of_forall fun v =>
    ((Real.continuous_fourierChar.comp (continuous_const.inner continuous_id)).smul
      continuous_const)

/-! ## The spatial derivative of an inverse Fourier transform -/

/-- The phase functional `v ↦ (dx ↦ 2πi ⟪v, dx⟫)`, bundled. -/
def phaseL : ES →L[ℝ] ES →L[ℝ] ℂ :=
  ((2 * Real.pi : ℂ) * Complex.I) •
    ((ContinuousLinearMap.compL ℝ ES ℝ ℂ Complex.ofRealCLM).comp (innerSL ℝ))

/-- The phase functional `dx ↦ 2πi ⟪v, dx⟫`. -/
def phaseCLM (v : ES) : ES →L[ℝ] ℂ := phaseL v

theorem phaseCLM_apply (v x : ES) :
    phaseCLM v x = (2 * Real.pi : ℂ) * Complex.I * ((⟪v, x⟫ : ℝ) : ℂ) := by
  simp [phaseCLM, phaseL]

theorem norm_phaseCLM_le (v : ES) : ‖phaseCLM v‖ ≤ 2 * Real.pi * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [phaseCLM_apply, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  have h2 : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by exact_mod_cast h2
  rw [this]
  have hi := abs_real_inner_le_norm v x
  have hp := Real.pi_pos
  nlinarith

theorem phase_exp_eq (v x : ES) :
    Complex.exp ((↑(2 * Real.pi * ⟪v, x⟫) * Complex.I)) = Complex.exp (phaseCLM v x) := by
  rw [phaseCLM_apply]
  congr 1
  push_cast
  ring

theorem norm_exp_phase (v x : ES) : ‖Complex.exp (phaseCLM v x)‖ = 1 := by
  rw [← phase_exp_eq]
  exact Complex.norm_exp_ofReal_mul_I _

theorem fourierInv_eq_exp (f : ES → ℂ) (x : ES) :
    𝓕⁻ f x = ∫ v, Complex.exp (phaseCLM v x) * f v := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [phase_exp_eq]

theorem norm_le_sum_coord (v : ES) : ‖v‖ ≤ ∑ j : Fin 3, |v j| := by
  have hv : v = ∑ j : Fin 3, EuclideanSpace.single j (v j) := by
    ext i
    simp [PiLp.single_apply]
  conv_lhs => rw [hv]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.norm_single 2 (fun _ : Fin 3 => ℝ), Real.norm_eq_abs]

theorem inner_eq_sum_coord (v x : ES) : ⟪v, x⟫ = ∑ j : Fin 3, v j * x j := by
  simp [PiLp.inner_apply, mul_comm]

/-- **Spatial Fréchet derivative of the inverse Fourier transform**, with the
first moments supplied as integrable profiles `g j = ξⱼ f`. -/
theorem hasFDerivAt_fourierInv {f : ES → ℂ} (hf : Integrable f) (g : Fin 3 → ES → ℂ)
    (hg : ∀ j, g j =ᵐ[volume] fun ξ : ES => ((ξ j : ℝ) : ℂ) * f ξ)
    (hgi : ∀ j, Integrable (g j)) (x : ES) :
    HasFDerivAt (𝓕⁻ f)
      (∑ j : Fin 3, (EuclideanSpace.proj j : ES →L[ℝ] ℝ).smulRight
        ((2 * Real.pi : ℂ) * Complex.I * 𝓕⁻ (g j) x)) x := by
  have hfun : 𝓕⁻ f = fun x => ∫ v, Complex.exp (phaseCLM v x) * f v :=
    funext (fourierInv_eq_exp f)
  set F' : ES → ES → ES →L[ℝ] ℂ := fun x v =>
    f v • (Complex.exp (phaseCLM v x) • phaseCLM v) with hF'
  have hmom : Integrable (fun v : ES => 2 * Real.pi * (‖v‖ * ‖f v‖)) := by
    have hsum : Integrable (fun v : ES => ∑ j : Fin 3, ‖g j v‖) :=
      integrable_finset_sum _ fun j _ => (hgi j).norm
    refine (hsum.const_mul (2 * Real.pi)).mono' ?_ ?_
    · exact aestronglyMeasurable_const.mul (continuous_norm.aestronglyMeasurable.mul hf.norm.1)
    · filter_upwards [ae_all_iff.mpr hg] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖v‖ * ‖f v‖ ≤ (∑ j : Fin 3, |v j|) * ‖f v‖ :=
            mul_le_mul_of_nonneg_right (norm_le_sum_coord v) (norm_nonneg _)
        _ = ∑ j : Fin 3, ‖g j v‖ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hv j, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hmeasF' : ∀ x, AEStronglyMeasurable (F' x) volume := fun x => by
    have hc : Continuous fun v : ES => Complex.exp (phaseCLM v x) • phaseCLM v := by
      have hp : Continuous fun v : ES => phaseCLM v := phaseL.continuous
      exact (Complex.continuous_exp.comp (hp.clm_apply continuous_const)).smul hp
    exact hf.1.smul hc.aestronglyMeasurable
  have hFint : ∀ y : ES, Integrable (fun v => Complex.exp (phaseCLM v y) * f v) := fun y => by
    refine hf.norm.mono' ?_ (Eventually.of_forall fun v => by
      rw [norm_mul, norm_exp_phase, one_mul])
    exact ((Complex.continuous_exp.comp
      (phaseL.continuous.clm_apply continuous_const)).aestronglyMeasurable).mul hf.1
  have hbound : ∀ y v, ‖F' y v‖ ≤ 2 * Real.pi * (‖v‖ * ‖f v‖) := fun y v => by
    rw [hF', norm_smul, norm_smul, norm_exp_phase, one_mul]
    have := norm_phaseCLM_le v
    nlinarith [norm_nonneg (f v)]
  have hF'int : Integrable (F' x) := hmom.mono' (hmeasF' x)
    (Eventually.of_forall fun v => hbound x v)
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun y v => Complex.exp (phaseCLM v y) * f v) (F' := F') (x₀ := x)
    (bound := fun v => 2 * Real.pi * (‖v‖ * ‖f v‖)) Filter.univ_mem
    (Eventually.of_forall fun y => (hFint y).aestronglyMeasurable) (hFint x) (hmeasF' x)
    (Eventually.of_forall fun v y _ => hbound y v) hmom
    (Eventually.of_forall fun v y _ =>
      ((phaseCLM v).hasFDerivAt.cexp).mul_const (f v))
  rw [hfun]
  refine hd.congr_fderiv ?_
  ext1 dx
  rw [ContinuousLinearMap.integral_apply hF'int]
  have hexp : ∀ j, Integrable (fun v : ES => Complex.exp (phaseCLM v x) * g j v) := fun j => by
    refine (hgi j).norm.mono' ?_ (Eventually.of_forall fun v => by
      rw [norm_mul, norm_exp_phase, one_mul])
    exact ((Complex.continuous_exp.comp
      (phaseL.continuous.clm_apply continuous_const)).aestronglyMeasurable).mul (hgi j).1
  have hpt : (fun v => F' x v dx) =ᵐ[volume] fun v => ∑ j : Fin 3,
      ((dx j : ℝ) : ℂ) * ((2 * Real.pi : ℂ) * Complex.I *
        (Complex.exp (phaseCLM v x) * g j v)) := by
    filter_upwards [ae_all_iff.mpr hg] with v hv
    have hL : F' x v dx = f v * (Complex.exp (phaseCLM v x) *
        ((2 * Real.pi : ℂ) * Complex.I * ((⟪v, dx⟫ : ℝ) : ℂ))) := by
      simp only [hF', ContinuousLinearMap.smul_apply, smul_eq_mul, phaseCLM_apply]
    rw [hL, inner_eq_sum_coord]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hv j]
    ring
  rw [integral_congr_ae hpt, integral_finsetSum _ fun j _ =>
    (((hexp j).const_mul _).const_mul _)]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.proj_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul, fourierInv_eq_exp, Complex.real_smul]

theorem fourierInv_smul (c : ℝ) (f : L1C) (x : ES) :
    𝓕⁻ (⇑(c • f)) x = c • 𝓕⁻ (⇑f) x := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c f] with v h
  rw [h, Pi.smul_apply, smul_comm]

/-! ## The joint derivative -/

namespace SmoothFourierPath

variable {T : ℝ} (P : SmoothFourierPath T)

/-- The time-coordinate functional, complexified. -/
def fstC : ℝ × ES →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ES)

/-- The `j`-th spatial-coordinate functional, complexified. -/
def coordC (j : Fin 3) : ℝ × ES →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((EuclideanSpace.proj j : ES →L[ℝ] ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ ES))

/-- The candidate joint derivative. -/
def Lfull (z : ℝ × ES) : ℝ × ES →L[ℝ] ℂ :=
  P.shiftT.phys z • fstC +
    ∑ j : Fin 3, ((2 * Real.pi : ℂ) * Complex.I * (P.shiftX j).phys z) • coordC j

theorem shiftX_D_zero (j : Fin 3) (t : ℝ) : (P.shiftX j).D 0 0 t = P.D 0 (ej j) t := by
  simp [shiftX]

/-- Spatial derivative at a fixed time. -/
theorem hasFDerivAt_phys_space (t : ℝ) (x : ES) :
    HasFDerivAt (fun y => 𝓕⁻ (⇑(P.D 0 0 t)) y)
      (∑ j : Fin 3, (EuclideanSpace.proj j : ES →L[ℝ] ℝ).smulRight
        ((2 * Real.pi : ℂ) * Complex.I * (P.shiftX j).phys (t, x))) x := by
  have h := hasFDerivAt_fourierInv (L1.integrable_coeFn (P.D 0 0 t))
    (fun j => ⇑(P.D 0 (ej j) t))
    (fun j => by simpa using P.mul 0 0 j t)
    (fun j => L1.integrable_coeFn _) x
  simpa [phys, shiftX_D_zero] using h

theorem Lfull_apply (z dz : ℝ × ES) :
    P.Lfull z dz = (dz.1 : ℂ) * P.shiftT.phys z +
      ∑ j : Fin 3, (EuclideanSpace.proj j : ES →L[ℝ] ℝ).smulRight
        ((2 * Real.pi : ℂ) * Complex.I * (P.shiftX j).phys z) dz.2 := by
  simp only [Lfull, fstC, coordC, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_fst',
    Complex.ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
    Complex.real_smul]
  refine congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun j _ => by ring)

/-- **The joint derivative within `[0, T) × ℝ³`.** -/
theorem hasFDerivWithinAt_phys {z : ℝ × ES} (hz : z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set ES)) :
    HasFDerivWithinAt P.phys (P.Lfull z) (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) z := by
  obtain ⟨t, x⟩ := z
  have ht : t ∈ Ico (0 : ℝ) T := hz.1
  set s : Set (ℝ × ES) := Ico (0 : ℝ) T ×ˢ (univ : Set ES) with hs
  set D := P.D 0 0 with hD
  set D' := P.D 1 0 t with hD'
  -- the three pieces
  have hA0 := (hasDerivWithinAt_iff_isLittleO.mp (P.deriv 0 0 t ht))
  have hfst : Tendsto Prod.fst (𝓝[s] (t, x)) (𝓝[Ico (0 : ℝ) T] t) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_fst.tendsto (t, x)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz using hz.1
  have hA1 := hA0.comp_tendsto hfst
  have hA : (fun z : ℝ × ES => 𝓕⁻ (⇑(D z.1)) z.2 - 𝓕⁻ (⇑(D t)) z.2 -
      (z.1 - t) • 𝓕⁻ (⇑D') z.2) =o[𝓝[s] (t, x)] fun z => z - (t, x) := by
    have hbig : (fun z : ℝ × ES => 𝓕⁻ (⇑(D z.1)) z.2 - 𝓕⁻ (⇑(D t)) z.2 -
        (z.1 - t) • 𝓕⁻ (⇑D') z.2) =O[𝓝[s] (t, x)]
        ((fun t' => D t' - D t - (t' - t) • D') ∘ Prod.fst) := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
      rw [one_mul, Function.comp_apply, ← fourierInv_sub, ← fourierInv_smul, ← fourierInv_sub]
      exact norm_fourierInv_le _ _
    refine hbig.trans_isLittleO (hA1.trans_isBigO ?_)
    refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    rw [one_mul, Function.comp_apply]
    exact (norm_fst_le (z - (t, x)))
  have hcont : Continuous fun y => 𝓕⁻ (⇑D') y := continuous_fourierInv (L1.integrable_coeFn D')
  have hB : (fun z : ℝ × ES => (z.1 - t) • (𝓕⁻ (⇑D') z.2 - 𝓕⁻ (⇑D') x))
      =o[𝓝[s] (t, x)] fun z => z - (t, x) := by
    refine IsLittleO.of_bound fun c hc => ?_
    have hev : ∀ᶠ z in 𝓝[s] (t, x), ‖𝓕⁻ (⇑D') z.2 - 𝓕⁻ (⇑D') x‖ ≤ c := by
      have h1 : Tendsto (fun z : ℝ × ES => 𝓕⁻ (⇑D') z.2) (𝓝 (t, x)) (𝓝 (𝓕⁻ (⇑D') x)) :=
        (hcont.comp continuous_snd).tendsto (t, x)
      have h2 := h1.mono_left (nhdsWithin_le_nhds (s := s))
      filter_upwards [(Metric.tendsto_nhds.mp h2) c hc] with z hz
      rw [← dist_eq_norm]; exact hz.le
    filter_upwards [hev] with z hz
    rw [norm_smul]
    calc ‖z.1 - t‖ * ‖𝓕⁻ (⇑D') z.2 - 𝓕⁻ (⇑D') x‖ ≤ ‖z - (t, x)‖ * c :=
          mul_le_mul (norm_fst_le (z - (t, x))) hz (norm_nonneg _) (norm_nonneg _)
      _ = c * ‖z - (t, x)‖ := mul_comm _ _
  have hC : (fun z : ℝ × ES => 𝓕⁻ (⇑(D t)) z.2 - 𝓕⁻ (⇑(D t)) x -
      (∑ j : Fin 3, (EuclideanSpace.proj j : ES →L[ℝ] ℝ).smulRight
        ((2 * Real.pi : ℂ) * Complex.I * (P.shiftX j).phys (t, x))) (z.2 - x))
      =o[𝓝[s] (t, x)] fun z => z - (t, x) := by
    have hx := (hasFDerivAt_iff_isLittleO.mp (P.hasFDerivAt_phys_space t x))
    have hsnd : Tendsto Prod.snd (𝓝[s] (t, x)) (𝓝 x) :=
      ((continuous_snd.tendsto (t, x)).mono_left nhdsWithin_le_nhds)
    refine (hx.comp_tendsto hsnd).trans_isBigO ?_
    refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    rw [one_mul, Function.comp_apply]
    exact norm_snd_le (z - (t, x))
  rw [hasFDerivWithinAt_iff_isLittleO]
  refine ((hA.add hB).add hC).congr_left fun z => ?_
  rw [Lfull_apply]
  simp only [phys, Prod.fst_sub, Prod.snd_sub, map_sub, hD, hD']
  simp only [shiftT, phys, Complex.real_smul, ContinuousLinearMap.sum_apply, map_sub,
    Finset.sum_sub_distrib]
  ring

end SmoothFourierPath

theorem uniqueDiffOn_slab {T : ℝ} (hT : 0 < T) :
    UniqueDiffOn ℝ (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) :=
  UniqueDiffOn.prod (uniqueDiffOn_Ico 0 T) uniqueDiffOn_univ

/-- **Joint smoothness of order `n`**, for every smooth Fourier path. -/
theorem contDiffOn_phys_nat {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ∀ P : SmoothFourierPath T,
      ContDiffOn ℝ n P.phys (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) := by
  induction n with
  | zero =>
      intro P
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun z hz => (P.hasFDerivWithinAt_phys hz).continuousWithinAt
  | succ n ih =>
      intro P
      have hU := uniqueDiffOn_slab (T := T) hT
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiffOn_succ_iff_fderivWithin hU]
      refine ⟨fun z hz => (P.hasFDerivWithinAt_phys hz).differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      have hL : ContDiffOn ℝ n P.Lfull (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) := by
        unfold SmoothFourierPath.Lfull
        refine ((ih P.shiftT).smul contDiffOn_const).add ?_
        exact ContDiffOn.sum fun j _ =>
          (contDiffOn_const.mul (ih (P.shiftX j))).smul contDiffOn_const
      exact hL.congr fun z hz => (P.hasFDerivWithinAt_phys hz).fderivWithin (hU z hz)

/-- **Joint `C^∞` smoothness of the inverse Fourier field of a smooth Fourier
path on `[0, T) × ℝ³`.** -/
theorem contDiffOn_phys {T : ℝ} (hT : 0 < T) (P : SmoothFourierPath T) :
    ContDiffOn ℝ ∞ P.phys (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) :=
  contDiffOn_infty.mpr fun n => contDiffOn_phys_nat hT n P

/-! ## The heat instance: a smooth Fourier path from any datum with all moments -/

/-- Second-order Taylor bound for `s ↦ e^{-as}` on `[0, ∞)`. -/
theorem abs_exp_taylor_le {a t t' : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    |Real.exp (-(a * t')) - Real.exp (-(a * t)) + (t' - t) * (a * Real.exp (-(a * t)))| ≤
      a ^ 2 * (t' - t) ^ 2 := by
  set φ : ℝ → ℝ := fun s =>
    Real.exp (-(a * s)) - Real.exp (-(a * t)) + (s - t) * (a * Real.exp (-(a * t))) with hφ
  set φ' : ℝ → ℝ := fun s => -(a * Real.exp (-(a * s))) + a * Real.exp (-(a * t)) with hφ'
  have hderiv : ∀ s, HasDerivAt φ (φ' s) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (-(a * s))) (Real.exp (-(a * s)) * -(a * 1)) s :=
      ((hasDerivAt_id s).const_mul a).neg.exp
    have h2 : HasDerivAt (fun s => (s - t) * (a * Real.exp (-(a * t))))
        (1 * (a * Real.exp (-(a * t)))) s :=
      ((hasDerivAt_id s).sub_const t).mul_const _
    have h3 := (h1.sub_const (Real.exp (-(a * t)))).add h2
    refine h3.congr_deriv ?_
    simp only [hφ']
    ring
  set S : Set ℝ := uIcc t t' with hS
  have hSnn : ∀ s ∈ S, 0 ≤ s := fun s hs => le_trans (le_min ht ht') hs.1
  have hbound : ∀ s ∈ S, ‖φ' s‖ ≤ a ^ 2 * |t' - t| := by
    intro s hs
    have hst : |t - s| ≤ |t' - t| := by
      rw [abs_sub_comm t s]
      exact abs_sub_left_of_mem_uIcc hs
    have hE := abs_exp_sub_exp_le ha (le_refl 0 |>.trans ht |> fun h => h) (hSnn s hs)
      (τ₀ := 0)
    rw [mul_zero, neg_zero, Real.exp_zero, mul_one] at hE
    rw [Real.norm_eq_abs, hφ']
    simp only
    rw [show -(a * Real.exp (-(a * s))) + a * Real.exp (-(a * t)) =
      a * (Real.exp (-(a * t)) - Real.exp (-(a * s))) by ring, abs_mul, abs_of_nonneg ha]
    calc a * |Real.exp (-(a * t)) - Real.exp (-(a * s))| ≤ a * (a * |t - s|) :=
          mul_le_mul_of_nonneg_left hE ha
      _ ≤ a * (a * |t' - t|) := by gcongr
      _ = a ^ 2 * |t' - t| := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hderiv s).hasDerivWithinAt) hbound (convex_uIcc t t')
    (left_mem_uIcc : t ∈ S) (right_mem_uIcc : t' ∈ S)
  have hφt : φ t = 0 := by simp [hφ]
  rw [hφt, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  calc |φ t'| ≤ a ^ 2 * |t' - t| * |t' - t| := hmvt
    _ = a ^ 2 * (t' - t) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- The Fourier monomial `ξ^α`. -/
def mono (α : Fin 3 → ℕ) (ξ : ES) : ℂ := ∏ j : Fin 3, ((ξ j : ℝ) : ℂ) ^ (α j)

theorem mono_add_ej (α : Fin 3 → ℕ) (j : Fin 3) (ξ : ES) :
    mono (α + ej j) ξ = ((ξ j : ℝ) : ℂ) * mono α ξ := by
  unfold mono
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

/-- Total degree of a multi-index. -/
def deg (α : Fin 3 → ℕ) : ℕ := ∑ j : Fin 3, α j

theorem norm_mono_le (α : Fin 3 → ℕ) (ξ : ES) : ‖mono α ξ‖ ≤ ‖ξ‖ ^ deg α := by
  unfold mono deg
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_
  rw [norm_pow, Complex.norm_real]
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le ξ j) _

section Heat

variable (ν : ℝ) (f : ES → ℂ)

/-- The heat-path coefficient `(-ν‖ξ‖²)ᵏ ξ^α e^{-ν‖ξ‖² t} f(ξ)`. -/
def heatSym (k : ℕ) (α : Fin 3 → ℕ) (t : ℝ) (ξ : ES) : ℂ :=
  ((-(ν * ‖ξ‖ ^ 2) : ℝ) : ℂ) ^ k * mono α ξ * (heatFactor ν (max t 0) ξ : ℂ) * f ξ

variable {ν f}

theorem norm_heatSym_le (hν : 0 ≤ ν) (k : ℕ) (α : Fin 3 → ℕ) (t : ℝ) (ξ : ES) :
    ‖heatSym ν f k α t ξ‖ ≤ ν ^ k * (‖ξ‖ ^ (2 * k + deg α) * ‖f ξ‖) := by
  unfold heatSym
  rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity),
    abs_of_nonneg (heatFactor_nonneg _ _ _)]
  have h1 := heatFactor_le_one hν (le_max_right t 0) ξ
  have h1' := heatFactor_nonneg ν (max t 0) ξ
  have h2 := norm_mono_le α ξ
  have h3 : (ν * ‖ξ‖ ^ 2) ^ k = ν ^ k * ‖ξ‖ ^ (2 * k) := by rw [mul_pow, ← pow_mul]
  rw [h3, pow_add]
  have hA : 0 ≤ ν ^ k * ‖ξ‖ ^ (2 * k) := by positivity
  calc ν ^ k * ‖ξ‖ ^ (2 * k) * ‖mono α ξ‖ * heatFactor ν (max t 0) ξ * ‖f ξ‖
      ≤ ν ^ k * ‖ξ‖ ^ (2 * k) * ‖ξ‖ ^ deg α * 1 * ‖f ξ‖ := by gcongr
    _ = ν ^ k * (‖ξ‖ ^ (2 * k) * ‖ξ‖ ^ deg α * ‖f ξ‖) := by ring

variable (hν : 0 ≤ ν) (hfm : AEStronglyMeasurable f volume)
  (hf : ∀ n : ℕ, Integrable (fun ξ : ES => ‖ξ‖ ^ n * ‖f ξ‖))
include hν hfm hf

theorem integrable_heatSym (k : ℕ) (α : Fin 3 → ℕ) (t : ℝ) :
    Integrable (heatSym ν f k α t) := by
  refine ((hf (2 * k + deg α)).const_mul (ν ^ k)).mono' ?_
    (Eventually.of_forall fun ξ => norm_heatSym_le hν k α t ξ)
  unfold heatSym
  refine (((Continuous.aestronglyMeasurable ?_).mul (Continuous.aestronglyMeasurable ?_)).mul
    (Continuous.aestronglyMeasurable ?_)).mul hfm
  · exact (Complex.continuous_ofReal.comp ((continuous_const.mul
      (continuous_norm.pow 2)).neg)).pow k
  · unfold mono; fun_prop
  · unfold heatFactor; fun_prop

/-- The heat path's coefficient classes. -/
def heatD (k : ℕ) (α : Fin 3 → ℕ) (t : ℝ) : L1C :=
  (integrable_heatSym hν hfm hf k α t).toL1 _

theorem coeFn_heatD (k : ℕ) (α : Fin 3 → ℕ) (t : ℝ) :
    ⇑(heatD hν hfm hf k α t) =ᵐ[volume] heatSym ν f k α t :=
  Integrable.coeFn_toL1 _

theorem heat_taylor_pt {k : ℕ} {α : Fin 3 → ℕ} {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (ξ : ES) :
    ‖heatSym ν f k α t' ξ - heatSym ν f k α t ξ - (t' - t) • heatSym ν f (k + 1) α t ξ‖ ≤
      ν ^ (k + 2) * (‖ξ‖ ^ (2 * (k + 2) + deg α) * ‖f ξ‖) * (t' - t) ^ 2 := by
  set a : ℝ := ν * ‖ξ‖ ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hdecomp : heatSym ν f k α t' ξ - heatSym ν f k α t ξ - (t' - t) • heatSym ν f (k + 1) α t ξ
      = (((-(a)) : ℝ) : ℂ) ^ k * mono α ξ * f ξ *
        ((Real.exp (-(a * t')) - Real.exp (-(a * t)) + (t' - t) * (a * Real.exp (-(a * t))) :
          ℝ) : ℂ) := by
    unfold heatSym heatFactor
    rw [max_eq_left ht, max_eq_left ht', ← ha]
    simp only [Complex.real_smul]
    push_cast
    ring_nf
  rw [hdecomp, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hT := abs_exp_taylor_le ha0 ht ht'
  have hbase : ‖(((-(a)) : ℝ) : ℂ) ^ k * mono α ξ * f ξ‖ ≤
      ν ^ k * (‖ξ‖ ^ (2 * k + deg α) * ‖f ξ‖) := by
    have := norm_heatSym_le (f := f) hν k α 0 ξ
    unfold heatSym at this
    rw [max_self, show heatFactor ν 0 ξ = 1 by simp [heatFactor], Complex.ofReal_one,
      mul_one] at this
    simpa [ha] using this
  calc ‖(((-(a)) : ℝ) : ℂ) ^ k * mono α ξ * f ξ‖ *
        |Real.exp (-(a * t')) - Real.exp (-(a * t)) + (t' - t) * (a * Real.exp (-(a * t)))|
      ≤ ν ^ k * (‖ξ‖ ^ (2 * k + deg α) * ‖f ξ‖) * (a ^ 2 * (t' - t) ^ 2) :=
        mul_le_mul hbase hT (abs_nonneg _) (by positivity)
    _ = ν ^ (k + 2) * (‖ξ‖ ^ (2 * (k + 2) + deg α) * ‖f ξ‖) * (t' - t) ^ 2 := by
        rw [ha]; ring

theorem heatD_mul (k : ℕ) (α : Fin 3 → ℕ) (j : Fin 3) (t : ℝ) :
    ⇑(heatD hν hfm hf k (α + ej j) t) =ᵐ[volume]
      fun ξ : ES => ((ξ j : ℝ) : ℂ) * heatD hν hfm hf k α t ξ := by
  filter_upwards [coeFn_heatD hν hfm hf k (α + ej j) t, coeFn_heatD hν hfm hf k α t]
    with ξ h1 h2
  rw [h1, h2]
  unfold heatSym
  rw [mono_add_ej]
  ring

theorem heatD_deriv (k : ℕ) (α : Fin 3 → ℕ) {T t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (heatD hν hfm hf k α) (heatD hν hfm hf (k + 1) α t) (Ico (0 : ℝ) T) t := by
  rw [hasDerivWithinAt_iff_isLittleO]
  set C : ℝ := ν ^ (k + 2) * ∫ ξ, ‖ξ‖ ^ (2 * (k + 2) + deg α) * ‖f ξ‖ with hC
  have hbound : ∀ t' : ℝ, 0 ≤ t' →
      ‖heatD hν hfm hf k α t' - heatD hν hfm hf k α t - (t' - t) • heatD hν hfm hf (k + 1) α t‖
        ≤ C * ‖t' - t‖ ^ 2 := by
    intro t' ht'
    rw [L1.norm_eq_integral_norm]
    have hae : (fun ξ => ‖(heatD hν hfm hf k α t' - heatD hν hfm hf k α t -
        (t' - t) • heatD hν hfm hf (k + 1) α t : L1C) ξ‖) =ᵐ[volume]
        fun ξ => ‖heatSym ν f k α t' ξ - heatSym ν f k α t ξ -
          (t' - t) • heatSym ν f (k + 1) α t ξ‖ := by
      filter_upwards [Lp.coeFn_sub (heatD hν hfm hf k α t' - heatD hν hfm hf k α t)
          ((t' - t) • heatD hν hfm hf (k + 1) α t),
        Lp.coeFn_sub (heatD hν hfm hf k α t') (heatD hν hfm hf k α t),
        Lp.coeFn_smul (t' - t) (heatD hν hfm hf (k + 1) α t),
        coeFn_heatD hν hfm hf k α t', coeFn_heatD hν hfm hf k α t,
        coeFn_heatD hν hfm hf (k + 1) α t] with ξ h1 h2 h3 h4 h5 h6
      rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, h5, h6]
    rw [integral_congr_ae hae, Real.norm_eq_abs, sq_abs, hC, mul_assoc, ← integral_mul_const,
      ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (((hf _).mul_const _).const_mul _) (Eventually.of_forall fun ξ => ?_)
    have := heat_taylor_pt hν hfm hf ht.1 ht' ξ (k := k) (α := α)
    simpa [mul_assoc] using this
  have hO : (fun t' => heatD hν hfm hf k α t' - heatD hν hfm hf k α t -
      (t' - t) • heatD hν hfm hf (k + 1) α t) =O[𝓝[Ico (0 : ℝ) T] t]
      fun t' => ‖t' - t‖ ^ 2 := by
    refine IsBigO.of_bound C ?_
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound t' ht'.1
  exact hO.trans_isLittleO ((isLittleO_pow_sub_sub t one_lt_two).mono nhdsWithin_le_nhds)

/-- **The heat instance.**  Any datum with every polynomial Fourier moment
integrable generates a smooth Fourier path. -/
def heatPathSFP (T : ℝ) : SmoothFourierPath T where
  D := heatD hν hfm hf
  mul := heatD_mul hν hfm hf
  deriv k α _ ht := heatD_deriv hν hfm hf k α ht

end Heat

end Navier.Analysis.WienerSmoothPath

set_option pp.fullNames true in
#check @Navier.Analysis.WienerSmoothPath.heatPathSFP
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerSmoothPath.heatPathSFP
