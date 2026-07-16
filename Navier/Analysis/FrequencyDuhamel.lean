import Navier.Analysis.FrequencyHeatLeray

/-!
# One-frequency mild (Duhamel) solutions: the Kato fixed-point layer

This file builds the mild-solution formulation of the Navier--Stokes scheme
over the landed one-frequency heat--Leray multipliers and proves local
existence and uniqueness by the Banach fixed-point theorem, following the
classical Kato pattern (T. Kato, *Strong L^p-solutions of the Navier–Stokes
equation in R^m*, Math. Z. 187 (1984); Fujita–Kato 1964) specialized to one
retained frequency.

A mild solution on `[0, T]` for viscosity `ν`, frequency `q`, convection
symbol `b` (an arbitrary continuous bilinear map on the frequency fiber), and
initial amplitude `u₀` is a continuous path `u` satisfying the Duhamel
identity

`u t = frequencyHeatLeray ν t q u₀ + ∫ s in 0..t, frequencyHeatLeray ν (t-s) q (b (u s) (u s))`.

The heat--Leray kernel already contains the Leray projection, exactly as the
projected Duhamel formula does on the PDE side.  The three analytic inputs
are all landed: the kernel contraction `frequencyHeatLeray_norm_le`, the
exact semigroup factorization of the scalar heat decay, and the bilinear
estimate through the transversality layer proved here
(`frequencyHeatLeray_bilinear_norm_le`).

Main results:
* `exists_isMildSolutionOn` — local existence in the closed ball of radius
  `R` under the explicit smallness `‖u₀‖ ≤ R/2` and `‖b‖ * R * T ≤ 4⁻¹`,
  by `ContractingWith.exists_fixedPoint'` on `C(Icc 0 T, E3)`.
* `isMildSolutionOn_unique` — uniqueness of mild solutions in that ball.
* `IsMildSolutionOn.apply_zero` — the mild solution launches from the Leray
  projection of the initial amplitude.
* `IsMildSolutionOn.inner_frequency_eq_zero` — mild solutions remain
  transverse to their frequency for all time: the divergence-free constraint
  propagates through the Duhamel integral.

This is finite-dimensional frequencywise infrastructure: it does not define
a Fourier transform on function spaces or a whole-space bilinear estimate.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.FrequencyDuhamel

open Navier.Analysis.LerayProjection
open Navier.Analysis.FrequencyHeatLeray
open MeasureTheory

/-- Exact factorization of the scalar heat decay across the Duhamel kernel. -/
theorem heatDecay_factor (ν t s : ℝ) (q : E3) :
    heatDecay ν (t - s) q = heatDecay ν t q * heatDecay ν (-s) q := by
  unfold heatDecay
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Bilinear estimate on the transversality layer**: the heat--Leray kernel
applied to a bilinear convection symbol is controlled by the product of the
input norms, uniformly in nonnegative viscosity and time. -/
theorem frequencyHeatLeray_bilinear_norm_le {ν τ : ℝ}
    (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (q : E3)
    (b : E3 →L[ℝ] E3 →L[ℝ] E3) (v w : E3) :
    ‖frequencyHeatLeray ν τ q (b v w)‖ ≤ ‖b‖ * ‖v‖ * ‖w‖ :=
  le_trans (frequencyHeatLeray_norm_le hν hτ q (b v w)) (b.le_opNorm₂ v w)

/-- Quadratic difference estimate for a continuous bilinear symbol. -/
theorem bilinear_diff_norm_le (b : E3 →L[ℝ] E3 →L[ℝ] E3) (v w : E3) :
    ‖b v v - b w w‖ ≤ ‖b‖ * (‖v‖ + ‖w‖) * ‖v - w‖ := by
  have h1 : b v (v - w) = b v v - b v w := map_sub (b v) v w
  have h2 : b (v - w) w = b v w - b w w := by
    rw [map_sub]
    rfl
  have hdecomp : b v v - b w w = b v (v - w) + b (v - w) w := by
    rw [h1, h2]
    abel
  calc ‖b v v - b w w‖ = ‖b v (v - w) + b (v - w) w‖ := by rw [hdecomp]
    _ ≤ ‖b v (v - w)‖ + ‖b (v - w) w‖ := norm_add_le _ _
    _ ≤ ‖b‖ * ‖v‖ * ‖v - w‖ + ‖b‖ * ‖v - w‖ * ‖w‖ :=
        add_le_add (b.le_opNorm₂ v (v - w)) (b.le_opNorm₂ (v - w) w)
    _ = ‖b‖ * (‖v‖ + ‖w‖) * ‖v - w‖ := by ring

/-- The mild (Duhamel) formulation at one frequency: a continuous path
satisfying the projected integral equation driven by the heat--Leray
kernel. -/
def IsMildSolutionOn (ν : ℝ) (q : E3) (b : E3 →L[ℝ] E3 →L[ℝ] E3)
    (u₀ : E3) (T : ℝ) (u : ℝ → E3) : Prop :=
  ContinuousOn u (Set.Icc 0 T) ∧
    ∀ t : ℝ, t ∈ Set.Icc 0 T →
      u t = frequencyHeatLeray ν t q u₀ +
        ∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) q (b (u s) (u s))

/-- The solution path space: continuous maps from the compact horizon. -/
abbrev PathSpace (T : ℝ) := C(Set.Icc (0:ℝ) T, E3)

section DuhamelMap

variable (ν : ℝ) (q : E3) (b : E3 →L[ℝ] E3 →L[ℝ] E3) (u₀ : E3)
variable {T : ℝ} (hT : (0:ℝ) ≤ T)

/-- Extend a path on the horizon to all of `ℝ` by clamping. -/
def pathExtend (f : PathSpace T) : ℝ → E3 :=
  Set.IccExtend hT f

theorem continuous_pathExtend (f : PathSpace T) :
    Continuous (pathExtend hT f) :=
  f.continuous.Icc_extend'

theorem pathExtend_of_mem (f : PathSpace T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    pathExtend hT f t = f ⟨t, ht⟩ :=
  Set.IccExtend_of_mem hT f ht

/-- Membership in the closed ball bounds every clamped evaluation. -/
theorem norm_pathExtend_le {f : PathSpace T} {R : ℝ}
    (hf : f ∈ Metric.closedBall (0 : PathSpace T) R) (s : ℝ) :
    ‖pathExtend hT f s‖ ≤ R := by
  have happly := ContinuousMap.dist_apply_le_dist
    (f := f) (g := (0 : PathSpace T)) (Set.projIcc 0 T hT s)
  have hball : dist f (0 : PathSpace T) ≤ R := Metric.mem_closedBall.1 hf
  have hthis : dist (f (Set.projIcc 0 T hT s)) 0 ≤ R := by
    simpa using happly.trans hball
  rw [dist_zero_right] at hthis
  show ‖f (Set.projIcc 0 T hT s)‖ ≤ R
  exact hthis

/-- The factorized Duhamel integrand at unit heat weight. -/
def duhamelIntegrand (f : PathSpace T) : ℝ → E3 :=
  fun s => heatDecay ν (-s) q •
    euclideanLeray q (b (pathExtend hT f s) (pathExtend hT f s))

theorem continuous_heatDecay_neg :
    Continuous fun s : ℝ => heatDecay ν (-s) q := by
  unfold heatDecay
  fun_prop

theorem continuous_bilinear_pathExtend (f : PathSpace T) :
    Continuous fun s : ℝ =>
      b (pathExtend hT f s) (pathExtend hT f s) := by
  have hext : Continuous (pathExtend hT f) := continuous_pathExtend hT f
  exact b.continuous₂.comp (hext.prodMk hext)

theorem continuous_duhamelIntegrand (f : PathSpace T) :
    Continuous (duhamelIntegrand ν q b hT f) := by
  exact (continuous_heatDecay_neg ν q).smul
    ((euclideanLeray q).continuous.comp
      (continuous_bilinear_pathExtend b hT f))

/-- The running Duhamel primitive. -/
def duhamelPrimitive (f : PathSpace T) : ℝ → E3 :=
  fun t => ∫ s in (0:ℝ)..t, duhamelIntegrand ν q b hT f s

theorem continuous_duhamelPrimitive (f : PathSpace T) :
    Continuous (duhamelPrimitive ν q b hT f) :=
  intervalIntegral.continuous_primitive
    (fun a b' => (continuous_duhamelIntegrand ν q b hT f).intervalIntegrable a b') 0

/-- The Duhamel map in factorized form. -/
def duhamelFun (f : PathSpace T) : ℝ → E3 :=
  fun t => frequencyHeatLeray ν t q u₀ +
    heatDecay ν t q • duhamelPrimitive ν q b hT f t

theorem continuous_heatDecay_time :
    Continuous fun t : ℝ => heatDecay ν t q := by
  unfold heatDecay
  fun_prop

theorem continuous_duhamelFun (f : PathSpace T) :
    Continuous (duhamelFun ν q b u₀ hT f) := by
  unfold duhamelFun
  have h1 : Continuous fun t : ℝ => frequencyHeatLeray ν t q u₀ := by
    have : (fun t : ℝ => frequencyHeatLeray ν t q u₀) =
        fun t : ℝ => heatDecay ν t q • euclideanLeray q u₀ := by
      funext t
      exact frequencyHeatLeray_apply ν t q u₀
    rw [this]
    exact (continuous_heatDecay_time ν q).smul continuous_const
  exact h1.add ((continuous_heatDecay_time ν q).smul
    (continuous_duhamelPrimitive ν q b hT f))

/-- The Duhamel self-map of the path space. -/
def duhamelMap (f : PathSpace T) : PathSpace T :=
  ⟨fun t => duhamelFun ν q b u₀ hT f t,
    (continuous_duhamelFun ν q b u₀ hT f).comp continuous_subtype_val⟩

@[simp] theorem duhamelMap_apply (f : PathSpace T) (t : Set.Icc (0:ℝ) T) :
    duhamelMap ν q b u₀ hT f t = duhamelFun ν q b u₀ hT f t := rfl

/-- The factorized Duhamel map agrees with the honest kernel integral. -/
theorem duhamelFun_eq_kernel (f : PathSpace T) (t : ℝ) :
    duhamelFun ν q b u₀ hT f t =
      frequencyHeatLeray ν t q u₀ +
        ∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) q
          (b (pathExtend hT f s) (pathExtend hT f s)) := by
  unfold duhamelFun duhamelPrimitive
  congr 1
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun s _hs => ?_
  show heatDecay ν t q • duhamelIntegrand ν q b hT f s = _
  unfold duhamelIntegrand
  rw [frequencyHeatLeray_apply, smul_smul, ← heatDecay_factor]

/-- Continuity of the kernel-form integrand. -/
theorem continuous_kernelIntegrand (f : PathSpace T) (t : ℝ) :
    Continuous fun s : ℝ => frequencyHeatLeray ν (t - s) q
      (b (pathExtend hT f s) (pathExtend hT f s)) := by
  have : (fun s : ℝ => frequencyHeatLeray ν (t - s) q
      (b (pathExtend hT f s) (pathExtend hT f s))) =
      fun s : ℝ => heatDecay ν (t - s) q •
        euclideanLeray q (b (pathExtend hT f s) (pathExtend hT f s)) := by
    funext s
    exact frequencyHeatLeray_apply ν (t - s) q _
  rw [this]
  have hheat : Continuous fun s : ℝ => heatDecay ν (t - s) q := by
    unfold heatDecay
    fun_prop
  exact hheat.smul ((euclideanLeray q).continuous.comp
    (continuous_bilinear_pathExtend b hT f))

end DuhamelMap

section Existence

variable {ν T R : ℝ} {q : E3} {b : E3 →L[ℝ] E3 →L[ℝ] E3} {u₀ : E3}

/-- Pointwise ball bound for the Duhamel image. -/
theorem norm_duhamelFun_le
    (hν : 0 ≤ ν) (hT : (0:ℝ) ≤ T) (hR : 0 ≤ R)
    (hu₀ : ‖u₀‖ ≤ R / 2) (hsmall : ‖b‖ * R * T ≤ 4⁻¹)
    {f : PathSpace T} (hf : f ∈ Metric.closedBall (0 : PathSpace T) R)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ‖duhamelFun ν q b u₀ hT f t‖ ≤ R := by
  obtain ⟨ht0, htT⟩ := ht
  rw [duhamelFun_eq_kernel]
  have hheat : ‖frequencyHeatLeray ν t q u₀‖ ≤ R / 2 :=
    le_trans (frequencyHeatLeray_norm_le hν ht0 q u₀) hu₀
  have hpoint : ∀ s ∈ Set.uIoc (0:ℝ) t,
      ‖frequencyHeatLeray ν (t - s) q
        (b (pathExtend hT f s) (pathExtend hT f s))‖ ≤ ‖b‖ * R * R := by
    intro s hs
    rw [Set.uIoc_of_le ht0] at hs
    have hts : 0 ≤ t - s := sub_nonneg.2 hs.2
    refine le_trans (frequencyHeatLeray_bilinear_norm_le hν hts q b _ _) ?_
    have h1 : ‖pathExtend hT f s‖ ≤ R := norm_pathExtend_le hT hf s
    have hb0 : (0:ℝ) ≤ ‖b‖ := norm_nonneg b
    calc ‖b‖ * ‖pathExtend hT f s‖ * ‖pathExtend hT f s‖
        ≤ ‖b‖ * R * ‖pathExtend hT f s‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left h1 hb0
      _ ≤ ‖b‖ * R * R :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hb0 hR)
  have hint : ‖∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) q
      (b (pathExtend hT f s) (pathExtend hT f s))‖ ≤ ‖b‖ * R * R * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have habs : |t - 0| ≤ T := by
    rw [sub_zero, abs_of_nonneg ht0]
    exact htT
  have hC : (0:ℝ) ≤ ‖b‖ * R * R :=
    mul_nonneg (mul_nonneg (norm_nonneg b) hR) hR
  have hint' : ‖∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) q
      (b (pathExtend hT f s) (pathExtend hT f s))‖ ≤ ‖b‖ * R * T * R := by
    refine le_trans hint ?_
    calc ‖b‖ * R * R * |t - 0| ≤ ‖b‖ * R * R * T :=
          mul_le_mul_of_nonneg_left habs hC
      _ = ‖b‖ * R * T * R := by ring
  have hquarter : ‖b‖ * R * T * R ≤ 4⁻¹ * R :=
    mul_le_mul_of_nonneg_right hsmall hR
  calc ‖frequencyHeatLeray ν t q u₀ +
        ∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) q
          (b (pathExtend hT f s) (pathExtend hT f s))‖
      ≤ ‖frequencyHeatLeray ν t q u₀‖ +
        ‖∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) q
          (b (pathExtend hT f s) (pathExtend hT f s))‖ := norm_add_le _ _
    _ ≤ R / 2 + 4⁻¹ * R := add_le_add hheat (le_trans hint' hquarter)
    _ ≤ R := by linarith

/-- The Duhamel map preserves the closed ball. -/
theorem duhamelMap_mapsTo
    (hν : 0 ≤ ν) (hT : (0:ℝ) ≤ T) (hR : 0 ≤ R)
    (hu₀ : ‖u₀‖ ≤ R / 2) (hsmall : ‖b‖ * R * T ≤ 4⁻¹) :
    Set.MapsTo (duhamelMap ν q b u₀ hT)
      (Metric.closedBall (0 : PathSpace T) R)
      (Metric.closedBall (0 : PathSpace T) R) := by
  intro f hf
  rw [Metric.mem_closedBall]
  rw [ContinuousMap.dist_le hR]
  intro x
  have hx := norm_duhamelFun_le (q := q) (b := b) (u₀ := u₀) hν hT hR hu₀ hsmall hf x.2
  show dist (duhamelFun ν q b u₀ hT f x) ((0 : PathSpace T) x) ≤ R
  rw [ContinuousMap.zero_apply, dist_zero_right]
  exact hx

/-- Half-Lipschitz estimate for the Duhamel map on the closed ball. -/
theorem dist_duhamelMap_le
    (hν : 0 ≤ ν) (hT : (0:ℝ) ≤ T) (hR : 0 ≤ R)
    (hsmall : ‖b‖ * R * T ≤ 4⁻¹)
    {f g : PathSpace T}
    (hf : f ∈ Metric.closedBall (0 : PathSpace T) R)
    (hg : g ∈ Metric.closedBall (0 : PathSpace T) R) :
    dist (duhamelMap ν q b u₀ hT f) (duhamelMap ν q b u₀ hT g) ≤
      2⁻¹ * dist f g := by
  have hd0 : (0:ℝ) ≤ 2⁻¹ * dist f g := by positivity
  rw [ContinuousMap.dist_le hd0]
  intro x
  obtain ⟨hx0, hxT⟩ := x.2
  rw [duhamelMap_apply, duhamelMap_apply, dist_eq_norm,
    duhamelFun_eq_kernel, duhamelFun_eq_kernel, add_sub_add_left_eq_sub]
  have hintf : IntervalIntegrable (fun s => frequencyHeatLeray ν ((x:ℝ) - s) q
      (b (pathExtend hT f s) (pathExtend hT f s))) volume 0 (x:ℝ) :=
    (continuous_kernelIntegrand ν q b hT f (x:ℝ)).intervalIntegrable 0 (x:ℝ)
  have hintg : IntervalIntegrable (fun s => frequencyHeatLeray ν ((x:ℝ) - s) q
      (b (pathExtend hT g s) (pathExtend hT g s))) volume 0 (x:ℝ) :=
    (continuous_kernelIntegrand ν q b hT g (x:ℝ)).intervalIntegrable 0 (x:ℝ)
  rw [← intervalIntegral.integral_sub hintf hintg]
  have hpoint : ∀ s ∈ Set.uIoc (0:ℝ) (x:ℝ),
      ‖frequencyHeatLeray ν ((x:ℝ) - s) q
          (b (pathExtend hT f s) (pathExtend hT f s)) -
        frequencyHeatLeray ν ((x:ℝ) - s) q
          (b (pathExtend hT g s) (pathExtend hT g s))‖ ≤
      ‖b‖ * (R + R) * dist f g := by
    intro s hs
    rw [Set.uIoc_of_le hx0] at hs
    have hts : 0 ≤ (x:ℝ) - s := sub_nonneg.2 hs.2
    rw [← map_sub]
    refine le_trans (frequencyHeatLeray_norm_le hν hts q _) ?_
    refine le_trans (bilinear_diff_norm_le b _ _) ?_
    have hsum : ‖pathExtend hT f s‖ + ‖pathExtend hT g s‖ ≤ R + R :=
      add_le_add (norm_pathExtend_le hT hf s) (norm_pathExtend_le hT hg s)
    have hdiff : ‖pathExtend hT f s - pathExtend hT g s‖ ≤ dist f g := by
      rw [← dist_eq_norm]
      show dist (pathExtend hT f s) (pathExtend hT g s) ≤ dist f g
      rw [pathExtend, pathExtend, Set.IccExtend, Set.IccExtend]
      exact ContinuousMap.dist_apply_le_dist _
    have hb0 : (0:ℝ) ≤ ‖b‖ := norm_nonneg b
    calc ‖b‖ * (‖pathExtend hT f s‖ + ‖pathExtend hT g s‖) *
          ‖pathExtend hT f s - pathExtend hT g s‖
        ≤ ‖b‖ * (R + R) * ‖pathExtend hT f s - pathExtend hT g s‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hsum hb0
      _ ≤ ‖b‖ * (R + R) * dist f g := by
          apply mul_le_mul_of_nonneg_left hdiff
          have : (0:ℝ) ≤ R + R := by linarith
          exact mul_nonneg hb0 this
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  refine le_trans hint ?_
  have habs : |(x:ℝ) - 0| ≤ T := by
    rw [sub_zero, abs_of_nonneg hx0]
    exact hxT
  have hC : (0:ℝ) ≤ ‖b‖ * (R + R) * dist f g := by positivity
  calc ‖b‖ * (R + R) * dist f g * |(x:ℝ) - 0|
      ≤ ‖b‖ * (R + R) * dist f g * T := mul_le_mul_of_nonneg_left habs hC
    _ = 2 * (‖b‖ * R * T) * dist f g := by ring
    _ ≤ 2 * 4⁻¹ * dist f g := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        linarith
    _ = 2⁻¹ * dist f g := by norm_num

/-- The restricted Duhamel map is a `2⁻¹`-contraction of the closed ball. -/
theorem duhamelMap_contracting
    (hν : 0 ≤ ν) (hT : (0:ℝ) ≤ T) (hR : 0 ≤ R)
    (hu₀ : ‖u₀‖ ≤ R / 2) (hsmall : ‖b‖ * R * T ≤ 4⁻¹) :
    ContractingWith 2⁻¹
      ((duhamelMap_mapsTo (q := q) (b := b) (u₀ := u₀)
        hν hT hR hu₀ hsmall).restrict (duhamelMap ν q b u₀ hT) _ _) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun a c => ?_⟩
  have hd := dist_duhamelMap_le (q := q) (b := b) (u₀ := u₀)
    hν hT hR hsmall a.2 c.2
  rw [Subtype.dist_eq, Subtype.dist_eq]
  simp only [Set.MapsTo.val_restrict_apply]
  calc dist (duhamelMap ν q b u₀ hT (a : PathSpace T))
        (duhamelMap ν q b u₀ hT (c : PathSpace T))
      ≤ 2⁻¹ * dist (a : PathSpace T) (c : PathSpace T) := hd
    _ = ((2⁻¹ : NNReal) : ℝ) * dist (a : PathSpace T) (c : PathSpace T) := by
        norm_num

/-- **Local existence of mild solutions** (Kato fixed-point scheme at one
frequency).  Under the explicit smallness conditions, a mild solution exists
on `[0, T]` with uniform bound `R`. -/
theorem exists_isMildSolutionOn
    (hν : 0 ≤ ν) (hT : (0:ℝ) ≤ T) (hR : 0 ≤ R)
    (hu₀ : ‖u₀‖ ≤ R / 2) (hsmall : ‖b‖ * R * T ≤ 4⁻¹) :
    ∃ u : ℝ → E3, IsMildSolutionOn ν q b u₀ T u ∧
      ∀ t ∈ Set.Icc (0:ℝ) T, ‖u t‖ ≤ R := by
  classical
  have hsc : IsComplete (Metric.closedBall (0 : PathSpace T) R) :=
    Metric.isClosed_closedBall.isComplete
  have hmaps := duhamelMap_mapsTo (q := q) (b := b) (u₀ := u₀)
    hν hT hR hu₀ hsmall
  have hcontr := duhamelMap_contracting (q := q) (b := b) (u₀ := u₀)
    hν hT hR hu₀ hsmall
  have h0mem : (0 : PathSpace T) ∈ Metric.closedBall (0 : PathSpace T) R := by
    simpa [Metric.mem_closedBall] using hR
  obtain ⟨y, hy_mem, hy_fix, -, -⟩ :=
    hcontr.exists_fixedPoint' hsc hmaps h0mem (edist_ne_top _ _)
  refine ⟨pathExtend hT y, ⟨(continuous_pathExtend hT y).continuousOn, ?_⟩, ?_⟩
  · intro t ht
    have happ : duhamelMap ν q b u₀ hT y ⟨t, ht⟩ = y ⟨t, ht⟩ := by
      rw [hy_fix]
    rw [pathExtend_of_mem hT y ht, ← happ, duhamelMap_apply,
      duhamelFun_eq_kernel]
  · intro t ht
    rw [pathExtend_of_mem hT y ht]
    have := ContinuousMap.dist_apply_le_dist
      (f := y) (g := (0 : PathSpace T)) ⟨t, ht⟩
    have hyR : dist y (0 : PathSpace T) ≤ R := Metric.mem_closedBall.1 hy_mem
    have hpt : dist (y ⟨t, ht⟩) 0 ≤ R := by
      simpa using this.trans hyR
    simpa [dist_zero_right] using hpt

/-- Any mild solution bounded by `R` restricts to a ball fixed point of the
Duhamel map. -/
theorem isMildSolutionOn_restrict_isFixedPt
    (hT : (0:ℝ) ≤ T) {u : ℝ → E3}
    (hu : IsMildSolutionOn ν q b u₀ T u)
    (hub : ∀ t ∈ Set.Icc (0:ℝ) T, ‖u t‖ ≤ R) :
    ∃ f : PathSpace T,
      (∀ t : Set.Icc (0:ℝ) T, f t = u t) ∧
      f ∈ Metric.closedBall (0 : PathSpace T) R ∧
      Function.IsFixedPt (duhamelMap ν q b u₀ hT) f := by
  classical
  refine ⟨⟨fun t => u t, ?_⟩, fun t => rfl, ?_, ?_⟩
  · exact hu.1.restrict
  · rw [Metric.mem_closedBall, ContinuousMap.dist_le]
    · intro x
      have := hub x x.2
      simpa [dist_zero_right] using this
    · rcases (Set.nonempty_Icc.2 hT) with ⟨t0, ht0⟩
      have := hub t0 ht0
      exact le_trans (norm_nonneg _) this
  · set f : PathSpace T := ⟨fun t => u t, hu.1.restrict⟩ with hf
    refine ContinuousMap.ext fun x => ?_
    rw [duhamelMap_apply, duhamelFun_eq_kernel]
    have hker : ∀ s ∈ Set.uIcc (0:ℝ) (x:ℝ),
        frequencyHeatLeray ν ((x:ℝ) - s) q
            (b (pathExtend hT f s) (pathExtend hT f s)) =
          frequencyHeatLeray ν ((x:ℝ) - s) q (b (u s) (u s)) := by
      intro s hs
      have hs' : s ∈ Set.Icc (0:ℝ) T := by
        rw [Set.uIcc_of_le x.2.1] at hs
        exact ⟨hs.1, le_trans hs.2 x.2.2⟩
      rw [pathExtend_of_mem hT f hs']
      rfl
    rw [intervalIntegral.integral_congr hker]
    show _ = f x
    have := (hu.2 (x:ℝ) x.2).symm
    rw [this]
    rfl

/-- **Uniqueness of mild solutions in the ball class**: two mild solutions on
`[0, T]` bounded by `R` agree on the whole horizon. -/
theorem isMildSolutionOn_unique
    (hν : 0 ≤ ν) (hT : (0:ℝ) ≤ T) (hR : 0 ≤ R)
    (hu₀ : ‖u₀‖ ≤ R / 2) (hsmall : ‖b‖ * R * T ≤ 4⁻¹)
    {u v : ℝ → E3}
    (hu : IsMildSolutionOn ν q b u₀ T u)
    (hv : IsMildSolutionOn ν q b u₀ T v)
    (hub : ∀ t ∈ Set.Icc (0:ℝ) T, ‖u t‖ ≤ R)
    (hvb : ∀ t ∈ Set.Icc (0:ℝ) T, ‖v t‖ ≤ R) :
    Set.EqOn u v (Set.Icc 0 T) := by
  classical
  obtain ⟨fu, hfu_eq, hfu_mem, hfu_fix⟩ :=
    isMildSolutionOn_restrict_isFixedPt hT hu hub
  obtain ⟨fv, hfv_eq, hfv_mem, hfv_fix⟩ :=
    isMildSolutionOn_restrict_isFixedPt hT hv hvb
  have hmaps := duhamelMap_mapsTo (q := q) (b := b) (u₀ := u₀)
    hν hT hR hu₀ hsmall
  have hcontr := duhamelMap_contracting (q := q) (b := b) (u₀ := u₀)
    hν hT hR hu₀ hsmall
  have hfixu : Function.IsFixedPt
      (hmaps.restrict (duhamelMap ν q b u₀ hT) _ _) ⟨fu, hfu_mem⟩ :=
    Subtype.ext (by
      simp only [Set.MapsTo.val_restrict_apply]
      exact hfu_fix)
  have hfixv : Function.IsFixedPt
      (hmaps.restrict (duhamelMap ν q b u₀ hT) _ _) ⟨fv, hfv_mem⟩ :=
    Subtype.ext (by
      simp only [Set.MapsTo.val_restrict_apply]
      exact hfv_fix)
  have hsame := hcontr.fixedPoint_unique' hfixu hfixv
  intro t ht
  have hval : fu = fv := congrArg Subtype.val hsame
  calc u t = fu ⟨t, ht⟩ := (hfu_eq ⟨t, ht⟩).symm
    _ = fv ⟨t, ht⟩ := by rw [hval]
    _ = v t := hfv_eq ⟨t, ht⟩

end Existence

section Structure

variable {ν T : ℝ} {q : E3} {b : E3 →L[ℝ] E3 →L[ℝ] E3} {u₀ : E3} {u : ℝ → E3}

/-- A mild solution launches from the Leray projection of its initial
amplitude. -/
theorem IsMildSolutionOn.apply_zero (hT : (0:ℝ) ≤ T)
    (hu : IsMildSolutionOn ν q b u₀ T u) :
    u 0 = euclideanLeray q u₀ := by
  have h := hu.2 0 (Set.left_mem_Icc.2 hT)
  simpa [intervalIntegral.integral_same, frequencyHeatLeray_zero_time]
    using h

/-- **Transversality propagates through the Duhamel integral**: a mild
solution remains orthogonal to its frequency at every time, whatever the
convection symbol.  This is the mild form of the divergence-free
constraint. -/
theorem IsMildSolutionOn.inner_frequency_eq_zero
    (hu : IsMildSolutionOn ν q b u₀ T u) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    inner ℝ q (u t) = 0 := by
  rw [hu.2 t ht, inner_add_right]
  rw [frequencyHeatLeray_transverse]
  rw [zero_add]
  have hcont : ContinuousOn
      (fun s : ℝ => frequencyHeatLeray ν (t - s) q (b (u s) (u s)))
      (Set.uIcc (0:ℝ) t) := by
    have hsub : Set.uIcc (0:ℝ) t ⊆ Set.Icc (0:ℝ) T := by
      rw [Set.uIcc_of_le ht.1]
      exact Set.Icc_subset_Icc le_rfl ht.2
    have huc : ContinuousOn u (Set.uIcc (0:ℝ) t) := hu.1.mono hsub
    have hbc : ContinuousOn (fun s : ℝ => b (u s) (u s))
        (Set.uIcc (0:ℝ) t) :=
      b.continuous₂.comp_continuousOn (huc.prodMk huc)
    have hshape : (fun s : ℝ => frequencyHeatLeray ν (t - s) q (b (u s) (u s))) =
        fun s : ℝ => heatDecay ν (t - s) q •
          euclideanLeray q (b (u s) (u s)) := by
      funext s
      exact frequencyHeatLeray_apply ν (t - s) q _
    rw [hshape]
    have hheat : Continuous fun s : ℝ => heatDecay ν (t - s) q := by
      unfold heatDecay
      fun_prop
    exact hheat.continuousOn.smul
      (((euclideanLeray q).continuous.comp_continuousOn hbc))
  have hint : IntervalIntegrable
      (fun s : ℝ => frequencyHeatLeray ν (t - s) q (b (u s) (u s)))
      volume 0 t := hcont.intervalIntegrable
  have hcomm := (innerSL ℝ q).intervalIntegral_comp_comm hint
  have hzero : ∀ s : ℝ,
      innerSL ℝ q (frequencyHeatLeray ν (t - s) q (b (u s) (u s))) = 0 := by
    intro s
    exact frequencyHeatLeray_transverse ν (t - s) q _
  calc inner ℝ q (∫ s in (0:ℝ)..t,
        frequencyHeatLeray ν (t - s) q (b (u s) (u s)))
      = innerSL ℝ q (∫ s in (0:ℝ)..t,
        frequencyHeatLeray ν (t - s) q (b (u s) (u s))) := rfl
    _ = ∫ s in (0:ℝ)..t, innerSL ℝ q
        (frequencyHeatLeray ν (t - s) q (b (u s) (u s))) := hcomm.symm
    _ = ∫ s in (0:ℝ)..t, (0:ℝ) := by
        refine intervalIntegral.integral_congr fun s _ => ?_
        exact hzero s
    _ = 0 := intervalIntegral.integral_zero

end Structure

end Navier.Analysis.FrequencyDuhamel
