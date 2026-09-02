import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The affine, time-dependent Grönwall step

`Navier/Analysis/BKMLogBootstrap.lean` reduces
`sliceSeminorm_locallyBounded` (Majda–Bertozzi §3.2.3) to a **weighted energy
inequality** of the shape

  `E'(t) ≤ a(t)·E(t) + b(t)`,

where `E(t) = ‖x^α D^β u(t)‖²_{L²}` is a polynomially weighted energy, `a` is
the commutator/Calderón–Zygmund rate and `b` collects the unweighted forcing.
The step that turns that differential inequality into a **single local bound**
is the affine, time-dependent Grönwall inequality proved here.

Mathlib supplies only the *constant-rate* `gronwallBound`
(`Mathlib/Analysis/ODE/Gronwall.lean`), and
`Navier.Analysis.BealeKatoMajda.gronwall_log_apriori` supplies only the
*purely multiplicative* time-dependent rate `Y' ≤ g·Y` (and requires `Y > 0`).
Neither covers `Y' ≤ a·Y + b`, which is what a weighted energy identity
produces: the commutator term is proportional to the weighted energy, but the
pressure/forcing term is not, so it appears additively.

Everything in this file is kernel-clean (`#print axioms` shows only `propext`,
`Classical.choice`, `Quot.sound`).

## Contents

* `gronwall_affine_apriori` — `Y' ≤ a·Y + b` on `(0,T)` with `a, b ≥ 0`
  continuous gives `Y t ≤ (Y 0 + ∫₀ᵗ b)·exp(∫₀ᵗ a)` on `[0,T]`.
* `exists_bound_of_affine_gronwall` — the local-boundedness shape the
  seminorm-propagation residual actually consumes: one constant `M` bounding
  `Y` on the whole window.
-/

namespace Navier.Analysis.GronwallAffine

open MeasureTheory intervalIntegral Set

/-- **Affine time-dependent Grönwall a-priori bound.**

If `Y` is continuous on `[0,T]`, differentiable on `(0,T)` with derivative
`Y'`, and satisfies `Y' t ≤ a t · Y t + b t` there, with `a` and `b`
continuous and nonnegative on `[0,T]`, then

  `Y t ≤ (Y 0 + ∫₀ᵗ b) · exp (∫₀ᵗ a)`   for every `t ∈ [0,T]`.

Proof: the integrating factor `W t = Y t·e^{−P t} − ∫₀ᵗ b·e^{−P}` with
`P t = ∫₀ᵗ a` has derivative `(Y' − a·Y − b)·e^{−P} ≤ 0`, hence is antitone;
`W t ≤ W 0 = Y 0` unwinds to the stated bound after `e^{−P} ≤ 1`.

Unlike `gronwall_log_apriori` this needs **no positivity of `Y`**: no
logarithm is taken. -/
theorem gronwall_affine_apriori
    {Y Y' a b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hac : ContinuousOn a (Set.Icc 0 T)) (hbc : ContinuousOn b (Set.Icc 0 T))
    (hanonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ a t)
    (hbnonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ b t)
    (hYc : ContinuousOn Y (Set.Icc 0 T))
    (hYderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hbound : ∀ t ∈ Set.Ioo 0 T, Y' t ≤ a t * Y t + b t) :
    ∀ t ∈ Set.Icc 0 T, Y t ≤ (Y 0 + ∫ s in (0:ℝ)..t, b s) * Real.exp (∫ s in (0:ℝ)..t, a s) := by
  have huIcc : Set.uIcc (0:ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hT
  have haint : IntegrableOn a (Set.Icc 0 T) volume := hac.integrableOn_compact isCompact_Icc
  set P : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, a s with hP
  have hPcont : ContinuousOn P (Set.Icc 0 T) := by
    have := continuousOn_primitive_interval (a := 0) (b := T) (f := a) (μ := volume)
      (by rw [huIcc]; exact haint)
    rwa [huIcc] at this
  -- `P` is nonnegative on the window (the rate is nonnegative).
  have hPnonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ P t := by
    intro t ht
    have hint : IntervalIntegrable a volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht.1]
      exact hac.mono (Set.Icc_subset_Icc le_rfl ht.2)
    exact intervalIntegral.integral_nonneg ht.1
      (fun s hs => hanonneg s ⟨hs.1, le_trans hs.2 ht.2⟩)
  -- The damped forcing `b·e^{−P}`.
  set F : ℝ → ℝ := fun s => b s * Real.exp (-(P s)) with hF
  have hFcont : ContinuousOn F (Set.Icc 0 T) :=
    hbc.mul ((hPcont.neg).rexp)
  have hFint : IntegrableOn F (Set.Icc 0 T) volume := hFcont.integrableOn_compact isCompact_Icc
  set Q : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, F s with hQ
  have hQcont : ContinuousOn Q (Set.Icc 0 T) := by
    have := continuousOn_primitive_interval (a := 0) (b := T) (f := F) (μ := volume)
      (by rw [huIcc]; exact hFint)
    rwa [huIcc] at this
  set W : ℝ → ℝ := fun t => Y t * Real.exp (-(P t)) - Q t with hW
  have hWc : ContinuousOn W (Set.Icc 0 T) := (hYc.mul (hPcont.neg).rexp).sub hQcont
  -- Derivative of `W` on the interior.
  have hWderiv : ∀ x ∈ Set.Ioo 0 T,
      HasDerivAt W ((Y' x - a x * Y x - b x) * Real.exp (-(P x))) x := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := le_of_lt hx.1
    have haatx : ContinuousAt a x := hac.continuousAt (Icc_mem_nhds hx.1 hx.2)
    have haint0x : IntervalIntegrable a volume 0 x := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx0]
      exact hac.mono (Set.Icc_subset_Icc le_rfl (le_of_lt hx.2))
    have hasmaf : StronglyMeasurableAtFilter a (nhds x) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hac.mono Set.Ioo_subset_Icc_self) x hx
    have hPd : HasDerivAt P (a x) x := integral_hasDerivAt_right haint0x hasmaf haatx
    have hEd : HasDerivAt (fun t => Real.exp (-(P t))) (-(a x) * Real.exp (-(P x))) x := by
      have hneg : HasDerivAt (fun t => -(P t)) (-(a x)) x := hPd.neg
      have h2 := hneg.exp
      have hr : Real.exp (-(P x)) * -(a x) = -(a x) * Real.exp (-(P x)) := by ring
      rwa [hr] at h2
    have hFatx : ContinuousAt F x := hFcont.continuousAt (Icc_mem_nhds hx.1 hx.2)
    have hFint0x : IntervalIntegrable F volume 0 x := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx0]
      exact hFcont.mono (Set.Icc_subset_Icc le_rfl (le_of_lt hx.2))
    have hFsmaf : StronglyMeasurableAtFilter F (nhds x) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hFcont.mono Set.Ioo_subset_Icc_self) x hx
    have hQd : HasDerivAt Q (b x * Real.exp (-(P x))) x := by
      have h := integral_hasDerivAt_right hFint0x hFsmaf hFatx
      simpa [hF] using h
    have hprod : HasDerivAt (fun t => Y t * Real.exp (-(P t)))
        (Y' x * Real.exp (-(P x)) + Y x * (-(a x) * Real.exp (-(P x)))) x :=
      (hYderiv x hx).mul hEd
    have hsub := hprod.sub hQd
    have heq : Y' x * Real.exp (-(P x)) + Y x * (-(a x) * Real.exp (-(P x)))
        - b x * Real.exp (-(P x)) = (Y' x - a x * Y x - b x) * Real.exp (-(P x)) := by ring
    rw [heq] at hsub
    rw [hW]
    exact hsub
  have hWanti : AntitoneOn W (Set.Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hWc
    · rw [interior_Icc]; intro x hx
      exact (hWderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      rw [(hWderiv x hx).deriv]
      have hxIcc : x ∈ Set.Icc 0 T := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hle : Y' x - a x * Y x - b x ≤ 0 := by linarith [hbound x hx]
      exact mul_nonpos_of_nonpos_of_nonneg hle (Real.exp_pos _).le
  intro t ht
  have h0mem : (0:ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hWle : W t ≤ W 0 := hWanti h0mem ht ht.1
  have hP0 : P 0 = 0 := by simp [hP]
  have hQ0 : Q 0 = 0 := by simp [hQ]
  have hW0 : W 0 = Y 0 := by simp [hW, hP0, hQ0]
  rw [hW0] at hWle
  -- Compare the damped forcing integral with the undamped one.
  have hbint : IntervalIntegrable b volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht.1]
    exact hbc.mono (Set.Icc_subset_Icc le_rfl ht.2)
  have hFint0t : IntervalIntegrable F volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht.1]
    exact hFcont.mono (Set.Icc_subset_Icc le_rfl ht.2)
  have hQle : Q t ≤ ∫ s in (0:ℝ)..t, b s := by
    refine intervalIntegral.integral_mono_on ht.1 hFint0t hbint ?_
    intro s hs
    have hsIcc : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 ht.2⟩
    have hexp : Real.exp (-(P s)) ≤ 1 := Real.exp_le_one_iff.mpr (by simpa using hPnonneg s hsIcc)
    have := hbnonneg s hsIcc
    calc b s * Real.exp (-(P s)) ≤ b s * 1 := by
          exact mul_le_mul_of_nonneg_left hexp this
      _ = b s := mul_one _
  -- Unwind.
  have hkey : Y t * Real.exp (-(P t)) ≤ Y 0 + ∫ s in (0:ℝ)..t, b s := by
    have : Y t * Real.exp (-(P t)) - Q t ≤ Y 0 := hWle
    linarith
  have hexp_pos : 0 < Real.exp (P t) := Real.exp_pos _
  have hmul : Y t = (Y t * Real.exp (-(P t))) * Real.exp (P t) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [hmul]
  exact mul_le_mul_of_nonneg_right hkey hexp_pos.le

/-- **The local-boundedness shape.**  The consumer in
`sliceSeminorm_locallyBounded` does not need the sharp Grönwall constant, only
*one* bound valid on the whole window.  This packages
`gronwall_affine_apriori` into that shape. -/
theorem exists_bound_of_affine_gronwall
    {Y Y' a b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hac : ContinuousOn a (Set.Icc 0 T)) (hbc : ContinuousOn b (Set.Icc 0 T))
    (hanonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ a t)
    (hbnonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ b t)
    (hYc : ContinuousOn Y (Set.Icc 0 T))
    (hYderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hbound : ∀ t ∈ Set.Ioo 0 T, Y' t ≤ a t * Y t + b t) :
    ∃ M : ℝ, ∀ t ∈ Set.Icc 0 T, Y t ≤ M := by
  have hcont : ContinuousOn
      (fun t => (Y 0 + ∫ s in (0:ℝ)..t, b s) * Real.exp (∫ s in (0:ℝ)..t, a s))
      (Set.Icc 0 T) := by
    have huIcc : Set.uIcc (0:ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hT
    have haint : IntegrableOn a (Set.Icc 0 T) volume := hac.integrableOn_compact isCompact_Icc
    have hbint : IntegrableOn b (Set.Icc 0 T) volume := hbc.integrableOn_compact isCompact_Icc
    have hPa : ContinuousOn (fun u => ∫ s in (0:ℝ)..u, a s) (Set.Icc 0 T) := by
      have := continuousOn_primitive_interval (a := 0) (b := T) (f := a) (μ := volume)
        (by rw [huIcc]; exact haint)
      rwa [huIcc] at this
    have hPb : ContinuousOn (fun u => ∫ s in (0:ℝ)..u, b s) (Set.Icc 0 T) := by
      have := continuousOn_primitive_interval (a := 0) (b := T) (f := b) (μ := volume)
        (by rw [huIcc]; exact hbint)
      rwa [huIcc] at this
    exact (continuousOn_const.add hPb).mul hPa.rexp
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  refine ⟨M, fun t ht => ?_⟩
  exact le_trans (gronwall_affine_apriori hT hac hbc hanonneg hbnonneg hYc hYderiv hbound t ht)
    (hM ⟨t, ht, rfl⟩)

end Navier.Analysis.GronwallAffine
