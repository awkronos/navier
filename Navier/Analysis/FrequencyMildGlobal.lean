import Navier.Analysis.FrequencyDuhamel

/-!
# Global mild solutions at one frequency: exact transversality cancellation

The classical fact that a single Fourier mode is an exact global solution of
Navier--Stokes is realized here at the mild layer.  The one-frequency
Navier--Stokes convection symbol pairs the frequency against the first
argument, so it annihilates transverse states; since transversality
propagates through the Duhamel integral
(`IsMildSolutionOn.inner_frequency_eq_zero`), the nonlinearity of any mild
solution vanishes identically and the mild equation collapses to the free
heat--Leray flow.

Consequences, with **no smallness hypotheses and on every horizon**:
* `isMildSolutionOn_iff_heatFlow` — for any transverse-annihilating symbol,
  mild solutions are exactly the heat--Leray path.
* `exists_isMildSolutionOn_global` / `isMildSolutionOn_unique_global` —
  unconditional global existence and uniqueness at this layer.
* `nsOneFrequencySymbol` — the actual one-frequency Navier--Stokes symbol
  `(v, w) ↦ ⟪q, v⟫ • w`, proved transverse-annihilating, with the global
  theorem instantiated (`nsOneFrequency_global_regularity`).

Scope: this is the regularity direction of the one-frequency laboratory.  It
does not bound multi-frequency interactions, where the R7 generated-support
growth obstruction lives.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.FrequencyDuhamel

open Navier.Analysis.LerayProjection
open Navier.Analysis.FrequencyHeatLeray
open MeasureTheory

/-- A convection symbol annihilates transverse states when its quadratic
diagonal vanishes on the plane orthogonal to the frequency. -/
def TransverseAnnihilating (q : E3) (b : E3 →L[ℝ] E3 →L[ℝ] E3) : Prop :=
  ∀ v : E3, inner ℝ q v = 0 → b v v = 0

variable {ν T : ℝ} {q : E3} {b : E3 →L[ℝ] E3 →L[ℝ] E3} {u₀ : E3}

/-- The free heat--Leray flow launched from `u₀`. -/
def heatFlow (ν : ℝ) (q : E3) (u₀ : E3) : ℝ → E3 :=
  fun t => frequencyHeatLeray ν t q u₀

theorem continuous_heatFlow : Continuous (heatFlow ν q u₀) := by
  have hshape : heatFlow ν q u₀ =
      fun t : ℝ => heatDecay ν t q • euclideanLeray q u₀ := by
    funext t
    exact frequencyHeatLeray_apply ν t q u₀
  rw [hshape]
  exact (continuous_heatDecay_time ν q).smul continuous_const

/-- The heat--Leray flow is transverse to its frequency at every time. -/
theorem heatFlow_transverse (t : ℝ) :
    inner ℝ q (heatFlow ν q u₀ t) = 0 :=
  frequencyHeatLeray_transverse ν t q u₀

/-- The heat--Leray flow is a global mild solution for every
transverse-annihilating convection symbol. -/
theorem heatFlow_isMildSolutionOn
    (hb : TransverseAnnihilating q b) (T : ℝ) :
    IsMildSolutionOn ν q b u₀ T (heatFlow ν q u₀) := by
  refine ⟨continuous_heatFlow.continuousOn, ?_⟩
  intro t _ht
  have hzero : ∀ s : ℝ,
      frequencyHeatLeray ν (t - s) q
        (b (heatFlow ν q u₀ s) (heatFlow ν q u₀ s)) = 0 := by
    intro s
    rw [hb (heatFlow ν q u₀ s) (heatFlow_transverse s)]
    exact map_zero _
  have hint : (∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) q
      (b (heatFlow ν q u₀ s) (heatFlow ν q u₀ s))) = 0 := by
    rw [show (fun s => frequencyHeatLeray ν (t - s) q
        (b (heatFlow ν q u₀ s) (heatFlow ν q u₀ s))) = fun _ => (0 : E3) from
      funext hzero]
    exact intervalIntegral.integral_zero
  rw [hint, add_zero]
  rfl

/-- **Exact collapse of the mild equation**: for a transverse-annihilating
symbol, the mild solutions on any horizon are precisely the heat--Leray
flow. -/
theorem isMildSolutionOn_iff_heatFlow
    (hb : TransverseAnnihilating q b) (u : ℝ → E3) :
    IsMildSolutionOn ν q b u₀ T u ↔
      (ContinuousOn u (Set.Icc 0 T) ∧
        ∀ t ∈ Set.Icc (0:ℝ) T, u t = heatFlow ν q u₀ t) := by
  constructor
  · intro hu
    refine ⟨hu.1, ?_⟩
    intro t ht
    have hmild := hu.2 t ht
    have hzero : ∀ s ∈ Set.uIcc (0:ℝ) t,
        frequencyHeatLeray ν (t - s) q (b (u s) (u s)) = 0 := by
      intro s hs
      have hs' : s ∈ Set.Icc (0:ℝ) T := by
        rw [Set.uIcc_of_le ht.1] at hs
        exact ⟨hs.1, le_trans hs.2 ht.2⟩
      have htrans : inner ℝ q (u s) = 0 :=
        hu.inner_frequency_eq_zero hs'
      rw [hb (u s) htrans]
      exact map_zero _
    have hint : (∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) q
        (b (u s) (u s))) = 0 := by
      rw [intervalIntegral.integral_congr hzero]
      exact intervalIntegral.integral_zero
    rw [hmild, hint, add_zero]
    rfl
  · intro ⟨hcont, heq⟩
    have hflow := heatFlow_isMildSolutionOn (ν := ν) (u₀ := u₀) hb T
    refine ⟨hcont, ?_⟩
    intro t ht
    rw [heq t ht]
    have hker : ∀ s ∈ Set.uIcc (0:ℝ) t,
        frequencyHeatLeray ν (t - s) q (b (u s) (u s)) =
          frequencyHeatLeray ν (t - s) q
            (b (heatFlow ν q u₀ s) (heatFlow ν q u₀ s)) := by
      intro s hs
      have hs' : s ∈ Set.Icc (0:ℝ) T := by
        rw [Set.uIcc_of_le ht.1] at hs
        exact ⟨hs.1, le_trans hs.2 ht.2⟩
      rw [heq s hs']
    rw [intervalIntegral.integral_congr hker]
    exact hflow.2 t ht

/-- **Unconditional global existence** at one frequency for
transverse-annihilating symbols: no smallness, every horizon, with the
amplitude bound `‖u t‖ ≤ ‖u₀‖` on all of forward time. -/
theorem exists_isMildSolutionOn_global
    (hb : TransverseAnnihilating q b) (hν : 0 ≤ ν) (T : ℝ) :
    ∃ u : ℝ → E3, IsMildSolutionOn ν q b u₀ T u ∧
      ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ ‖u₀‖ := by
  refine ⟨heatFlow ν q u₀, heatFlow_isMildSolutionOn hb T, ?_⟩
  intro t ht
  exact frequencyHeatLeray_norm_le hν ht q u₀


/-- **Unconditional global uniqueness** at one frequency for
transverse-annihilating symbols: any two mild solutions agree on the whole
horizon, with no ball constraint. -/
theorem isMildSolutionOn_unique_global
    (hb : TransverseAnnihilating q b)
    {u v : ℝ → E3}
    (hu : IsMildSolutionOn ν q b u₀ T u)
    (hv : IsMildSolutionOn ν q b u₀ T v) :
    Set.EqOn u v (Set.Icc 0 T) := by
  intro t ht
  have h1 := ((isMildSolutionOn_iff_heatFlow hb u).1 hu).2 t ht
  have h2 := ((isMildSolutionOn_iff_heatFlow hb v).1 hv).2 t ht
  rw [h1, h2]

/-- The one-frequency Navier--Stokes convection symbol
`(v, w) ↦ ⟪q, v⟫ • w`: the frequency pairs against the transport slot. -/
def nsOneFrequencySymbol (q : E3) : E3 →L[ℝ] E3 →L[ℝ] E3 :=
  (ContinuousLinearMap.lsmul ℝ ℝ).comp (innerSL ℝ q)

@[simp] theorem nsOneFrequencySymbol_apply (q v w : E3) :
    nsOneFrequencySymbol q v w = (inner ℝ q v) • w := rfl

/-- The Navier--Stokes one-frequency symbol annihilates transverse states. -/
theorem nsOneFrequencySymbol_transverseAnnihilating (q : E3) :
    TransverseAnnihilating q (nsOneFrequencySymbol q) := by
  intro v hv
  rw [nsOneFrequencySymbol_apply, hv, zero_smul]

/-- **One-frequency global regularity for the Navier--Stokes symbol**: the
single retained mode launches a unique global mild solution whose amplitude
never exceeds the initial amplitude.  This is the mild form of the classical
single-Fourier-mode exact solution. -/
theorem nsOneFrequency_global_regularity {ν : ℝ} (hν : 0 ≤ ν)
    (q u₀ : E3) (T : ℝ) :
    (∃ u : ℝ → E3,
      IsMildSolutionOn ν q (nsOneFrequencySymbol q) u₀ T u ∧
        ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ ‖u₀‖) ∧
    ∀ u v : ℝ → E3,
      IsMildSolutionOn ν q (nsOneFrequencySymbol q) u₀ T u →
      IsMildSolutionOn ν q (nsOneFrequencySymbol q) u₀ T v →
      Set.EqOn u v (Set.Icc 0 T) :=
  ⟨exists_isMildSolutionOn_global
      (nsOneFrequencySymbol_transverseAnnihilating q) hν T,
    fun _u _v hu hv => isMildSolutionOn_unique_global
      (nsOneFrequencySymbol_transverseAnnihilating q) hu hv⟩

end Navier.Analysis.FrequencyDuhamel
