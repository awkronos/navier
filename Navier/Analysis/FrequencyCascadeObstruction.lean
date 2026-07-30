import Navier.Analysis.FrequencyMildGlobal

/-!
# Frequency-cascade obstruction: the transversality mechanism is single-frequency

`Navier.Analysis.FrequencyMildGlobal` proves **unconditional global regularity
at one frequency**: the one-frequency Navier–Stokes convection symbol
`nsOneFrequencySymbol q v w = ⟪q,v⟫ • w` is `TransverseAnnihilating`, so any mild
solution launched transverse to `q` has an identically vanishing nonlinearity and
collapses to the free heat–Leray flow.  The natural R2 question toward full 3D
regularity: **does this exact-cancellation mechanism extend to several
frequencies?**

## The answer, certified: no — modes transport each other

For a genuine two-mode state (amplitudes `v₁`, `v₂` at distinct frequencies
`q₁`, `q₂`) the convective nonlinearity produces, at the sum frequency, the
*cross-transport* term

  `crossInteraction q₁ q₂ v₁ v₂ = ⟪q₂, v₁⟫ • v₂ + ⟪q₁, v₂⟫ • v₁`

— each mode transported by the velocity of the other.  The one-frequency
cancellation needs `v` transverse to its *own* frequency; but transversality of
`v₁` to `q₁` says **nothing** about `⟪q₂, v₁⟫`.  `crossInteraction_survives_
transversality` exhibits a concrete configuration — `q₁ = e₀`, `q₂ = e₁`,
`v₁ = e₁`, `v₂ = e₀` — where each mode is transverse to its own frequency yet the
cross-interaction is `e₀ + e₁ ≠ 0`.

`crossInteraction_diagonal_eq_two_symbol` and `crossInteraction_diagonal_
transverse_eq_zero` confirm this is the *right* generalization: on the diagonal
`q₁=q₂=q`, `v₁=v₂=v` the cross-interaction is exactly twice the one-frequency
symbol, and it vanishes precisely when `v ⟂ q` — recovering
`nsOneFrequencySymbol`'s transverse annihilation.  So the obstruction is
genuinely two-frequency, not an artifact of a mismatched definition.

## Honest scope (this is an obstruction, not a falsification)

This does **not** prove `Navier.ProblemStatements.WholeSpaceGlobalRegularity` false, and it constructs no
blow-up.  It certifies that the *exact-transversality-cancellation* route — the
mechanism behind one-frequency global regularity — cannot by itself close the
multi-frequency problem: the surviving cross-transport term is exactly the
nonlinear cascade that constitutes the global-regularity difficulty.  The REDIRECT it
records: a multi-frequency regularity route must **control** cross-mode transport
(an energy / a-priori estimate — e.g. the Beale–Kato–Majda vorticity bound in
`Navier.Analysis.BealeKatoMajda`), never eliminate it by cancellation.  The R2
wall (numbered in `.claude/ladder.md`) stands; this file delimits one exhausted
technique.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.FrequencyCascadeObstruction

open Navier.Analysis.LerayProjection
open Navier.Analysis.FrequencyDuhamel

/-- The two-mode cross-frequency convective interaction: mode `1` (amplitude
`v₁` at frequency `q₁`) and mode `2` (amplitude `v₂` at `q₂`) produce, at the
sum frequency, the transport terms `⟪q₂,v₁⟫ • v₂ + ⟪q₁,v₂⟫ • v₁` — each mode
carried by the velocity of the other.  This is the multi-frequency
generalization of the single-frequency symbol `nsOneFrequencySymbol`. -/
def crossInteraction (q₁ q₂ v₁ v₂ : E3) : E3 :=
  (inner ℝ q₂ v₁) • v₂ + (inner ℝ q₁ v₂) • v₁

/-- **Consistency with the one-frequency symbol.**  On the diagonal
(`q₁=q₂=q`, `v₁=v₂=v`) the cross-interaction is exactly twice the one-frequency
Navier–Stokes convection symbol `nsOneFrequencySymbol q v v = ⟪q,v⟫ • v`. -/
theorem crossInteraction_diagonal_eq_two_symbol (q v : E3) :
    crossInteraction q q v v = (2 : ℝ) • nsOneFrequencySymbol q v v := by
  rw [nsOneFrequencySymbol_apply]
  simp only [crossInteraction]
  module

/-- **Recovers the one-frequency cancellation.**  On the diagonal with `v`
transverse to `q`, the cross-interaction vanishes — matching
`nsOneFrequencySymbol_transverseAnnihilating`.  The obstruction below is
therefore genuinely a two-frequency effect. -/
theorem crossInteraction_diagonal_transverse_eq_zero
    (q v : E3) (h : (inner ℝ q v : ℝ) = 0) :
    crossInteraction q q v v = 0 := by
  simp [crossInteraction, h]

/-- **The frequency-cascade obstruction.**  There exist two frequencies and two
amplitudes, each amplitude transverse to its own frequency, whose cross-transport
interaction is nonzero.  Hence the single-frequency transversality-cancellation
mechanism does **not** extend to several frequencies: individually
divergence-free modes still transport one another.

Concrete witness: `q₁ = e₀`, `q₂ = e₁`, `v₁ = e₁`, `v₂ = e₀`, giving
`⟪q₁,v₁⟫ = ⟪e₀,e₁⟫ = 0`, `⟪q₂,v₂⟫ = ⟪e₁,e₀⟫ = 0`, yet
`crossInteraction = ⟪e₁,e₁⟫•e₀ + ⟪e₀,e₀⟫•e₁ = e₀ + e₁ ≠ 0`. -/
theorem crossInteraction_survives_transversality :
    ∃ q₁ q₂ v₁ v₂ : E3,
      (inner ℝ q₁ v₁ : ℝ) = 0 ∧ (inner ℝ q₂ v₂ : ℝ) = 0 ∧
      crossInteraction q₁ q₂ v₁ v₂ ≠ 0 := by
  refine ⟨EuclideanSpace.single 0 1, EuclideanSpace.single 1 1,
         EuclideanSpace.single 1 1, EuclideanSpace.single 0 1, ?_, ?_, ?_⟩
  · simp [EuclideanSpace.inner_single_left]
  · simp [EuclideanSpace.inner_single_left]
  · simp only [crossInteraction, EuclideanSpace.inner_single_left,
      map_one, one_mul]
    intro h
    have hc := congrArg (fun w : E3 => w 0) h
    simp at hc

end Navier.Analysis.FrequencyCascadeObstruction
