import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Navier.Analysis.OfficialABEncoding
import Navier.Problem

/-!
# Sobolev embeddings for the Navier-Stokes assembly (no sorry)

The Sobolev inequality `H¹(ℝ³) → L^q(ℝ³)` for `q ≥ 6` (i.e.,
`q⁻¹ ≤ 2⁻¹ - 3⁻¹ = 1/6`), on functions with support in a bounded set.

This file bridges Mathlib's `eLpNorm_le_eLpNorm_fderiv_of_le` (the
Gagliardo-Nirenberg-Sobolev inequality) to the concrete measure `volume`
on `Space = ℝ³`, and chains it with the L² → L^q inclusion to produce
the `H¹ → L^{10/3}` bound used by the Caccioppoli energy iteration.

All declarations are proven by the kernel (0 sorries, 0 extra axioms).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Navier.Analysis.SobolevEmbeddings

open Navier

-- The Lebesgue measure on Space = ℝ³
local notation "μ" => (volume : Measure Space)

/-- The dimension of `Space = ℝ³` is 3. -/
lemma finrank_Space : finrank ℝ Space = 3 := by
  simp

/-- Sobolev inequality `H¹ → L^q` on a bounded set, for `q ≥ 6` (sharp `p = 2`,
`n = 3` Gagliardo-Nirenberg-Sobolev).  Let `u` be once continuously differentiable,
supported in a bounded open set `s`.  For any exponent `q` satisfying
`q⁻¹ ≤ 2⁻¹ - 3⁻¹ = 1/6` (equivalently `q ≥ 6`), the `L^q` norm of `u` is
bounded by a constant (depending on `s`, `q`) times the `L²` norm of the
Fréchet derivative:  `‖u‖_{L^q(μ)} ≤ C(s, q) · ‖fderiv u‖_{L²(μ)}`.

The constant `C = eLpNormLESNormFDerivOfLeConst Space μ s (2 : ℝ≥0) q` is the
one from the GNS file (irreducible, depends on `s`, `q`). -/
theorem H1_to_Lq_on_bounded
    (u : Space → Space) (hu : ContDiff ℝ 1 u)
    {s : Set Space} (hu_supp : u.support ⊆ s) (hs : Bornology.IsBounded s)
    {q : ℝ≥0} (hq : (2 : ℝ≥0)⁻¹ - (3 : ℝ≥0)⁻¹ ≤ (q : ℝ)⁻¹) :
    eLpNorm u q μ ≤
      (eLpNormLESNormFDerivOfLeConst Space μ s (2 : ℝ≥0) q : ℝ≥0∞) *
        eLpNorm (fderiv ℝ u) 2 μ := by
  have hp : 1 ≤ (2 : ℝ≥0) := by norm_num
  have h2p : (2 : ℝ≥0) < finrank ℝ Space := by
    rw [finrank_Space]; exact by norm_num
  have hpq : ((2 : ℝ≥0) : ℝ)⁻¹ - (finrank ℝ Space : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by
    rw [finrank_Space]; exact hq
  refine eLpNorm_le_eLpNorm_fderiv_of_le (μ := μ) hu hu_supp hp h2p hpq hs

/-- **`H¹ → L^{10/3}` on a bounded set.**  We verify that
`(10/3)⁻¹ = 3/10 ≥ 2⁻¹ - 3⁻¹ = 1/6` so that `H1_to_Lq_on_bounded` applies.
This exponent is used by the Caccioppoli energy inequality on space-time
cylinders (the Ladyzhenskaya inequality). -/
theorem H1_to_L10_3_on_bounded
    (u : Space → Space) (hu : ContDiff ℝ 1 u)
    {s : Set Space} (hu_supp : u.support ⊆ s) (hs : Bornology.IsBounded s) :
    eLpNorm u (10/3 : ℝ≥0) μ ≤
      (eLpNormLESNormFDerivOfLeConst Space μ s (2 : ℝ≥0) (10/3 : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fderiv ℝ u) 2 μ := by
  have hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (finrank ℝ Space : ℝ)⁻¹ ≤ ((10/3 : ℝ≥0) : ℝ)⁻¹ := by
    rw [finrank_Space]; norm_num
  exact H1_to_Lq_on_bounded u hu hu_supp hs hq

/-- **`H¹ → L^6` (sharp Sobolev exponent) on a bounded set.**  This is the
critical GNS embedding `p' = 6` when `p = 2`, `n = 3`. -/
theorem H1_to_L6_on_bounded
    (u : Space → Space) (hu : ContDiff ℝ 1 u)
    {s : Set Space} (hu_supp : u.support ⊆ s) (hs : Bornology.IsBounded s) :
    eLpNorm u (6 : ℝ≥0) μ ≤
      (eLpNormLESNormFDerivOfLeConst Space μ s (2 : ℝ≥0) (6 : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fderiv ℝ u) 2 μ := by
  have hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (finrank ℝ Space : ℝ)⁻¹ ≤ ((6 : ℝ≥0) : ℝ)⁻¹ := by
    rw [finrank_Space]; norm_num
  exact H1_to_Lq_on_bounded u hu hu_supp hs hq

end Navier.Analysis.SobolevEmbeddings