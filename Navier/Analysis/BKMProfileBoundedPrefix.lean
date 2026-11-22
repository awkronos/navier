import Navier.Analysis.BKMProfileSelectedEnvelope

/-!
# The `hbdd` hypothesis of the polynomial-upper / axis-lower bridge is automatic

`BKMProfileSelectedEnvelope.vorticityRateBound_of_polyUpper_axisLower` takes
`hbdd : ∃ C₃, ∀ t ∈ Ico 0 t₀, V u t ≤ C₃`.  For a competitor with the
`R3CompactCandidate.Properties` package, `V u` is continuous on `[0,1)`, hence
bounded on the compact `[0,t₀]` for every `t₀ < 1`.  This removes `hbdd` from the
bridge's hypothesis list; the upper envelope `hup` and axis lower envelope
`haxis` remain the open transports.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open Navier Navier.Analysis.BKMVorticityIntegralDivergence
open Navier.Analysis.BKMProfileGronwallPair
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity
open Navier.Construction.ProblemStatement
open Navier.Construction.R3CompactCandidate

namespace Navier.Analysis.BKMProfileBoundedPrefix

theorem V_bddOn_prefix {u p f : _} (h : Properties u p f) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) : ∃ C : ℝ, ∀ t ∈ Ico (0 : ℝ) t₀, V u t ≤ C := by
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  have hcont : ContinuousOn (V u) (Ico (0 : ℝ) 1) :=
    V_continuousOn h.velocity_smooth hK hsupp
  have hsub : Icc (0 : ℝ) t₀ ⊆ Ico (0 : ℝ) 1 := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 ht₀.2⟩
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, ⟨le_rfl, ht₀.1⟩⟩ : (Icc (0:ℝ) t₀).Nonempty) (hcont.mono hsub)
  exact ⟨V u x, fun t ht => hmax ⟨ht.1, ht.2.le⟩⟩

end Navier.Analysis.BKMProfileBoundedPrefix
#print axioms Navier.Analysis.BKMProfileBoundedPrefix.V_bddOn_prefix
