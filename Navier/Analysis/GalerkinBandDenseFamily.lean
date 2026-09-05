import Navier.Analysis.GalerkinUniformBandAssembly

/-! Countable approximation in the actual velocity–curl graph norm, within
any prescribed Fourier band. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Navier.Analysis.GalerkinBandDenseFamily

open GalerkinBasis DivFreeGradientEnstrophy

abbrev VelocityL2 := Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space)

def velocityCurlGraph (u : SchwartzVelocity) : VelocityL2 × VelocityL2 :=
  (toL2 u, toL2 (curlSchwartzCLM u))

def bandFields (B : Set EuclSpace) : Set SchwartzVelocity :=
  {u | DivergenceFreeInitial u ∧ ∀ ξ, ξ ∉ B → (𝓕 (euclModel u)) ξ = 0}

theorem zero_mem_bandFields (B : Set EuclSpace) :
    (0 : SchwartzVelocity) ∈ bandFields B := by
  constructor
  · intro x
    simp [staticDivergence]
  · intro ξ hξ
    simp [euclModel]

/-- The approximating sequence consists of actual divergence-free Schwartz
fields in the same band. It approximates both velocity and curl, rather than
only the velocity in `L²`. -/
theorem exists_dense_band_family (B : Set EuclSpace) :
    ∃ v : ℕ → SchwartzVelocity,
      (∀ j, v j ∈ bandFields B) ∧
      ∀ u ∈ bandFields B, ∀ ε : ℝ, 0 < ε →
        ∃ j, ‖toL2 u - toL2 (v j)‖ < ε ∧
          ‖toL2 (curlSchwartzCLM u) - toL2 (curlSchwartzCLM (v j))‖ < ε := by
  classical
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  let S : Set (VelocityL2 × VelocityL2) := velocityCurlGraph '' bandFields B
  haveI : Nonempty S := ⟨⟨velocityCurlGraph 0, 0, zero_mem_bandFields B, rfl⟩⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq S
  have hex : ∀ j, ∃ w ∈ bandFields B, velocityCurlGraph w = (d j).val :=
    fun j => (d j).property
  choose v hv heq using hex
  refine ⟨v, hv, ?_⟩
  intro u hu ε hε
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp hd
    ⟨velocityCurlGraph u, u, hu, rfl⟩ ε hε
  refine ⟨j, ?_⟩
  have hdist : dist (velocityCurlGraph u) (velocityCurlGraph (v j)) < ε := by
    rw [heq j]
    simpa only [Subtype.dist_eq] using hj
  change max (dist (toL2 u) (toL2 (v j)))
    (dist (toL2 (curlSchwartzCLM u)) (toL2 (curlSchwartzCLM (v j)))) < ε at hdist
  simpa only [dist_eq_norm, max_lt_iff] using hdist

end Navier.Analysis.GalerkinBandDenseFamily
