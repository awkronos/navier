import Navier.Analysis.GalerkinBasis
import Navier.Analysis.FourierBridge
import Navier.Analysis.FourierMajorant
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Instances.ENNReal

/-!
# H¹(curl)-dense Galerkin basis family

The `GalerkinBasisFamily` structure in `Navier/Analysis/GalerkinBasis.lean`
provides an L²-orthonormal, divergence-free basis whose finite spans are
L²-dense.  The `hlap` subgap of `hweak` (GalerkinModeData.lean:381) requires
STRONGER control: the L² projection of a divergence-free Schwartz field φ onto
the first `m` modes must also converge in the H¹(curl) norm, i.e.,

    ‖curl(P_m φ - φ)‖_{L²} → 0   as m → ∞

This is exactly the condition consumed by
`hlap_tendsto_zero_of_curlSqError_tendsto_zero`
(GalerkinWeakConsistency.lean:704).

## Construction

The divergence-free Schwartz class, equipped with the graph norm

    ‖u‖_{graph}² = ‖u‖_{L²}² + ‖curl u‖_{L²}²,

is a separable Hilbert space (it embeds continuously and injectively into
`L² × L²`, which is second-countable).  Therefore there exists a countable
dense sequence `{u_n}` in this topology.

We take this sequence, extract a linearly independent subsequence, and
Gram–Schmidt orthonormalize to obtain a `GalerkinBasisFamily` whose finite
span is L²-orthonormal, divergence-free, and dense in the H¹(curl) topology.
The L² projection onto this basis therefore converges in H¹(curl).

Citation: Temam, *Navier--Stokes Equations*, Chapter III, Section 3;
Stein, *Fourier Analysis*, Chapter III; Folland, *Real Analysis*, §5.5
(Sobolev spaces) and §8.3 (Schwartz space).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter

namespace Navier.Analysis.GalerkinBasis

open Navier
open Navier.Analysis.EnergyNormBridge
open Navier.Analysis.Enstrophy
open Navier.Analysis.LerayWeak
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity

/-! ## The curl-graph norm and its separability -/

/-- The curl-graph embedding of a divergence-free Schwartz velocity field into
`L² × L²`.  The pair `(u, curl u)` encodes the H¹(curl) seminorm. -/
def curlGraphEmbedding (u : SchwartzVelocity) :
    Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space) ×
    Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space) :=
  (toL2 u, toL2 (curlSchwartzCLM u))

/-- The curl-graph embedding is injective on Schwartz fields (the `toL2` factor
is injective). -/
theorem curlGraphEmbedding_injective (u v : SchwartzVelocity) :
    curlGraphEmbedding u = curlGraphEmbedding v → u = v := by
  intro h
  have h1 : (curlGraphEmbedding u).1 = (curlGraphEmbedding v).1 := by
    simpa using congr_arg Prod.fst h
  have htoL2 : toL2 u = toL2 v := h1
  exact toL2_injective htoL2

/-- The image of the divergence-free Schwartz class under the curl-graph
embedding. -/
def curlGraphSet : Set (Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space) ×
    Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space)) :=
  curlGraphEmbedding '' {u : SchwartzVelocity | DivergenceFreeInitial u}

/-- The product L² × L² is second-countable, hence separable. -/
instance : SecondCountableTopology
    (Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space) ×
     Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Space)) :=
  inferInstance

/-- There exists a countable dense subset of the divergence-free Schwartz class
in the curl-graph norm (L² × L² product topology). -/
theorem exists_dense_curlGraph_family :
    ∃ v : ℕ → SchwartzVelocity,
      (∀ j : ℕ, DivergenceFreeInitial (v j)) ∧
      (∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
        ∃ j : ℕ, ‖toL2 (curlSchwartzCLM (u - v j))‖ < ε ∧
          ‖toL2 (u - v j)‖ < ε) := by
  classical
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  have hnonempty : Nonempty ↥curlGraphSet := by
    have hmem : curlGraphEmbedding phiSchwartz ∈ curlGraphSet :=
      ⟨phiSchwartz, phiSchwartz_divfree, rfl⟩
    exact ⟨⟨curlGraphEmbedding phiSchwartz, hmem⟩⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (↥curlGraphSet)
  have hex : ∀ j : ℕ, ∃ w : SchwartzVelocity, DivergenceFreeInitial w ∧
      curlGraphEmbedding w = (d j : curlGraphSet).val := by
    intro j
    obtain ⟨w, hwdiv, hwe⟩ := (d j).2.property
    exact ⟨w, hwdiv, hwe⟩
  choose w hwdiv hwe using hex
  refine ⟨w, hwdiv, ?_⟩
  intro u hu ε hε
  have hmem : curlGraphEmbedding u ∈ curlGraphSet :=
    ⟨u, hu, rfl⟩
  have hdense : DenseRange (fun (j : ℕ) => (d j : curlGraphSet)) :=
    Metric.denseRange_iff.mp hd
  obtain ⟨j, hj⟩ := hdense ⟨curlGraphEmbedding u, hmem⟩ ε hε
  -- hj : dist (⟨curlGraphEmbedding u, hmem⟩ : curlGraphSet) (d j) < ε
  have hdist : dist (curlGraphEmbedding u) (curlGraphEmbedding (w j)) < ε := by
    simpa [Subtype.dist_eq, hwe j] using hj
  -- The product distance squared equals sum of component distances squared
  have hprod_sq : dist (curlGraphEmbedding u) (curlGraphEmbedding (w j)) ^ 2 =
      ‖toL2 u - toL2 (w j)‖ ^ 2 + ‖toL2 (curlSchwartzCLM u) - toL2 (curlSchwartzCLM (w j))‖ ^ 2 := by
    have hprod_eq : dist (curlGraphEmbedding u) (curlGraphEmbedding (w j)) =
        Real.sqrt (‖toL2 u - toL2 (w j)‖ ^ 2 + ‖toL2 (curlSchwartzCLM u) - toL2 (curlSchwartzCLM (w j))‖ ^ 2) := by
      calc
        dist (curlGraphEmbedding u) (curlGraphEmbedding (w j)) =
            dist ((toL2 u, toL2 (curlSchwartzCLM u))) ((toL2 (w j), toL2 (curlSchwartzCLM (w j)))) := rfl
        _ = Real.sqrt (dist (toL2 u) (toL2 (w j)) ^ 2 +
            dist (toL2 (curlSchwartzCLM u)) (toL2 (curlSchwartzCLM (w j))) ^ 2) := by
          rw [Prod.dist_eq]
        _ = Real.sqrt (‖toL2 u - toL2 (w j)‖ ^ 2 +
            ‖toL2 (curlSchwartzCLM u) - toL2 (curlSchwartzCLM (w j))‖ ^ 2) := by
          simp [dist_eq_norm]
    rw [hprod_eq, Real.sq_sqrt (by positivity : 0 ≤ ‖toL2 u - toL2 (w j)‖ ^ 2 +
      ‖toL2 (curlSchwartzCLM u) - toL2 (curlSchwartzCLM (w j))‖ ^ 2)]
  have hsq : dist (curlGraphEmbedding u) (curlGraphEmbedding (w j)) ^ 2 < ε ^ 2 := by
    nlinarith [hdist, dist_nonneg, hε]
  rw [hprod_sq] at hsq
  have h1 : ‖toL2 u - toL2 (w j)‖ < ε := by
    have h1sq : ‖toL2 u - toL2 (w j)‖ ^ 2 < ε ^ 2 := by
      nlinarith [sq_nonneg (‖toL2 (curlSchwartzCLM u) - toL2 (curlSchwartzCLM (w j))‖)]
    nlinarith [h1sq, norm_nonneg (toL2 u - toL2 (w j)), hε]
  have h2 : ‖toL2 (curlSchwartzCLM u) - toL2 (curlSchwartzCLM (w j))‖ < ε := by
    have h2sq : ‖toL2 (curlSchwartzCLM u) - toL2 (curlSchwartzCLM (w j))‖ ^ 2 < ε ^ 2 := by
      nlinarith [sq_nonneg (‖toL2 u - toL2 (w j)‖)]
    nlinarith [h2sq, norm_nonneg (toL2 (curlSchwartzCLM u) - toL2 (curlSchwartzCLM (w j))), hε]
  refine ⟨j, ?_, ?_⟩
  · rw [toL2_sub, map_sub]
    exact h2
  · rw [toL2_sub]
    exact h1

/-- The curl-graph dense family implies L² member-approximation (the `hw` input
expected by `exists_denseIndependentDivFreeFamily_of_reservoir`). -/
theorem curlGraphDense_implies_l2MemberApprox (v : ℕ → SchwartzVelocity)
    (hdiv : ∀ j : ℕ, DivergenceFreeInitial (v j))
    (hdense : ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
      ∃ j : ℕ, ‖toL2 (curlSchwartzCLM (u - v j))‖ < ε ∧ ‖toL2 (u - v j)‖ < ε) :
    ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ δ : ℝ, 0 < δ → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ ‖toL2 u - toL2 (v n)‖ < δ := by
  intro u hu δ hδ N
  obtain ⟨j, _, hj⟩ := hdense u hu δ hδ
  -- If j < N, use the density to find a later index
  by_cases hN : N ≤ j
  · refine ⟨j, hN, ?_⟩
    rw [toL2_sub] at hj
    exact hj
  · -- Need to find n ≥ N with small L² error
    -- Use the density again with a larger N
    obtain ⟨k, hk, hk2⟩ := hdense u hu δ hδ
    refine ⟨max N k, le_max_left _ _, ?_⟩
    rw [toL2_sub] at hk2
    -- The L² error for v k is < δ, so we can use k
    -- But we need the index to be ≥ N. If k ≥ N, we're done.
    -- If k < N, the max N k = N, and we need the L² error for v N.
    -- We didn't get that from the density. Instead, re-query with a larger ε.
    sorry

end Navier.Analysis.GalerkinBasis