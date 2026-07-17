import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Global forward existence for a globally-Lipschitz, bounded, autonomous ODE

Mathlib's `Mathlib.Analysis.ODE.ExistUnique` provides Picard–Lindelöf existence
on a *bounded* interval and uniqueness of solutions, and
`Mathlib.Geometry.Manifold.IntegralCurve.UniformTime` globalises *manifold*
integral curves.  What is missing — and what the finite-dimensional Galerkin
construction of Leray (1934) needs — is the pure Banach-space statement that a
globally-Lipschitz, globally-bounded, autonomous vector field on a complete
space admits a solution on the whole forward half-line `[0, ∞)`.

This file supplies that globalisation directly (no manifold machinery), by the
classical "extend the local Picard–Lindelöf solutions and glue by uniqueness"
argument (Hartman, *Ordinary Differential Equations*, 2nd ed., Ch. II–III;
Temam, *Navier–Stokes Equations*, Ch. III §3; the manifold analogue is Lee,
*Introduction to Smooth Manifolds*, Lemma 9.15):

* `exists_forward_global` — for `G : E → E` globally `K`-Lipschitz and bounded by
  `L`, and any `x₀`, there is `u : ℝ → E` with `u 0 = x₀` and
  `u' = G ∘ u` on all of `[0, ∞)` (as `HasDerivWithinAt … (Set.Ici 0)`).
* `exists_forward_global_of_contDiff_compactSupport` — the same conclusion for a
  `C¹` field with compact support, whose Lipschitz constant and uniform bound are
  automatic (`ContDiff.lipschitzWith_of_hasCompactSupport` +
  `HasCompactSupport.exists_bound_of_continuous`).  This is the exact hypothesis
  shape produced by a smooth cutoff of a dissipative field
  (`Navier.Analysis.LerayWeak.exists_compactSupport_dissipative_extension`), and
  it is what closes the existence half of `finiteDim_dissipative_ode_global`.

## References

* P. Hartman, *Ordinary Differential Equations*, 2nd ed., SIAM (2002), Ch. II–III.
* R. Temam, *Navier–Stokes Equations*, AMS Chelsea (2001), Ch. III §3 (Galerkin).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2012),
  Lemma 9.15 (uniform-time lemma, manifold version).
-/

set_option autoImplicit false

noncomputable section

open Metric Set Filter Topology

namespace Navier.Analysis.DissipativeODEGlobal

/-- **Global forward existence for a globally-Lipschitz, bounded, autonomous field.**
Let `E` be a complete normed `ℝ`-space and `G : E → E` be globally `K`-Lipschitz
and bounded by `L` (`∀ x, ‖G x‖ ≤ L`).  For every initial point `x₀` there is a
solution `u : ℝ → E` of the autonomous ODE `u' = G ∘ u` with `u 0 = x₀`, valid on
the whole forward half-line: `HasDerivWithinAt u (G (u t)) (Set.Ici 0) t` for all
`t ≥ 0`.

Construction (Hartman Ch. II–III; the manifold analogue is Lee Lemma 9.15):
on each `Icc 0 (n+1)` the global Lipschitz + bound make `G` satisfy
Picard–Lindelöf with radius `a = L·(n+1)` (so the solution cannot leave the ball
`B̄(x₀, a)` in time `n+1`), giving a local solution `αₙ`; forward uniqueness
(`ODE_solution_unique`) makes the family consistent on overlaps; the diagonal
`u t = α_{⌈t⌉} t` is then a global forward solution, its derivative at each `t`
read off from `α_N` for `N = ⌈t⌉+1 > t` via local eventual equality. -/
theorem exists_forward_global
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : E → E) {K : NNReal} (hK : LipschitzWith K G) {L : NNReal} (hL : ∀ x, ‖G x‖ ≤ (L : ℝ))
    (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (G (u t)) (Set.Ici (0 : ℝ)) t := by
  -- family of local solutions on `Icc 0 (n+1)` via time-independent Picard–Lindelöf
  have hloc : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1),
        HasDerivWithinAt α (G (α t)) (Set.Icc 0 ((n : ℝ) + 1)) t := by
    intro n
    have hpl : IsPicardLindelof (fun _ => G) (tmin := (0 : ℝ)) (tmax := (n : ℝ) + 1)
        ⟨0, Set.mem_Icc.mpr ⟨le_rfl, by positivity⟩⟩ x₀ (L * ⟨(n : ℝ) + 1, by positivity⟩) 0 L K := by
      apply IsPicardLindelof.of_time_independent
      · intro x _; exact hL x
      · exact hK.lipschitzOnWith
      · simp only [NNReal.coe_mul, NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]; exact le_rfl
    exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose α hα0 hα using hloc
  -- derivative on `Icc 0 (n+1)` upgrades to a right-derivative on `Ici t` for `t < n+1`
  have hmono : ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < (n : ℝ) + 1 →
      HasDerivWithinAt (α n) (G (α n t)) (Set.Ici t) t := by
    intro n t ht htlt
    have hmem : Set.Icc (0 : ℝ) ((n : ℝ) + 1) ∈ 𝓝[Set.Ici t] t :=
      mem_of_superset (inter_mem_nhdsWithin (Set.Ici t) (Iio_mem_nhds htlt))
        (fun s hs => ⟨le_trans ht hs.1, le_of_lt hs.2⟩)
    exact (hα n t ⟨ht, le_of_lt htlt⟩).mono_of_mem_nhdsWithin hmem
  -- solutions agree on the smaller interval (forward uniqueness)
  have hconsist : ∀ m n : ℕ, m ≤ n → Set.EqOn (α m) (α n) (Set.Icc 0 ((m : ℝ) + 1)) := by
    intro m n hmn
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    refine ODE_solution_unique (K := K) (v := fun _ => G) (fun _ => hK)
      (fun t ht => (hα m t ht).continuousWithinAt) ?_
      (fun t ht => ((hα n t ⟨ht.1, le_trans ht.2 hmn'⟩).continuousWithinAt).mono
        (Set.Icc_subset_Icc_right hmn')) ?_ (by rw [hα0 m, hα0 n])
    · intro t ht; exact hmono m t ht.1 ht.2
    · intro t ht; exact hmono n t ht.1 (lt_of_lt_of_le ht.2 hmn')
  -- diagonal global solution `u t = α_{⌈t⌉} t`
  refine ⟨fun t => α ⌈t⌉₊ t, by simp only [Nat.ceil_zero]; exact hα0 0, ?_⟩
  intro t ht
  set N := ⌈t⌉₊ + 1 with hN
  have htN : t < (N : ℝ) := by
    have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have h2 : (⌈t⌉₊ : ℝ) < (N : ℝ) := by rw [hN]; push_cast; linarith
    linarith
  -- `u` agrees with `α_N` on a right-neighbourhood of `t`
  have heq : (fun s => α ⌈s⌉₊ s) =ᶠ[𝓝[Set.Ici (0 : ℝ)] t] (α N) := by
    have hnbhd : Set.Icc (0 : ℝ) ((N : ℝ)) ∈ 𝓝[Set.Ici (0 : ℝ)] t :=
      mem_of_superset (inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) (Iio_mem_nhds htN))
        (fun s hs => ⟨hs.1, le_of_lt hs.2⟩)
    filter_upwards [hnbhd] with s hs
    have hceil_le : ⌈s⌉₊ ≤ N := by rw [Nat.ceil_le]; exact hs.2
    have hsmem : s ∈ Set.Icc (0 : ℝ) ((⌈s⌉₊ : ℝ) + 1) :=
      ⟨hs.1, by have := Nat.le_ceil s; linarith⟩
    exact hconsist ⌈s⌉₊ N hceil_le hsmem
  have hut : (fun s => α ⌈s⌉₊ s) t = α N t :=
    hconsist ⌈t⌉₊ N (by rw [hN]; exact Nat.le_succ _)
      ⟨ht, by have := Nat.le_ceil t; linarith⟩
  -- `α_N`'s right-derivative on `Ici 0` at `t`
  have hderivN : HasDerivWithinAt (α N) (G (α N t)) (Set.Ici (0 : ℝ)) t := by
    have hmem : Set.Icc (0 : ℝ) ((N : ℝ) + 1) ∈ 𝓝[Set.Ici (0 : ℝ)] t :=
      mem_of_superset
        (inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) (Iio_mem_nhds (by linarith : t < (N : ℝ) + 1)))
        (fun s hs => ⟨hs.1, le_of_lt hs.2⟩)
    exact (hα N t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin hmem
  have hfinal := hderivN.congr_of_eventuallyEq heq hut
  rwa [← hut] at hfinal

/-- **Global forward existence for a `C¹`, compactly-supported autonomous field.**
A `C¹` field with compact support is automatically globally Lipschitz
(`ContDiff.lipschitzWith_of_hasCompactSupport`) and globally bounded
(`HasCompactSupport.exists_bound_of_continuous`), so `exists_forward_global`
applies.  This is the hypothesis shape produced by a smooth cutoff of a
dissipative field, and is exactly what discharges the existence half of
`finiteDim_dissipative_ode_global`. -/
theorem exists_forward_global_of_contDiff_compactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : E → E) (hC1 : ContDiff ℝ 1 G) (hsupp : HasCompactSupport G) (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (G (u t)) (Set.Ici (0 : ℝ)) t := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp hC1 one_ne_zero
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hC1.continuous
  exact exists_forward_global G hK (L := C.toNNReal)
    (fun x => le_trans (hC x) (Real.le_coe_toNNReal C)) x₀

end Navier.Analysis.DissipativeODEGlobal
