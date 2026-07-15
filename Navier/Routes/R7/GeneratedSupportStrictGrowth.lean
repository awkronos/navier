import Navier.Routes.R7.GeneratedSupport
import Navier.Routes.R7.FiniteSupportClosureObstruction

/-!
# Strict growth of recursively generated finite support

At every nonzero common scale, the recursive six-mode support contains a
fixed nonzero seed frequency and remains centrally symmetric. The finite
additive-closure obstruction therefore rules out equality with its next
unrestricted pairwise-sum generation. Consequently, every generation is a
strict subset of its successor, the support cardinalities strictly increase,
a genuinely new frequency exists at every step, and the cardinalities are
unbounded.

These are support-combinatorics statements. They do not assert that a new
frequency has nonzero Fourier amplitude after coefficient cancellation, nor
do they establish energy transfer, a cascade, or a Navier--Stokes solution.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Routes.R7

/-- The positive witness K-frequency is nonzero at every nonzero scale. -/
theorem scaledSymWitnessModeWave_posK_ne_zero
    {s : ℝ} (hs : s ≠ 0) :
    scaledSymWitnessModeWave s .posK ≠ 0 := by
  intro h
  have hcoord := congrArg (fun v : Space => v 0) h
  simp [scaledSymWitnessModeWave, scaledWitnessK, witnessK,
    Matrix.cons_val_zero] at hcoord
  exact hs hcoord

/-- At nonzero scale, every recursive support is a strict subset of its next
unrestricted convolution-support generation. -/
theorem generatedSupport_ssubset_succ
    {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    generatedSupport s n ⊂ generatedSupport s (n + 1) := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨generatedSupport_subset_succ s n, ?_⟩
  intro hEq
  have hfixed :
      generatedSupportStep (generatedSupport s n) =
        generatedSupport s n := by
    change generatedSupport s (n + 1) = generatedSupport s n
    exact hEq.symm
  exact
    nontrivial_centrallySymmetric_generatedSupportStep_ne_self
      (generatedSupport_centrallySymmetric s n)
      (scaledSymWitnessModeWave_mem_generatedSupport s .posK n)
      (scaledSymWitnessModeWave_posK_ne_zero hs)
      hfixed

/-- At nonzero scale, support cardinality increases at every generation. -/
theorem generatedSupport_card_lt_succ
    {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    (generatedSupport s n).card <
      (generatedSupport s (n + 1)).card :=
  Finset.card_lt_card (generatedSupport_ssubset_succ hs n)

/-- The recursive supports are strictly monotone under inclusion at every
nonzero scale. -/
theorem generatedSupport_strictMono
    {s : ℝ} (hs : s ≠ 0) :
    StrictMono (generatedSupport s) :=
  strictMono_nat_of_lt_succ (generatedSupport_ssubset_succ hs)

/-- The recursive support cardinalities are strictly monotone at every
nonzero scale. -/
theorem generatedSupport_card_strictMono
    {s : ℝ} (hs : s ≠ 0) :
    StrictMono (fun n => (generatedSupport s n).card) :=
  strictMono_nat_of_lt_succ (generatedSupport_card_lt_succ hs)

/-- Every generation at nonzero scale contains an exact new-frequency witness
that was absent from the preceding support. -/
theorem exists_new_frequency_generatedSupport_succ
    {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    ∃ q : Space,
      q ∈ generatedSupport s (n + 1) ∧
        q ∉ generatedSupport s n := by
  simpa only [and_assoc] using
    Finset.exists_mem_notMem_of_card_lt_card
      (generatedSupport_card_lt_succ hs n)

/-- Generation number is a uniform lower bound for support cardinality at
every nonzero scale. -/
theorem generation_le_generatedSupport_card
    {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    n ≤ (generatedSupport s n).card := by
  induction n with
  | zero =>
      exact Nat.zero_le _
  | succ n ih =>
      have hgrowth := generatedSupport_card_lt_succ hs n
      omega

/-- At every nonzero scale, generated-support cardinalities exceed every
prescribed finite lower bound. -/
theorem generatedSupport_card_unbounded
    {s : ℝ} (hs : s ≠ 0) (M : ℕ) :
    ∃ n : ℕ, M ≤ (generatedSupport s n).card :=
  ⟨M, generation_le_generatedSupport_card hs M⟩

/-- At nonzero scale, the recursive support sequence is not eventually
constant. -/
theorem generatedSupport_not_eventually_constant
    {s : ℝ} (hs : s ≠ 0) :
    ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      generatedSupport s n = generatedSupport s N := by
  rintro ⟨N, hN⟩
  have hEq :
      generatedSupport s (N + 1) = generatedSupport s N :=
    hN (N + 1) (Nat.le_succ N)
  exact
    (Finset.ssubset_iff_subset_ne.mp
      (generatedSupport_ssubset_succ hs N)).2 hEq.symm

end Navier.Routes.R7
