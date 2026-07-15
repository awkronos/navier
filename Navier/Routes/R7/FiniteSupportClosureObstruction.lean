import Navier.Routes.R7.GeneratedSupport

/-!
# Finite additive-support closure obstruction

A finite set of real Fourier frequencies cannot contain zero, contain a
nonzero frequency, and remain closed under unrestricted pairwise addition.
Indeed, closure retains every natural multiple of the nonzero frequency, while
those multiples are all distinct.

For a centrally symmetric nontrivial support, exact invariance under the
untruncated convolution-support step would force zero into the support and
then force this impossible additive closure. Thus every such finite support
strictly acquires a new frequency under unrestricted convolution generation.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Routes.R7

/-- Closure of a finite Fourier support under unrestricted pairwise addition. -/
def PairwiseAddClosed (S : Finset Space) : Prop :=
  ∀ ⦃k l : Space⦄, k ∈ S → l ∈ S → k + l ∈ S

/-- Zero and pairwise-additive closure retain every natural multiple of an
occupied frequency. -/
theorem nsmul_mem_of_pairwiseAddClosed
    {S : Finset Space} (hzero : (0 : Space) ∈ S)
    (hclosed : PairwiseAddClosed S) {q : Space} (hq : q ∈ S) :
    ∀ n : ℕ, n • q ∈ S := by
  intro n
  induction n with
  | zero =>
      simpa using hzero
  | succ n ih =>
      rw [succ_nsmul]
      exact hclosed ih hq

/-- Natural multiples of a nonzero real three-frequency are all distinct. -/
theorem nsmul_injective_of_ne_zero
    {q : Space} (hq : q ≠ 0) :
    Function.Injective (fun n : ℕ => n • q) := by
  intro m n hmn
  have hcoord : ∃ i : Fin 3, q i ≠ 0 := by
    by_contra h
    apply hq
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  rcases hcoord with ⟨i, hi⟩
  have hc : (m : ℝ) * q i = (n : ℝ) * q i := by
    simpa [nsmul_eq_mul] using congrArg (fun v : Space => v i) hmn
  have hcast : (m : ℝ) = (n : ℝ) :=
    mul_right_cancel₀ hi hc
  exact_mod_cast hcast

/-- Every member of a finite pairwise-additively closed real support containing
zero is zero. The contradiction embeds Fin (S.card + 1) into S by natural
multiples of a hypothetical nonzero member. -/
theorem mem_eq_zero_of_finite_pairwiseAddClosed
    {S : Finset Space} (hzero : (0 : Space) ∈ S)
    (hclosed : PairwiseAddClosed S) {q : Space} (hq : q ∈ S) :
    q = 0 := by
  by_contra hqzero
  let f : Fin (S.card + 1) → {x : Space // x ∈ S} :=
    fun n => ⟨n.val • q,
      nsmul_mem_of_pairwiseAddClosed hzero hclosed hq n.val⟩
  have hf : Function.Injective f := by
    intro m n hmn
    apply Fin.ext
    apply nsmul_injective_of_ne_zero hqzero
    exact congrArg Subtype.val hmn
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

/-- The only finite pairwise-additively closed real support containing zero is
the singleton support containing only zero. -/
theorem eq_singleton_zero_of_finite_pairwiseAddClosed
    {S : Finset Space} (hzero : (0 : Space) ∈ S)
    (hclosed : PairwiseAddClosed S) :
    S = {0} := by
  apply Finset.Subset.antisymm
  · intro q hq
    have hqzero :=
      mem_eq_zero_of_finite_pairwiseAddClosed hzero hclosed hq
    simp [hqzero]
  · intro q hq
    rw [Finset.mem_singleton] at hq
    subst q
    exact hzero

/-- Exact invariance under the unrestricted convolution-support step is
equivalent to closure under all pairwise frequency sums. -/
theorem generatedSupportStep_eq_self_iff_pairwiseAddClosed
    {S : Finset Space} :
    generatedSupportStep S = S ↔ PairwiseAddClosed S := by
  constructor
  · intro hfixed k l hk hl
    rw [← hfixed]
    exact add_mem_generatedSupportStep hk hl
  · intro hclosed
    apply Finset.Subset.antisymm
    · intro q hq
      rw [generatedSupportStep, Finset.mem_union] at hq
      rcases hq with hq | hq
      · exact hq
      · rw [pairwiseMinkowskiSum, Finset.mem_image] at hq
        rcases hq with ⟨⟨k, l⟩, hkl, rfl⟩
        rw [Finset.mem_product] at hkl
        exact hclosed hkl.1 hkl.2
    · exact subset_generatedSupportStep S

/-- No finite centrally symmetric support containing a nonzero frequency is
exactly invariant under unrestricted convolution-support generation. -/
theorem nontrivial_centrallySymmetric_generatedSupportStep_ne_self
    {S : Finset Space} (hSym : CentrallySymmetricSupport S)
    {q : Space} (hq : q ∈ S) (hqzero : q ≠ 0) :
    generatedSupportStep S ≠ S := by
  intro hfixed
  have hclosed : PairwiseAddClosed S :=
    generatedSupportStep_eq_self_iff_pairwiseAddClosed.mp hfixed
  have hzero : (0 : Space) ∈ S := by
    simpa using hclosed hq (hSym q hq)
  exact hqzero
    (mem_eq_zero_of_finite_pairwiseAddClosed hzero hclosed hq)

end Navier.Routes.R7
