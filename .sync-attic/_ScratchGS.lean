import Navier.Analysis.GalerkinBasis
open MeasureTheory Navier Navier.Analysis.Enstrophy Navier.Analysis.LerayWeak Navier.Analysis.OfficialABEncoding
open Navier.Analysis.GalerkinBasis Filter
noncomputable section

-- Gram–Schmidt normalized family via well-founded recursion on Fin n subterms.
noncomputable def gsVec (v : ℕ → SchwartzVelocity) : ℕ → SchwartzVelocity
  | n =>
    let u := v n - ∑ k : Fin n, schwartzL2Inner (v n) (gsVec v k.1) • gsVec v k.1
    (1 / Real.sqrt (schwartzL2Inner u u)) • u
termination_by n => n
decreasing_by exact k.isLt

-- un-normalized residual
def gsU (v : ℕ → SchwartzVelocity) (n : ℕ) : SchwartzVelocity :=
  v n - ∑ k : Fin n, schwartzL2Inner (v n) (gsVec v k.1) • gsVec v k.1

-- unfolding: gsVec = normalize (gsU)
theorem gsVec_eq (v : ℕ → SchwartzVelocity) (n : ℕ) :
    gsVec v n = (1 / Real.sqrt (schwartzL2Inner (gsU v n) (gsU v n))) • gsU v n := by
  rw [gsVec]; rfl

theorem divFree_const_smul (c : ℝ) (f : SchwartzVelocity) (hf : DivergenceFreeInitial f) :
    DivergenceFreeInitial (c • f) := by
  intro x
  have h : (fun y => (c • f) y) = fun y => c • (f y) := by funext y; simp
  rw [h, staticDivergence_const_smul _ _ _ (schwartz_differentiableAt _ x), hf x, mul_zero]

theorem divFree_add (f g : SchwartzVelocity)
    (hf : DivergenceFreeInitial f) (hg : DivergenceFreeInitial g) :
    DivergenceFreeInitial (f + g) := by
  intro x
  have h : (fun y => (f + g) y) = fun y => f y + g y := by funext y; simp
  rw [h, staticDivergence_add _ _ x (schwartz_differentiableAt _ x)
    (schwartz_differentiableAt _ x), hf x, hg x, add_zero]

theorem divFree_sub (f g : SchwartzVelocity)
    (hf : DivergenceFreeInitial f) (hg : DivergenceFreeInitial g) :
    DivergenceFreeInitial (f - g) := by
  have h : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h]; exact divFree_add f _ hf (divFree_const_smul _ _ hg)

theorem divFree_sum_mem (s : Finset ℕ) (c : ℕ → ℝ) (v : ℕ → SchwartzVelocity)
    (hv : ∀ j ∈ s, DivergenceFreeInitial (v j)) :
    DivergenceFreeInitial (∑ j ∈ s, c j • v j) := by
  induction s using Finset.induction_on with
  | empty => intro x; simp [staticDivergence]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact divFree_add _ _ (divFree_const_smul _ _ (hv a (Finset.mem_insert_self a s)))
      (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

theorem gsU_range (v : ℕ → SchwartzVelocity) (n : ℕ) :
    gsU v n = v n - ∑ k ∈ Finset.range n, schwartzL2Inner (v n) (gsVec v k) • gsVec v k := by
  unfold gsU
  rw [← Fin.sum_univ_eq_sum_range (fun k => schwartzL2Inner (v n) (gsVec v k) • gsVec v k) n]

theorem gsVec_divFree (R : RawDivFreeFamily) (n : ℕ) : DivergenceFreeInitial (gsVec R.v n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [gsVec_eq]
    apply divFree_const_smul
    rw [gsU_range]
    exact divFree_sub _ _ (R.divergence_free n)
      (divFree_sum_mem _ _ _ (fun j hj => ih j (Finset.mem_range.mp hj)))

theorem gsVec_orthonormal_of_pos (v : ℕ → SchwartzVelocity)
    (hpos : ∀ i, 0 < schwartzL2Inner (gsU v i) (gsU v i)) (i j : ℕ) :
    schwartzL2Inner (gsVec v i) (gsVec v j) = if i = j then 1 else 0 := by
  suffices H : ∀ n, ∀ i < n, ∀ j < n,
      schwartzL2Inner (gsVec v i) (gsVec v j) = if i = j then 1 else 0 by
    exact H (max i j + 1) i (by omega) j (by omega)
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n hn =>
    have horth : ∀ a b, a < n → b < n →
        schwartzL2Inner (gsVec v a) (gsVec v b) = if a = b then 1 else 0 :=
      fun a b ha hb => hn a ha b hb
    have hres : ∀ b, b < n → schwartzL2Inner (gsU v n) (gsVec v b) = 0 := by
      intro b hb; rw [gsU_range]; exact gramSchmidt_residual_inner (gsVec v) n horth (v n) hb
    have hnn : schwartzL2Inner (gsVec v n) (gsVec v n) = 1 := by
      rw [gsVec_eq v n]; exact schwartzL2Inner_normalize_self (gsU v n) (hpos n)
    have hnb : ∀ b, b < n → schwartzL2Inner (gsVec v n) (gsVec v b) = 0 := by
      intro b hb; rw [gsVec_eq v n, schwartzL2Inner_smul_left, hres b hb, mul_zero]
    have hbn : ∀ b, b < n → schwartzL2Inner (gsVec v b) (gsVec v n) = 0 := by
      intro b hb; rw [schwartzL2Inner_comm]; exact hnb b hb
    intro i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
      · exact horth i j hi' hj'
      · rw [hj', if_neg (show ¬ i = n by omega)]; exact hbn i hi'
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
      · rw [hi', if_neg (show ¬ n = j by omega)]; exact hnb j hj'
      · rw [hi', hj', if_pos rfl]; exact hnn

-- HONEST SORRY: positivity from independence (span-coefficient tracking, RRS Ch.4)
theorem gsU_pos (R : RawDivFreeFamily) (n : ℕ) :
    0 < schwartzL2Inner (gsU R.v n) (gsU R.v n) := by
  sorry

-- HONEST SORRY: dense_span transfer via span-equality (RRS Ch.4)
theorem gsVec_dense_span (R : RawDivFreeFamily) :
    ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
      ∃ (m : ℕ) (c : ℕ → ℝ),
        schwartzL2Inner (u - ∑ j ∈ Finset.range m, c j • gsVec R.v j)
          (u - ∑ j ∈ Finset.range m, c j • gsVec R.v j) < ε := by
  sorry

theorem rawDivFree_orthonormalize' (R : RawDivFreeFamily) : Nonempty GalerkinBasisFamily :=
  ⟨{ w := gsVec R.v
     divergence_free := gsVec_divFree R
     orthonormal := gsVec_orthonormal_of_pos R.v (gsU_pos R)
     dense_span := gsVec_dense_span R }⟩

#print axioms gsVec_orthonormal_of_pos
#print axioms gsVec_divFree
