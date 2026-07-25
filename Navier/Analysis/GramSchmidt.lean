import Navier.Analysis.GalerkinBasis

/-!
# Gram–Schmidt orthonormalization of a raw divergence-free family

The recursion layer for the named residual `rawDivFree_orthonormalize`
(`Navier/Analysis/GalerkinBasis.lean`).  Given a `RawDivFreeFamily` — a
countable, `L²`-dense, `L²`-linearly-independent family of divergence-free
Schwartz fields — the classical Gram–Schmidt recursion
`w_n = normalize(v_n − ∑_{k<n} ⟨v_n, w_k⟩ • w_k)` in the `schwartzL2Inner`
seminorm produces the `GalerkinBasisFamily`
[Robinson–Rodrigo–Sadowski, *The Three-Dimensional Navier–Stokes
Equations*, Ch. 4; Temam, *Navier–Stokes Equations*, Ch. III §3].

## Derived here (no sorry)

* `gsVec` / `gsU` / `gsVec_eq` — the well-founded recursion, the
  un-normalized residual, and the unfolding equation `w_n = normalize(u_n)`.
* `divFree_const_smul`, `divFree_add`, `divFree_sub`, `divFree_sum_mem` —
  closure of the divergence-free class under finite `ℝ`-combinations at the
  `staticDivergence` level (pointwise linearity).
* `gsU_range` — `Finset.range` reindexing of the residual sum.
* `gsVec_divFree` — **every Gram–Schmidt mode is divergence-free** (strong
  induction: each mode is a finite combination of raw modes).
* `gsVec_orthonormal_of_pos` — **orthonormality** `⟨w_i, w_j⟩ = δ_ij` by
  nested induction, from the banked `gramSchmidt_residual_inner` and
  `schwartzL2Inner_normalize_self`, conditional on residual positivity.

## Derived here (recursion bridge, no sorry)

* `gsVec_eq_gramSchmidtField` — this file's `gsVec`/`gsU` recursion coincides
  with the banked `gramSchmidtField`/`gsResidual` recursion of
  `GalerkinBasis.lean` (strong induction; same normalization recursion, only
  the sum presentation differs).
* `gsU_pos` — residual positivity, derived from `gsResidual_inner_pos`
  (`GalerkinBasis.lean`, `L²`-independence ⇒ positive residual seminorm)
  through the bridge.
* `gsVec_dense_span` — density transfer, derived from
  `gramSchmidtField_dense_span` (`GalerkinBasis.lean`) through the bridge.

`rawDivFree_orthonormalize'` assembles the `GalerkinBasisFamily` from those
facts with no remaining sorry.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Navier Navier.Analysis.Enstrophy Navier.Analysis.LerayWeak
  Navier.Analysis.OfficialABEncoding Navier.Analysis.GalerkinBasis Filter

namespace Navier.Analysis.GramSchmidt

/-- **The Gram–Schmidt normalized family.**  `w_n = (1/√⟨u_n, u_n⟩) • u_n`
with `u_n` the residual of `v n` against the previous modes, by well-founded
recursion on `n` (each subterm uses `k < n`). -/
noncomputable def gsVec (v : ℕ → SchwartzVelocity) : ℕ → SchwartzVelocity
  | n =>
    let u := v n - ∑ k : Fin n, schwartzL2Inner (v n) (gsVec v k.1) • gsVec v k.1
    (1 / Real.sqrt (schwartzL2Inner u u)) • u
termination_by n => n
decreasing_by exact k.isLt

/-- **The un-normalized Gram–Schmidt residual** `u_n = v_n − ∑_{k<n}
⟨v_n, w_k⟩ • w_k`. -/
def gsU (v : ℕ → SchwartzVelocity) (n : ℕ) : SchwartzVelocity :=
  v n - ∑ k : Fin n, schwartzL2Inner (v n) (gsVec v k.1) • gsVec v k.1

/-- **Unfolding equation**: `gsVec v n = normalize (gsU v n)`. -/
theorem gsVec_eq (v : ℕ → SchwartzVelocity) (n : ℕ) :
    gsVec v n = (1 / Real.sqrt (schwartzL2Inner (gsU v n) (gsU v n))) • gsU v n := by
  rw [gsVec]; rfl

/-- The divergence-free class is closed under constant scaling. -/
theorem divFree_const_smul (c : ℝ) (f : SchwartzVelocity) (hf : DivergenceFreeInitial f) :
    DivergenceFreeInitial (c • f) := by
  intro x
  have h : (fun y => (c • f) y) = fun y => c • (f y) := by funext y; simp
  rw [h, staticDivergence_const_smul _ _ _ (schwartz_differentiableAt _ x), hf x, mul_zero]

/-- The divergence-free class is closed under addition. -/
theorem divFree_add (f g : SchwartzVelocity)
    (hf : DivergenceFreeInitial f) (hg : DivergenceFreeInitial g) :
    DivergenceFreeInitial (f + g) := by
  intro x
  have h : (fun y => (f + g) y) = fun y => f y + g y := by funext y; simp
  rw [h, staticDivergence_add _ _ x (schwartz_differentiableAt _ x)
    (schwartz_differentiableAt _ x), hf x, hg x, add_zero]

/-- The divergence-free class is closed under subtraction. -/
theorem divFree_sub (f g : SchwartzVelocity)
    (hf : DivergenceFreeInitial f) (hg : DivergenceFreeInitial g) :
    DivergenceFreeInitial (f - g) := by
  have h : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h]; exact divFree_add f _ hf (divFree_const_smul _ _ hg)

/-- **Finite `ℝ`-combinations over an arbitrary index finset of
divergence-free fields are divergence-free** (induction on the finset). -/
theorem divFree_sum_mem (s : Finset ℕ) (c : ℕ → ℝ) (v : ℕ → SchwartzVelocity)
    (hv : ∀ j ∈ s, DivergenceFreeInitial (v j)) :
    DivergenceFreeInitial (∑ j ∈ s, c j • v j) := by
  induction s using Finset.induction_on with
  | empty => intro x; simp [staticDivergence]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact divFree_add _ _ (divFree_const_smul _ _ (hv a (Finset.mem_insert_self a s)))
      (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

/-- The residual sum reindexed from `Fin n` to `Finset.range n`. -/
theorem gsU_range (v : ℕ → SchwartzVelocity) (n : ℕ) :
    gsU v n = v n - ∑ k ∈ Finset.range n, schwartzL2Inner (v n) (gsVec v k) • gsVec v k := by
  unfold gsU
  rw [← Fin.sum_univ_eq_sum_range (fun k => schwartzL2Inner (v n) (gsVec v k) • gsVec v k) n]

/-- **Every Gram–Schmidt mode of a raw divergence-free family is
divergence-free** [Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3].  Strong
induction on `n`: `w_n` is a scalar multiple of `v n − (finite combination
of earlier modes)`, and the class is closed under finite `ℝ`-combinations. -/
theorem gsVec_divFree (R : RawDivFreeFamily) (n : ℕ) : DivergenceFreeInitial (gsVec R.v n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [gsVec_eq]
    apply divFree_const_smul
    rw [gsU_range]
    exact divFree_sub _ _ (R.divergence_free n)
      (divFree_sum_mem _ _ _ (fun j hj => ih j (Finset.mem_range.mp hj)))

/-- **Gram–Schmidt orthonormality** [Robinson–Rodrigo–Sadowski, *The
Three-Dimensional Navier–Stokes Equations*, Ch. 4; Temam,
*Navier–Stokes Equations*, Ch. III §3]: if every residual has strictly
positive `L²` seminorm (which `R.independent` supplies via `gsU_pos`), then
`⟨w_i, w_j⟩ = δ_ij`.  Nested induction on `n > max i j`: the new mode
normalizes to unit seminorm (`schwartzL2Inner_normalize_self`) and is
orthogonal to every earlier mode (`gramSchmidt_residual_inner` against the
orthonormal prefix). -/
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

/-- **Recursion bridge**: the `gsVec`/`gsU` recursion of this file coincides
with the banked `gramSchmidtField`/`gsResidual` recursion of
`GalerkinBasis.lean` — the same normalization recursion
`w_n = normalize(v_n − ∑_{k<n} ⟨v_n, w_k⟩ w_k)`, differing only in the sum
presentation (`Fin n` vs `Finset.range n`).  Strong induction on `n`: the
residuals agree termwise from the induction hypothesis on the earlier modes
(`gsVec R.v k = gramSchmidtField R k` for `k < n`), hence the normalized fields
agree. -/
theorem gsVec_eq_gramSchmidtField (R : RawDivFreeFamily) (n : ℕ) :
    gsVec R.v n = gramSchmidtField R n ∧ gsU R.v n = gsResidual R n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hU : gsU R.v n = gsResidual R n := by
      rw [gsU_range]
      calc R.v n - ∑ k ∈ Finset.range n,
              schwartzL2Inner (R.v n) (gsVec R.v k) • gsVec R.v k
          = R.v n - ∑ k ∈ Finset.range n,
              schwartzL2Inner (R.v n) (gramSchmidtField R k) • gramSchmidtField R k := by
            congr 1
            exact Finset.sum_congr rfl fun k hk => by
              rw [(ih k (Finset.mem_range.mp hk)).1]
        _ = gsResidual R n := rfl
    exact ⟨by rw [gsVec_eq, hU, ← gramSchmidtField_eq], hU⟩

/-- **Positivity of the Gram–Schmidt residual** [Robinson–Rodrigo–Sadowski
Ch. 4; Temam III §3].  `L²`-linear independence of the raw family forces every
residual to have strictly positive `L²` seminorm — the well-definedness of the
normalization.  Derived through `gsVec_eq_gramSchmidtField` from the banked
`gsResidual_inner_pos` (`GalerkinBasis.lean`), whose proof runs the
span-representation contradiction (`gsResidual_repr` + `R.independent`). -/
theorem gsU_pos (R : RawDivFreeFamily) (n : ℕ) :
    0 < schwartzL2Inner (gsU R.v n) (gsU R.v n) := by
  rw [(gsVec_eq_gramSchmidtField R n).2]
  exact gsResidual_inner_pos R n

/-- **Dense-span transfer through Gram–Schmidt** [Robinson–Rodrigo–Sadowski
Ch. 4; Temam III §3].  The raw family's `L²`-dense finite spans transfer to the
Gram–Schmidt family (invertible triangular change-of-basis).  Derived through
`gsVec_eq_gramSchmidtField` from the banked `gramSchmidtField_dense_span`
(`GalerkinBasis.lean`), whose proof re-expresses each raw approximant in the
Gram–Schmidt span via `raw_inSpanW`. -/
theorem gsVec_dense_span (R : RawDivFreeFamily) :
    ∀ u : SchwartzVelocity, DivergenceFreeInitial u → ∀ ε : ℝ, 0 < ε →
      ∃ (m : ℕ) (c : ℕ → ℝ),
        schwartzL2Inner (u - ∑ j ∈ Finset.range m, c j • gsVec R.v j)
          (u - ∑ j ∈ Finset.range m, c j • gsVec R.v j) < ε := by
  have hfun : gsVec R.v = gramSchmidtField R :=
    funext fun n => (gsVec_eq_gramSchmidtField R n).1
  rw [hfun]
  exact gramSchmidtField_dense_span R

/-- **Assembly: a raw dense divergence-free family orthonormalizes into a
`GalerkinBasisFamily`** [Robinson–Rodrigo–Sadowski Ch. 4; Temam III §3] —
ProvedModulo the two named leaves `gsU_pos` (residual positivity) and
`gsVec_dense_span` (density transfer); divergence-free preservation and
orthonormality are fully derived above.  This is the recursion-side half of
the named residual `rawDivFree_orthonormalize` in `GalerkinBasis.lean`. -/
theorem rawDivFree_orthonormalize' (R : RawDivFreeFamily) : Nonempty GalerkinBasisFamily :=
  ⟨{ w := gsVec R.v
     divergence_free := gsVec_divFree R
     orthonormal := gsVec_orthonormal_of_pos R.v (gsU_pos R)
     dense_span := gsVec_dense_span R }⟩

end Navier.Analysis.GramSchmidt
