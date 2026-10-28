import Navier.Problem

/- Exact whole-space carrier obstruction, not a finite surrogate:
   every nonzero spatial dilation leaves a nonzero period vector. A Schwartz
   field invariant under any nonzero translation is zero. This rules out direct
   periodic lattice physical realization even after scalar spatial rescaling.
   Original consumer: Navier.ProblemStatements.WholeSpaceGlobalRegularity via
   IsClassicalSolution.initial_condition; no PDE or terminal bound is assumed.
   Consumer fold imports the actual Navier.Problem endpoint, now materialized.
-/
noncomputable section
namespace SolNavierTransport

theorem schwartz_eq_zero_of_nonzero_translation
    (f : SchwartzMap (Fin 3 → ℝ) (Fin 3 → ℝ))
    (v : Fin 3 → ℝ) (hv : v ≠ 0)
    (hperiod : ∀ x, f (x + v) = f x) : f = 0 := by
  ext x i
  suffices hn : ‖f x‖ = 0 by
    have hx : f x = 0 := norm_eq_zero.mp hn
    simp [hx]
  obtain ⟨C, _hC, hdec⟩ := f.decay 1 0
  have hshift : ∀ n : ℕ, f (x + (n : ℝ) • v) = f x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs : x + ((n + 1 : ℕ) : ℝ) • v = (x + (n : ℝ) • v) + v := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rw [hs, hperiod, ih]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hbound : ∀ n : ℕ, ((n : ℝ) * ‖v‖ - ‖x‖) * ‖f x‖ ≤ C := by
    intro n
    have hd := hdec (x + (n : ℝ) • v)
    rw [norm_iteratedFDeriv_zero, pow_one, hshift n] at hd
    have ht : (n : ℝ) * ‖v‖ - ‖x‖ ≤ ‖x + (n : ℝ) • v‖ := by
      have htri := norm_add_le (-(x)) (x + (n : ℝ) • v)
      have heq : -x + (x + (n : ℝ) • v) = (n : ℝ) • v := by abel
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n), norm_neg] at htri
      linarith
    exact (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans hd
  by_contra hne
  have hp : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  obtain ⟨n, hn⟩ := exists_nat_gt ((C / ‖f x‖ + ‖x‖) / ‖v‖)
  have hn' : C / ‖f x‖ + ‖x‖ < (n : ℝ) * ‖v‖ := (div_lt_iff₀ hvpos).mp hn
  have hlt : C / ‖f x‖ < (n : ℝ) * ‖v‖ - ‖x‖ := by linarith
  have hstrict := (div_lt_iff₀ hp).mp hlt
  linarith [hbound n]

/-- A direct dilation of a periodic whole-space field cannot agree with a
nonzero Schwartz datum. The transformed period is exactly c⁻¹ • v; no limit,
finite grid, or PDE surrogate is substituted for the physical space. -/
theorem no_scaled_periodic_initial_trace
    (f : SchwartzMap (Fin 3 → ℝ) (Fin 3 → ℝ)) (hf : f ≠ 0)
    (g : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (v : Fin 3 → ℝ) (hv : v ≠ 0) (hperiod : ∀ x, g (x + v) = g x)
    (c a : ℝ) (hc : c ≠ 0) :
    ¬ (∀ x, f x = a • g (c • x)) := by
  intro htrace
  have hw : c⁻¹ • v ≠ 0 := smul_ne_zero (inv_ne_zero hc) hv
  apply hf
  apply schwartz_eq_zero_of_nonzero_translation f (c⁻¹ • v) hw
  intro x
  rw [htrace, htrace]
  congr 1
  have hs : c • (x + c⁻¹ • v) = c • x + v := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [hs, hperiod]

/-- Exact original endpoint obstruction. A scalar dilation of a periodic
velocity cannot satisfy even the initial condition of IsClassicalSolution for
nonzero Schwartz data. This refutes this transport route, not the A endpoint. -/
theorem no_scaled_periodic_classical_solution
    (ν : ℝ) (force : Navier.ForceField)
    (u₀ : Navier.SchwartzVelocity) (hu₀ : u₀ ≠ 0)
    (u : Navier.VelocityEvolution) (p : Navier.PressureEvolution)
    (v : Navier.Space) (hv : v ≠ 0)
    (hperiod : ∀ x, u 0 (x + v) = u 0 x)
    (c a : ℝ) (hc : c ≠ 0) :
    ¬ Navier.IsClassicalSolution ν force u₀
        (fun t x => a • u (c ^ 2 * t) (c • x)) p := by
  intro hsol
  apply no_scaled_periodic_initial_trace u₀ hu₀ (u 0) v hv hperiod c a hc
  intro x
  simpa using (hsol.initial_condition x).symm




end SolNavierTransport
