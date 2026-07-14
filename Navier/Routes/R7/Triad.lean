import Navier.Routes.R7.ExactSymbol

/-!
# Exact divergence-free triad energy-transfer probe

This file proves a finite-dimensional algebraic identity for one three-wave
interaction.  It does not construct Fourier series, prove convergence or shell
summability, model Tao's averaged operator, or imply Navier--Stokes regularity.

For wavevectors `k + l + m = 0` and amplitudes `a ⊥ k`, `b ⊥ l`,
`c ⊥ m`, the six ordered convection energy-transfer scalars cancel in
three pairs, one pair for each advecting mode.  A concrete triad shows that the
individual ordered transfers need not vanish or have a fixed sign.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix

namespace Navier.Routes.R7

/-- The real scalar part of the ordered interaction in which `advector`
advects `advected` at wavevector `advectedWave`, with the output paired against
`receiver`.  For a divergence-free receiver at the output wavevector, the
Leray projection drops out of this energy pairing. -/
def orderedTransfer
    (advector advected receiver advectedWave : Space) : ℝ :=
  (advector ⬝ᵥ advectedWave) * (advected ⬝ᵥ receiver)

/-- Pairing the denominator-free Leray numerator against a vector orthogonal
to its frequency removes the longitudinal correction. -/
theorem receiver_dot_lerayNumerator
    (q b c : Space) (hc : c ⬝ᵥ q = 0) :
    c ⬝ᵥ lerayNumerator q b = (q ⬝ᵥ q) * (b ⬝ᵥ c) := by
  simp only [lerayNumerator, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hc, mul_zero, sub_zero, dotProduct_comm c b]

/-- The two ordered transfers with a fixed advecting mode cancel. -/
theorem advector_pair_cancels
    (p q r u v w : Space)
    (htriad : p + q + r = 0)
    (hdiv : p ⬝ᵥ u = 0) :
    orderedTransfer u v w q + orderedTransfer u w v r = 0 := by
  have hqr : q + r = -p := by
    calc
      q + r = (p + q + r) - p := by abel
      _ = -p := by rw [htriad]; simp
  have hup : u ⬝ᵥ p = 0 := by
    rw [dotProduct_comm]
    exact hdiv
  have huqr : u ⬝ᵥ q + u ⬝ᵥ r = 0 := by
    calc
      u ⬝ᵥ q + u ⬝ᵥ r = u ⬝ᵥ (q + r) :=
        (dotProduct_add u q r).symm
      _ = u ⬝ᵥ (-p) := by rw [hqr]
      _ = -(u ⬝ᵥ p) := by simp
      _ = 0 := by rw [hup]; simp
  calc
    orderedTransfer u v w q + orderedTransfer u w v r =
        (u ⬝ᵥ q + u ⬝ᵥ r) * (v ⬝ᵥ w) := by
          simp only [orderedTransfer]
          rw [dotProduct_comm w v]
          ring
    _ = 0 := by rw [huqr]; ring

/-- The six ordered transfers cancel in three pairs, grouped by advecting
mode `a`, then `b`, then `c`. -/
theorem grouped_six_transfer_cancellation
    (k l m a b c : Space)
    (htriad : k + l + m = 0)
    (ha : k ⬝ᵥ a = 0) (hb : l ⬝ᵥ b = 0) (hc : m ⬝ᵥ c = 0) :
    orderedTransfer a b c l + orderedTransfer a c b m = 0 ∧
    orderedTransfer b a c k + orderedTransfer b c a m = 0 ∧
    orderedTransfer c a b k + orderedTransfer c b a l = 0 := by
  have htriad_b : l + k + m = 0 := by
    calc
      l + k + m = k + l + m := by abel
      _ = 0 := htriad
  have htriad_c : m + k + l = 0 := by
    calc
      m + k + l = k + l + m := by abel
      _ = 0 := htriad
  exact ⟨advector_pair_cancels k l m a b c htriad ha,
    advector_pair_cancels l k m b a c htriad_b hb,
    advector_pair_cancels m k l c a b htriad_c hc⟩

/-- The sum of all six ordered convection energy transfers. -/
def sixTransferSum (k l m a b c : Space) : ℝ :=
  (orderedTransfer a b c l + orderedTransfer a c b m) +
  (orderedTransfer b a c k + orderedTransfer b c a m) +
  (orderedTransfer c a b k + orderedTransfer c b a l)

/-- Exact global energy cancellation for one divergence-free three-wave
interaction. -/
theorem six_transfer_sum_zero
    (k l m a b c : Space)
    (htriad : k + l + m = 0)
    (ha : k ⬝ᵥ a = 0) (hb : l ⬝ᵥ b = 0) (hc : m ⬝ᵥ c = 0) :
    sixTransferSum k l m a b c = 0 := by
  obtain ⟨hA, hB, hC⟩ :=
    grouped_six_transfer_cancellation k l m a b c htriad ha hb hc
  simp [sixTransferSum, hA, hB, hC]

def witnessK : Space := ![(1 : ℝ), 0, 0]
def witnessL : Space := ![(0 : ℝ), 1, 0]
def witnessM : Space := ![(-1 : ℝ), -1, 0]
def witnessA : Space := ![(0 : ℝ), 1, 0]
def witnessB : Space := ![(1 : ℝ), 0, 0]
def witnessC : Space := ![(1 : ℝ), -1, 0]

/-- The concrete wavevectors form a triad and each amplitude is
divergence-free at its own wavevector. -/
theorem witness_admissible :
    witnessK + witnessL + witnessM = 0 ∧
    witnessK ⬝ᵥ witnessA = 0 ∧
    witnessL ⬝ᵥ witnessB = 0 ∧
    witnessM ⬝ᵥ witnessC = 0 := by
  constructor
  · ext i
    fin_cases i <;>
      norm_num [witnessK, witnessL, witnessM,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · norm_num [witnessK, witnessL, witnessM, witnessA, witnessB, witnessC,
      Matrix.vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

/-- The first ordered transfer is `1`, while the full six-term sum is zero.
Thus the cancellation is genuinely collective rather than termwise. -/
theorem witness_nontermwise_cancellation :
    orderedTransfer witnessA witnessB witnessC witnessL = 1 ∧
    sixTransferSum witnessK witnessL witnessM witnessA witnessB witnessC = 0 := by
  constructor
  · norm_num [orderedTransfer, witnessA, witnessB, witnessC, witnessL,
      Matrix.vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
  · rcases witness_admissible with ⟨htriad, ha, hb, hc⟩
    exact six_transfer_sum_zero
      witnessK witnessL witnessM witnessA witnessB witnessC htriad ha hb hc

end Navier.Routes.R7
