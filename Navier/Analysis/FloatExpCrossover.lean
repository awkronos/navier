import Mathlib

/-!
# The float64 `exp` crossover points at the 1-ulp level

The solver's overflow guard uses `X_MAX = 709.782712893384` and its
underflow guard uses `X_MIN = -745.1332191019411`. This module proves, for
the real exponential at the exact rationals those floats carry, that each
guard sits strictly between its float and its single representable neighbor
with respect to the round-to-nearest thresholds

* `θ = (2^54 - 1) * 2^970`, the midpoint between the largest finite float64
  `2^1024 - 2^971` and `2^1024`, and
* `H = 2^-1075`, half the smallest positive subnormal,

via the ladder

```text
nextDown X_MIN < log H < X_MIN      and      X_MAX < log θ < nextUp X_MAX
```

(stated exactly in `crossoverLadder` below). Interpreted under IEEE-754
round-to-nearest this is the 1-ulp statement that `exp` first overflows
between `X_MAX` and its next float and first underflows to zero between
`X_MIN` and its previous float; the rounding interpretation itself is not
formalized here.

## Proof method

No transcendental fact is decided by a black box. `exp x = exp (x/1024)^1024`
(`Real.exp_nat_mul`). For `0 ≤ w ≤ 1`, `Real.exp w` is enclosed between the
41-term Taylor partial sum `∑ k ≤ 40, w^k/k!` and that sum plus Mathlib's
explicit remainder `w^41 * 42 / (41! * 41)` (`Real.sum_le_exp_of_nonneg`,
`Real.exp_bound'`; this remainder is far tighter than the coarse geometric
tail `2 (w/2)^41 / (1 - w/2)` used by `scripts/exp_crossover_cert.py`, and
the same dyadic literals bound both). The enclosing sums are precomputed
externally as dyadic rationals with 128 fractional bits (the same constants
`scripts/exp_crossover_cert.py` prints), and the remaining comparisons
`B^1024 < θ`, `θ < B'^1024`, `B''^1024 < 2^1075`, `2^1075 < B'''^1024` are
exact rational arithmetic discharged by `norm_num` (kernel-computed
evaluation of `Rat` operations; no `decide` is used on these because the
`Rat.blt` reduction path in this toolchain does not evaluate them, and no
`native_decide`/`Lean.ofReduceBool` appears anywhere in the file). The
relative slack between the Taylor enclosure and the thresholds is at least
1.4e-14 — see the margin report printed by the script — while the dyadic
rounding costs 1024 * 2^-128.

The anchor floats carry exactly the stated rationals; the bit patterns are
checked by `decide` on `Float.toBits` below.

This is numerical observation: the file states facts about the real
exponential at four named rationals and says nothing about any particular
libm implementation's `exp`.
-/

set_option exponentiation.threshold 4096

namespace Navier.FloatExpCrossover

/-! ### Anchors, thresholds, and their exact rational values -/

/-- `709.782712893384` as an exact rational (the value carried by that float).
Bit pattern `0x40862e42fefa39ef`. -/
def xMaxR : ℚ := 6243314768165359 / 8796093022208

/-- The next float above `xMaxR` as an exact rational
(`xMaxR + 2^-43`; pattern `0x40862e42fefa39f0`). -/
def xMaxUpR : ℚ := 390207173010335 / 549755813888

/-- `-745.1332191019411` as an exact rational (pattern `0xc0874910d52d3051`). -/
def xMinR : ℚ := (-6554261109157969 / 8796093022208 : ℚ)

/-- The next float below `xMinR` as an exact rational
(`xMinR - 2^-42`; pattern `0xc0874910d52d3052`). -/
def xMinDownR : ℚ := (-3277130554578985 / 4398046511104 : ℚ)

/-- `θ` as an exact rational. -/
private def thetaQ : ℚ := (2^54 - 1) * 2^970

/-- `θ`, the round-to-nearest overflow threshold of the float64 grid. -/
def thetaT : ℝ := (thetaQ : ℝ)

/-- `H = 2^-1075` as an exact rational. -/
private def halfHQ : ℚ := 1 / 2^1075

/-- `H`, the round-to-nearest underflow threshold of the float64 grid. -/
def halfH : ℝ := (halfHQ : ℝ)

-- The anchor literals carry exactly these float64 bit patterns.
example : Float.toBits 709.782712893384 = 0x40862e42fefa39ef := by decide

example : Float.toBits 709.7827128933841 = 0x40862e42fefa39f0 := by decide

example : Float.toBits (-745.1332191019411) = 0xc0874910d52d3051 := by decide

example : Float.toBits (-745.1332191019412) = 0xc0874910d52d3052 := by decide

/-! ### Taylor enclosure of `exp` (native Mathlib bounds, 41 terms) -/

/-- Mathlib's native upper bound, specialized to the 41-term Taylor sum:
`Real.exp w ≤ ∑ k ≤ 40, w^k/k! + w^41 * 42 / (41! * 41)` for `0 ≤ w ≤ 1`. -/
theorem exp_le_taylor41_add_remainder {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Real.exp w ≤
      (∑ k ∈ Finset.range 41, w ^ k / k.factorial) +
        w ^ 41 * (41 + 1) / ((41 : ℕ).factorial * 41) :=
  Real.exp_bound' (n := 41) hw0 hw1 (by norm_num)

/-- Mathlib's native lower bound, specialized to the 41-term Taylor sum:
`∑ k ≤ 40, w^k/k! ≤ Real.exp w` for `0 ≤ w`. -/
theorem taylor41_le_exp {w : ℝ} (hw0 : 0 ≤ w) :
    (∑ k ∈ Finset.range 41, w ^ k / k.factorial) ≤ Real.exp w :=
  Real.sum_le_exp_of_nonneg hw0 41

/-! ### Dyadic enclosure literals (computed by scripts/exp_crossover_cert.py)

Each bound below is the 40-term Taylor sum, plus the geometric tail
`2 * (w/2)^41 / (1 - w/2)` for the upper bounds, rounded outward to a dyadic
with 128 fractional bits — the constants the certificate script prints. -/

/-- `w = X_MAX/1024` as an exact rational. -/
private def wX : ℚ := 6243314768165359 / 9007199254740992

/-- `w = nextUp(X_MAX)/1024` as an exact rational. -/
private def wU : ℚ := 390207173010335 / 562949953421312

/-- `w = (-X_MIN)/1024` as an exact rational. -/
private def wM : ℚ := 6554261109157969 / 9007199254740992

/-- `w = (-nextDown(X_MIN))/1024` as an exact rational. -/
private def wD : ℚ := 3277130554578985 / 4503599627370496

/-- Dyadic upper bound for `exp wX` (Taylor + tail, rounded up). -/
def bUpXMax : ℚ :=
  170141183460469227821289107050334591211 / 85070591730234615865843651857942052864

/-- Dyadic lower bound for `exp wU` (Taylor sum, rounded down). -/
def bDnXUp : ℚ :=
  340282366920938493350999082228133204079 / 170141183460469231731687303715884105728

/-- Dyadic upper bound for `exp wM` (Taylor + tail, rounded up). -/
def bUpNegXMin : ℚ :=
  704469419606451269814964662808002527143 / 340282366920938463463374607431768211456

/-- Dyadic lower bound for `exp wD` (Taylor sum, rounded down). -/
def bDnNegD1 : ℚ :=
  704469419606451346964200082651752200465 / 340282366920938463463374607431768211456

private def taylorTail (w : ℚ) (m : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (m + 1), w ^ k / k.factorial) +
    w ^ (m + 1) * (m + 2) / ((m + 1).factorial * (m + 1))

private def taylorHead (w : ℚ) (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), w ^ k / k.factorial

-- Exact-rational bridges: kernel-computed `Rat` arithmetic (the same
-- computations scripts/exp_crossover_cert.py performs).

private theorem tailBridgeXMax : taylorTail wX 40 ≤ bUpXMax := by
  simp only [taylorTail, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [wX, bUpXMax]

private theorem headBridgeXUp : bDnXUp ≤ taylorHead wU 40 := by
  simp only [taylorHead, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [wU, bDnXUp]

private theorem tailBridgeNegXMin : taylorTail wM 40 ≤ bUpNegXMin := by
  simp only [taylorTail, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [wM, bUpNegXMin]

private theorem headBridgeNegD1 : bDnNegD1 ≤ taylorHead wD 40 := by
  simp only [taylorHead, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [wD, bDnNegD1]

private theorem powBridgeXMax : bUpXMax ^ 1024 < thetaQ := by
  norm_num [bUpXMax, thetaQ]

private theorem powBridgeXUp : thetaQ < bDnXUp ^ 1024 := by
  norm_num [bDnXUp, thetaQ]

private theorem powBridgeNegXMin : bUpNegXMin ^ 1024 < (2 : ℚ) ^ 1075 := by
  norm_num [bUpNegXMin]

private theorem powBridgeNegD1 : (2 : ℚ) ^ 1075 < bDnNegD1 ^ 1024 := by
  norm_num [bDnNegD1]

-- Cast identities linking the `w` abbreviations to the anchors, and the
-- side conditions `0 ≤ w ≤ 1`.

private theorem wX_link : (xMaxR : ℚ) = 1024 * wX := by
  norm_num [xMaxR, wX]

private theorem wU_link : (xMaxUpR : ℚ) = 1024 * wU := by
  norm_num [xMaxUpR, wU]

private theorem wM_link : (-xMinR : ℚ) = 1024 * wM := by
  norm_num [xMinR, wM]

private theorem wD_link : (-xMinDownR : ℚ) = 1024 * wD := by
  norm_num [xMinDownR, wD]

private theorem wX_pos : 0 ≤ (wX : ℝ) := by exact_mod_cast (by norm_num [wX] : 0 ≤ wX)

private theorem wX_le1 : (wX : ℝ) ≤ 1 := by exact_mod_cast (by norm_num [wX] : wX ≤ 1)

private theorem wU_pos : 0 ≤ (wU : ℝ) := by exact_mod_cast (by norm_num [wU] : 0 ≤ wU)

private theorem wU_le1 : (wU : ℝ) ≤ 1 := by exact_mod_cast (by norm_num [wU] : wU ≤ 1)

private theorem wM_pos : 0 ≤ (wM : ℝ) := by exact_mod_cast (by norm_num [wM] : 0 ≤ wM)

private theorem wM_le1 : (wM : ℝ) ≤ 1 := by exact_mod_cast (by norm_num [wM] : wM ≤ 1)

private theorem wD_pos : 0 ≤ (wD : ℝ) := by exact_mod_cast (by norm_num [wD] : 0 ≤ wD)

private theorem wD_le1 : (wD : ℝ) ≤ 1 := by exact_mod_cast (by norm_num [wD] : wD ≤ 1)

private theorem bUpXMax_pos : (0 : ℝ) < (bUpXMax : ℝ) := by
  exact_mod_cast (by norm_num [bUpXMax] : (0 : ℚ) < bUpXMax)

private theorem bDnXUp_pos : (0 : ℝ) < (bDnXUp : ℝ) := by
  exact_mod_cast (by norm_num [bDnXUp] : (0 : ℚ) < bDnXUp)

private theorem bUpNegXMin_pos : (0 : ℝ) < (bUpNegXMin : ℝ) := by
  exact_mod_cast (by norm_num [bUpNegXMin] : (0 : ℚ) < bUpNegXMin)

private theorem bDnNegD1_pos : (0 : ℝ) < (bDnNegD1 : ℝ) := by
  exact_mod_cast (by norm_num [bDnNegD1] : (0 : ℚ) < bDnNegD1)

private theorem thetaT_pos : (0 : ℝ) < thetaT := by
  show (0 : ℝ) < (thetaQ : ℝ)
  exact_mod_cast (by norm_num [thetaQ] : (0 : ℚ) < thetaQ)

private theorem halfH_pos : (0 : ℝ) < halfH := by
  show (0 : ℝ) < (halfHQ : ℝ)
  exact_mod_cast (by norm_num [halfHQ] : (0 : ℚ) < halfHQ)

/-- `2^1075 > 0` in `ℝ`, as a named fact (used as an `inv_lt_inv₀` side
condition; `positivity` is not relied on for the cast power). -/
private theorem two1075_pos : (0 : ℝ) < ((2 : ℚ) ^ 1075 : ℝ) := by
  norm_cast

/-- The underflow literal as an inverse, so the `2^1075` comparisons go
through `inv_lt_inv₀`. -/
private theorem halfHQ_cast_inv : (halfHQ : ℝ) = ((2 : ℚ) ^ 1075 : ℝ)⁻¹ := by
  norm_cast
  norm_num [halfHQ]

/-! ### Transport from `ℝ` back to the dyadic literals -/

private theorem exp_le_bUpXMax : Real.exp (wX : ℝ) ≤ (bUpXMax : ℝ) := by
  have hc : (taylorTail wX 40 : ℝ) =
      (∑ k ∈ Finset.range 41, (wX : ℝ) ^ k / k.factorial) +
        (wX : ℝ) ^ 41 * (41 + 1) / ((41 : ℕ).factorial * 41) := by
    simp only [taylorTail]
    push_cast
    ring
  have h : Real.exp (wX : ℝ) ≤ (taylorTail wX 40 : ℝ) := by
    rw [hc]
    exact exp_le_taylor41_add_remainder wX_pos wX_le1
  exact h.trans (by exact_mod_cast tailBridgeXMax)

private theorem bDnXUp_le_exp : (bDnXUp : ℝ) ≤ Real.exp (wU : ℝ) := by
  have hc : (taylorHead wU 40 : ℝ) =
      (∑ k ∈ Finset.range 41, (wU : ℝ) ^ k / k.factorial) := by
    simp only [taylorHead]
    push_cast
    rfl
  have h : (taylorHead wU 40 : ℝ) ≤ Real.exp (wU : ℝ) := by
    rw [hc]
    exact taylor41_le_exp wU_pos
  exact ((by exact_mod_cast headBridgeXUp :
      (bDnXUp : ℝ) ≤ (taylorHead wU 40 : ℝ))).trans h

private theorem exp_le_bUpNegXMin : Real.exp (wM : ℝ) ≤ (bUpNegXMin : ℝ) := by
  have hc : (taylorTail wM 40 : ℝ) =
      (∑ k ∈ Finset.range 41, (wM : ℝ) ^ k / k.factorial) +
        (wM : ℝ) ^ 41 * (41 + 1) / ((41 : ℕ).factorial * 41) := by
    simp only [taylorTail]
    push_cast
    ring
  have h : Real.exp (wM : ℝ) ≤ (taylorTail wM 40 : ℝ) := by
    rw [hc]
    exact exp_le_taylor41_add_remainder wM_pos wM_le1
  exact h.trans (by exact_mod_cast tailBridgeNegXMin)

private theorem bDnNegD1_le_exp : (bDnNegD1 : ℝ) ≤ Real.exp (wD : ℝ) := by
  have hc : (taylorHead wD 40 : ℝ) =
      (∑ k ∈ Finset.range 41, (wD : ℝ) ^ k / k.factorial) := by
    simp only [taylorHead]
    push_cast
    rfl
  have h : (taylorHead wD 40 : ℝ) ≤ Real.exp (wD : ℝ) := by
    rw [hc]
    exact taylor41_le_exp wD_pos
  exact ((by exact_mod_cast headBridgeNegD1 :
      (bDnNegD1 : ℝ) ≤ (taylorHead wD 40 : ℝ))).trans h

/-! ### The four crossover comparisons -/

/-- `exp X_MAX` is strictly below the round-to-nearest overflow threshold:
round-to-nearest keeps it finite. -/
theorem exp_xMaxR_lt_theta : Real.exp (xMaxR : ℝ) < thetaT := by
  have hw : (xMaxR : ℝ) = ((1024 : ℕ) : ℝ) * (wX : ℝ) := by
    norm_cast
    exact wX_link
  have hp : Real.exp (xMaxR : ℝ) = Real.exp (wX : ℝ) ^ 1024 := by
    rw [hw, Real.exp_nat_mul]
  rw [hp]
  refine lt_of_le_of_lt (pow_le_pow_left₀ (Real.exp_nonneg _) exp_le_bUpXMax 1024) ?_
  show (bUpXMax : ℝ) ^ 1024 < (thetaQ : ℝ)
  exact_mod_cast powBridgeXMax

/-- `exp (nextUp X_MAX)` is strictly above the overflow threshold:
round-to-nearest overflows. -/
theorem thetaT_lt_exp_xMaxUpR : thetaT < Real.exp (xMaxUpR : ℝ) := by
  have hw : (xMaxUpR : ℝ) = ((1024 : ℕ) : ℝ) * (wU : ℝ) := by
    norm_cast
    exact wU_link
  have hp : Real.exp (xMaxUpR : ℝ) = Real.exp (wU : ℝ) ^ 1024 := by
    rw [hw, Real.exp_nat_mul]
  rw [hp]
  refine lt_of_lt_of_le ?_ (pow_le_pow_left₀
    (bDnXUp_pos.le) bDnXUp_le_exp 1024)
  show (thetaQ : ℝ) < (bDnXUp : ℝ) ^ 1024
  exact_mod_cast powBridgeXUp

/-- `exp X_MIN` is strictly above the underflow threshold `2^-1075`:
round-to-nearest keeps it (as the smallest subnormal). -/
theorem halfH_lt_exp_xMinR : halfH < Real.exp (xMinR : ℝ) := by
  have hv : ((-xMinR : ℚ) : ℝ) = ((1024 : ℕ) : ℝ) * (wM : ℝ) := by
    norm_cast
    exact wM_link
  have hE : Real.exp ((-xMinR : ℚ) : ℝ) = Real.exp (wM : ℝ) ^ 1024 := by
    rw [hv, Real.exp_nat_mul]
  have hle : Real.exp ((-xMinR : ℚ) : ℝ) ≤ (bUpNegXMin : ℝ) ^ 1024 := by
    rw [hE]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) exp_le_bUpNegXMin 1024
  have cn : ((-xMinR : ℚ) : ℝ) = -(xMinR : ℝ) := by
    push_cast
    rfl
  have h1 : Real.exp (xMinR : ℝ) = (Real.exp ((-xMinR : ℚ) : ℝ))⁻¹ := by
    rw [cn, Real.exp_neg]
    field_simp
  have h2 : ((bUpNegXMin : ℝ) ^ 1024)⁻¹ ≤ (Real.exp ((-xMinR : ℚ) : ℝ))⁻¹ :=
    (inv_le_inv₀ (pow_pos bUpNegXMin_pos 1024)
      (Real.exp_pos _)).mpr hle
  have h3 : halfH < ((bUpNegXMin : ℝ) ^ 1024)⁻¹ := by
    show (halfHQ : ℝ) < ((bUpNegXMin : ℝ) ^ 1024)⁻¹
    rw [halfHQ_cast_inv]
    refine (inv_lt_inv₀ two1075_pos (pow_pos bUpNegXMin_pos 1024)).mpr ?_
    show ((bUpNegXMin : ℝ) ^ 1024) < ((2 : ℚ) ^ 1075 : ℝ)
    exact_mod_cast powBridgeNegXMin
  rw [h1]
  exact lt_of_lt_of_le h3 h2

/-- `exp (nextDown X_MIN)` is strictly below the underflow threshold:
round-to-nearest gives zero. -/
theorem exp_xMinDownR_lt_halfH : Real.exp (xMinDownR : ℝ) < halfH := by
  have hv : ((-xMinDownR : ℚ) : ℝ) = ((1024 : ℕ) : ℝ) * (wD : ℝ) := by
    norm_cast
    exact wD_link
  have hE : Real.exp ((-xMinDownR : ℚ) : ℝ) = Real.exp (wD : ℝ) ^ 1024 := by
    rw [hv, Real.exp_nat_mul]
  have hge : (bDnNegD1 : ℝ) ^ 1024 ≤ Real.exp ((-xMinDownR : ℚ) : ℝ) := by
    rw [hE]
    exact pow_le_pow_left₀ (bDnNegD1_pos.le) bDnNegD1_le_exp 1024
  have cn : ((-xMinDownR : ℚ) : ℝ) = -(xMinDownR : ℝ) := by
    push_cast
    rfl
  have h1 : Real.exp (xMinDownR : ℝ) = (Real.exp ((-xMinDownR : ℚ) : ℝ))⁻¹ := by
    rw [cn, Real.exp_neg]
    field_simp
  have h2 : (Real.exp ((-xMinDownR : ℚ) : ℝ))⁻¹ ≤ ((bDnNegD1 : ℝ) ^ 1024)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) (pow_pos bDnNegD1_pos 1024)).mpr hge
  have h3 : ((bDnNegD1 : ℝ) ^ 1024)⁻¹ < halfH := by
    show ((bDnNegD1 : ℝ) ^ 1024)⁻¹ < (halfHQ : ℝ)
    rw [halfHQ_cast_inv]
    refine (inv_lt_inv₀ (pow_pos bDnNegD1_pos 1024) two1075_pos).mpr ?_
    show ((2 : ℚ) ^ 1075 : ℝ) < (bDnNegD1 : ℝ) ^ 1024
    exact_mod_cast powBridgeNegD1
  rw [h1]
  exact lt_of_le_of_lt h2 h3

/-! ### The 1-ulp crossover ladder -/

/-- `X_MAX < log θ`: the guard float itself is below the overflow point. -/
theorem xMax_lt_log_theta : (xMaxR : ℝ) < Real.log thetaT := by
  rw [Real.lt_log_iff_exp_lt thetaT_pos]
  exact exp_xMaxR_lt_theta

/-- `log θ < nextUp X_MAX`: the next float is above the overflow point. -/
theorem log_theta_lt_xMaxUp : Real.log thetaT < (xMaxUpR : ℝ) := by
  have h : Real.exp (Real.log thetaT) < Real.exp (xMaxUpR : ℝ) := by
    rw [Real.exp_log thetaT_pos]
    exact thetaT_lt_exp_xMaxUpR
  exact Real.exp_lt_exp.mp h

/-- `nextDown X_MIN < log H`: the previous float is below the underflow point. -/
theorem xMinDown_lt_log_halfH : (xMinDownR : ℝ) < Real.log halfH := by
  have h : Real.exp (xMinDownR : ℝ) < Real.exp (Real.log halfH) := by
    rw [Real.exp_log halfH_pos]
    exact exp_xMinDownR_lt_halfH
  exact Real.exp_lt_exp.mp h

/-- `log H < X_MIN`: the guard float itself is above the underflow point. -/
theorem log_halfH_lt_xMin : Real.log halfH < (xMinR : ℝ) := by
  have h : Real.exp (Real.log halfH) < Real.exp (xMinR : ℝ) := by
    rw [Real.exp_log halfH_pos]
    exact halfH_lt_exp_xMinR
  exact Real.exp_lt_exp.mp h

/-- The full 1-ulp crossover ladder at the two guard floats. -/
theorem crossoverLadder :
    (xMinDownR : ℝ) < Real.log halfH ∧
      Real.log halfH < (xMinR : ℝ) ∧
        (xMaxR : ℝ) < Real.log thetaT ∧
          Real.log thetaT < (xMaxUpR : ℝ) :=
  ⟨xMinDown_lt_log_halfH, log_halfH_lt_xMin, xMax_lt_log_theta,
    log_theta_lt_xMaxUp⟩

#print axioms Navier.FloatExpCrossover.exp_xMaxR_lt_theta
#print axioms Navier.FloatExpCrossover.thetaT_lt_exp_xMaxUpR
#print axioms Navier.FloatExpCrossover.halfH_lt_exp_xMinR
#print axioms Navier.FloatExpCrossover.exp_xMinDownR_lt_halfH
#print axioms Navier.FloatExpCrossover.crossoverLadder

end Navier.FloatExpCrossover
