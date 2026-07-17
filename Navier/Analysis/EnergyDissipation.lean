import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Integrated energy-dissipation identity for the projected (Galerkin) system

For the abstract projected Navier–Stokes system `u' = −ν A u + B u` on a real
inner-product space — `A` the (projected) Stokes operator, `B` the projected
nonlinearity with the skew property `⟨B u, u⟩ = 0` — pairing the equation with
`u` and integrating in time gives the **energy-dissipation identity**

  `‖u(T)‖² + 2ν ∫₀ᵀ ⟨A u(t), u(t)⟩ dt = ‖u(0)‖²`,

the exact finite-mode energy *equality* of the Galerkin construction
[Leray, Acta Math. 63 (1934), §§18–20; Temam, *Navier–Stokes Equations*,
Ch. III §3, eq. (3.29); Constantin–Foias, *NSE*, Ch. II].  Its `t ≥ 0`
half-line form consumes exactly the forward solutions produced by
`Navier.Analysis.LerayWeak.finiteDim_dissipative_ode_global`
(right-derivatives within `Set.Ici 0`), using the right-derivative fundamental
theorem of calculus (`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`,
which needs the derivative only on the open interior `Ioo 0 T`).

* `energy_dissipation_identity_forward` — the identity itself.
* `dissipation_integral_le_forward` — the `Set.Ioc`-integral corollary
  `∫_{(0,T]} ⟨A u, u⟩ ≤ ‖u(0)‖²/(2ν)`: with `A := A_m` the projected Stokes
  operator (`⟨A_m u, u⟩` = enstrophy of the finite-mode field) this is
  pointwise-in-`m` exactly the `UniformEnstrophyBound` field of
  `Navier.Analysis.LerayWeak.GalerkinApproximation`, with the uniform constant
  `C = ‖u₀‖²/(2ν)`.  This banks the dissipation-bound engine of
  `galerkin_approximation_exists`; only the finite-mode basis and the
  time-regularity/consistency bookkeeping remain there.

Sign conventions match `Navier.Analysis.LerayWeak.galerkin_apriori_bound`
(`u' = −(ν • A u) + B u`, `A` dissipative, `B` skew); the identity itself does
not need dissipativity of `A` — only the skewness of `B` — and the corollary
needs only `ν > 0` and `‖u(T)‖² ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open intervalIntegral MeasureTheory Set

namespace Navier.Analysis.EnergyDissipation

/-- **Integrated energy-dissipation identity (forward form).**  If `u` solves
the abstract projected system `u' = −(ν • A u) + B u` forward in time (as
right-derivatives within `Set.Ici 0`, the exact output shape of
`finiteDim_dissipative_ode_global`), with `B` skew along the trajectory and
`t ↦ ⟨A u(t), u(t)⟩` continuous on `[0, ∞)`, then for every `T ≥ 0`

  `‖u T‖² + 2ν ∫₀ᵀ ⟨A (u t), u t⟩ dt = ‖u 0‖²`.

Pairing the ODE with `u` kills the skew term, so `(‖u‖²)' = −2ν⟨A u, u⟩`; the
right-derivative FTC (`integral_eq_sub_of_hasDeriv_right_of_le`, derivative
needed only on `Ioo 0 T`) integrates this exactly.  [Leray 1934 §§18–20;
Temam III §3 eq. (3.29).] -/
theorem energy_dissipation_identity_forward
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ν : ℝ) (A B : E → E) (u u' : ℝ → E)
    (hu : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (u' t) (Set.Ici (0 : ℝ)) t)
    (hode : ∀ t : ℝ, 0 ≤ t → u' t = -(ν • A (u t)) + B (u t))
    (hB : ∀ t : ℝ, 0 ≤ t → inner ℝ (B (u t)) (u t) = 0)
    (hcont : ContinuousOn (fun t : ℝ => (inner ℝ (A (u t)) (u t) : ℝ)) (Set.Ici (0 : ℝ)))
    {T : ℝ} (hT : 0 ≤ T) :
    ‖u T‖ ^ 2 + 2 * ν * (∫ t in (0 : ℝ)..T, (inner ℝ (A (u t)) (u t) : ℝ)) = ‖u 0‖ ^ 2 := by
  -- the squared norm has right-derivative `−2ν⟨A u, u⟩` on the interior
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => ‖u s‖ ^ 2)
        (-(2 * ν) * (inner ℝ (A (u x)) (u x) : ℝ)) (Set.Ioi x) x := by
    intro x hx
    have hd : HasDerivWithinAt u (u' x) (Set.Ioi x) x :=
      (hu x hx.1.le).mono (fun y hy => le_trans hx.1.le (le_of_lt hy))
    have h := hd.inner ℝ hd
    have hrw : (fun s => ‖u s‖ ^ 2) = (fun s => (inner ℝ (u s) (u s) : ℝ)) := by
      funext s; rw [real_inner_self_eq_norm_sq]
    have heq : (inner ℝ (u x) (u' x) : ℝ) + inner ℝ (u' x) (u x)
        = -(2 * ν) * inner ℝ (A (u x)) (u x) := by
      rw [real_inner_comm (u' x) (u x), hode x hx.1.le, inner_add_left, inner_neg_left,
        inner_smul_left, hB x hx.1.le]
      simp only [conj_trivial, add_zero]
      ring
    rw [hrw, ← heq]
    exact h
  -- `‖u‖²` is continuous on `[0, T]` (from the within-derivatives)
  have hcontOn : ContinuousOn (fun s => ‖u s‖ ^ 2) (Set.Icc (0 : ℝ) T) := by
    intro s hs
    exact ((((hu s hs.1).continuousWithinAt).mono Set.Icc_subset_Ici_self).norm).pow 2
  -- the dissipation density is interval-integrable
  have hint : IntervalIntegrable
      (fun t => -(2 * ν) * (inner ℝ (A (u t)) (u t) : ℝ)) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact continuousOn_const.mul (hcont.mono Set.Icc_subset_Ici_self)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hcontOn hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  linarith [hftc]

/-- **Uniform dissipation-integral bound (`UniformEnstrophyBound` shape).**  For
`ν > 0`, a forward solution of the projected system has

  `∫_{(0,T]} ⟨A (u t), u t⟩ dt ≤ ‖u 0‖² / (2ν)`  for every `T ≥ 0`.

This is the energy-dissipation identity plus `‖u T‖² ≥ 0`, in the
`Set.Ioc`-integral form that the `enstrophy_bounded` field of
`GalerkinApproximation` consumes: with `A := A_m` the projected Stokes operator
(`⟨A_m u, u⟩` = enstrophy of the finite-mode field) and
`‖u_m(0)‖ ≤ ‖u₀‖_{L²}` (Galerkin projection contraction), the constant
`C = ‖u₀‖²_{L²}/(2ν)` is uniform in `m`.  [Temam III §3; Leray 1934 §20.] -/
theorem dissipation_integral_le_forward
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ν : ℝ} (hν : 0 < ν) (A B : E → E) (u u' : ℝ → E)
    (hu : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (u' t) (Set.Ici (0 : ℝ)) t)
    (hode : ∀ t : ℝ, 0 ≤ t → u' t = -(ν • A (u t)) + B (u t))
    (hB : ∀ t : ℝ, 0 ≤ t → inner ℝ (B (u t)) (u t) = 0)
    (hcont : ContinuousOn (fun t : ℝ => (inner ℝ (A (u t)) (u t) : ℝ)) (Set.Ici (0 : ℝ)))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Set.Ioc (0 : ℝ) T, (inner ℝ (A (u t)) (u t) : ℝ)) ≤ ‖u 0‖ ^ 2 / (2 * ν) := by
  have hid := energy_dissipation_identity_forward ν A B u u' hu hode hB hcont hT
  rw [intervalIntegral.integral_of_le hT] at hid
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ν)]
  nlinarith [hid, sq_nonneg ‖u T‖]

end Navier.Analysis.EnergyDissipation
