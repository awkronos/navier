import Navier.Analysis.Vorticity

/-!
# The weighted-transport commutator `[xᵅ, u·∇]`

`sliceSeminorm_locallyBounded` (`Navier/Analysis/BKMLogBootstrap.lean`) is now
derived, with no unproved step, from `WeightedEnergyAffineControl` via the
certified affine Grönwall leaf (`Navier/Analysis/GronwallAffine.lean`).  The
honest residual moved down to `weightedEnergyAffineControl_of_navierStokes`,
which carries exactly three things: the polynomially weighted `L²` energy
identity, **its commutator estimate**, and the Calderón–Zygmund pressure bound.

This file certifies the commutator, kernel-clean.  The weighted energy method
for `‖xᵅ D^β u‖_{L²}` tests the transport equation against `xᵅ D^β u`, and the
convective term is only usable after the weight is moved through `u·∇`.  That
move is an *algebraic* identity — no analysis, no smallness, no
divergence-freeness:

  `[x_j, u·∇] f = − u_j · f`,   `[(x_j)^k, u·∇] f = − k (x_j)^{k−1} u_j · f`.

The commutator is therefore **order zero**: it costs no derivative of `f`, one
power of the weight, and one power of `u` — which is exactly why the weighted
energy inequality closes as an *affine* Grönwall inequality `Y' ≤ aY + b`
rather than a quasilinear one, and so why `GronwallAffine` is the right leaf.

Everything here is kernel-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Navier.Analysis.WeightedCommutator

open Navier
open Navier.Analysis.Vorticity
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The convective (material) derivative `u·∇f` of a field `f` along `u`,
written as the derivative of `f` in the direction `u x`. -/
noncomputable def convectiveDeriv (u : VelocityField) (f : Space → E) (x : Space) : E :=
  fderiv ℝ f x (u x)

/-- The `j`-th coordinate functional on `Space`, as a continuous linear map. -/
noncomputable def coordCLM (j : Fin 3) : Space →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j)

@[simp] theorem coordCLM_apply (j : Fin 3) (x : Space) : coordCLM j x = x j := rfl

/-- **The one-coordinate commutator (certified).**  Moving a single coordinate
weight `x_j` through the convective derivative costs exactly the `j`-th
component of the velocity, with no derivative of `f`:

  `u·∇ (x_j · f) = x_j · (u·∇ f) + u_j · f`,  i.e. `[x_j, u·∇] f = − u_j f`. -/
theorem convectiveDeriv_coord_smul (u : VelocityField) (f : Space → E) (j : Fin 3)
    {x : Space} (hf : DifferentiableAt ℝ f x) :
    convectiveDeriv u (fun y => (y j) • f y) x
      = (x j) • convectiveDeriv u f x + (u x j) • f x := by
  have hc : HasFDerivAt (fun y : Space => (coordCLM j) y) (coordCLM j) x :=
    (coordCLM j).hasFDerivAt
  have hd : HasFDerivAt (fun y : Space => (y j) • f y)
      ((x j) • (fderiv ℝ f x) + (coordCLM j).smulRight (f x)) x :=
    hc.smul hf.hasFDerivAt
  simp [convectiveDeriv, hd.fderiv, add_comm]

/-- **The power-weight commutator (certified).**  For the weight `(x_j)^k`,

  `u·∇ ((x_j)^k · f) = (x_j)^k · (u·∇ f) + k · (x_j)^{k−1} · u_j · f`,

so `[(x_j)^k, u·∇] f = − k (x_j)^{k−1} u_j f`.  The commutator is again of
order zero in `f`: it trades one power of the weight for one power of `u`.
This is the term that supplies the *additive* forcing `b` in the affine
Grönwall inequality `Y' ≤ aY + b` of `Navier.Analysis.GronwallAffine`. -/
theorem convectiveDeriv_coord_pow_smul (u : VelocityField) (f : Space → E) (j : Fin 3)
    (k : ℕ) {x : Space} (hf : DifferentiableAt ℝ f x) :
    convectiveDeriv u (fun y => ((y j) ^ k) • f y) x
      = ((x j) ^ k) • convectiveDeriv u f x
        + ((k : ℝ) * (x j) ^ (k - 1) * (u x j)) • f x := by
  induction k with
  | zero => simp [convectiveDeriv]
  | succ k ih =>
      have hdiff : DifferentiableAt ℝ (fun y : Space => ((y j) ^ k) • f y) x :=
        (((coordCLM j).differentiableAt).pow k).smul hf
      have hstep := convectiveDeriv_coord_smul u (fun y => ((y j) ^ k) • f y) j hdiff
      have hfun : (fun y : Space => (y j) • (((y j) ^ k) • f y))
          = fun y : Space => ((y j) ^ (k + 1)) • f y := by
        funext y
        rw [smul_smul]
        congr 1
        ring
      rw [hfun] at hstep
      rw [hstep, ih]
      cases k with
      | zero => simp
      | succ m =>
          simp only [Nat.add_sub_cancel]
          push_cast
          module

end Navier.Analysis.WeightedCommutator
