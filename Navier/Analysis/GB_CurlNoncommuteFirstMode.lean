/-
Original work, lane W31-NCS2-0929 (2026-09-29).

# The `m = 1` escape hatch closes: explicit-witness curl noncommutation (F-029 follow-on)

`Analysis.GB_CurlEigenfieldObstruction` (ledger F-029, registry row NAVIER-01)
refutes the route hypothesis `∀ m u, curl (P_m u) = P_m (curl u)` for every
`GalerkinBasisFamily`.  A `¬ ∀ m u` refutation leaves one escape open in
principle: commutation could still hold at a single fixed index, and the
downstream consumers `curl_proj_sq_le_of_commutes` / `curl_proj_converges_of_commutes`
would recover their hypothesis if any `P_m` committed.  This file closes that
hatch at the lowest index and sharpens the obstruction from a bare
`¬ ∀` to a **constructed witness**:

* `curl_proj_ne_proj_curl_of_coeff_ne_zero` — for EVERY field `u` with a
  nonzero first-mode coefficient, `curl (P₁ u) ≠ P₁ (curl u)`.  The failure
  set of first-mode commutation contains the complement of the hyperplane
  `⟪u, w₀⟫ = 0`; the obstruction is not an isolated counterexample but an
  open dense condition on the input.
* `curl_proj_not_commute_first_mode` — the kernel `∃`-refutation: the first
  mode `w₀` itself is an explicit witness field.  (`not_forall_curl_commutes`
  is nonconstructive in `m` and `u`; this supplies the data.)
* `not_forall_curl_commutes_at_first_mode` — `¬ ∀ u, curl (P₁ u) = P₁ (curl u)`:
  the commutation hypothesis is dead already at `m = 1`, per family.

The proof is the rank-one algebra `P₁ u = ⟪u, w₀⟫ • w₀` (`proj_one`), divided
by the nonzero coefficient, which turns any commuting `u` into an eigenfield
relation for `w₀`; `first_mode_not_curl_eigenfield` (F-029) refutes every
real eigenvalue, and `‖w₀‖ = 1` (`orthonormal 0 0`, i.e. `coeff_first_mode_one`)
supplies the nonvanishing that makes the division legal.

Downstream status unchanged and honest: the structural `GraphDense ∧ CurlStable`
ordering (`exists_hCurlStableGalerkinBasisFamily`) remains the only live route
for `curl_proj_converges`; no commutation hypothesis of ANY fixed index,
including `m = 1`, can be supplied by any Galerkin basis.
-/
import Navier.Analysis.GalerkinBasis
import Navier.Analysis.GB_CurlEigenfieldObstruction

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.GalerkinBasis

open Navier Navier.Analysis.DivFreeGradientEnstrophy

/-- The first-mode projection is rank one: `P₁ u = ⟪u, w₀⟫ • w₀`. -/
theorem proj_one (W : GalerkinBasisFamily) (u : SchwartzVelocity) :
    W.proj 1 u = W.coeff u 0 • W.w 0 := by
  unfold GalerkinBasisFamily.proj
  rw [Finset.sum_range_one]

/-- The first mode is `L²`-unit: `⟪w₀, w₀⟫ = 1`, so its coefficient functional
does not vanish on it. -/
theorem coeff_first_mode_one (W : GalerkinBasisFamily) : W.coeff (W.w 0) 0 = 1 := by
  unfold GalerkinBasisFamily.coeff
  simpa using W.orthonormal 0 0

/-- **Every field with a nonzero first-mode coefficient fails to commute with
`P₁` under `curl`.**  If `curl (P₁ u) = P₁ (curl u)` held with `⟪u, w₀⟫ ≠ 0`,
dividing the rank-one identity by `⟪u, w₀⟫` would exhibit `w₀` as a `curl`
eigenfield with real eigenvalue `⟪curl u, w₀⟫ · ⟪u, w₀⟫⁻¹` — excluded by
`first_mode_not_curl_eigenfield` (F-029). -/
theorem curl_proj_ne_proj_curl_of_coeff_ne_zero (W : GalerkinBasisFamily)
    (u : SchwartzVelocity) (hu : W.coeff u 0 ≠ 0) :
    curlSchwartzCLM (W.proj 1 u) ≠ W.proj 1 (curlSchwartzCLM u) := by
  intro h
  rw [proj_one W u, proj_one W (curlSchwartzCLM u),
    ContinuousLinearMap.map_smul] at h
  have h2 : curlSchwartzCLM (W.w 0) =
      ((W.coeff u 0)⁻¹ * W.coeff (curlSchwartzCLM u) 0) • W.w 0 := by
    have := congrArg (fun t : SchwartzVelocity => (W.coeff u 0)⁻¹ • t) h
    rwa [inv_smul_smul₀ hu, smul_smul] at this
  exact first_mode_not_curl_eigenfield W _ h2

/-- **The constructed `∃`-witness (kernel refutation with data).**  The first
mode `w₀` itself is a concrete field on which curl fails to commute with `P₁`:
`curl (P₁ w₀) ≠ P₁ (curl w₀)`.  This upgrades `not_forall_curl_commutes`
(F-029), which supplies neither an index-`1` failure nor a witness field. -/
theorem curl_proj_not_commute_first_mode (W : GalerkinBasisFamily) :
    ∃ u : SchwartzVelocity,
      curlSchwartzCLM (W.proj 1 u) ≠ W.proj 1 (curlSchwartzCLM u) :=
  ⟨W.w 0, curl_proj_ne_proj_curl_of_coeff_ne_zero W (W.w 0)
    (by rw [coeff_first_mode_one]; norm_num)⟩

/-- **The `m = 1` escape hatch closes.**  No Galerkin basis has curl commuting
with `P₁` on every field: `¬ ∀ u, curl (P₁ u) = P₁ (curl u)`.  The commutation
hypothesis of `curl_proj_sq_le_of_commutes` / `curl_proj_converges_of_commutes`
cannot be recovered by restricting to the first projection. -/
theorem not_forall_curl_commutes_at_first_mode (W : GalerkinBasisFamily) :
    ¬ ∀ u : SchwartzVelocity,
      curlSchwartzCLM (W.proj 1 u) = W.proj 1 (curlSchwartzCLM u) := by
  intro h
  obtain ⟨u, hu⟩ := curl_proj_not_commute_first_mode W
  exact hu (h u)

-- Registry footer: axiom probes are run externally via proof-loop.py.

end Navier.Analysis.GalerkinBasis
