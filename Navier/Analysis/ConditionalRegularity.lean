import Navier.Analysis.BealeKatoMajda
import Navier.Scaling

/-!
# Conditional regularity bridges: Prodi–Serrin and Constantin–Fefferman

Two classical conditional-regularity criteria for the repository's partial
classical solutions, stated as skeletons with hypothesis-carried norms
(Step-0e: explicit integrability keeps the Bochner integrals honest; the
conclusion is the same continuation surrogate as the BKM layer — a uniform
velocity bound on `[0,T)`, which `PointEvaluationBreakdownWitness` machinery
turns into "no pointwise blow-up").

Per the ladder (rung 5, R3 class, ≤1 conditional bridge per headline), these
do not advance the headline; they delimit the conditional-regularity surface
honestly.

## Skeletons

* `prodiSerrin_velocity_bounded` — the Ladyzhenskaya–Prodi–Serrin continuation
  criterion: a critical mixed-norm bound `u ∈ L^q_t L^p_x`, `2/q + 3/p = 1`,
  `p > 3`, forces a uniform velocity bound
  [Prodi, Ann. Mat. Pura Appl. 48 (1959); Serrin, ARMA 9 (1962);
  Escauriaza–Serëgin–Šverák (2003) for the `p = 3` endpoint; est ~800 LOC].
* `constantinFefferman_velocity_bounded` — the vorticity-direction coherence
  criterion: if the direction of the vorticity is `ρ`-coherent (division-free
  form: `|ω(x) ⨯ ω(y)| ≤ (|x−y|/ρ)·|ω(x)||ω(y)|`) wherever the vorticity is
  large, a finite-energy classical solution stays bounded
  [Constantin–Fefferman, Indiana Univ. Math. J. 42 (1993) 775–789;
  est ~600 LOC].
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace Navier.Analysis.ConditionalRegularity

open scoped Matrix

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Breakdown

/-- **[SKELETON — Ladyzhenskaya–Prodi–Serrin; Prodi 1959, Serrin 1962, ESŠ
2003; est ~800 LOC.]**  A partial classical solution on `[0,T)` whose velocity
carries a finite critical mixed norm — `∫₀^{T'} (∫ |u|^p)^{q/p} ≤ M` uniformly
in `T' < T`, with `(p,q)` on the Serrin critical line `2/q + 3/p = 1` and
`p > 3` — is uniformly bounded on `[0,T)`.  The spatial integrability of
`|u|^p` per time slice is hypothesis-carried so the mixed norm is a genuine
integral, not the Bochner junk value.

Closure route: local smoothing of the mild formulation + the critical-norm
bootstrap (De Giorgi/Moser or the ESŠ backward-uniqueness route at the
endpoint); Mathlib-absent: parabolic regularity theory. -/
theorem prodiSerrin_velocity_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (p q : ℝ) (hp : 3 < p) (hcrit : Navier.Scaling.CriticalLine p q)
    (hint : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ p))
    (M : ℝ)
    (hM : ∀ T' : ℝ, 0 ≤ T' → T' < T →
      (∫ s in (0:ℝ)..T',
        (∫ x : Space, ‖sol.velocity s x‖ ^ p) ^ (q / p)) ≤ M) :
    ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Space,
      ‖sol.velocity t x‖ ≤ R := by
  sorry

/-- **[SKELETON — Constantin–Fefferman direction coherence; Indiana Univ.
Math. J. 42 (1993) 775–789; est ~600 LOC.]**  A finite-energy partial
classical solution whose vorticity direction is `ρ`-coherent in the
high-vorticity region — in the division-free cross-product form
`|ω(x) ⨯ ω(y)| ≤ (|x−y|/ρ)·|ω(x)|·|ω(y)|` whenever both vorticities exceed
`Ω₀` — is uniformly bounded on `[0,T)`.  (`|sin θ(ω(x), ω(y))| ≤ |x−y|/ρ` in
Constantin–Fefferman's notation; the cross product bilinearizes the sine.)

Closure route: the stretching term in the enstrophy budget
(`Navier.Analysis.Enstrophy`) is geometrically depleted by direction
coherence — the singular-integral kernel of `(ω·∇)u` against aligned
vorticity gains a factor of `sin θ`; Mathlib-absent: the Biot–Savart singular
integral, as in the BKM tower. -/
theorem constantinFefferman_velocity_bounded
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    (E : ℝ)
    (henergy : ∀ t : ℝ, 0 ≤ t → t < T →
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 2) ∧
        kineticEnergy sol.velocity t ≤ E)
    (ρ Ω₀ : ℝ) (hρ : 0 < ρ) (hΩ₀ : 0 < Ω₀)
    (hcoh : ∀ t : ℝ, 0 ≤ t → t < T → ∀ x y : Space,
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t x) →
      Ω₀ ≤ officialEuclideanNorm (vorticity sol.velocity t y) →
      officialEuclideanNorm
          (vorticity sol.velocity t x ⨯₃ vorticity sol.velocity t y) ≤
        (officialEuclideanNorm (fun i => x i - y i) / ρ) *
          (officialEuclideanNorm (vorticity sol.velocity t x) *
            officialEuclideanNorm (vorticity sol.velocity t y))) :
    ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Space,
      ‖sol.velocity t x‖ ≤ R := by
  sorry

end Navier.Analysis.ConditionalRegularity
