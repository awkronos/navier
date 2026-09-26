import Navier.Problem
import Navier.Analysis.VectorCalculus
import Navier.Analysis.CurlIdentities
import Navier.Analysis.MadelungDecoderCurlObstruction

/-!
# The Hopf–Cole bridge: complex-phase limit of the Madelung transform

Fleet NSQM-0926 lane M-C.  The Hopf–Cole transform had ZERO formalization in
this repository (`grep -rn "Hopf|Cole"` over `*.lean` hits only Leray–Hopf
weak solutions); the prose claim "Hopf–Cole is 1D exact" is kernelized here at
whatever dimension the algebra supports:

1. `colehopf_burgers_of_logheat` — for a `C^∞` log-amplitude `W` on spacetime
   `ℝ × (ι → ℝ)` (arbitrary dimension `ι`) satisfying the logarithmic heat
   equation `∂t W = ν(ΔW + ‖∇W‖²)` — which is the heat equation for
   `θ = e^W > 0` written in the log variable — the field `u := -2ν ∇W`
   satisfies the vector Burgers system `∂t uᵢ + Σⱼ uⱼ ∂ⱼuᵢ = ν Δuᵢ` at every
   spacetime point, in componentwise Fréchet form.  The proof is pointwise
   Fréchet algebra; no PDE analysis beyond the heat hypothesis.
2. `colehopf_jacobian_symmetric` / `colehopf_staticCurl_zero` /
   `colehopf_stretching_zero` — the Cole–Hopf velocity is irrotational by
   construction: symmetric spatial Jacobian, hence zero curl, zero vorticity
   and zero vortex stretching `(ω·∇)u`.  This is the SAME wall as the scalar
   Madelung decoder (`Navier/Analysis/MadelungDecoderCurlObstruction.lean`:
   `madelung_decoder_mixed_partial_comm` — cited, not edited).
3. `complexPhase_logDeriv` and its two readers — the complex-phase Madelung
   ansatz `ψ = exp((iS - Γ)/ħ)` has logarithmic derivative
   `(Dψ·v)/ψ = (i D S·v - DΓ·v)/ħ` exactly; the repo's Madelung decoder law
   (`MadelungInitialDecoder`) reads the IMAGINARY part and gets `∝ ∇S`
   (Bridge 1 read below), while the Cole–Hopf velocity of the strictly
   positive amplitude `θ = e^{-Γ/ħ}` reads the REAL part
   (`complexPhase_colehopf_eq_negRe`).  Bridges 1 and 3 are the two halves of
   one checked identity; positivity here is `Real.exp_pos`, no hypothesis.
4. `no_colehopf_of_plane_rotation` — the gradient carrier cannot represent
   rotational data: in dimension 2 the plane-rotation field
   `(x₀,x₁) ↦ (-x₁, x₀)` admits no Cole–Hopf representation, because its
   Jacobian is antisymmetric where Cole–Hopf Jacobians are symmetric
   (`1 = -1`).  The same proof works in every dimension ≥ 2.

Honesty notes:
* The interchange facts are kernelized from Mathlib's `IsSymmSndFDerivAt`
  (`ContDiffAt.isSymmSndFDerivAt`), applied pointwise and composed — NOT from
  a general iterated-FD permutation theorem, which Mathlib does not have
  (measured gap 2026-09-26).  The two adjacent-swap generators
  `swap3_inner` / `swap3_outer` are proved here once, in arbitrary dimension,
  and generate the third-order symmetry the Burgers assembly consumes.
* The heat hypothesis is taken in the log variable `W`.  The converse
  direction — a positive heat solution `θ` transported to `W = log θ` via the
  chain-rule expansion `Δ logθ = Δθ/θ − ‖∇θ‖²/θ²` — is discharged in §5
  (`colehopf_logheat_of_pos_heat`), together with an `ε`-exhaustion
  (`colehopf_burgers_of_heat_eps`) showing global positivity is NOT needed to
  run Cole–Hopf: `θ ≥ 0` and positivity at a single point suffice for the
  pointwise limit `−2ν∇θ/θ` (`colehopf_eps_tendsto_formal`).  §6 bridges the
  abstract spacetime `ι` formulation to the concrete dim-3 `coleHopfSlice`
  carrier through the slice embedding (`coleHopfU_eq_coleHopfSlice`) and
  restates vorticity vanishing through the bridge
  (`coleHopfU_vorticity_zero`).  The equivalence is two-sided:
  `colehopf_heat_of_pos_logheat` exponentiates any log-heat field to a
  strictly positive heat solution, and `coordAmp` (with
  `colehopf_positivity_sharp`) exhibits a smooth global heat solution — a
  spatial coordinate — that admits NO log transport at all, so blanket
  positivity is exactly the obstruction, not a convenience.
* All vocabulary is repo-native or local to this file: `amplitude_is_heat`
  is a local binder name for the log-heat hypothesis, and every cited
  declaration lives in the four imported navier modules above
  (`MadelungInitialDecoder` in MadelungDecoderCurlObstruction, curl carriers
  in CurlIdentities).  This file imports nothing outside navier and carries no
  cross-repository citation (root correction 2026-09-26: a phantom peer frame
  attributed a "ComplexProgenitor" relay to the fleet lead; unverifiable and
  removed).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators ContDiff
open Navier Filter Set Metric Function

/-! ## 1. The Schwarz swaps, arbitrary dimension, from `IsSymmSndFDerivAt` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `swap2'` — mixed partials commute, Fréchet component form, arbitrary
normed space `E`, at `x`, for `C^∞` `f : E → ℝ`. -/
theorem swap2' {f : E → ℝ} (hf : ContDiff ℝ ⊤ f) (x : E) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  have hf2 : ContDiffAt ℝ 2 f x := (hf.contDiffAt).of_le (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    hf2.isSymmSndFDerivAt (by simp [minSmoothness])
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have h2 : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hf2.fderiv_right le_rfl
    exact h2.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hEval : ∀ (a b : E),
      fderiv ℝ (fun y => fderiv ℝ f y b) x a = (fderiv ℝ (fderiv ℝ f) x a) b := by
    intro a b
    let T : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ b
    have hT : HasFDerivAt (fun L : E →L[ℝ] ℝ => L b) T (fderiv ℝ f x) :=
      T.hasFDerivAt
    have hcomp := (hT.comp x hdiff.hasFDerivAt).fderiv
    rw [show (fun y => fderiv ℝ f y b) = (fun L => L b) ∘ (fderiv ℝ f) from rfl, hcomp]
    rfl
  rw [hEval, hEval]
  exact hsymm _ _

/-- First Fréchet partials of a smooth function along a fixed direction are
smooth. -/
theorem contDiff_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ ⊤ f) (v : E) :
    ContDiff ℝ ⊤ (fun x => fderiv ℝ f x v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp (hf.fderiv_right le_top)

/-- **`swap3_inner`** — transpose the two innermost derivations of a third
Fréchet derivative: `∂c(∂b ∂a f) = ∂c(∂a ∂b f)`. -/
theorem swap3_inner {f : E → ℝ} (hf : ContDiff ℝ ⊤ f) (x a b c : E) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => fderiv ℝ f y a) q b) x c =
      fderiv ℝ (fun q => fderiv ℝ (fun y => fderiv ℝ f y b) q a) x c :=
  congrArg (fun H : E → ℝ => fderiv ℝ H x c)
    (funext fun q => swap2' hf q a b)

/-- **`swap3_outer`** — transpose the two outermost derivations of a third
Fréchet derivative: `∂c(∂b ∂a f) = ∂b(∂c ∂a f)`. -/
theorem swap3_outer {f : E → ℝ} (hf : ContDiff ℝ ⊤ f) (x a b c : E) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => fderiv ℝ f y a) q b) x c =
      fderiv ℝ (fun q => fderiv ℝ (fun y => fderiv ℝ f y a) q c) x b :=
  swap2' (contDiff_fderiv_apply hf a) x b c

/-! ## 2. Hopf–Cole exactness: log-heat ⇒ vector Burgers, arbitrary dimension -/

/-- Spacetime in dimension `#ι`: time `ℝ` times space `ι → ℝ`. -/
abbrev Spacetime (ι : Type*) := ℝ × (ι → ℝ)

/-- The unit time direction. -/
def dirT (ι : Type*) : Spacetime ι := (1, 0)

/-- The `i`-th unit spatial direction. -/
def dirS (ι : Type*) [DecidableEq ι] (i : ι) : Spacetime ι :=
  (0, fun k => if k = i then (1 : ℝ) else 0)

/-- Spatial Laplacian, Fréchet component form. -/
def heatLap (ι : Type*) [Fintype ι] [DecidableEq ι] (W : Spacetime ι → ℝ)
    (p : Spacetime ι) : ℝ :=
  ∑ i : ι, fderiv ℝ (fun q => fderiv ℝ W q (dirS ι i)) p (dirS ι i)

/-- Squared spatial gradient. -/
def heatGsq (ι : Type*) [Fintype ι] [DecidableEq ι] (W : Spacetime ι → ℝ)
    (p : Spacetime ι) : ℝ :=
  ∑ i : ι, (fderiv ℝ W p (dirS ι i)) ^ 2

/-- The Cole–Hopf velocity field `u = -2ν ∇W` of a log-amplitude `W`. -/
def coleHopfU (ι : Type*) [DecidableEq ι] (ν : ℝ) (W : Spacetime ι → ℝ)
    (p : Spacetime ι) : ι → ℝ :=
  fun i => (-2 * ν) • fderiv ℝ W p (dirS ι i)

/-- **Hopf–Cole exactness (arbitrary dimension).**  If the smooth
log-amplitude `W` satisfies `∂t W = ν(ΔW + ‖∇W‖²)` — the heat equation for
`θ = e^W` in the log variable — then `u = -2ν∇W` satisfies the vector Burgers
system pointwise in componentwise Fréchet form.  The proof is the swap-cancel
assembly: the time derivative of a component (hT1) is `-2ν²(S₁ + 2S₂)`, the
convective term (hT2) `4ν²S₂`, and the diffusion term (hT3) `-2ν·(-2νS₁)`, so
the three cancel by `ring`.  Here S₁ is the double-gradient sum `heatLap` of
the i-th component in the summed direction and S₂ the matched product sum. -/
theorem colehopf_burgers_of_logheat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : ℝ) (W : Spacetime ι → ℝ) (hW : ContDiff ℝ ⊤ W)
    (amplitude_is_heat : ∀ p,
      fderiv ℝ W p (dirT ι) = ν * (heatLap ι W p + heatGsq ι W p)) :
    ∀ (p : Spacetime ι) (i : ι),
      fderiv ℝ (coleHopfU ι ν W · i) p (dirT ι)
        + ∑ j : ι, coleHopfU ι ν W p j * fderiv ℝ (coleHopfU ι ν W · i) p (dirS ι j)
        - ν * ∑ j : ι,
            fderiv ℝ (fun q => fderiv ℝ (coleHopfU ι ν W · i) q (dirS ι j)) p (dirS ι j) = 0 := by
  intro p i
  -- Derivative of a Cole–Hopf component at any base point, in any direction.
  have key (r : Spacetime ι) (k : ι) (v : Spacetime ι) :
      fderiv ℝ (fun q => coleHopfU ι ν W q k) r v
        = (-2 * ν) • fderiv ℝ (fun q => fderiv ℝ W q (dirS ι k)) r v := by
    have hk : DifferentiableAt ℝ (fun q : Spacetime ι => fderiv ℝ W q (dirS ι k)) r :=
      Differentiable.differentiableAt
        (ContDiff.differentiable (contDiff_fderiv_apply hW (dirS ι k)) (by simp))
    show fderiv ℝ ((-2 * ν) • (fun q : Spacetime ι => fderiv ℝ W q (dirS ι k))) r v = _
    rw [fderiv_const_smul hk (-2 * ν), ContinuousLinearMap.smul_apply]
  have hfun : (fun q : Spacetime ι => fderiv ℝ W q (dirT ι))
      = (fun q => ν * (heatLap ι W q + heatGsq ι W q)) := funext amplitude_is_heat
  have hslap : ContDiff ℝ ⊤ (fun q : Spacetime ι => heatLap ι W q) := by
    show ContDiff ℝ ⊤ (fun q =>
      ∑ i : ι, fderiv ℝ (fun q' => fderiv ℝ W q' (dirS ι i)) q (dirS ι i))
    refine ContDiff.sum fun j _ => ?_
    exact contDiff_fderiv_apply (contDiff_fderiv_apply hW (dirS ι j)) (dirS ι j)
  have hsq : ContDiff ℝ ⊤ (fun q : Spacetime ι => heatGsq ι W q) := by
    show ContDiff ℝ ⊤ (fun q => ∑ i : ι, (fderiv ℝ W q (dirS ι i)) ^ 2)
    refine ContDiff.sum fun j _ => ?_
    exact ContDiff.pow (contDiff_fderiv_apply hW (dirS ι j)) 2
  -- Time derivative of the i-th component: swap, transport the log-heat law, expand.
  have hT1 : fderiv ℝ (fun q => coleHopfU ι ν W q i) p (dirT ι)
      = (-2 * ν) • ν •
          (∑ j : ι, fderiv ℝ (fun q => fderiv ℝ (fun y => fderiv ℝ W y (dirS ι i)) q (dirS ι j))
              p (dirS ι j)
            + 2 * ∑ j : ι, fderiv ℝ W p (dirS ι j)
                * fderiv ℝ (fun q => fderiv ℝ W q (dirS ι i)) p (dirS ι j)) := by
    have hAeq : fderiv ℝ (fun q : Spacetime ι => heatLap ι W q) p (dirS ι i)
        = ∑ j : ι, fderiv ℝ (fun q => fderiv ℝ (fun y => fderiv ℝ W y (dirS ι i)) q (dirS ι j))
            p (dirS ι j) := by
      have hlapSum : (fun q : Spacetime ι => heatLap ι W q)
          = ∑ j : ι, (fun q : Spacetime ι =>
              fderiv ℝ (fun q' : Spacetime ι => fderiv ℝ W q' (dirS ι j)) q (dirS ι j)) :=
        funext fun q => by show heatLap ι W q = _; rw [Finset.sum_apply]; rfl
      rw [hlapSum]
      rw [fderiv_sum (fun j _ => Differentiable.differentiableAt
          (ContDiff.differentiable
            (contDiff_fderiv_apply (contDiff_fderiv_apply hW (dirS ι j)) (dirS ι j))
            (by simp)))]
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [swap3_outer hW p (dirS ι j) (dirS ι j) (dirS ι i),
        swap3_inner hW p (dirS ι j) (dirS ι i) (dirS ι j)]
    have hjd (j : ι) : DifferentiableAt ℝ (fun q : Spacetime ι => fderiv ℝ W q (dirS ι j)) p :=
      Differentiable.differentiableAt
        (ContDiff.differentiable (contDiff_fderiv_apply hW (dirS ι j)) (by simp))
    have hBeq : fderiv ℝ (fun q : Spacetime ι => heatGsq ι W q) p (dirS ι i)
        = 2 * ∑ j : ι, fderiv ℝ W p (dirS ι j)
            * fderiv ℝ (fun q => fderiv ℝ W q (dirS ι i)) p (dirS ι j) := by
      have hgsqSum : (fun q : Spacetime ι => heatGsq ι W q)
          = ∑ j : ι, (fun q : Spacetime ι => (fderiv ℝ W q (dirS ι j)) ^ 2) :=
        funext fun q => by show heatGsq ι W q = _; rw [Finset.sum_apply]; rfl
      rw [hgsqSum]
      rw [fderiv_sum (fun j _ => Differentiable.differentiableAt
          (ContDiff.differentiable (ContDiff.pow (contDiff_fderiv_apply hW (dirS ι j)) 2)
            (by simp)))]
      rw [ContinuousLinearMap.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show (fderiv ℝ ((fun q : Spacetime ι => fderiv ℝ W q (dirS ι j)) ^ 2) p) (dirS ι i) = _
      rw [show fderiv ℝ ((fun q : Spacetime ι => fderiv ℝ W q (dirS ι j)) ^ 2) p
            = (2 • fderiv ℝ W p (dirS ι j) ^ (2 - 1)) •
              fderiv ℝ (fun q : Spacetime ι => fderiv ℝ W q (dirS ι j)) p from fderiv_pow 2 (hjd j)]
      simp only [ContinuousLinearMap.smul_apply, Pi.smul_apply, pow_one, smul_eq_mul,
        nsmul_eq_mul]
      rw [swap2' hW p (dirS ι j) (dirS ι i)]
      ring
    have hd2 : DifferentiableAt ℝ (fun q : Spacetime ι => heatLap ι W q + heatGsq ι W q) p :=
      Differentiable.differentiableAt (ContDiff.differentiable (hslap.add hsq) (by simp))
    have hsumf : fderiv ℝ (fun q : Spacetime ι => heatLap ι W q + heatGsq ι W q) p
        = fderiv ℝ (fun q => heatLap ι W q) p + fderiv ℝ (fun q => heatGsq ι W q) p :=
      fderiv_add (Differentiable.differentiableAt (ContDiff.differentiable hslap (by simp)))
        (Differentiable.differentiableAt (ContDiff.differentiable hsq (by simp)))
    calc fderiv ℝ (fun q => coleHopfU ι ν W q i) p (dirT ι)
        = (-2 * ν) • fderiv ℝ (fun q => fderiv ℝ W q (dirS ι i)) p (dirT ι) := key p i (dirT ι)
      _ = (-2 * ν) • fderiv ℝ (fun q => fderiv ℝ W q (dirT ι)) p (dirS ι i) := by
          congr 1
          exact swap2' hW p (dirS ι i) (dirT ι)
      _ = (-2 * ν) • fderiv ℝ (fun q : Spacetime ι =>
          ν * (heatLap ι W q + heatGsq ι W q)) p (dirS ι i) := by
          congr 1
          exact congrArg (fun H : Spacetime ι → ℝ => fderiv ℝ H p (dirS ι i)) hfun
      _ = (-2 * ν) • ν • (fderiv ℝ (fun q : Spacetime ι => heatLap ι W q) p (dirS ι i)
          + fderiv ℝ (fun q : Spacetime ι => heatGsq ι W q) p (dirS ι i)) := by
          congr 1
          have hsm : (fun q : Spacetime ι => ν * (heatLap ι W q + heatGsq ι W q))
              = (ν • (fun q : Spacetime ι => heatLap ι W q + heatGsq ι W q)) := rfl
          rw [hsm, fderiv_const_smul hd2 ν, hsumf, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.add_apply]
      _ = (-2 * ν) • ν •
          (∑ j : ι, fderiv ℝ (fun q => fderiv ℝ (fun y => fderiv ℝ W y (dirS ι i)) q (dirS ι j))
              p (dirS ι j)
            + 2 * ∑ j : ι, fderiv ℝ W p (dirS ι j)
                * fderiv ℝ (fun q => fderiv ℝ W q (dirS ι i)) p (dirS ι j)) := by
          congr 1
          rw [hAeq, hBeq]
  -- Convective term: `4 ν² S₂` with the same atom shapes as `hT1`.
  have hT2 : ∑ j : ι, coleHopfU ι ν W p j
        * fderiv ℝ (fun q => coleHopfU ι ν W q i) p (dirS ι j)
      = (4 * ν * ν) * ∑ j : ι, fderiv ℝ W p (dirS ι j)
          * fderiv ℝ (fun q => fderiv ℝ W q (dirS ι i)) p (dirS ι j) := by
    calc ∑ j : ι, coleHopfU ι ν W p j
            * fderiv ℝ (fun q => coleHopfU ι ν W q i) p (dirS ι j)
        = ∑ j : ι, (4 * ν * ν) *
            (fderiv ℝ W p (dirS ι j)
              * fderiv ℝ (fun q => fderiv ℝ W q (dirS ι i)) p (dirS ι j)) :=
            Finset.sum_congr rfl fun j _ => by
              rw [show coleHopfU ι ν W p j = (-2 * ν) • fderiv ℝ W p (dirS ι j) from rfl,
                key p i (dirS ι j)]
              simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
              ring
      _ = (4 * ν * ν) * ∑ j : ι, fderiv ℝ W p (dirS ι j)
          * fderiv ℝ (fun q => fderiv ℝ W q (dirS ι i)) p (dirS ι j) :=
            by rw [← Finset.mul_sum]
  -- Diffusion term: `-2 ν S₁` with the same atom shape as `hT1`.
  have hT3 : ∑ j : ι, fderiv ℝ (fun q => fderiv ℝ (fun x => coleHopfU ι ν W x i) q (dirS ι j))
        p (dirS ι j)
      = (-2 * ν) * ∑ j : ι, fderiv ℝ (fun q => fderiv ℝ (fun y => fderiv ℝ W y (dirS ι i))
          q (dirS ι j)) p (dirS ι j) := by
    calc ∑ j : ι, fderiv ℝ (fun q => fderiv ℝ (fun x => coleHopfU ι ν W x i) q (dirS ι j))
            p (dirS ι j)
        = ∑ j : ι, (-2 * ν) • fderiv ℝ
            (fun q => fderiv ℝ (fun y => fderiv ℝ W y (dirS ι i)) q (dirS ι j)) p (dirS ι j) :=
            Finset.sum_congr rfl fun j _ => by
              have hj : (fun q : Spacetime ι =>
                  fderiv ℝ (fun x => coleHopfU ι ν W x i) q (dirS ι j))
                  = ((-2 * ν) • (fun q : Spacetime ι =>
                    fderiv ℝ (fun y : Spacetime ι => fderiv ℝ W y (dirS ι i)) q (dirS ι j))) :=
                funext fun q => key q i (dirS ι j)
              have hdj : DifferentiableAt ℝ (fun q : Spacetime ι =>
                  fderiv ℝ (fun y : Spacetime ι => fderiv ℝ W y (dirS ι i)) q (dirS ι j)) p :=
                Differentiable.differentiableAt
                  (ContDiff.differentiable
                    (contDiff_fderiv_apply (contDiff_fderiv_apply hW (dirS ι i)) (dirS ι j))
                    (by simp))
              rw [hj, fderiv_const_smul hdj (-2 * ν), ContinuousLinearMap.smul_apply]
      _ = (-2 * ν) • ∑ j : ι, fderiv ℝ
          (fun q => fderiv ℝ (fun y => fderiv ℝ W y (dirS ι i)) q (dirS ι j)) p (dirS ι j) :=
            (Finset.smul_sum (f := fun j =>
              fderiv ℝ (fun q => fderiv ℝ (fun y => fderiv ℝ W y (dirS ι i)) q (dirS ι j)) p
                (dirS ι j))).symm
      _ = (-2 * ν) * ∑ j : ι, fderiv ℝ (fun q => fderiv ℝ (fun y => fderiv ℝ W y (dirS ι i))
          q (dirS ι j)) p (dirS ι j) := by rw [smul_eq_mul]
  -- Assembly: `-2ν²(S₁ + 2S₂) + 4ν²S₂ - ν(-2ν S₁) = 0`.
  rw [hT1, hT2, hT3]
  simp only [smul_eq_mul]
  ring
/-! ## 3. Irrotationality: the curl-free boundary (dimension 3, repo carriers) -/

namespace Navier.Analysis

open Navier
open Navier.Analysis.Vorticity

/-- The Cole–Hopf slice velocity field of a smooth log-amplitude
`W : Space → ℝ`: `u = -2ν ∇W` as a repo `VelocityField`. -/
noncomputable def coleHopfSlice (ν : ℝ) (W : PressureField) : VelocityField :=
  fun x => (-2 * ν) • staticGradient W x

/-- **Boundary theorem (component form).**  The spatial Jacobian of a
Cole–Hopf velocity is symmetric at every point — mixed partials of the log
amplitude commute (`swap2'`).  This is the SAME irrotationality wall the
scalar Madelung decoder hits
(`Navier/Analysis/MadelungDecoderCurlObstruction.lean`, cited, not edited).
PROVED (fleet NSQM-0926) by `congrArg ((-2ν) • ·) ∘ swap2'` modulo the
`fderiv_const_smul` side conditions. -/
theorem colehopf_jacobian_symmetric (ν : ℝ) {W : PressureField} (hW : ContDiff ℝ ⊤ W)
    (x : Space) (i j : Fin 3) :
    fderiv ℝ (fun y => coleHopfSlice ν W y i) x (basisVector j)
      = fderiv ℝ (fun y => coleHopfSlice ν W y j) x (basisVector i) := by
  have key (k m : Fin 3) :
      fderiv ℝ (fun y => coleHopfSlice ν W y k) x (basisVector m)
        = (-2 * ν) • fderiv ℝ (fun y => fderiv ℝ W y (basisVector k)) x (basisVector m) := by
      have hk : DifferentiableAt ℝ (fun y : Space => fderiv ℝ W y (basisVector k)) x :=
        Differentiable.differentiableAt
          (ContDiff.differentiable (contDiff_fderiv_apply hW (basisVector k)) (by simp))
      show fderiv ℝ ((-2 * ν) • (fun z : Space => fderiv ℝ W z (basisVector k))) x
          (basisVector m) = _
      rw [fderiv_const_smul hk (-2 * ν), ContinuousLinearMap.smul_apply]
  rw [key i j, key j i]
  exact congrArg ((-2 * ν) • ·) (swap2' hW x (basisVector i) (basisVector j))

/-- **Cole–Hopf velocities are irrotational (repo carrier).**  Write
`c • ∇W = ∇(cW)` and apply the repo's public
`staticCurl_staticGradient_eq_zero` (namespace `Navier.Analysis.CurlIdentities`).
PROVED by the one-line calc via `staticCurl_staticGradient_eq_zero`. -/
theorem colehopf_staticCurl_zero (ν : ℝ) {W : PressureField} (hW : ContDiff ℝ ⊤ W)
    (x : Space) : staticCurl (coleHopfSlice ν W) x = 0 := by
  have hc : coleHopfSlice ν W = staticGradient (fun y : Space => (-2 * ν) • W y) := by
    ext y i
    have hWy : DifferentiableAt ℝ W y :=
      Differentiable.differentiableAt (ContDiff.differentiable hW (by simp))
    simp only [coleHopfSlice, staticGradient, Pi.smul_apply]
    show (-2 * ν) • fderiv ℝ W y (basisVector i) = fderiv ℝ ((-2 * ν) • W) y (basisVector i)
    rw [fderiv_const_smul hWy (-2 * ν), ContinuousLinearMap.smul_apply]
  rw [hc]
  exact CurlIdentities.staticCurl_staticGradient_eq_zero (fun y : Space => (-2 * ν) • W y) x
    ((hW.const_smul (-2 * ν)).contDiffAt.of_le (by simp))

/-- Cole–Hopf slices carry zero vorticity: immediate from
`colehopf_staticCurl_zero`. -/
theorem colehopf_vorticity_zero (ν : ℝ) {W : PressureField} (hW : ContDiff ℝ ⊤ W)
    (t : ℝ) (x : Space) :
    vorticity (fun s y => coleHopfSlice ν W y) t x = 0 :=
  colehopf_staticCurl_zero ν hW x

/-- **Zero vortex stretching.**  The NS nonlinear term `(ω·∇)u` evaluated on
a Cole–Hopf slice vanishes because `ω = 0`: the transport derivative is a
continuous linear map applied to the zero vector. PROVED (one `rw`). -/
theorem colehopf_stretching_zero (ν : ℝ) {W : PressureField} (hW : ContDiff ℝ ⊤ W)
    (t : ℝ) (x : Space) :
    spatialDerivative (fun s y => coleHopfSlice ν W y) t x
        (vorticity (fun s y => coleHopfSlice ν W y) t x) = 0 := by
  rw [colehopf_vorticity_zero ν hW t x]
  exact map_zero _

end Navier.Analysis

/-! ## 4. The complex-phase Madelung ansatz: bridges 1 and 3 are two halves
of one logarithmic derivative. -/

open Navier

/-- The complex-phase ansatz `ψ = exp((iS - Γ)/ħ)`: phase `S` on the
imaginary slot, Cole–Hopf log-amplitude `Γ` on the real slot. -/
noncomputable def complexPhaseWave (ħ : ℝ) (S Γ : PressureField) (x : Space) : ℂ :=
  Complex.exp (Complex.I * (S x / ħ) - Γ x / ħ)

/-- `ψ` never vanishes. -/
theorem complexPhaseWave_ne (ħ : ℝ) (S Γ : PressureField) (x : Space) :
    complexPhaseWave ħ S Γ x ≠ 0 := Complex.exp_ne_zero _

/-- The Cole–Hopf amplitude of the real slot, `θ = e^{-Γ/ħ}`; its positivity
is kernel-checked by `Real.exp_pos`, no hypothesis. -/
noncomputable def complexPhaseAmplitude (ħ : ℝ) (Γ : PressureField) (x : Space) : ℝ :=
  Real.exp (-Γ x / ħ)

theorem complexPhaseAmplitude_pos (ħ : ℝ) (Γ : PressureField) (x : Space) :
    0 < complexPhaseAmplitude ħ Γ x := Real.exp_pos _

/-- **The logarithmic derivative of the complex-phase ansatz.**
`(Dψ·v)/ψ = i·(DS·v)/ħ - (DΓ·v)/ħ`: one computation, two readers.
Proof: exp-chain over `ℂ` (`HasFDerivAt.cexp`, `Complex.ofRealCLM` transport,
`mul_const` for the `ħ⁻¹` factors), cancel `exp (g x) ≠ 0`. -/
theorem complexPhase_logDeriv {ħ : ℝ} (hħ : ħ ≠ 0) (S Γ : PressureField)
    (hS : ContDiff ℝ ⊤ S) (hΓ : ContDiff ℝ ⊤ Γ) (x v : Space) :
    fderiv ℝ (complexPhaseWave ħ S Γ) x v / complexPhaseWave ħ S Γ x =
      Complex.I * (fderiv ℝ S x v / ħ) - fderiv ℝ Γ x v / ħ := by
  have hSx : HasFDerivAt S (fderiv ℝ S x) x :=
    (Differentiable.differentiableAt (ContDiff.differentiable hS (by simp))).hasFDerivAt
  have hΓx : HasFDerivAt Γ (fderiv ℝ Γ x) x :=
    (Differentiable.differentiableAt (ContDiff.differentiable hΓ (by simp))).hasFDerivAt
  -- (S·/ħ) and (Γ/ħ) as ℂ-valued (real division, lifted), with derivative CLMs
  have hs1 : HasFDerivAt (fun y : Space => (S y / ħ : ℂ))
      (Complex.ofRealCLM ∘L (ħ⁻¹ • fderiv ℝ S x)) x := by
    have h0 := hSx.mul_const (ħ⁻¹ : ℝ)
    have h1 :=
      HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt (f := Complex.ofRealCLM)) h0
    exact HasFDerivAt.congr_of_eventuallyEq h1 (Filter.EventuallyEq.of_eq
      (funext fun y => by
        rw [div_eq_mul_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
        simp only [Function.comp_apply, Complex.ofRealCLM_apply]))
  have hG1 : HasFDerivAt (fun y : Space => (Γ y / ħ : ℂ))
      (Complex.ofRealCLM ∘L (ħ⁻¹ • fderiv ℝ Γ x)) x := by
    have h0 := hΓx.mul_const (ħ⁻¹ : ℝ)
    have h1 :=
      HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt (f := Complex.ofRealCLM)) h0
    exact HasFDerivAt.congr_of_eventuallyEq h1 (Filter.EventuallyEq.of_eq
      (funext fun y => by
        rw [div_eq_mul_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
        simp only [Function.comp_apply, Complex.ofRealCLM_apply]))
  have hI : HasFDerivAt (fun y : Space => Complex.I * (S y / ħ))
      (Complex.I • (Complex.ofRealCLM ∘L (ħ⁻¹ • fderiv ℝ S x))) x := by
    have h : (fun y : Space => Complex.I * (S y / ħ))
        = (fun y : Space => (S y / ħ : ℂ) * Complex.I) := by
      ext y
      rw [mul_comm]
    rw [h]
    exact hs1.mul_const Complex.I
  have hg : HasFDerivAt (fun y : Space => Complex.I * (S y / ħ) - Γ y / ħ)
      (Complex.I • (Complex.ofRealCLM ∘L (ħ⁻¹ • fderiv ℝ S x))
        - Complex.ofRealCLM ∘L (ħ⁻¹ • fderiv ℝ Γ x)) x := hI.sub hG1
  have hψ : HasFDerivAt (complexPhaseWave ħ S Γ)
      (Complex.exp (Complex.I * (S x / ħ) - Γ x / ħ) •
        (Complex.I • (Complex.ofRealCLM ∘L (ħ⁻¹ • fderiv ℝ S x))
          - Complex.ofRealCLM ∘L (ħ⁻¹ • fderiv ℝ Γ x))) x := by
    show HasFDerivAt (fun y : Space => Complex.exp (Complex.I * (S y / ħ) - Γ y / ħ))
      (Complex.exp (Complex.I * (S x / ħ) - Γ x / ħ) •
        (Complex.I • (Complex.ofRealCLM ∘L (ħ⁻¹ • fderiv ℝ S x))
          - Complex.ofRealCLM ∘L (ħ⁻¹ • fderiv ℝ Γ x))) x
    exact hg.cexp
  have den : complexPhaseWave ħ S Γ x =
      Complex.exp (Complex.I * (S x / ħ) - Γ x / ħ) := rfl
  rw [hψ.fderiv, den]
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [hħ, Complex.exp_ne_zero]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  field_simp [hħ]
theorem complexPhase_colehopf_eq_negRe {ħ ν : ℝ} (hħ : ħ ≠ 0) (S Γ : PressureField)
    (hS : ContDiff ℝ ⊤ S) (hΓ : ContDiff ℝ ⊤ Γ) (x : Space) (i : Fin 3) :
    (-2 * ν) • fderiv ℝ (fun y => Real.log (complexPhaseAmplitude ħ Γ y)) x
        (basisVector i)
      = (-2 * ν) * (fderiv ℝ (complexPhaseWave ħ S Γ) x (basisVector i)
          / complexPhaseWave ħ S Γ x).re := by
  have hGd : DifferentiableAt ℝ Γ x :=
    Differentiable.differentiableAt (ContDiff.differentiable hΓ (by simp))
  have hfun : (fun y : Space => Real.log (complexPhaseAmplitude ħ Γ y))
      = (fun y => -(Γ y) / ħ) :=
    funext fun y => Real.log_exp _
  have hsmul : (fun y : Space => -(Γ y) / ħ) = (fun y => (-ħ⁻¹ : ℝ) • Γ y) :=
    funext fun y => by simp only [neg_mul, div_eq_mul_inv]; ring
  rw [hfun, hsmul]
  show (-2 * ν) • (fderiv ℝ ((-ħ⁻¹ : ℝ) • Γ) x) (basisVector i) = _
  rw [fderiv_const_smul hGd (-ħ⁻¹), ContinuousLinearMap.smul_apply]
  rw [complexPhase_logDeriv hħ S Γ hS hΓ x (basisVector i)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.sub_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.div_re, Complex.div_im, Complex.normSq_ofReal, mul_zero,
    zero_mul, sub_self, zero_div, add_zero]
  try field_simp [hħ]
  try ring
/-- **Separation.**  In dimension 2 the plane-rotation field
`rot(x₀,x₁) = (-x₁, x₀)` equals `-2ν∇W` for NO smooth `W` and NO viscosity
`ν`: Jacobian symmetry (`swap2'`) forces `∂₁u₀ = ∂₀u₁`, while the field
itself gives `∂₁u₀ = -1` and `∂₀u₁ = 1`, i.e. `1 = -1`.  The witness is this
file's own public field; the repo's private bump machinery (`datumFn` in
`MadelungDecoderCurlObstruction.lean`) is NOT reused. Proof: component
function equalities from the hypothesis, directional `fderiv` of the
coordinate linear functionals at the origin, and the `swap2'`-forced
`-1 = 1` contradiction via `linarith`. -/
theorem no_colehopf_of_plane_rotation :
    ¬ ∃ (ν : ℝ) (W : Spacetime (Fin 2) → ℝ), ContDiff ℝ ⊤ W ∧
      ∀ p, coleHopfU (Fin 2) ν W p = fun i => if i = 0 then -(p.2 1) else p.2 0 := by
  rintro ⟨ν, W, hW, hEq⟩
  have he0 : (fun p : Spacetime (Fin 2) => coleHopfU (Fin 2) ν W p 0)
      = (fun p => -(p.2 1)) := by
    funext p
    rw [hEq]
    rfl
  have he1 : (fun p : Spacetime (Fin 2) => coleHopfU (Fin 2) ν W p 1)
      = (fun p => p.2 0) := by
    funext p
    rw [hEq]
    rfl
  -- differentiating the Cole–Hopf side in a spatial direction
  have key (k m : Fin 2) :
      fderiv ℝ (fun p : Spacetime (Fin 2) => coleHopfU (Fin 2) ν W p k) (0, 0)
          (dirS (Fin 2) m)
        = (-2 * ν) • fderiv ℝ (fun q => fderiv ℝ W q (dirS (Fin 2) k)) (0, 0)
            (dirS (Fin 2) m) := by
    have hk : DifferentiableAt ℝ
        (fun q : Spacetime (Fin 2) => fderiv ℝ W q (dirS (Fin 2) k)) (0, 0) :=
      Differentiable.differentiableAt
        (ContDiff.differentiable (contDiff_fderiv_apply hW (dirS (Fin 2) k)) (by simp))
    show fderiv ℝ ((-2 * ν) • (fun p : Spacetime (Fin 2) => fderiv ℝ W p (dirS (Fin 2) k)))
        (0, 0) (dirS (Fin 2) m) = _
    rw [fderiv_const_smul hk (-2 * ν), ContinuousLinearMap.smul_apply]
  -- differentiating the two coordinate functions at the origin; each is the
  -- bundled evaluation-at-index linear functional on `ℝ × (Fin 2 → ℝ)`
  let ev1 : Spacetime (Fin 2) →L[ℝ] ℝ :=
    { toFun := fun p => p.2 1,
      map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl,
      cont := (continuous_apply (1 : Fin 2)).comp continuous_snd }
  let ev0 : Spacetime (Fin 2) →L[ℝ] ℝ :=
    { toFun := fun p => p.2 0,
      map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl,
      cont := (continuous_apply (0 : Fin 2)).comp continuous_snd }
  have key1 : ⇑ev1 = fun p : Spacetime (Fin 2) => p.2 1 := by
    ext p
    rfl
  have key0 : ⇑ev0 = fun p : Spacetime (Fin 2) => p.2 0 := by
    ext p
    rfl
  have h0 : HasFDerivAt (fun p : Spacetime (Fin 2) => -(p.2 1)) (-ev1) (0, 0) := by
    refine ((ev1.hasFDerivAt.congr_of_eventuallyEq ?_).neg)
    exact Filter.EventuallyEq.of_eq (funext fun p => rfl)
  have h1 : HasFDerivAt (fun p : Spacetime (Fin 2) => p.2 0) ev0 (0, 0) := by
    refine (ev0.hasFDerivAt.congr_of_eventuallyEq ?_)
    exact Filter.EventuallyEq.of_eq (funext fun p => rfl)
  have d0 : fderiv ℝ (fun p : Spacetime (Fin 2) => -(p.2 1)) (0, 0) (dirS (Fin 2) 1) = -1 := by
    rw [h0.fderiv, ContinuousLinearMap.neg_apply, key1]
    rfl
  have d1 : fderiv ℝ (fun p : Spacetime (Fin 2) => p.2 0) (0, 0) (dirS (Fin 2) 0) = 1 := by
    rw [h1.fderiv, key0]
    rfl
  -- chain the contradiction: same derivative, forced to be -1 and 1
  have hA : (-2 * ν) • fderiv ℝ (fun q => fderiv ℝ W q (dirS (Fin 2) 0)) (0, 0)
      (dirS (Fin 2) 1) = -1 := by
    have h := congrArg (fun k : Spacetime (Fin 2) → ℝ =>
        fderiv ℝ k (0, 0) (dirS (Fin 2) 1)) he0
    rwa [key 0 1, d0] at h
  have hB : (-2 * ν) • fderiv ℝ (fun q => fderiv ℝ W q (dirS (Fin 2) 1)) (0, 0)
      (dirS (Fin 2) 0) = 1 := by
    have h := congrArg (fun k : Spacetime (Fin 2) → ℝ =>
        fderiv ℝ k (0, 0) (dirS (Fin 2) 0)) he1
    rwa [key 1 0, d1] at h
  have hX : fderiv ℝ (fun q => fderiv ℝ W q (dirS (Fin 2) 0)) (0, 0) (dirS (Fin 2) 1)
      = fderiv ℝ (fun q => fderiv ℝ W q (dirS (Fin 2) 1)) (0, 0) (dirS (Fin 2) 0) :=
    swap2' hW (0, 0) (dirS (Fin 2) 0) (dirS (Fin 2) 1)
  have contra : (-1 : ℝ) = 1 :=
    calc (-1 : ℝ)
        = (-2 * ν) • fderiv ℝ (fun q => fderiv ℝ W q (dirS (Fin 2) 0)) (0, 0)
            (dirS (Fin 2) 1) := hA.symm
      _ = (-2 * ν) • fderiv ℝ (fun q => fderiv ℝ W q (dirS (Fin 2) 1)) (0, 0)
            (dirS (Fin 2) 0) := congrArg ((-2 * ν) • ·) hX
      _ = 1 := hB
  linarith
/-! ## 5. R1 positivity transport: heat in `θ` ⇒ log-heat in `log θ`, and the
ε-exhaustion that removes global positivity -/

namespace Navier.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Directional derivative of `log ∘ θ`, pointwise in the base point. -/
theorem colehopf_logFD {θ : Spacetime ι → ℝ} (hθ : ContDiff ℝ ⊤ θ) (hpos : ∀ p, 0 < θ p)
    (q v : Spacetime ι) :
    fderiv ℝ (fun p : Spacetime ι => Real.log (θ p)) q v = (θ q)⁻¹ • fderiv ℝ θ q v := by
  have hθd : HasFDerivAt θ (fderiv ℝ θ q) q :=
    (Differentiable.differentiableAt (ContDiff.differentiable hθ (by simp))).hasFDerivAt
  have h : fderiv ℝ (fun p : Spacetime ι => Real.log (θ p)) q = (θ q)⁻¹ • fderiv ℝ θ q :=
    (hθd.log ((hpos q).ne')).fderiv
  rw [h]
  exact ContinuousLinearMap.smul_apply _ _ _

/-- Slope function identity for `log ∘ θ`. -/
theorem colehopf_logSlope {θ : Spacetime ι → ℝ} (hθ : ContDiff ℝ ⊤ θ) (hpos : ∀ p, 0 < θ p)
    (w : Spacetime ι) :
    (fun q : Spacetime ι => fderiv ℝ (fun p : Spacetime ι => Real.log (θ p)) q w)
      = (fun q : Spacetime ι => (θ q)⁻¹ • fderiv ℝ θ q w) :=
  funext fun q => colehopf_logFD hθ hpos q w

/-- Product rule for the slope function of the log. -/
theorem colehopf_logSlopeFD {θ : Spacetime ι → ℝ} (hθ : ContDiff ℝ ⊤ θ) (hpos : ∀ p, 0 < θ p)
    (p : Spacetime ι) (w v : Spacetime ι) :
    fderiv ℝ (fun q : Spacetime ι => (θ q)⁻¹ • fderiv ℝ θ q w) p v
      = (θ p)⁻¹ • fderiv ℝ (fun q : Spacetime ι => fderiv ℝ θ q w) p v
        + (-(θ p)⁻¹ * (θ p)⁻¹ * fderiv ℝ θ p v) * fderiv ℝ θ p w := by
  have hθd : HasFDerivAt θ (fderiv ℝ θ p) p :=
    (Differentiable.differentiableAt (ContDiff.differentiable hθ (by simp))).hasFDerivAt
  have hA : HasFDerivAt (fun q : Spacetime ι => (θ q)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ ℝ (θ p)⁻¹ (θ p)⁻¹) ∘L fderiv ℝ θ p) p :=
    (hasFDerivAt_inv' ((hpos p).ne' : (θ p : ℝ) ≠ 0)).comp p hθd
  have hB : HasFDerivAt (fun q : Spacetime ι => fderiv ℝ θ q w)
      (fderiv ℝ (fun q : Spacetime ι => fderiv ℝ θ q w) p) p :=
    (Differentiable.differentiableAt
      (ContDiff.differentiable (contDiff_fderiv_apply hθ w) (by simp))).hasFDerivAt
  have hprod := (hA.smul hB).fderiv
  rw [show (fun q : Spacetime ι => (θ q)⁻¹ • fderiv ℝ θ q w)
      = ((fun q : Spacetime ι => (θ q)⁻¹) • (fun q : Spacetime ι => fderiv ℝ θ q w)) from rfl,
    hprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compSL_apply,
    ContinuousLinearMap.neg_apply, smul_eq_mul]
  ring

/-- **R1 positivity transport.**  If `θ > 0` is a smooth heat solution
(`∂t θ = ν Δθ`), then `log ∘ θ` satisfies the log-heat equation. -/
theorem colehopf_logheat_of_pos_heat (ν : ℝ) (θ : Spacetime ι → ℝ) (hθ : ContDiff ℝ ⊤ θ)
    (hpos : ∀ p, 0 < θ p)
    (heat : ∀ p, fderiv ℝ θ p (dirT ι) = ν * heatLap ι θ p) :
    ∀ p, fderiv ℝ (fun p : Spacetime ι => Real.log (θ p)) p (dirT ι)
      = ν * (heatLap ι (fun p : Spacetime ι => Real.log (θ p)) p
          + heatGsq ι (fun p : Spacetime ι => Real.log (θ p)) p) := by
  intro p
  have hT : fderiv ℝ (fun p : Spacetime ι => Real.log (θ p)) p (dirT ι)
      = (θ p)⁻¹ • fderiv ℝ θ p (dirT ι) := colehopf_logFD hθ hpos p (dirT ι)
  have key : (fun j : ι => fderiv ℝ (fun q : Spacetime ι =>
        fderiv ℝ (fun p : Spacetime ι => Real.log (θ p)) q (dirS ι j)) p (dirS ι j))
      = (fun j : ι => (θ p)⁻¹ *
            fderiv ℝ (fun q : Spacetime ι => fderiv ℝ θ q (dirS ι j)) p (dirS ι j)
          - (θ p)⁻¹ * (θ p)⁻¹ *
              (fderiv ℝ θ p (dirS ι j) * fderiv ℝ θ p (dirS ι j))) := by
    funext j
    rw [colehopf_logSlope hθ hpos (dirS ι j),
      colehopf_logSlopeFD hθ hpos p (dirS ι j) (dirS ι j)]
    simp only [smul_eq_mul]
    ring
  have hlap : heatLap ι (fun p : Spacetime ι => Real.log (θ p)) p
      = (θ p)⁻¹ * heatLap ι θ p - (θ p)⁻¹ * (θ p)⁻¹ * heatGsq ι θ p := by
    show ∑ j : ι, fderiv ℝ (fun q : Spacetime ι =>
        fderiv ℝ (fun p : Spacetime ι => Real.log (θ p)) q (dirS ι j)) p (dirS ι j) = _
    rw [key, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [show (∑ j : ι, fderiv ℝ (fun q : Spacetime ι => fderiv ℝ θ q (dirS ι j)) p (dirS ι j))
          = heatLap ι θ p from rfl,
        Finset.sum_congr rfl fun j _ => (pow_two _).symm,
        show (∑ j : ι, (fderiv ℝ θ p (dirS ι j)) ^ 2) = heatGsq ι θ p from rfl]
  have key2 : (fun j : ι =>
        (fderiv ℝ (fun p : Spacetime ι => Real.log (θ p)) p (dirS ι j)) ^ 2)
      = (fun j : ι => (θ p)⁻¹ * (θ p)⁻¹ *
            (fderiv ℝ θ p (dirS ι j) * fderiv ℝ θ p (dirS ι j))) := by
    funext j
    rw [colehopf_logFD hθ hpos p (dirS ι j)]
    simp only [smul_eq_mul]
    ring
  have hgsq : heatGsq ι (fun p : Spacetime ι => Real.log (θ p)) p
      = (θ p)⁻¹ * (θ p)⁻¹ * heatGsq ι θ p := by
    show ∑ j : ι, (fderiv ℝ (fun p : Spacetime ι => Real.log (θ p)) p (dirS ι j)) ^ 2 = _
    rw [key2, ← Finset.mul_sum,
      Finset.sum_congr rfl fun j _ => (pow_two _).symm,
      show (∑ j : ι, (fderiv ℝ θ p (dirS ι j)) ^ 2) = heatGsq ι θ p from rfl]
  calc fderiv ℝ (fun p : Spacetime ι => Real.log (θ p)) p (dirT ι)
      = (θ p)⁻¹ • fderiv ℝ θ p (dirT ι) := hT
    _ = (θ p)⁻¹ • (ν * heatLap ι θ p) := by rw [heat p]
    _ = ν * (heatLap ι (fun p : Spacetime ι => Real.log (θ p)) p
        + heatGsq ι (fun p : Spacetime ι => Real.log (θ p)) p) := by
        rw [hlap, hgsq]
        simp only [smul_eq_mul]
        ring

/-- **R1 crown consumer.**  A strictly positive smooth heat amplitude yields a
Cole–Hopf velocity satisfying vector Burgers. -/
theorem colehopf_burgers_of_positive_heat (ν : ℝ) {θ : Spacetime ι → ℝ}
    (hθ : ContDiff ℝ ⊤ θ) (hpos : ∀ p, 0 < θ p)
    (heat : ∀ p, fderiv ℝ θ p (dirT ι) = ν * heatLap ι θ p) :
    ∀ (p : Spacetime ι) (i : ι),
      fderiv ℝ (coleHopfU ι ν (fun q => Real.log (θ q)) · i) p (dirT ι)
        + ∑ j : ι, coleHopfU ι ν (fun q => Real.log (θ q)) p j
            * fderiv ℝ (coleHopfU ι ν (fun q => Real.log (θ q)) · i) p (dirS ι j)
        - ν * ∑ j : ι,
            fderiv ℝ (fun q =>
              fderiv ℝ (coleHopfU ι ν (fun q => Real.log (θ q)) · i) q (dirS ι j))
              p (dirS ι j) = 0 :=
  colehopf_burgers_of_logheat ν (fun q => Real.log (θ q))
    (hθ.log fun q => (hpos q).ne')
    (colehopf_logheat_of_pos_heat ν θ hθ hpos heat)

/-- The unregularized formal Cole–Hopf velocity of an amplitude, `-2ν ∇θ / θ`. -/
def formalColeHopfU (ν : ℝ) (θ : Spacetime ι → ℝ) (p : Spacetime ι) : ι → ℝ :=
  fun i => (-2 * ν) * (θ p)⁻¹ * fderiv ℝ θ p (dirS ι i)

/-- On the positivity set the two shapes of the velocity agree. -/
theorem coleHopfU_log_eq_formal (ν : ℝ) {θ : Spacetime ι → ℝ} (hθ : ContDiff ℝ ⊤ θ)
    (hpos : ∀ p, 0 < θ p) (p : Spacetime ι) :
    coleHopfU ι ν (fun q => Real.log (θ q)) p = formalColeHopfU ν θ p := by
  funext i
  show (-2 * ν) • fderiv ℝ (fun q : Spacetime ι => Real.log (θ q)) p (dirS ι i) = _
  rw [colehopf_logFD hθ hpos p (dirS ι i)]
  simp only [formalColeHopfU, smul_eq_mul]
  ring

/-- **R1 exhaustion by positive parts.**  Nonnegativity alone suffices to run
Cole–Hopf on the `ε`-regularization `θ + ε`: each member of the family is a
Burgers solution with NO pointwise positivity hypothesis on `θ`. -/
theorem colehopf_burgers_of_heat_eps (ν : ℝ) {θ : Spacetime ι → ℝ} (hθ : ContDiff ℝ ⊤ θ)
    (hnonneg : ∀ p, 0 ≤ θ p) (ε : ℝ) (hε : 0 < ε)
    (heat : ∀ p, fderiv ℝ θ p (dirT ι) = ν * heatLap ι θ p) :
    ∀ (p : Spacetime ι) (i : ι),
      fderiv ℝ (coleHopfU ι ν (fun q => Real.log (θ q + ε)) · i) p (dirT ι)
        + ∑ j : ι, coleHopfU ι ν (fun q => Real.log (θ q + ε)) p j
            * fderiv ℝ (coleHopfU ι ν (fun q => Real.log (θ q + ε)) · i) p (dirS ι j)
        - ν * ∑ j : ι,
            fderiv ℝ (fun q =>
              fderiv ℝ (coleHopfU ι ν (fun q => Real.log (θ q + ε)) · i) q (dirS ι j))
              p (dirS ι j) = 0 := by
  have hpos : ∀ p, 0 < θ p + ε := fun p => by linarith [hnonneg p]
  have hθe : ContDiff ℝ ⊤ (fun p : Spacetime ι => θ p + ε) := hθ.add contDiff_const
  have heatε : ∀ p, fderiv ℝ (fun p : Spacetime ι => θ p + ε) p (dirT ι)
      = ν * heatLap ι (fun p : Spacetime ι => θ p + ε) p := by
    intro p
    have d1ε (w : Spacetime ι) :
        (fun q : Spacetime ι => fderiv ℝ (fun x : Spacetime ι => θ x + ε) q w)
          = (fun q : Spacetime ι => fderiv ℝ θ q w) := by
      funext q
      have hθd : HasFDerivAt θ (fderiv ℝ θ q) q :=
        (Differentiable.differentiableAt
          (ContDiff.differentiable hθ (by simp))).hasFDerivAt
      have h2 : HasFDerivAt (fun x : Spacetime ι => θ x + ε) (fderiv ℝ θ q) q := by
        have h := hθd.add (hasFDerivAt_const ε q)
        rw [add_zero] at h
        exact h
      rw [h2.fderiv]
    have heqT : fderiv ℝ (fun x : Spacetime ι => θ x + ε) p (dirT ι)
        = fderiv ℝ θ p (dirT ι) := congrFun (d1ε (dirT ι)) p
    have heqL : heatLap ι (fun x : Spacetime ι => θ x + ε) p = heatLap ι θ p := by
      show ∑ j : ι, fderiv ℝ (fun q : Spacetime ι =>
          fderiv ℝ (fun x : Spacetime ι => θ x + ε) q (dirS ι j)) p (dirS ι j)
          = ∑ j : ι, fderiv ℝ (fun q : Spacetime ι =>
              fderiv ℝ θ q (dirS ι j)) p (dirS ι j)
      rw [Finset.sum_congr rfl fun j _ => by rw [d1ε (dirS ι j)]]
    rw [heqT, heqL]
    exact heat p
  exact colehopf_burgers_of_positive_heat ν hθe hpos heatε

/-- The `ε`-family converges pointwise, at every point where `θ p > 0`, to the
formal Cole–Hopf velocity `-2ν ∇θ/θ`.  Positivity is needed only AT THE LIMIT
POINT, not on the whole field. -/
theorem colehopf_eps_tendsto_formal (ν : ℝ) {θ : Spacetime ι → ℝ} (hθ : ContDiff ℝ ⊤ θ)
    (p : Spacetime ι) (i : ι) (hp : 0 < θ p) :
    Tendsto (fun ε : ℝ => coleHopfU ι ν (fun q => Real.log (θ q + ε)) p i)
      (nhds 0) (nhds (formalColeHopfU ν θ p i)) := by
  have hθd : HasFDerivAt θ (fderiv ℝ θ p) p :=
    (Differentiable.differentiableAt (ContDiff.differentiable hθ (by simp))).hasFDerivAt
  have val (ε : ℝ) (hεn : θ p + ε ≠ 0) :
      coleHopfU ι ν (fun q => Real.log (θ q + ε)) p i
        = (-2 * ν) • ((θ p + ε)⁻¹ • fderiv ℝ θ p (dirS ι i)) := by
    have h : HasFDerivAt (fun x : Spacetime ι => θ x + ε) (fderiv ℝ θ p) p := by
      have h2 := hθd.add (hasFDerivAt_const ε p)
      rw [add_zero] at h2
      exact h2
    have hl : fderiv ℝ (fun x : Spacetime ι => Real.log (θ x + ε)) p
        = (θ p + ε)⁻¹ • fderiv ℝ θ p := (h.log hεn).fderiv
    show (-2 * ν) • fderiv ℝ (fun q : Spacetime ι => Real.log (θ q + ε)) p (dirS ι i) = _
    rw [hl, ContinuousLinearMap.smul_apply]
  have htarget : ((-2 * ν) • ((θ p)⁻¹ • fderiv ℝ θ p (dirS ι i)))
      = formalColeHopfU ν θ p i := by
    simp only [formalColeHopfU, smul_eq_mul]
    ring
  have hopen : ∀ᶠ (ε : ℝ) in nhds 0, θ p + ε ≠ 0 := by
    have hcont : ContinuousAt (fun ε : ℝ => θ p + ε) 0 :=
      continuousAt_const.add continuousAt_id
    refine hcont.eventually_ne ?_
    rw [add_zero]
    exact hp.ne'
  have hlim : Tendsto (fun ε : ℝ => (-2 * ν) • ((θ p + ε)⁻¹ • fderiv ℝ θ p (dirS ι i)))
      (nhds 0) (nhds (formalColeHopfU ν θ p i)) := by
    have h0 : Tendsto (fun ε : ℝ => θ p + ε) (nhds 0) (nhds (θ p)) := by
      convert tendsto_const_nhds.add tendsto_id using 1
      · funext ε
        rfl
      · rw [add_zero]
      · infer_instance
    have h1 : Tendsto (fun ε : ℝ => (θ p + ε)⁻¹) (nhds 0) (nhds (θ p)⁻¹) := h0.inv₀ hp.ne'
    have h2 : Tendsto (fun ε : ℝ => (θ p + ε)⁻¹ • fderiv ℝ θ p (dirS ι i)) (nhds 0)
        (nhds ((θ p)⁻¹ • fderiv ℝ θ p (dirS ι i))) :=
      h1.smul tendsto_const_nhds
    convert h2.const_smul (-2 * ν) using 1
    rw [htarget]
  refine Tendsto.congr' ?_ hlim
  filter_upwards [hopen] with ε hε
  rw [val ε hε]

/-! ### R2: the slice bridge -/

/-- Spatial slice of spacetime at time `t`. -/
def spacetimeSliceAt (t : ℝ) : Space → Spacetime (Fin 3) := fun x => (t, x)

/-- Differential of the slice: the continuous linear embedding `v ↦ (0, v)`. -/
def spacetimeSliceDir : Space →L[ℝ] Spacetime (Fin 3) :=
  ContinuousLinearMap.prod (0 : Space →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ Space)

theorem hasFDerivAt_spacetimeSliceAt (t : ℝ) (x : Space) :
    HasFDerivAt (spacetimeSliceAt t) spacetimeSliceDir x :=
  (hasFDerivAt_const t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) (E := Space) x)

/-- **Hom bridge.**  The derivative of a spacetime field composed with a time
slice is the derivative precomposed with the embedding. -/
theorem fderiv_spacetimeSlice_comp {W : Spacetime (Fin 3) → ℝ} (t : ℝ) (x : Space)
    (hW : DifferentiableAt ℝ W (t, x)) :
    fderiv ℝ (fun y : Space => W (t, y)) x = fderiv ℝ W (t, x) ∘L spacetimeSliceDir := by
  have hs := hasFDerivAt_spacetimeSliceAt t x
  have heq : (fun y : Space => W (t, y)) = W ∘ spacetimeSliceAt t := rfl
  rw [heq, fderiv_comp (f := spacetimeSliceAt t) (x := x) hW hs.differentiableAt, hs.fderiv]
  simp only [spacetimeSliceAt]

theorem dirS_spacetimeSliceDir (i : Fin 3) :
    spacetimeSliceDir (basisVector i) = dirS (Fin 3) i := by
  simp only [spacetimeSliceDir, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.id_apply, dirS, basisVector]
  rw [Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  funext k
  rw [Pi.single_apply]

/-- **R2 field bridge.**  The abstract Cole–Hopf field of a spacetime
amplitude, sliced at time `t`, IS the concrete dim-3 `coleHopfSlice` of the
sliced amplitude. -/
theorem coleHopfU_eq_coleHopfSlice (ν : ℝ) (W : Spacetime (Fin 3) → ℝ)
    (hW : ContDiff ℝ ⊤ W) (t : ℝ) :
    (fun y : Space => coleHopfU (Fin 3) ν W (t, y))
      = coleHopfSlice ν (fun y : Space => W (t, y)) := by
  ext x i
  have hWd : DifferentiableAt ℝ W (t, x) :=
    Differentiable.differentiableAt (ContDiff.differentiable hW (by simp))
  have hx : fderiv ℝ (fun y : Space => W (t, y)) x = fderiv ℝ W (t, x) ∘L spacetimeSliceDir :=
    fderiv_spacetimeSlice_comp t x hWd
  calc coleHopfU (Fin 3) ν W (t, x) i
      = (-2 * ν) • fderiv ℝ W (t, x) (dirS (Fin 3) i) := rfl
    _ = (-2 * ν) • fderiv ℝ W (t, x) (spacetimeSliceDir (basisVector i)) := by
        rw [← dirS_spacetimeSliceDir i]
    _ = (-2 * ν) • (fderiv ℝ W (t, x) ∘L spacetimeSliceDir) (basisVector i) := by
        rw [ContinuousLinearMap.comp_apply]
    _ = (-2 * ν) • fderiv ℝ (fun y : Space => W (t, y)) x (basisVector i) := by rw [hx]
    _ = coleHopfSlice ν (fun y : Space => W (t, y)) x i := rfl

/-- **R2 crown restatement.**  The abstract Cole–Hopf spacetime field, viewed
through the bridge, is a repo `VelocityEvolution` whose VORTICITY (the
dynamical NS carrier) vanishes at every time. -/
theorem coleHopfU_vorticity_zero (ν : ℝ) (W : Spacetime (Fin 3) → ℝ) (hW : ContDiff ℝ ⊤ W)
    (t : ℝ) (x : Space) :
    Vorticity.vorticity (fun s y => coleHopfU (Fin 3) ν W (s, y)) t x = 0 := by
  show Vorticity.staticCurl (fun y : Space => coleHopfU (Fin 3) ν W (t, y)) x = 0
  rw [coleHopfU_eq_coleHopfSlice ν W hW t]
  refine colehopf_staticCurl_zero ν ?_ x
  exact hW.comp (ContDiff.prodMk contDiff_const contDiff_id)

/-! ### R1(c): the exp direction — log-heat ⇒ positive heat, completing the
chain-rule equivalence the module header promised. -/

/-- Directional derivative of `exp ∘ W`. -/
theorem colehopf_expFD {W : Spacetime ι → ℝ} (hW : ContDiff ℝ ⊤ W) (q v : Spacetime ι) :
    fderiv ℝ (fun p : Spacetime ι => Real.exp (W p)) q v =
      Real.exp (W q) • fderiv ℝ W q v := by
  have hWd : HasFDerivAt W (fderiv ℝ W q) q :=
    (Differentiable.differentiableAt (ContDiff.differentiable hW (by simp))).hasFDerivAt
  have h : fderiv ℝ (fun p : Spacetime ι => Real.exp (W p)) q =
      Real.exp (W q) • fderiv ℝ W q := (hWd.exp).fderiv
  rw [h]
  exact ContinuousLinearMap.smul_apply _ _ _

/-- Slope function identity for `exp ∘ W`. -/
theorem colehopf_expSlope {W : Spacetime ι → ℝ} (hW : ContDiff ℝ ⊤ W) (w : Spacetime ι) :
    (fun q : Spacetime ι => fderiv ℝ (fun p : Spacetime ι => Real.exp (W p)) q w)
      = (fun q : Spacetime ι => Real.exp (W q) • fderiv ℝ W q w) :=
  funext fun q => colehopf_expFD hW q w

/-- Product rule for the slope function of the exp. -/
theorem colehopf_expSlopeFD {W : Spacetime ι → ℝ} (hW : ContDiff ℝ ⊤ W)
    (p : Spacetime ι) (w v : Spacetime ι) :
    fderiv ℝ (fun q : Spacetime ι => Real.exp (W q) • fderiv ℝ W q w) p v
      = Real.exp (W p) • fderiv ℝ (fun q : Spacetime ι => fderiv ℝ W q w) p v
        + Real.exp (W p) * fderiv ℝ W p v * fderiv ℝ W p w := by
  have hWd : HasFDerivAt W (fderiv ℝ W p) p :=
    (Differentiable.differentiableAt (ContDiff.differentiable hW (by simp))).hasFDerivAt
  have hA : HasFDerivAt (fun q : Spacetime ι => Real.exp (W q))
      (Real.exp (W p) • fderiv ℝ W p) p := hWd.exp
  have hB : HasFDerivAt (fun q : Spacetime ι => fderiv ℝ W q w)
      (fderiv ℝ (fun q : Spacetime ι => fderiv ℝ W q w) p) p :=
    (Differentiable.differentiableAt
      (ContDiff.differentiable (contDiff_fderiv_apply hW w) (by simp))).hasFDerivAt
  have hprod := (hA.smul hB).fderiv
  rw [show (fun q : Spacetime ι => Real.exp (W q) • fderiv ℝ W q w)
      = ((fun q : Spacetime ι => Real.exp (W q)) • (fun q : Spacetime ι => fderiv ℝ W q w))
        from rfl,
    hprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, smul_eq_mul]

/-- **R1 equivalence, exp direction.**  A log-heat field `W` exponentiates to
a strictly positive heat solution `θ = e^W`. -/
theorem colehopf_heat_of_pos_logheat (ν : ℝ) (W : Spacetime ι → ℝ) (hW : ContDiff ℝ ⊤ W)
    (hlog : ∀ p, fderiv ℝ W p (dirT ι)
        = ν * (heatLap ι W p + heatGsq ι W p)) :
    ∀ p, fderiv ℝ (fun p : Spacetime ι => Real.exp (W p)) p (dirT ι)
      = ν * heatLap ι (fun p : Spacetime ι => Real.exp (W p)) p := by
  intro p
  have hT : fderiv ℝ (fun p : Spacetime ι => Real.exp (W p)) p (dirT ι)
      = Real.exp (W p) • fderiv ℝ W p (dirT ι) := colehopf_expFD hW p (dirT ι)
  have key : (fun j : ι => fderiv ℝ (fun q : Spacetime ι =>
        fderiv ℝ (fun p : Spacetime ι => Real.exp (W p)) q (dirS ι j)) p (dirS ι j))
      = (fun j : ι => Real.exp (W p) *
            fderiv ℝ (fun q : Spacetime ι => fderiv ℝ W q (dirS ι j)) p (dirS ι j)
          + Real.exp (W p) * (fderiv ℝ W p (dirS ι j) * fderiv ℝ W p (dirS ι j))) := by
    funext j
    rw [colehopf_expSlope hW (dirS ι j),
      colehopf_expSlopeFD hW p (dirS ι j) (dirS ι j)]
    simp only [smul_eq_mul]
    ring
  have hlap : heatLap ι (fun p : Spacetime ι => Real.exp (W p)) p
      = Real.exp (W p) * (heatLap ι W p + heatGsq ι W p) := by
    show ∑ j : ι, fderiv ℝ (fun q : Spacetime ι =>
        fderiv ℝ (fun p : Spacetime ι => Real.exp (W p)) q (dirS ι j)) p (dirS ι j) = _
    rw [key, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [show (∑ j : ι, fderiv ℝ (fun q : Spacetime ι => fderiv ℝ W q (dirS ι j)) p (dirS ι j))
          = heatLap ι W p from rfl,
        show (∑ j : ι, fderiv ℝ W p (dirS ι j) * fderiv ℝ W p (dirS ι j)) = heatGsq ι W p
          from by
            rw [Finset.sum_congr rfl fun j _ => (pow_two _).symm,
              show (∑ j : ι, (fderiv ℝ W p (dirS ι j)) ^ 2) = heatGsq ι W p from rfl]]
    ring
  calc fderiv ℝ (fun p : Spacetime ι => Real.exp (W p)) p (dirT ι)
      = Real.exp (W p) • fderiv ℝ W p (dirT ι) := hT
    _ = Real.exp (W p) • (ν * (heatLap ι W p + heatGsq ι W p)) := by rw [hlog p]
    _ = ν * (Real.exp (W p) * (heatLap ι W p + heatGsq ι W p)) := by
        simp only [smul_eq_mul]
        ring
    _ = ν * heatLap ι (fun p : Spacetime ι => Real.exp (W p)) p := by rw [← hlap]

/-- The exponentiated amplitude: smooth, strictly positive, and a heat
solution — the full positive-amplitude package a log-heat field produces. -/
theorem colehopf_exp_is_positive_heat (ν : ℝ) (W : Spacetime ι → ℝ) (hW : ContDiff ℝ ⊤ W)
    (hlog : ∀ p, fderiv ℝ W p (dirT ι)
        = ν * (heatLap ι W p + heatGsq ι W p)) :
    let θ := fun p : Spacetime ι => Real.exp (W p)
    ContDiff ℝ ⊤ θ ∧ (∀ p, 0 < θ p) ∧
      (∀ p, fderiv ℝ θ p (dirT ι) = ν * heatLap ι θ p) :=
  ⟨hW.exp, fun p => Real.exp_pos _, colehopf_heat_of_pos_logheat ν W hW hlog⟩

/-! ### R1(d): sharpness — a global smooth heat solution whose zero set
genuinely blocks the log route.  Blanket positivity is not cosmetic. -/

/-- The first spatial coordinate on dimension-1 spacetime, as a continuous
linear functional. -/
noncomputable def coordAmp : Spacetime (Fin 1) →L[ℝ] ℝ where
  toFun := fun p => p.2 0
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := (continuous_apply 0).comp continuous_snd

theorem coordAmp_fderiv (p v : Spacetime (Fin 1)) :
    fderiv ℝ (fun q : Spacetime (Fin 1) => q.2 0) p v = v.2 0 := by
  have h : HasFDerivAt (fun q : Spacetime (Fin 1) => q.2 0) coordAmp p :=
    coordAmp.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- `coordAmp` solves the heat equation for every viscosity: both sides are
identically zero. -/
theorem coordAmp_heat (ν : ℝ) (p : Spacetime (Fin 1)) :
    fderiv ℝ (fun q : Spacetime (Fin 1) => q.2 0) p (dirT (Fin 1))
      = ν * heatLap (Fin 1) (fun q : Spacetime (Fin 1) => q.2 0) p := by
  have hzero (j : Fin 1) : fderiv ℝ (fun q : Spacetime (Fin 1) =>
      fderiv ℝ (fun r : Spacetime (Fin 1) => r.2 0) q (dirS (Fin 1) j)) p (dirS (Fin 1) j) = 0 := by
    have hj : (fun q : Spacetime (Fin 1) =>
        fderiv ℝ (fun r : Spacetime (Fin 1) => r.2 0) q (dirS (Fin 1) j))
      = (fun _q : Spacetime (Fin 1) => (dirS (Fin 1) j).2 0) :=
      funext fun q => coordAmp_fderiv q (dirS (Fin 1) j)
    rw [hj]
    have hc := (hasFDerivAt_const (𝕜 := ℝ) ((dirS (Fin 1) j).2 0) p).fderiv
    rw [hc]
    simp
  have hsum : heatLap (Fin 1) (fun q : Spacetime (Fin 1) => q.2 0) p = 0 := by
    show ∑ j : Fin 1, fderiv ℝ (fun q : Spacetime (Fin 1) =>
        fderiv ℝ (fun r : Spacetime (Fin 1) => r.2 0) q (dirS (Fin 1) j)) p (dirS (Fin 1) j) = 0
    exact ((Finset.sum_congr rfl fun j _ => hzero j).trans Finset.sum_const_zero)
  have h0 : fderiv ℝ (fun q : Spacetime (Fin 1) => q.2 0) p (dirT (Fin 1)) = 0 := by
    rw [coordAmp_fderiv]
    rfl
  rw [h0, hsum]
  ring

/-- `coordAmp` is not strictly positive anywhere on the hyperplane. -/
theorem coordAmp_not_pos : ¬ (∀ p : Spacetime (Fin 1), 0 < (p : Spacetime (Fin 1)).2 0) := by
  intro h
  exact lt_irrefl 0 (h (0, 0))

/-- The log of `coordAmp` is not smooth: it is `Real.log` along the spatial
axis, which is not differentiable at `0`. -/
theorem coordAmp_not_log_smooth :
    ¬ContDiff ℝ ⊤ (fun p : Spacetime (Fin 1) => Real.log (p.2 0)) := by
  intro h
  have he : ContDiff ℝ ⊤ (fun x : ℝ => ((0 : ℝ), fun _ : Fin 1 => x)) :=
    ContDiff.prodMk contDiff_const (contDiff_pi.2 fun _ => contDiff_id)
  have hcomp : DifferentiableAt ℝ
      (fun x : ℝ => Real.log (((fun y : ℝ => ((0 : ℝ), fun _ : Fin 1 => y)) x).2 0)) 0 :=
    ((h.comp he).differentiable (by simp)).differentiableAt
  have hdef : (fun x : ℝ => Real.log (((fun y : ℝ => ((0 : ℝ), fun _ : Fin 1 => y)) x).2 0))
      = Real.log := by
    funext x
    rfl
  rw [hdef] at hcomp
  exact ((Real.differentiableAt_log_iff (x := 0)).mp hcomp) rfl

/-- **R1 sharpness.**  There is a smooth global heat solution that admits no
log transport at all: blanket positivity is exactly the obstruction, and the
`ε`-exhaustion of §5 is the residual removal, not a convenience. -/
theorem colehopf_positivity_sharp (ν : ℝ) :
    ∃ θ : Spacetime (Fin 1) → ℝ,
      (∀ p, fderiv ℝ θ p (dirT (Fin 1)) = ν * heatLap (Fin 1) θ p) ∧
      ¬ (∀ p, 0 < θ p) ∧ ¬ ContDiff ℝ ⊤ (fun p => Real.log (θ p)) :=
  ⟨fun p => p.2 0, coordAmp_heat ν, coordAmp_not_pos, coordAmp_not_log_smooth⟩
end Navier.Analysis
