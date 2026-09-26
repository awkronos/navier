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
* The heat hypothesis is taken in the log variable `W`.  Converting a
  pre-given positive heat solution `θ` into `W = log θ` is the chain-rule
  equivalence `∂t θ = νΔθ ↔ ∂t logθ = ν(Δlogθ + ‖∇logθ‖²)`; it is a genuine
  second-derivative product-rule expansion and is stated as the residual in
  the module footer rather than claimed.
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
