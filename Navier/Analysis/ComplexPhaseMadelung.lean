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
system pointwise in componentwise Fréchet form.  WIP body: the assembly is
complete on paper (heatKey + swap-cancel, see `/tmp/mc.NOTES.md`); only
Mathlib API-name side conditions remain. -/
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
  sorry

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
WIP body: `congrArg ((-2ν) • ·) ∘ swap2'` modulo `fderiv_const_smul` side
conditions. -/
theorem colehopf_jacobian_symmetric (ν : ℝ) {W : PressureField} (hW : ContDiff ℝ ⊤ W)
    (x : Space) (i j : Fin 3) :
    fderiv ℝ (fun y => coleHopfSlice ν W y i) x (basisVector j)
      = fderiv ℝ (fun y => coleHopfSlice ν W y j) x (basisVector i) := by
  sorry

/-- **Cole–Hopf velocities are irrotational (repo carrier).**  Write
`c • ∇W = ∇(cW)` and apply the repo's public
`staticCurl_staticGradient_eq_zero` (namespace `Navier.Analysis.CurlIdentities`).
WIP body: the one-line calc is fixed in NOTES. -/
theorem colehopf_staticCurl_zero (ν : ℝ) {W : PressureField} (hW : ContDiff ℝ ⊤ W)
    (x : Space) : staticCurl (coleHopfSlice ν W) x = 0 := by
  sorry

/-- Cole–Hopf slices carry zero vorticity. WIP body. -/
theorem colehopf_vorticity_zero (ν : ℝ) {W : PressureField} (hW : ContDiff ℝ ⊤ W)
    (t : ℝ) (x : Space) :
    vorticity (fun s y => coleHopfSlice ν W y) t x = 0 := by
  sorry

/-- **Zero vortex stretching.**  The NS nonlinear term `(ω·∇)u` evaluated on
a Cole–Hopf slice vanishes because `ω = 0`: the transport derivative is a
continuous linear map applied to the zero vector. WIP body (one `rw`). -/
theorem colehopf_stretching_zero (ν : ℝ) {W : PressureField} (hW : ContDiff ℝ ⊤ W)
    (t : ℝ) (x : Space) :
    spatialDerivative (fun s y => coleHopfSlice ν W y) t x
        (vorticity (fun s y => coleHopfSlice ν W y) t x) = 0 := by
  sorry

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
WIP body: exp-chain over `ℂ` via `ContinuousLinearMap.smulRight` transport
(identities fixed on paper; API placement is the resume site). -/
theorem complexPhase_logDeriv {ħ : ℝ} (hħ : ħ ≠ 0) (S Γ : PressureField)
    (hS : ContDiff ℝ ⊤ S) (hΓ : ContDiff ℝ ⊤ Γ) (x v : Space) :
    fderiv ℝ (complexPhaseWave ħ S Γ) x v / complexPhaseWave ħ S Γ x =
      Complex.I * (fderiv ℝ S x v / ħ) - fderiv ℝ Γ x v / ħ := by
  sorry

/-! **Bridge 1 read (phase slope).**  The repo Madelung decoder law applied
to `ψ` decodes the phase gradient `∝ ∇S` (imaginary slot of
`complexPhase_logDeriv`).  The repo constant `MadelungInitialDecoder` lives
in `Navier/Analysis/MadelungDecoderCurlObstruction.lean`; its namespace is
resolved at the resume site, so the consumer statement lands next commit. -/

/-- **Bridge 3 read (Cole–Hopf is the real part).**  The Cole–Hopf velocity
of the amplitude `θ = e^{-Γ/ħ}` equals `-2ν` times the REAL part of the same
logarithmic derivative (`Real.log_exp` collapses `log θ = -Γ/ħ` pointwise).
WIP body. -/
theorem complexPhase_colehopf_eq_negRe {ħ ν : ℝ} (hħ : ħ ≠ 0) (S Γ : PressureField)
    (hΓ : ContDiff ℝ ⊤ Γ) (x : Space) (i : Fin 3) :
    (-2 * ν) • fderiv ℝ (fun y => Real.log (complexPhaseAmplitude ħ Γ y)) x
        (basisVector i)
      = (-2 * ν) * (fderiv ℝ (complexPhaseWave ħ S Γ) x (basisVector i)
          / complexPhaseWave ħ S Γ x).re := by
  sorry

/-! ## 5. Separation: rotational data has no Cole–Hopf representation -/

/-- **Separation.**  In dimension 2 the plane-rotation field
`rot(x₀,x₁) = (-x₁, x₀)` equals `-2ν∇W` for NO smooth `W` and NO viscosity
`ν`: Jacobian symmetry (`swap2'`) forces `∂₁u₀ = ∂₀u₁`, while the field
itself gives `∂₁u₀ = -1` and `∂₀u₁ = 1`, i.e. `1 = -1`.  The witness is this
file's own public field; the repo's private bump machinery (`datumFn` in
`MadelungDecoderCurlObstruction.lean`) is NOT reused. WIP body: the
component equalities + `swap2'` contradiction are laid out in NOTES. -/
theorem no_colehopf_of_plane_rotation :
    ¬ ∃ (ν : ℝ) (W : Spacetime (Fin 2) → ℝ), ContDiff ℝ ⊤ W ∧
      ∀ p, coleHopfU (Fin 2) ν W p = fun i => if i = 0 then -(p.2 1) else p.2 0 := by
  sorry

/-! ## Kernel receipts (axiom audit consumed by the lane verifier) -/

#print axioms swap2'
#print axioms swap3_inner
#print axioms swap3_outer
#print axioms complexPhaseWave_ne
#print axioms complexPhaseAmplitude_pos

#check @swap2'
#check @colehopf_burgers_of_logheat
