import Mathlib

/-!
# Smooth wavefunctions and singular Madelung velocity

Units are chosen so that hbar/m = 1. The plane is identified with C.
The current is constructed from the actual real Frechet derivatives of the
wavefunction. The explicit field psi(z)=z is smooth, including its zero, while
its decoded velocity is unbounded in every punctured neighborhood of that zero.
It also satisfies the stationary free Schrodinger equation. This is not a
finite-energy global GP or Navier--Stokes solution.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.QuantumVortexRegularity

open Complex
open scoped ContDiff

def density (ψ : ℂ → ℂ) (z : ℂ) : ℝ := Complex.normSq (ψ z)

/-- The two components of Im(conj(psi) grad psi), using real derivatives. -/
def current (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ⟨(starRingEnd ℂ (ψ z) * fderiv ℝ ψ z 1).im,
    (starRingEnd ℂ (ψ z) * fderiv ℝ ψ z Complex.I).im⟩

/-- Physical use is restricted to nonzero density. Lean's totalized division
does not supply a physical value at a node. -/
def velocity (ψ : ℂ → ℂ) (z : ℂ) : ℂ := current ψ z / (density ψ z : ℂ)

/-- A pointwise Madelung pairing controls velocity by the wavefunction's
logarithmic derivative. This applies in any real inner-product-space dimension. -/
theorem norm_le_of_madelung_pairing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E) (ψ : ℂ) (D : E →L[ℝ] ℂ) (κ : ℝ)
    (hψ : ψ ≠ 0)
    (hdecode : ∀ d : E, inner ℝ u d = κ * (D d / ψ).im) :
    ‖u‖ ≤ |κ| * ‖D‖ / ‖ψ‖ := by
  by_cases hu : u = 0
  · subst u
    simpa using div_nonneg (mul_nonneg (abs_nonneg κ) (norm_nonneg D)) (norm_nonneg ψ)
  have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hψ_norm : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hinner := hdecode u
  rw [real_inner_self_eq_norm_sq] at hinner
  have hquad :
      ‖u‖ * ‖u‖ ≤ (|κ| * ‖D‖ / ‖ψ‖) * ‖u‖ := by
    calc
      ‖u‖ * ‖u‖ = |‖u‖ ^ 2| := by
        rw [pow_two, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      _ = |κ * (D u / ψ).im| := congrArg abs hinner
      _ = |κ| * |(D u / ψ).im| := abs_mul _ _
      _ ≤ |κ| * ‖D u / ψ‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg κ)
      _ = |κ| * (‖D u‖ / ‖ψ‖) := by rw [norm_div]
      _ ≤ |κ| * ((‖D‖ * ‖u‖) / ‖ψ‖) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (D.le_opNorm u) hψ_norm.le) (abs_nonneg κ)
      _ = (|κ| * ‖D‖ / ‖ψ‖) * ‖u‖ := by
        field_simp
  exact le_of_mul_le_mul_right hquad hu_norm

/-- The planar decoder is exactly the imaginary logarithmic derivative paired
with a direction; the derivative is the actual real Fréchet derivative. -/
theorem inner_velocity_eq_im_fderiv_div
    (ψ : ℂ → ℂ) (z d : ℂ) :
    inner ℝ (velocity ψ z) d = (fderiv ℝ ψ z d / ψ z).im := by
  have hd : d = d.re • (1 : ℂ) + d.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hd, map_add, map_smul, map_smul]
  simp [velocity, current, density, Complex.inner, Complex.div_re, Complex.div_im,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  field_simp
  ring

/-- Pointwise control of the planar decoder by the operator norm of the actual
real Fréchet derivative. -/
theorem velocity_norm_le_fderiv (ψ : ℂ → ℂ) (z : ℂ) (hz : ψ z ≠ 0) :
    ‖velocity ψ z‖ ≤ ‖fderiv ℝ ψ z‖ / ‖ψ z‖ := by
  simpa using norm_le_of_madelung_pairing (velocity ψ z) (ψ z) (fderiv ℝ ψ z) 1 hz
    (fun d => by simpa using inner_velocity_eq_im_fderiv_div ψ z d)

theorem density_smooth {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (density ψ) := by
  have h : density ψ = fun z => (ψ z).re ^ 2 + (ψ z).im ^ 2 := by
    funext z
    simp [density, Complex.normSq_apply, pow_two]
  rw [h]
  exact ((Complex.reCLM.contDiff.comp hψ).pow 2).add
    ((Complex.imCLM.contDiff.comp hψ).pow 2)

theorem current_smooth {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (current ψ) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ ψ z 1) := hd.clm_apply contDiff_const
  have hi : ContDiff ℝ ∞ (fun z => fderiv ℝ ψ z Complex.I) := hd.clm_apply contDiff_const
  have hc : ContDiff ℝ ∞ (fun z => starRingEnd ℂ (ψ z)) :=
    Complex.conjCLE.contDiff.comp hψ
  have hx := Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp (hc.mul h1))
  have hy := Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp (hc.mul hi))
  have he : current ψ = fun z =>
      ((starRingEnd ℂ (ψ z) * fderiv ℝ ψ z 1).im : ℂ) +
        ((starRingEnd ℂ (ψ z) * fderiv ℝ ψ z Complex.I).im : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;> simp [current]
  rw [he]
  exact hx.add (hy.mul contDiff_const)

/-- Away from nodes, the actual Madelung decoder preserves smoothness. -/
theorem velocity_smoothAt_of_nonzero {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    {z : ℂ} (hz : ψ z ≠ 0) : ContDiffAt ℝ ∞ (velocity ψ) z := by
  unfold velocity
  simp only [div_eq_mul_inv]
  exact (current_smooth hψ).contDiffAt.mul
    ((Complex.ofRealCLM.contDiff.comp (density_smooth hψ)).contDiffAt.inv
      (Complex.ofReal_ne_zero.mpr (mt Complex.normSq_eq_zero.mp hz)))

def unitVortex : ℂ → ℂ := fun z => z

theorem unitVortex_smooth : ContDiff ℝ ∞ unitVortex := contDiff_id

theorem unitVortex_zero_iff (z : ℂ) : unitVortex z = 0 ↔ z = 0 := Iff.rfl

private theorem unitVortex_fderiv (z : ℂ) :
    fderiv ℝ unitVortex z = ContinuousLinearMap.id ℝ ℂ :=
  fderiv_fun_id

/-- The ordinary two-dimensional spatial Laplacian, expressed with actual
real Frechet derivatives in the orthonormal directions 1 and i. -/
def planeLaplacian (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  fderiv ℝ (fun w => fderiv ℝ ψ w 1) z 1 +
    fderiv ℝ (fun w => fderiv ℝ ψ w Complex.I) z Complex.I

theorem unitVortex_harmonic (z : ℂ) : planeLaplacian unitVortex z = 0 := by
  simp [planeLaplacian, unitVortex_fderiv]

/-- The smooth unit-vortex field is an exact stationary free Schrodinger
solution, i*d_t psi = -(1/2)*Delta psi. No finite-energy assertion is made. -/
theorem unitVortex_freeSchrodinger (t : ℝ) (z : ℂ) :
    Complex.I * deriv (fun _ : ℝ => unitVortex z) t =
      -(1 / 2 : ℂ) * planeLaplacian unitVortex z := by
  simp [unitVortex_harmonic]

theorem unitVortex_density (z : ℂ) : density unitVortex z = z.re ^ 2 + z.im ^ 2 := by
  simp [density, unitVortex, Complex.normSq_apply, pow_two]

theorem unitVortex_current (z : ℂ) : current unitVortex z = Complex.I * z := by
  apply Complex.ext <;>
    simp [current, unitVortex_fderiv, unitVortex, Complex.mul_re, Complex.mul_im]

theorem unitVortex_velocity_real (r : ℝ) (hr : r ≠ 0) :
    velocity unitVortex (r : ℂ) = Complex.I / (r : ℂ) := by
  unfold velocity
  rw [unitVortex_current, unitVortex_density]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_pow (by decide : 2 ≠ 0), add_zero,
    Complex.ofReal_pow]
  have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  field_simp

theorem unitVortex_velocity_norm_real (r : ℝ) (hr : 0 < r) :
    ‖velocity unitVortex (r : ℂ)‖ = 1 / r := by
  rw [unitVortex_velocity_real r hr.ne']
  simp [abs_of_pos hr]

/-- Arbitrarily large decoded velocity occurs arbitrarily close to the smooth
wavefunction's core. All witnesses have strictly positive density. -/
theorem unitVortex_velocity_unbounded_at_core
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    ∃ z : ℂ, 0 < ‖z‖ ∧ ‖z‖ < ε ∧ 0 < density unitVortex z ∧
      M < ‖velocity unitVortex z‖ := by
  let r : ℝ := min (ε / 2) (1 / (M + 1))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrε : r < ε := (min_le_left _ _).trans_lt (by linarith)
  have hrecip : M + 1 ≤ 1 / r := by
    have h := one_div_le_one_div_of_le hr (min_le_right (ε / 2) (1 / (M + 1)))
    simpa using h
  refine ⟨(r : ℂ), ?_, ?_, ?_, ?_⟩
  · simpa [abs_of_pos hr] using hr
  · simpa [abs_of_pos hr] using hrε
  · rw [unitVortex_density]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_pow (by decide : 2 ≠ 0), add_zero]
    exact sq_pos_of_pos hr
  · rw [unitVortex_velocity_norm_real r hr]
    linarith

/-- Smooth wavefunction, density, and current do not imply local boundedness
of the Madelung velocity at a node. -/
theorem smooth_wavefunction_does_not_bound_decoded_velocity :
    ∃ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ (density ψ) ∧
      ContDiff ℝ ∞ (current ψ) ∧ ψ 0 = 0 ∧
      ∀ ε : ℝ, 0 < ε → ∀ M : ℝ, 0 ≤ M →
        ∃ z : ℂ, 0 < ‖z‖ ∧ ‖z‖ < ε ∧ 0 < density ψ z ∧
          M < ‖velocity ψ z‖ := by
  exact ⟨unitVortex, unitVortex_smooth, density_smooth unitVortex_smooth,
    current_smooth unitVortex_smooth, rfl, fun _ hε _ hM =>
      unitVortex_velocity_unbounded_at_core hε hM⟩

end Navier.Analysis.QuantumVortexRegularity
