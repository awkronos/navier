import Navier.Analysis.EnergyPointwiseBalance

/-!
# Coordinatewise official PDE bridge

`Navier/Problem.lean` states the momentum equation with total Frechet
derivatives on `Space = Fin 3 → ℝ`, while Fefferman's clauses (1)--(2) are
written coordinatewise: `∂u_i/∂t + ∑_j u_j ∂u_i/∂x_j = ν Δu_i − ∂p/∂x_i + f_i`
and `∑_i ∂u_i/∂x_i = 0`.  This file closes the `problemFrechetCoordinatePDEEquivalence`
residual between those two encodings.

Official partial derivatives are taken literally: `∂g/∂x_j` is the classical
line derivative `lineDeriv ℝ g x (basisVector j)` (the one-dimensional
derivative of `s ↦ g (x + s • e_j)` at `0`), and `∂/∂t` on nonnegative time is
the one-sided `derivWithin` on `Set.Ici 0`, matching the convention already
fixed by `timeDerivative`.  Under the smoothness carried by
`IsClassicalSolution`, every Frechet-encoded operator agrees with its
coordinatewise official counterpart, and the two momentum systems are
equivalent clause by clause.

The remaining representation content of the residual after this file is only
the choice of `derivWithin` on `Set.Ici 0` as the reading of Fefferman's
one-sided time derivative, which `Navier/Problem.lean` already documents.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CoordinatePDEBridge

open Navier
open Navier.Analysis.EnergyViscousDissipation
open Navier.Analysis.EnergyPointwiseBalance
open scoped ContDiff BigOperators

/-- Official coordinatewise spatial partial `∂g/∂x_j`: the classical line
derivative along the `j`th coordinate direction. -/
def spatialPartial (j : Fin 3) (g : Space → ℝ) (x : Space) : ℝ :=
  lineDeriv ℝ g x (basisVector j)

/-- Official one-sided coordinatewise time partial `∂u_i/∂t` on nonnegative
time. -/
def timePartial (u : VelocityEvolution) (t : ℝ) (x : Space) (i : Fin 3) : ℝ :=
  derivWithin (fun s : ℝ => u s x i) (Set.Ici 0) t

/-- Fefferman's coordinatewise momentum equations (1). -/
def OfficialCoordinateEquations (ν : ℝ) (f : ForceField)
    (u : VelocityEvolution) (p : PressureEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ∀ i : Fin 3,
    timePartial u t x i +
        ∑ j : Fin 3, u t x j * spatialPartial j (fun y => u t y i) x =
      ν * (∑ j : Fin 3,
          spatialPartial j (fun y => spatialPartial j (fun z => u t z i) y) x)
        - spatialPartial i (p t) x + f t x i

/-- Fefferman's coordinatewise incompressibility (2). -/
def OfficialCoordinateDivergenceFree (u : VelocityEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
    ∑ i : Fin 3, spatialPartial i (fun y => u t y i) x = 0

/-- At a point of differentiability, the official coordinatewise partial of a
component slice is the matching entry of the total Frechet derivative. -/
theorem spatialPartial_slice_eq (g : Space → Space) {x : Space}
    (hg : DifferentiableAt ℝ g x) (i j : Fin 3) :
    spatialPartial j (fun y => g y i) x = fderiv ℝ g x (basisVector j) i := by
  have hgi : DifferentiableAt ℝ (fun y => g y i) x :=
    differentiableAt_pi.1 hg i
  rw [spatialPartial, hgi.lineDeriv_eq_fderiv, fderiv_apply hg i]
  rfl

/-- The official scalar partial agrees with the Frechet derivative for scalar
fields. -/
theorem spatialPartial_eq_fderiv (g : Space → ℝ) {x : Space}
    (hg : DifferentiableAt ℝ g x) (j : Fin 3) :
    spatialPartial j g x = fderiv ℝ g x (basisVector j) :=
  hg.lineDeriv_eq_fderiv

/-- The official one-sided time partial is the matching component of the
repository's Frechet-within time derivative. -/
theorem timePartial_eq_timeDerivative (u : VelocityEvolution) {t : ℝ}
    (ht : 0 ≤ t) (x : Space)
    (hdiff : DifferentiableWithinAt ℝ (fun s : ℝ => u s x) (Set.Ici 0) t)
    (i : Fin 3) :
    timePartial u t x i = timeDerivative u t x i := by
  have huniq : UniqueDiffWithinAt ℝ (Set.Ici (0 : ℝ)) t :=
    uniqueDiffOn_Ici 0 t ht
  show derivWithin (fun s : ℝ => u s x i) (Set.Ici 0) t
      = fderivWithin ℝ (fun s : ℝ => u s x) (Set.Ici 0) t 1 i
  rw [show derivWithin (fun s : ℝ => u s x i) (Set.Ici 0) t
      = fderivWithin ℝ (fun s : ℝ => u s x i) (Set.Ici 0) t 1 from rfl,
    fderivWithin_apply hdiff huniq i]
  rfl

/-- The convective term is the official weighted sum of first partials. -/
theorem convection_eq_official_sum (u : VelocityEvolution) {t : ℝ} {x : Space}
    (hslice : DifferentiableAt ℝ (u t) x) (i : Fin 3) :
    convection u t x i =
      ∑ j : Fin 3, u t x j * spatialPartial j (fun y => u t y i) x := by
  have hexp : convection u t x =
      ∑ j : Fin 3, u t x j • fderiv ℝ (u t) x (basisVector j) := by
    unfold convection spatialDerivative
    conv_lhs =>
      rw [show u t x = ∑ j : Fin 3, u t x j • basisVector j from by
        simpa [basisVector] using pi_eq_sum_univ' (u t x)]
    rw [map_sum]
    simp
  rw [hexp, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, spatialPartial_slice_eq (u t) hslice i j]

/-- The componentwise Laplacian is the official sum of repeated coordinate
partials. -/
theorem laplacian_eq_official_sum (u : VelocityEvolution) {t : ℝ} {x : Space}
    (hu : ContDiff ℝ ∞ (u t)) (i : Fin 3) :
    laplacian u t x i =
      ∑ j : Fin 3,
        spatialPartial j (fun y => spatialPartial j (fun z => u t z i) y) x := by
  unfold laplacian
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hDj : Differentiable ℝ (coordinateDerivativeField (u t) j) :=
    differentiable_coordinateDerivativeField_of_contDiff (u t) hu j
  have hinner : (fun y => spatialPartial j (fun z => u t z i) y)
      = fun y => coordinateDerivativeField (u t) j y i := by
    funext y
    exact spatialPartial_slice_eq (u t) (hu.differentiable (by simp) y) i j
  rw [hinner,
    spatialPartial_slice_eq (coordinateDerivativeField (u t)  j) (hDj x) i j]
  rfl

/-- The pressure-gradient component is the official pressure partial. -/
theorem pressureGradient_eq_official (p : PressureEvolution) {t : ℝ}
    {x : Space} (hp : DifferentiableAt ℝ (p t) x) (i : Fin 3) :
    pressureGradient p t x i = spatialPartial i (p t) x := by
  unfold pressureGradient spatialPartial
  exact hp.lineDeriv_eq_fderiv.symm

/-- The Frechet divergence is the official coordinatewise divergence. -/
theorem divergence_eq_official_sum (u : VelocityEvolution) {t : ℝ} {x : Space}
    (hslice : DifferentiableAt ℝ (u t) x) :
    divergence u t x = ∑ i : Fin 3, spatialPartial i (fun y => u t y i) x := by
  unfold divergence spatialDerivative
  exact Finset.sum_congr rfl fun i _ =>
    (spatialPartial_slice_eq (u t) hslice i i).symm

/-- The static divergence of an initial datum is the official coordinatewise
divergence. -/
theorem staticDivergence_eq_official_sum (f : VelocityField) {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    staticDivergence f x = ∑ i : Fin 3, spatialPartial i (fun y => f y i) x := by
  unfold staticDivergence
  exact Finset.sum_congr rfl fun i _ =>
    (spatialPartial_slice_eq f hf i i).symm

/-- **The `problemFrechetCoordinatePDEEquivalence` bridge, momentum half.**
Under the smoothness carried by the classical-solution predicate, the
repository's Frechet momentum equation and Fefferman's coordinatewise
equations (1) hold simultaneously. -/
theorem satisfiesNavierStokes_iff_officialCoordinateEquations
    (ν : ℝ) (f : ForceField) (u : VelocityEvolution) (p : PressureEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u)
    (hp : SmoothPressureOnNonnegativeTime p) :
    SatisfiesNavierStokes ν f u p ↔ OfficialCoordinateEquations ν f u p := by
  unfold SatisfiesNavierStokes OfficialCoordinateEquations
  refine forall_congr' fun t => ?_
  refine forall_congr' fun ht => ?_
  refine forall_congr' fun x => ?_
  have hslice : ContDiff ℝ ∞ (u t) :=
    contDiff_spatialSlice_of_smoothVelocity u hu t ht
  have hpslice : ContDiff ℝ ∞ (p t) :=
    contDiff_spatialSlice_of_smoothPressure p hp t ht
  have hDA : DifferentiableAt ℝ (u t) x := hslice.differentiable (by simp) x
  have hpDA : DifferentiableAt ℝ (p t) x := hpslice.differentiable (by simp) x
  have htime : DifferentiableWithinAt ℝ (fun s : ℝ => u s x) (Set.Ici 0) t :=
    differentiableWithinAt_timeSlice_of_smoothVelocity u hu t ht x
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← timePartial_eq_timeDerivative u ht x htime i,
    convection_eq_official_sum u hDA i,
    laplacian_eq_official_sum u hslice i,
    pressureGradient_eq_official p hpDA i]

/-- **The `problemFrechetCoordinatePDEEquivalence` bridge, divergence half.**
Under velocity smoothness, Frechet incompressibility and Fefferman's
coordinatewise clause (2) hold simultaneously. -/
theorem incompressible_iff_officialCoordinateDivergenceFree
    (u : VelocityEvolution) (hu : SmoothVelocityOnNonnegativeTime u) :
    Incompressible u ↔ OfficialCoordinateDivergenceFree u := by
  unfold Incompressible OfficialCoordinateDivergenceFree
  refine forall_congr' fun t => ?_
  refine forall_congr' fun ht => ?_
  refine forall_congr' fun x => ?_
  have hslice : ContDiff ℝ ∞ (u t) :=
    contDiff_spatialSlice_of_smoothVelocity u hu t ht
  rw [divergence_eq_official_sum u (hslice.differentiable (by simp) x)]

/-- A Schwartz initial datum is divergence-free in the repository encoding
iff it satisfies Fefferman's literal coordinatewise divergence clause. -/
theorem divergenceFreeInitial_iff_official (u₀ : SchwartzVelocity) :
    DivergenceFreeInitial u₀ ↔
      ∀ x : Space, ∑ i : Fin 3, spatialPartial i (fun y => u₀ y i) x = 0 := by
  unfold DivergenceFreeInitial
  refine forall_congr' fun x => ?_
  rw [staticDivergence_eq_official_sum (fun y => u₀ y)
    (u₀.smooth'.differentiable (by simp) x)]

/-- Every classical solution satisfies Fefferman's coordinatewise momentum
equations (1). -/
theorem IsClassicalSolution.officialCoordinateEquations
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (sol : IsClassicalSolution ν f u₀ u p) :
    OfficialCoordinateEquations ν f u p :=
  (satisfiesNavierStokes_iff_officialCoordinateEquations ν f u p
    sol.velocity_smooth sol.pressure_smooth).1 sol.equation

/-- Every classical solution satisfies Fefferman's coordinatewise
incompressibility clause (2). -/
theorem IsClassicalSolution.officialCoordinateDivergenceFree
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (sol : IsClassicalSolution ν f u₀ u p) :
    OfficialCoordinateDivergenceFree u :=
  (incompressible_iff_officialCoordinateDivergenceFree u
    sol.velocity_smooth).1 sol.incompressible

end Navier.Analysis.CoordinatePDEBridge
