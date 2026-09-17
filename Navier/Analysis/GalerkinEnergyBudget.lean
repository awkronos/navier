/-
W7O-NV2 (O50 swarm, 2026-09-16): the uniform modal enstrophy budget.

This file closes the single named analytic residual `henst` — a uniform-in-m
time-integrated enstrophy budget for the actual projected Galerkin flow — from
the banked abstract energy–dissipation identity `dissipation_integral_le_forward`
plus the certified Stokes/enstrophy identification `stokesOperator_inner_eq_enstrophy`,
Bessel's inequality `initialCoefficients_norm_sq_le`, and convection skew-symmetry
`convectionOperator_inner_self`.  Nothing here assumes the bound it produces.

The budget is consumed twice in-slice:

* `timeEquicontinuous_modalApprox_of_flow` — feeds the certified leaf
  `galerkinCoefficientFlow_timeEquicontinuous` [GalerkinModeData] through
  `timeEquicontinuous_of_coefficientDisplacement` [GalerkinBasis], turning the
  time-equicontinuity conclusion of the mode-data assembly into a consequence
  of the ODE data alone (replacing its `hderivative` + `henstrophy_budget`
  hypothesis pair).
* `spaceEquicontinuous_modalApprox_of_flow` — feeds
  `spaceEquicontinuous_of_modalFamily` [GalerkinSpaceEquicontinuity], turning
  the `hspace` residual hypothesis of the same assembly into a consequence of
  the ODE data alone.

With both, `galerkinModeData_of_modalFlow` repackages `GalerkinModeData` from
the ODE data plus the single surviving analytic input `hprojectedWeak` — the
weak-consistency (defect/commutator) bookkeeping routed through
`modalFlow_fixedTest_projectedResidual_tendsto_of_commutators` and
`GalerkinWeakConsistency`.

Route placement (docs/BARRIERS.md): the R4/R9 compactness row and ledger F-013's
permitted successor ("prove strong local compactness or carry and eliminate a
defect measure") — the budget is the Riesz–Kolmogorov/Aubin–Lions input that the
already-certified `aubin_lions_l2loc_compactness` and the spatial equicontinuity
leaf consume.  It is the classical Leray modal energy inequality [LERAY1934 §20;
Temam III §3], instantiated for this repository's concrete projected operators;
it is not the F-001 energy-size-to-critical-norm claim (nothing here controls a
critical norm), and it does not touch the curl-projection-commutation route
kernel-refuted at `ebefa7a` (the budget uses only the diagonal skew-symmetry and
Stokes positivity, both projection-stable).

References: [LERAY1934]; Temam, *Navier–Stokes Equations*, Ch. III §3;
Robinson–Rodrigo–Sadowski, Ch. 4.
-/

import Navier.Analysis.GalerkinBasis
import Navier.Analysis.GalerkinModeData
import Navier.Analysis.GalerkinSpaceEquicontinuity
import Navier.Analysis.EnergyDissipation

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.GalerkinEnergyBudget

open Navier
open Navier.Analysis.LerayWeak
open Navier.Analysis.GalerkinBasis
open Navier.Analysis.GalerkinSpaceEquicontinuity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity
open Navier.Analysis.EnergyDissipation
open Set MeasureTheory Filter
open scoped BigOperators

/-- The datum's official Euclidean energy `∫ Σᵢ (u₀ᵢ)²` — the exact constant
the `GalerkinModeData` energy fields carry. -/
def datumEnergy (u₀ : SchwartzVelocity) : ℝ :=
  ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2

theorem datumEnergy_nonneg (u₀ : SchwartzVelocity) : 0 ≤ datumEnergy u₀ :=
  integral_nonneg fun _x => Finset.sum_nonneg fun _i _ => pow_two_nonneg _

/-- `schwartzL2Inner u u = datumEnergy u`: the pairing unfolds to the official
sum-of-squares integral. -/
theorem datumEnergy_eq_schwartzL2Inner (u : SchwartzVelocity) :
    datumEnergy u = schwartzL2Inner u u := by
  unfold datumEnergy schwartzL2Inner
  apply integral_congr_ae
  filter_upwards with x
  rw [officialInner_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [pow_two])

/-- **Uniform modal enstrophy budget at the initial coefficient norm** — the
Leray dissipation inequality for the concrete projected Galerkin flow: every
mode count integrates enstrophy over `(0, T]` at most `‖c m 0‖²/(2ν)`.

Proof is `dissipation_integral_le_forward` fed by the certified concrete data:
`A := W.stokesOperator m` (a continuous linear operator, so the dissipation
integrand is continuous along the flow), skew-symmetry
`convectionOperator_inner_self`, and the exact identification
`stokesOperator_inner_eq_enstrophy`.  No hypothesis beyond the ODE property is
used. -/
theorem coefficientEnstrophy_budget (W : GalerkinBasisFamily)
    {ν : ℝ} (_hν : 0 < ν)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Set.Ioc (0 : ℝ) T, W.coefficientEnstrophy (c m t)) ≤
      ‖c m 0‖ ^ 2 / (2 * ν) := by
  have hc' : ContinuousOn (c m) (Set.Ici (0 : ℝ)) :=
    fun t ht => (hc m t ht).continuousWithinAt
  have hA_cont : ContinuousOn (fun t => W.stokesOperator m (c m t))
      (Set.Ici (0 : ℝ)) :=
    (W.stokesOperator m).continuous.comp_continuousOn hc'
  have hinner_cont : ContinuousOn
      (fun t => (inner ℝ (W.stokesOperator m (c m t)) (c m t) : ℝ))
      (Set.Ici (0 : ℝ)) := hA_cont.inner hc'
  have hform : (∫ t in Set.Ioc (0 : ℝ) T,
      (inner ℝ (W.stokesOperator m (c m t)) (c m t) : ℝ)) ≤
      ‖c m 0‖ ^ 2 / (2 * ν) :=
    dissipation_integral_le_forward _hν (W.stokesOperator m)
      (W.convectionOperator m) (c m)
      (fun t => -(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
      (hc m) (fun _ _ => rfl) (fun t _ => convectionOperator_inner_self W m (c m t))
      hinner_cont hT
  have hrew : ∀ t, (inner ℝ (W.stokesOperator m (c m t)) (c m t) : ℝ) =
      W.coefficientEnstrophy (c m t) :=
    fun t => stokesOperator_inner_eq_enstrophy W m (c m t)
  rw [setIntegral_congr_fun measurableSet_Ioc fun _t _ht => (hrew _t).symm]
  exact hform

/-- **The initial coefficient norm is budgeted by the datum.** -/
theorem initialFlow_norm_sq_le_datumEnergy (W : GalerkinBasisFamily)
    (u₀ : SchwartzVelocity)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc0 : ∀ m : ℕ, c m 0 = W.initialCoefficients u₀ m)
    (m : ℕ) : ‖c m 0‖ ^ 2 ≤ datumEnergy u₀ := by
  rw [hc0 m, datumEnergy_eq_schwartzL2Inner]
  exact initialCoefficients_norm_sq_le W u₀ m

/-- **The datum constant is uniform in the mode count.**  With the projected
initial condition `c m 0 = W.initialCoefficients u₀ m`, Bessel's inequality
`initialCoefficients_norm_sq_le` turns the per-`m` budget into the single
uniform budget `datumEnergy u₀ / (2 * ν)`. -/
theorem coefficientEnstrophy_budget_of_datum (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν) (u₀ : SchwartzVelocity)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (hc0 : ∀ m : ℕ, c m 0 = W.initialCoefficients u₀ m)
    (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Set.Ioc (0 : ℝ) T, W.coefficientEnstrophy (c m t)) ≤
      datumEnergy u₀ / (2 * ν) := by
  refine le_trans (coefficientEnstrophy_budget W hν c hc m hT) ?_
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ν)
    (by positivity : (0 : ℝ) < 2 * ν)]
  exact mul_le_mul_of_nonneg_right
    (initialFlow_norm_sq_le_datumEnergy W u₀ c hc0 m) (by positivity)

/-- **Time equicontinuity discharged from the ODE data alone.**  The certified
coefficient-level Aubin–Lions leaf `galerkinCoefficientFlow_timeEquicontinuous`
fed by the budget, then transported to the field by
`timeEquicontinuous_of_coefficientDisplacement`.  This replaces the
`hderivative` (uniform projected-vector-field bound) + `henstrophy_budget`
hypothesis pair of `galerkinModeData_of_basis_modalFlow`: the derivative bound
was only a sufficient input for time equicontinuity, and the budget — not the
derivative bound — is what the certified leaf consumes. -/
theorem timeEquicontinuous_modalApprox_of_flow (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν) (u₀ : SchwartzVelocity)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (hc0 : ∀ m : ℕ, c m 0 = W.initialCoefficients u₀ m) :
    TimeEquicontinuous (W.modalApprox c) :=
  timeEquicontinuous_of_coefficientDisplacement W c
    (fun m => continuous_forwardExtend (c m)
      (fun t => -(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
      (hc m))
    (galerkinCoefficientFlow_timeEquicontinuous W hν c hc
      (datumEnergy u₀ / (2 * ν))
      (fun m _T hT => coefficientEnstrophy_budget_of_datum W hν u₀ c hc hc0 m hT))

/-- Realizing forward-extended coefficients as a modal field is the concrete
coefficient field. -/
theorem modalField_coefficientField (W : GalerkinBasisFamily)
    (c' : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m)) (m : ℕ) (a : ℝ) :
    modalField W.finiteModes c' m a =
      W.coefficientField (c' m a) := by
  change (∑ i : Fin m, c' m a i • W.finiteModes m i) = _
  rfl

/-- **Spatial equicontinuity discharged from the ODE data alone.**  The certified
spatial equicontinuity leaf `spaceEquicontinuous_of_modalFamily` fed by the same
budget: on the window `(0, T]` the forward extension is the flow itself, the
modal field is the concrete coefficient field, and its curl energy is
definitionally the budgeted `coefficientEnstrophy`. -/
theorem spaceEquicontinuous_modalApprox_of_flow (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν) (u₀ : SchwartzVelocity)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (hc0 : ∀ m : ℕ, c m 0 = W.initialCoefficients u₀ m) :
    SpaceEquicontinuous (W.modalApprox c) := by
  have hc' : ∀ m : ℕ, Continuous (fun t : ℝ => forwardExtend (c m) t) :=
    fun m => continuous_forwardExtend (c m)
      (fun t => -(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
      (hc m)
  have henst : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      (∫ t in Set.Ioc (0 : ℝ) T,
        ∫ x : Space,
          officialEuclideanNorm (staticCurl (⇑(modalField W.finiteModes
            (fun m => forwardExtend (c m)) m t)) x) ^ 2) ≤
        datumEnergy u₀ / (2 * ν) := by
    intro m T hT
    have hpt : ∀ t : ℝ,
        (∫ x : Space,
            officialEuclideanNorm (staticCurl
              (⇑(modalField W.finiteModes (fun m => forwardExtend (c m)) m t)) x) ^ 2) =
          W.coefficientEnstrophy (forwardExtend (c m) t) := by
      intro t
      rw [modalField_coefficientField W (fun m => forwardExtend (c m)) m t]
      unfold GalerkinBasisFamily.coefficientEnstrophy
      rfl
    have hext : ∀ t : ℝ, 0 ≤ t →
        W.coefficientEnstrophy (forwardExtend (c m) t) =
          W.coefficientEnstrophy (c m t) := by
      intro t ht
      rw [forwardExtend_eq_of_nonneg (c m) ht]
    have hae : ∀ᵐ t ∂(volume : Measure ℝ),
        t ∈ Set.Ioc (0 : ℝ) T →
          (∫ x : Space,
              officialEuclideanNorm (staticCurl (⇑(modalField W.finiteModes
                (fun m => forwardExtend (c m)) m t)) x) ^ 2) =
            W.coefficientEnstrophy (c m t) :=
      Filter.Eventually.of_forall fun t ht => (hpt t).trans (hext t ht.1.le)
    calc ∫ t in Set.Ioc (0 : ℝ) T,
          ∫ x : Space,
            officialEuclideanNorm (staticCurl (⇑(modalField W.finiteModes
              (fun m => forwardExtend (c m)) m t)) x) ^ 2
        _ = ∫ t in Set.Ioc (0 : ℝ) T, W.coefficientEnstrophy (c m t) :=
          setIntegral_congr_ae measurableSet_Ioc hae
        _ ≤ datumEnergy u₀ / (2 * ν) :=
          coefficientEnstrophy_budget_of_datum W hν u₀ c hc hc0 m hT
  have h := spaceEquicontinuous_of_modalFamily W.finiteModes
    (fun m i => W.divergence_free i) (fun m => forwardExtend (c m)) hc'
    (datumEnergy u₀ / (2 * ν)) (div_nonneg (datumEnergy_nonneg u₀) (by positivity))
    henst
  have hid : (fun m t x =>
      modalField W.finiteModes (fun m => forwardExtend (c m)) m t x) =
      W.modalApprox c := by
    funext m t x
    rw [modalField_coefficientField W (fun m => forwardExtend (c m)) m t,
      modalApprox_eq_coefficientField_forwardExtend W c m t]
  rw [← hid]
  exact h

/-- The coefficient energy is uniformly budgeted by the datum along the flow
(restatement of the banked `coefficientFlow_energy_le_data` at the
`datumEnergy` name). -/
theorem coefficientFlow_norm_sq_le_datumEnergy (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν) (u₀ : SchwartzVelocity)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (hc0 : ∀ m : ℕ, c m 0 = W.initialCoefficients u₀ m)
    (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : ‖c m t‖ ^ 2 ≤ datumEnergy u₀ :=
  coefficientFlow_energy_le_data W hν u₀ c hc hc0 m ht

/-- **Reduced mode-data assembly.**  Given a certified divergence-free
Galerkin basis, a viscosity `ν > 0`, a divergence-free Schwartz datum, and an
actual projected coefficient flow, `GalerkinModeData ν u₀` is inhabited modulo
the single named analytic input `hprojectedWeak` — the weak-consistency
(defect/commutator) bookkeeping.  Compared with
`galerkinModeData_of_basis_modalFlow`, this drops the kinetic-bound pair
(`hkin`, `henstrophy_budget`), the uniform projected-vector-field bound
(`hderivative`, `derivativeBound`), and the spatial equicontinuity hypothesis
(`hspace`): all are now derived above from the ODE data.  The energy constant is
the exact datum energy (so `bound_le` is `le_rfl`) and the enstrophy constant is
`datumEnergy u₀ / (2 * ν)`, decoupled from the kinetic bound as the structure's
docstring anticipates for `ν < 1/2`. -/
theorem galerkinModeData_of_modalFlow (W : GalerkinBasisFamily)
    {ν : ℝ} (hν : 0 < ν) (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m)
        (-(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
        (Set.Ici (0 : ℝ)) t)
    (hc0 : ∀ m : ℕ, c m 0 = W.initialCoefficients u₀ m)
    (hprojectedWeak : ∀ φ : DivergenceFreeTestFunction,
      Filter.Tendsto (fun m => weakFormResidual ν (W.proj m u₀) (W.modalApprox c m) φ)
        Filter.atTop (nhds 0)) :
    Nonempty (GalerkinModeData ν u₀) := by
  have hoff : UniformOfficialKineticBound (W.modalApprox c) (datumEnergy u₀) := by
    intro m t ht
    rw [modalApprox_kineticEnergy_eq W c m t, forwardExtend_eq_of_nonneg (c m) ht]
    exact coefficientFlow_energy_le_data W hν u₀ c hc hc0 m ht
  have hjm := galerkinModalApprox_jointlyMeasurable (fun m => m) c
    (fun m t => -(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t))
    hc (fun m => W.finiteModes m)
  have hmeas : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      AEStronglyMeasurable (W.modalApprox c m t) := by
    intro m t _
    exact (hjm m).comp (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable
  have hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      Integrable (fun x : Space => ‖W.modalApprox c m t x‖ ^ 2) :=
    galerkinModalApprox_sq_integrable (fun m => m) c (fun m => W.finiteModes m)
  have hbudget : ∀ m : ℕ, ‖c m 0‖ ^ 2 / (2 * ν) ≤ datumEnergy u₀ / (2 * ν) := by
    intro m
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ν)
      (by positivity : (0 : ℝ) < 2 * ν)]
    exact mul_le_mul_of_nonneg_right
      (initialFlow_norm_sq_le_datumEnergy W u₀ c hc0 m) (by positivity)
  refine ⟨{
    approx := W.modalApprox c
    initialMode := fun m => W.proj m u₀
    initial_eq := modalApprox_initial_eq_proj W u₀ c hc0
    bound := datumEnergy u₀
    bound_nonneg := datumEnergy_nonneg u₀
    bound_le := le_rfl
    kinetic_bounded := uniformKineticBound_of_official hmeas hint hoff
    official_kinetic_bounded := hoff
    enstrophyBound := datumEnergy u₀ / (2 * ν)
    enstrophyBound_nonneg :=
      div_nonneg (datumEnergy_nonneg u₀) (by positivity)
    enstrophy_bounded := modalApprox_uniformEnstrophyBound W hν
      (fun m => W.stokesOperator m) (fun m => W.convectionOperator m) c hc
      (convectionOperator_inner_self W) (stokesOperator_inner_eq_enstrophy W)
      (datumEnergy u₀ / (2 * ν)) hbudget
    time_equicontinuous :=
      timeEquicontinuous_modalApprox_of_flow W hν u₀ c hc hc0
    space_equicontinuous :=
      spaceEquicontinuous_modalApprox_of_flow W hν u₀ c hc hc0
    jointly_measurable := ?_
    sq_integrable := ?_
    initial_converges_L2 := proj_initial_converges_L2 W u₀ hu₀
    weak_consistent := modalApprox_weakConsistent_of_projectedDatum
      W ν u₀ hu₀ c hprojectedWeak }⟩
  · simpa [GalerkinBasisFamily.modalApprox] using
      galerkinModalApprox_jointlyMeasurable (fun m => m) c
        (fun m t =>
          -(ν • W.stokesOperator m (c m t)) + W.convectionOperator m (c m t)) hc
        (fun m => W.finiteModes m)
  · simpa [GalerkinBasisFamily.modalApprox] using
      galerkinModalApprox_sq_integrable (fun m => m) c (fun m => W.finiteModes m)

end Navier.Analysis.GalerkinEnergyBudget
