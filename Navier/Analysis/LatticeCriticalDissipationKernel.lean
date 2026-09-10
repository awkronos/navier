import Mathlib.Algebra.Module.ZLattice.Summable
import Navier.Analysis.LeiLinCoerciveTerminal

/-!
# Summability of the critical lattice dissipation kernel

The inverse fourth power of the physical Euclidean frequency is summable on
the three-dimensional integer lattice after the zero mode is removed.  The
proof transports Mathlib's inverse-power summability theorem for `ℤ`-lattices
along the concrete coordinate embedding of `LatticeMode`.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.LatticeCriticalDissipationKernel

open Navier
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.LeiLinCoerciveTerminal
open Submodule
open Module

/-- Real Euclidean three-space used to invoke the `ℤ`-lattice summability theorem. -/
private abbrev RealE3 := EuclideanSpace ℝ (Fin 3)

/-- The standard real basis of Euclidean three-space. -/
private def realE3Basis : Basis (Fin 3) ℝ RealE3 :=
  PiLp.basisFun 2 ℝ (Fin 3)

/-- The standard integer lattice inside real Euclidean three-space. -/
private def realIntegerLattice : Submodule ℤ RealE3 :=
  Submodule.span ℤ (Set.range realE3Basis)

private noncomputable instance : DiscreteTopology realIntegerLattice := by
  unfold realIntegerLattice
  infer_instance

private noncomputable instance : IsZLattice ℝ realIntegerLattice := by
  unfold realIntegerLattice
  infer_instance

/-- A lattice mode regarded as an element of the standard real integer lattice. -/
private def realLatticePoint (k : LatticeMode) : realIntegerLattice :=
  ⟨WithLp.toLp 2 (latticeFrequency k), by
    change WithLp.toLp 2 (latticeFrequency k) ∈
      Submodule.span ℤ (Set.range realE3Basis)
    rw [realE3Basis.mem_span_iff_repr_mem ℤ]
    intro i
    fin_cases i
    · exact ⟨k.1, by simp [realE3Basis, latticeFrequency]⟩
    · exact ⟨k.2.1, by simp [realE3Basis, latticeFrequency]⟩
    · exact ⟨k.2.2, by simp [realE3Basis, latticeFrequency]⟩⟩

private theorem realLatticePoint_injective : Function.Injective realLatticePoint := by
  intro k l h
  have h0 := congrArg (fun x : realIntegerLattice => x.1 0) h
  have h1 := congrArg (fun x : realIntegerLattice => x.1 1) h
  have h2 := congrArg (fun x : realIntegerLattice => x.1 2) h
  apply Prod.ext
  · have h0' : (k.1 : ℝ) = (l.1 : ℝ) := by
      simpa [realLatticePoint, latticeFrequency] using h0
    exact_mod_cast h0'
  · apply Prod.ext
    · have h1' : (k.2.1 : ℝ) = (l.2.1 : ℝ) := by
        simpa [realLatticePoint, latticeFrequency] using h1
      exact_mod_cast h1'
    · have h2' : (k.2.2 : ℝ) = (l.2.2 : ℝ) := by
        simpa [realLatticePoint, latticeFrequency] using h2
      exact_mod_cast h2'

private theorem norm_realLatticePoint (k : LatticeMode) :
    ‖realLatticePoint k‖ = latticeModeSize k := by
  have hreal : ‖realLatticePoint k‖ ^ 2 =
      (k.1 : ℝ) ^ 2 + (k.2.1 : ℝ) ^ 2 + (k.2.2 : ℝ) ^ 2 := by
    change ‖(↑(realLatticePoint k) : RealE3)‖ ^ 2 = _
    rw [EuclideanSpace.norm_sq_eq]
    simp [realLatticePoint, latticeFrequency, Fin.sum_univ_three]
  have hcomplex : latticeModeSize k ^ 2 =
      (k.1 : ℝ) ^ 2 + (k.2.1 : ℝ) ^ 2 + (k.2.2 : ℝ) ^ 2 := by
    unfold latticeModeSize
    rw [EuclideanSpace.norm_sq_eq]
    simp [complexFrequency_apply, latticeFrequency, Fin.sum_univ_three, sq_abs]
  nlinarith [norm_nonneg (realLatticePoint k), latticeModeSize_nonneg k]

/-- The inverse fourth-power kernel associated with the physical lattice size.
The zero mode is explicitly removed. -/
def inverseFourthKernel (k : LatticeMode) : ℝ :=
  if k = 0 then 0 else (latticeModeSize k ^ 4)⁻¹

/-- In dimension three, the inverse fourth power of the physical lattice
frequency is summable. -/
theorem summable_inverseFourthKernel : Summable inverseFourthKernel := by
  have hrank : Module.finrank ℤ realIntegerLattice = 3 := by
    rw [ZLattice.rank ℝ realIntegerLattice]
    simp [RealE3]
  have hL : Summable (fun z : realIntegerLattice => ‖z‖⁻¹ ^ 4) :=
    ZLattice.summable_norm_pow_inv realIntegerLattice 4 (by omega)
  refine (hL.comp_injective realLatticePoint_injective).congr ?_
  intro k
  change ‖realLatticePoint k‖⁻¹ ^ 4 = inverseFourthKernel k
  rw [norm_realLatticePoint]
  by_cases hk : k = 0
  · simp [inverseFourthKernel, hk, latticeModeSize_zero]
  · simp [inverseFourthKernel, hk, inv_pow]

end Navier.Analysis.LatticeCriticalDissipationKernel
