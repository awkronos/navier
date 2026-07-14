import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.DeriveFintype

/-!
# Proof-bearing scientific dispositions

This module separates evidence about a proposition from the finite status used
by executable frontier views.  Only `ScientificDisposition.realized` contains
an unconditional proof and only that constructor can make `readiness` true.

A conditional disposition records both a named assumption and the actual map
from that assumption to the target.  It deliberately supplies no unconditional
projection.  A falsified disposition carries a proof of the negation; conjecture
and quarantine carry no proof of the target.
-/

set_option autoImplicit false

namespace Navier

/-- Evidence-sensitive scientific disposition for a proposition `P`. -/
inductive ScientificDisposition (P : Prop) : Type where
  | realized (proof : P)
  | falsified (counterproof : ¬ P)
  | conditional (assumption : Prop) (derivation : assumption → P)
  | conjectural
  | quarantined (reason : String)

/-- Proof-erased finite status for frontier tables and audit adapters. -/
inductive ScientificStatus where
  | realized
  | falsified
  | conditional
  | conjectural
  | quarantined
  deriving DecidableEq, Repr, Fintype

namespace ScientificDisposition

/-- Forget proof payloads while retaining the disposition class. -/
def status {P : Prop} : ScientificDisposition P → ScientificStatus
  | .realized _ => .realized
  | .falsified _ => .falsified
  | .conditional _ _ => .conditional
  | .conjectural => .conjectural
  | .quarantined _ => .quarantined

/-- Executable readiness is true exactly for unconditional realization. -/
def readiness {P : Prop} : ScientificDisposition P → Bool
  | .realized _ => true
  | .falsified _ => false
  | .conditional _ _ => false
  | .conjectural => false
  | .quarantined _ => false

@[simp] theorem readiness_realized {P : Prop} (proof : P) :
    readiness (.realized proof) = true := rfl

@[simp] theorem readiness_falsified {P : Prop} (counterproof : ¬ P) :
    readiness (.falsified counterproof) = false := rfl

@[simp] theorem readiness_conditional {P A : Prop} (derivation : A → P) :
    readiness (.conditional A derivation) = false := rfl

@[simp] theorem readiness_conjectural {P : Prop} :
    readiness (ScientificDisposition.conjectural : ScientificDisposition P) = false := rfl

@[simp] theorem readiness_quarantined {P : Prop} (reason : String) :
    readiness (ScientificDisposition.quarantined reason : ScientificDisposition P) = false := rfl

/-- Readiness is equivalent to the proof-bearing realized status. -/
@[simp] theorem readiness_eq_true_iff_status_eq_realized {P : Prop}
    (disposition : ScientificDisposition P) :
    readiness disposition = true ↔ status disposition = .realized := by
  cases disposition <;> simp [readiness, status]

/-- The complementary characterization of every non-realized disposition. -/
@[simp] theorem readiness_eq_false_iff_status_ne_realized {P : Prop}
    (disposition : ScientificDisposition P) :
    readiness disposition = false ↔ status disposition ≠ .realized := by
  cases disposition <;> simp [readiness, status]

/-- A proposition may be projected only after its disposition passes the
realization-only readiness gate. -/
theorem proof_of_readiness {P : Prop} {disposition : ScientificDisposition P}
    (ready : readiness disposition = true) : P := by
  cases disposition with
  | realized proof => exact proof
  | falsified _ => simp [readiness] at ready
  | conditional _ _ => simp [readiness] at ready
  | conjectural => simp [readiness] at ready
  | quarantined _ => simp [readiness] at ready

/-- A non-realized status cannot pass the readiness gate. -/
theorem nonrealized_cannot_be_ready {P : Prop}
    {disposition : ScientificDisposition P}
    (nonrealized : status disposition ≠ .realized) :
    readiness disposition ≠ true := by
  intro ready
  exact nonrealized
    ((readiness_eq_true_iff_status_eq_realized disposition).mp ready)

end ScientificDisposition

/-- The proof-erased status type has exactly the five advertised cases. -/
theorem scientificStatus_card : Fintype.card ScientificStatus = 5 := by
  decide

end Navier
