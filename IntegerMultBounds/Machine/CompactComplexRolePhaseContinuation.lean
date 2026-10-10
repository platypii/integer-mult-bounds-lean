import IntegerMultBounds.Machine.CompactComplexRolePhaseSite
import IntegerMultBounds.Machine.FiniteFlow

/-! A real original-role phase block enters a fixed continuation with one
physical tape-preserving transition. No continuation execution contract is
needed to prove arrival at its actual start state. -/
namespace IntegerMultBounds.Machine.CompactComplexRolePhaseContinuation
noncomputable section
open Networks.Shared50ModularControl (prime)
open Networks.ComplexRecursiveCallSchema (Occurrence)
open ActivePrefixStageHeadersData (Order)
variable {q t k : ℕ}

abbrev tapes (t : ℕ) :=
  CompactNativeRoleSourcePorts.callerTapes t CompactComplexRolePhaseSite.roleCount+
    CompactNativeRoleConjugatedLifecycle.privateTapes

namespace Block
variable {a tapesCount phaseStates : ℕ}
def states (phaseStates k : ℕ) : Fin 2 → ℕ :=
  Fin.cases phaseStates (fun _ : Fin 1 => k)
def family (P : Program tapesCount phaseStates a) (K : Program tapesCount k a) :
    ∀ i,Program tapesCount (states phaseStates k i) a :=
  Fin.cases P (fun _ : Fin 1 => K)
def next (phaseStates k : ℕ) : FiniteFlow.Next (states phaseStates k) :=
  Fin.cases (fun _ => some (1 : Fin 2)) (fun _ : Fin 1 => fun _ => none)
def program (P : Program tapesCount phaseStates a) (K : Program tapesCount k a) (entry : Fin 2) :=
  FiniteFlow.program (family P K) (next phaseStates k) entry

def Reached (P : Program tapesCount phaseStates a) (K : Program tapesCount k a)
    (entry : Fin 2) (before after : Tapes tapesCount a) (time : ℕ) : Prop :=
    ∃ n,n≤time+1 ∧ run (program P K entry) n
      ((before.start P).mapState (FiniteFlow.embed (states phaseStates k) 0))=
      some ((after.start K).mapState (FiniteFlow.embed (states phaseStates k) 1))

theorem ready (P : Program tapesCount phaseStates a) (K : Program tapesCount k a)
    (entry : Fin 2) (before after : Tapes tapesCount a) (time : ℕ)
    (hphase : HoareTime P (fun z => z=before) (fun z => z=after) time) :
    ∃ n,n≤time+1 ∧ run (program P K entry) n
      ((before.start P).mapState (FiniteFlow.embed (states phaseStates k) 0))=
      some ((after.start K).mapState (FiniteFlow.embed (states phaseStates k) 1)) := by
  obtain ⟨n,c,hn,hr,hhalt,hpost⟩ := hphase before rfl
  change c.tapes=after at hpost
  have h := FiniteFlow.block_then_jump (family P K) (next phaseStates k)
    entry 0 1 before n c hr hhalt rfl
  change run (program P K entry) (n+1)
    ((before.start P).mapState (FiniteFlow.embed (states phaseStates k) 0))=
    some ((c.tapes.start K).mapState (FiniteFlow.embed (states phaseStates k) 1)) at h
  rw [hpost] at h
  exact ⟨n+1,by omega,h⟩
end Block

def program (P : Program ActivePrefixStageNative.tapes q prime) (site : Occurrence) (order : Order)
    (K : Program (tapes t) k prime) (entry : Fin 2) :=
  Block.program (CompactComplexRolePhaseSite.program P t site order) K entry

/-- An actual role-phase run reaches the continuation's literal start state. -/
theorem ready (P : Program ActivePrefixStageNative.tapes q prime) (site : Occurrence) (order : Order)
    (K : Program (tapes t) k prime) (entry : Fin 2) (before after : Tapes (tapes t) prime) (time : ℕ)
    (hphase : HoareTime (CompactComplexRolePhaseSite.program P t site order)
      (fun z => z=before) (fun z => z=after) time) :
    Block.Reached (CompactComplexRolePhaseSite.program P t site order) K entry before after time :=
  Block.ready (CompactComplexRolePhaseSite.program P t site order) K entry before after time hphase

end
end IntegerMultBounds.Machine.CompactComplexRolePhaseContinuation
