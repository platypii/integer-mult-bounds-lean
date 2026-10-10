import IntegerMultBounds.Machine.CompactComplexFixedNodeTable
import IntegerMultBounds.Machine.FiniteFlowPath

/-! Reachability-local block contracts produce genuine nonhalting paths in
one fixed cyclic node table. No uniform contract over invalid event banks,
whole-node trace, or recursive execution oracle is assumed. -/
namespace IntegerMultBounds.Machine.CompactComplexFixedNodePaths
noncomputable section
open Networks
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexFixedNodeTable
open CompactComplexScheduledPCLayout (originalCount eventPC nextPC callNextPC)
open CompactComplexScheduledPCDecode (callAddress savedPC)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth
variable {t : ℕ}

def nodeStates (ht : 0<t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2) :=
  fun pc => (tablePrograms ht childReturn controls event pc).1

def nodeBlocks (ht : 0<t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2) :=
  fun pc => (tablePrograms ht childReturn controls event pc).2

def nodeEdges (ht : 0<t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) :=
  tableEdgesWith (returnPrograms ht childReturn)
    controls (fun i => event (schedule.get i))
    (fun address _ => returnDestination address)
    (controlEdgesWith (N:=originalCount) (length:=schedule.length) controls isStopped)
    (fun i _ => eventDestination i)

private def familyWith {N extra k : ℕ} (stack : Fin t)
    (programs : Fin (N+extra) → Σ q,Program t q 2) :=
  GuardedFiniteReturnExtraFlow.family (k:=k) stack
    (fun i => (programs i).1) (fun i => (programs i).2)

private def nextWith {N extra k : ℕ} (hN : N≤2^k)
    (programs : Fin (N+extra) → Σ q,Program t q 2)
    (edges : ∀ pc,Fin (programs pc).1 → Option (Fin (N+extra+2))) :=
  GuardedFiniteReturnExtraFlow.next hN (fun i => (programs i).1) edges

private def pathWith {N extra k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (programs : Fin (N+extra) → Σ q,Program t q 2)
    (edges : ∀ pc,Fin (programs pc).1 → Option (Fin (N+extra+2))) :=
  FiniteFlowPath.Path (familyWith (k:=k) stack programs) (nextWith hN programs edges)

/-- One locally valid halted block plus its actual edge costs one paid join. -/
theorem guarded_local_path {N extra k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (programs : Fin (N+extra) → Σ q,Program t q 2)
    (edges : ∀ pc,Fin (programs pc).1 → Option (Fin (N+extra+2)))
    (pc : Fin (N+extra)) (dest : Fin (N+extra+2)) (before after : Tapes t 2) (B : ℕ)
    (hlocal : HoareTime (programs pc).2 (fun v => v=before) (fun v => v=after) B)
    (hedge : ∀ st,edges pc st=some dest) :
    ∃ n≤B+1,pathWith hN stack programs edges pc.succ.succ before n dest after := by
  unfold pathWith familyWith nextWith
  have hlocal' : HoareTime
      (GuardedFiniteReturnExtraFlow.family (k:=k) stack (fun i => (programs i).1)
        (fun i => (programs i).2) pc.succ.succ)
      (fun v => v=before) (fun v => v=after) B := by
    simpa [GuardedFiniteReturnExtraFlow.family,GuardedFiniteReturnExtraFlow.states,
      Fin.cases,Fin.induction,Fin.induction.go] using hlocal
  obtain ⟨n,out,hn,hr,hh,ha⟩ := hlocal' before rfl
  refine ⟨n+1,by omega,?_⟩
  have he : GuardedFiniteReturnExtraFlow.next hN (fun i => (programs i).1) edges
      pc.succ.succ out.state=some dest := by
    simpa [GuardedFiniteReturnExtraFlow.next,GuardedFiniteReturnExtraFlow.states,
      Fin.cases,Fin.induction,Fin.induction.go] using hedge out.state
  have hp := FiniteFlowPath.block_path
    (family:=GuardedFiniteReturnExtraFlow.family stack (fun i => (programs i).1) (fun i => (programs i).2))
    (next:=GuardedFiniteReturnExtraFlow.next hN (fun i => (programs i).1) edges)
    pc.succ.succ dest before n out hr hh he
  rw [ha] at hp
  exact hp

/-- The family and next relation used by the actual fixed cyclic program. -/
def nodeFamily (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2) :=
  familyWith (N:=originalCount) (extra:=4+schedule.length) (k:=CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (tableProgramsWith (returnPrograms ht childReturn) controls (fun i => event (schedule.get i)))

def nodeNext (ht : 0<t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) :=
  nextWith (N:=originalCount) (extra:=4+schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3))
    (tableProgramsWith (returnPrograms ht childReturn) controls (fun i => event (schedule.get i))) (nodeEdges ht childReturn controls event isStopped)

theorem fixedProgramWith_eq {N length k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (returns : Fin N → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (isStopped : Fin (controls 0).1 → Bool)
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2))) :
    fixedProgramWith hN stack returns controls events re isStopped ee=
      FiniteFlow.program (familyWith (k:=k) stack (tableProgramsWith returns controls events))
        (nextWith hN (tableProgramsWith returns controls events)
          (tableEdgesWith returns controls events re
            (controlEdgesWith (N:=N) (length:=length) controls isStopped) ee))
        (controlPCFor N length 0) := rfl

attribute [local irreducible] fixedProgramWith familyWith nextWith FiniteFlow.program

theorem fixedProgram_eq (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) :
    fixedProgram ht stack childReturn controls event isStopped=
      FiniteFlow.program (nodeFamily ht stack childReturn controls event)
        (nodeNext ht childReturn controls event isStopped)
        (controlPCFor originalCount schedule.length 0) :=
  fixedProgramWith_eq (N:=originalCount) (length:=schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (returnPrograms ht childReturn) controls (fun i => event (schedule.get i))
    (fun address _ => returnDestination address) isStopped (fun i _ => eventDestination i)

/-- Reachability in the family of the actual fixed cyclic table. -/
def nodePath (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) :=
  pathWith (N:=originalCount) (extra:=4+schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (tableProgramsWith (returnPrograms ht childReturn) controls (fun i => event (schedule.get i)))
    (nodeEdges ht childReturn controls event isStopped)

theorem nodePath_iff (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool)
    (pc last : Fin (originalCount+(4+schedule.length)+2)) (before after : Tapes t 2) (n : ℕ) :
    nodePath ht stack childReturn controls event isStopped pc before n last after ↔
      FiniteFlowPath.Path (nodeFamily ht stack childReturn controls event)
        (nodeNext ht childReturn controls event isStopped) pc before n last after := Iff.rfl

private theorem hoare_program_eq {P Q : Σ q,Program t q 2} (he : P=Q)
    {before after : Tapes t 2} {B : ℕ}
    (h : HoareTime Q.2 (fun v => v=before) (fun v => v=after) B) :
    HoareTime P.2 (fun v => v=before) (fun v => v=after) B := by
  cases he
  exact h

private theorem mpr_constant {q r P : ℕ}
    (h : (Fin q → Option (Fin P))=(Fin r → Option (Fin P)))
    (hq : q=r) (f : Fin r → Option (Fin P)) (dest : Fin P)
    (hf : ∀ st,f st=some dest) (st : Fin q) : Eq.mpr h f st=some dest := by
  subst r
  have hh : h=rfl := Subsingleton.elim _ _
  cases hh
  exact hf st

private theorem event_edge {N length : ℕ}
    (returns : Fin N → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ce : ∀ pc,Fin (controls pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (i : Fin length) (dest : Fin (N+(4+length)+2))
    (he : ∀ st,ee i st=some dest) :
    ∀ st,tableEdgesWith returns controls events re ce ee
      (Fin.natAdd N (Fin.natAdd 4 i)) st=some dest := by
  intro st
  simp only [tableEdgesWith,Fin.addCases_right]
  generalize_proofs h
  exact mpr_constant h (by simp only [tableProgramsWith,Fin.addCases_right]) _ dest he st

private theorem return_edge {N length : ℕ}
    (returns : Fin N → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ce : ∀ pc,Fin (controls pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (i : Fin N) (dest : Fin (N+(4+length)+2))
    (he : ∀ st,re i st=some dest) :
    ∀ st,tableEdgesWith returns controls events re ce ee
      (Fin.castAdd (4+length) i) st=some dest := by
  intro st
  simp only [tableEdgesWith,Fin.addCases_left]
  generalize_proofs h
  exact mpr_constant h (by simp only [tableProgramsWith,Fin.addCases_left]) _ dest he st

private theorem control_edge {N length : ℕ}
    (returns : Fin N → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ce : ∀ pc,Fin (controls pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (i : Fin 4) (dest : Fin (N+(4+length)+2))
    (he : ∀ st,ce i st=some dest) :
    ∀ st,tableEdgesWith returns controls events re ce ee
      (Fin.natAdd N (Fin.castAdd length i)) st=some dest := by
  intro st
  simp only [tableEdgesWith,Fin.addCases_right,Fin.addCases_left]
  generalize_proofs h
  exact mpr_constant h (by simp only [tableProgramsWith,Fin.addCases_right,Fin.addCases_left]) _ dest he st

theorem event_local_path {N length k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (returns : Fin N → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ce : ∀ pc,Fin (controls pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (i : Fin length) (dest : Fin (N+(4+length)+2)) (before after : Tapes t 2) (B : ℕ)
    (hlocal : HoareTime (events i).2 (fun v => v=before) (fun v => v=after) B)
    (he : ∀ st,ee i st=some dest) :
    ∃ n≤B+1,pathWith hN stack (tableProgramsWith returns controls events)
      (tableEdgesWith returns controls events re ce ee)
      (Fin.natAdd N (Fin.natAdd 4 i)).succ.succ before n dest after := by
  apply guarded_local_path hN stack (tableProgramsWith returns controls events)
    (tableEdgesWith returns controls events re ce ee) _ dest before after B
  · exact hoare_program_eq (by simp only [tableProgramsWith,Fin.addCases_right]) hlocal
  · exact event_edge returns controls events re ce ee i dest he

theorem return_local_path {N length k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (returns : Fin N → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ce : ∀ pc,Fin (controls pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (i : Fin N) (dest : Fin (N+(4+length)+2)) (before after : Tapes t 2) (B : ℕ)
    (hlocal : HoareTime (returns i).2 (fun v => v=before) (fun v => v=after) B)
    (he : ∀ st,re i st=some dest) :
    ∃ n≤B+1,pathWith hN stack (tableProgramsWith returns controls events)
      (tableEdgesWith returns controls events re ce ee)
      (Fin.castAdd (4+length) i).succ.succ before n dest after := by
  apply guarded_local_path hN stack (tableProgramsWith returns controls events)
    (tableEdgesWith returns controls events re ce ee) _ dest before after B
  · exact hoare_program_eq (by simp only [tableProgramsWith,Fin.addCases_left]) hlocal
  · exact return_edge returns controls events re ce ee i dest he

theorem control_local_path {N length k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (returns : Fin N → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ce : ∀ pc,Fin (controls pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (i : Fin 4) (dest : Fin (N+(4+length)+2)) (before after : Tapes t 2) (B : ℕ)
    (hlocal : HoareTime (controls i).2 (fun v => v=before) (fun v => v=after) B)
    (he : ∀ st,ce i st=some dest) :
    ∃ n≤B+1,pathWith hN stack (tableProgramsWith returns controls events)
      (tableEdgesWith returns controls events re ce ee)
      (Fin.natAdd N (Fin.castAdd length i)).succ.succ before n dest after := by
  apply guarded_local_path hN stack (tableProgramsWith returns controls events)
    (tableEdgesWith returns controls events re ce ee) _ dest before after B
  · exact hoare_program_eq (by simp only [tableProgramsWith,Fin.addCases_right,Fin.addCases_left]) hlocal
  · exact control_edge returns controls events re ce ee i dest he

private theorem terminal_edge {N length : ℕ}
    (controls : Fin 4 → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) (tag : Fin 4) (htag : tag=1 ∨ tag=3) :
    ∀ st,controlEdgesWith (N:=N) (length:=length) controls isStopped tag st=some 0 := by
  rcases htag with rfl | rfl
  · exact stopped_edge controls isStopped
  · exact final_return_edge controls isStopped

variable (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool)

/-- A scalar contract at this reachable bank advances to its actual successor. -/
theorem scalar_path (i : Fin schedule.length)
    (g : CompactComplexScalarIntegerRows.GroupIndex) (hi : schedule.get i=Event.scalar g)
    (before after : Tapes t 2) (B : ℕ)
    (hlocal : HoareTime (event (Event.scalar g)).2
      (fun v => v=before) (fun v => v=after) B) :
    ∃ n≤B+1,nodePath ht stack childReturn controls event isStopped (eventPC i) before n (nextPC i) after := by
  apply event_local_path (N:=originalCount) (length:=schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (returnPrograms ht childReturn) controls (fun i => event (schedule.get i))
    (fun address _ => returnDestination address)
    (controlEdgesWith (N:=originalCount) (length:=schedule.length) controls isStopped)
    (fun i _ => eventDestination i) i (nextPC i) before after B
  · exact hoare_program_eq (congrArg event hi) hlocal
  · intro st
    exact eventDestination_scalar i g hi

/-- A locally executed child prefix re-enters the same shared fixed table. -/
theorem child_prefix_path (i : Fin schedule.length) (c : ComplexRecursiveCallSchema.Call)
    (hi : schedule.get i=Event.child c) (before after : Tapes t 2) (B : ℕ)
    (hlocal : HoareTime (event (Event.child c)).2
      (fun v => v=before) (fun v => v=after) B) :
    ∃ n≤B+1,nodePath ht stack childReturn controls event isStopped
      (eventPC i) before n (controlPCFor originalCount schedule.length 0) after := by
  apply event_local_path (N:=originalCount) (length:=schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (returnPrograms ht childReturn) controls (fun i => event (schedule.get i))
    (fun address _ => returnDestination address)
    (controlEdgesWith (N:=originalCount) (length:=schedule.length) controls isStopped)
    (fun i _ => eventDestination i) i (controlPCFor originalCount schedule.length 0) before after B
  · exact hoare_program_eq (congrArg event hi) hlocal
  · intro st
    exact eventDestination_child i c hi

/-- A genuine decoded child return enters the unique next original event. -/
theorem decoded_return_path (c : ComplexRecursiveCallSchema.Call)
    (before after : Tapes t 2) (B : ℕ)
    (hlocal : HoareTime (childReturn c).2
      (fun v => v=before) (fun v => v=after) B) :
    ∃ n≤B+1,nodePath ht stack childReturn controls event isStopped (savedPC c) before n (callNextPC c) after := by
  apply return_local_path (N:=originalCount) (length:=schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (returnPrograms ht childReturn) controls (fun i => event (schedule.get i))
    (fun address _ => returnDestination address)
    (controlEdgesWith (N:=originalCount) (length:=schedule.length) controls isStopped)
    (fun i _ => eventDestination i) (callAddress c) (callNextPC c) before after B
  · apply hoare_program_eq _ hlocal
    simp only [returnPrograms,CompactComplexScheduledPCDecode.decodeCall_actual]
  · intro st
    exact returnDestination_actual c

/-- Either terminal control returns to the genuine stack guard. -/
theorem terminal_control_path (tag : Fin 4) (htag : tag=1 ∨ tag=3)
    (before after : Tapes t 2) (B : ℕ)
    (hlocal : HoareTime (controls tag).2
      (fun v => v=before) (fun v => v=after) B) :
    ∃ n≤B+1,nodePath ht stack childReturn controls event isStopped
      (controlPCFor originalCount schedule.length tag) before n 0 after := by
  apply control_local_path (N:=originalCount) (length:=schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (returnPrograms ht childReturn) controls (fun i => event (schedule.get i))
    (fun address _ => returnDestination address)
    (controlEdgesWith (N:=originalCount) (length:=schedule.length) controls isStopped)
    (fun i _ => eventDestination i) tag 0 before after B hlocal
  exact terminal_edge (N:=originalCount) (length:=schedule.length) controls isStopped tag htag


end
end IntegerMultBounds.Machine.CompactComplexFixedNodePaths
