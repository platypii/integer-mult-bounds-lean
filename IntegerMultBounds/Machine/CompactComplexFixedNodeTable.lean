import IntegerMultBounds.Machine.CompactComplexScheduledPCDecode
import IntegerMultBounds.Machine.CompactComplexScheduledEventExecution

/-! A fixed node table retains original return addresses, four shared control
blocks, and every event of the actual interleaved schedule. Local block programs
are fixed arguments; recursive depth changes tape data, never this table. -/
namespace IntegerMultBounds.Machine.CompactComplexFixedNodeTable
noncomputable section
open Networks
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexScheduledPCLayout (originalCount eventPC nextPC callNextPC finalPC)
open CompactComplexScheduledPCDecode (decodeCall callAddress)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  schedule CompactComplexScalarSegmentRows.block
variable {t N length : ℕ}

def tableProgramsWith (returns : Fin N → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2) :
    Fin (N+(4+length)) → Σ q,Program t q 2 :=
  Fin.addCases returns (Fin.addCases controls events)

private def returnPrograms (ht : 0<t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (address : Fin originalCount) : Σ q,Program t q 2 :=
  match decodeCall address with
  | some c => childReturn c
  | none => ⟨1,skip t 2 ht⟩

/-- Original padded return slots, then the four controls, then real events. -/
def tablePrograms (ht : 0<t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2)
    (event : Event → Σ q,Program t q 2) :=
  tableProgramsWith (returnPrograms ht childReturn) controls (fun i => event (schedule.get i))

theorem table_return (ht : 0<t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (c : ComplexRecursiveCallSchema.Call) :
    tablePrograms ht childReturn controls event (Fin.castAdd (4+schedule.length) (callAddress c))=
      childReturn c := by
  simp only [tablePrograms,tableProgramsWith,Fin.addCases_left,returnPrograms,
    CompactComplexScheduledPCDecode.decodeCall_actual]

theorem table_event (ht : 0<t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (i : Fin schedule.length) :
    tablePrograms ht childReturn controls event (Fin.natAdd originalCount (Fin.natAdd 4 i))=
      event (schedule.get i) := by
  simp only [tablePrograms,tableProgramsWith,Fin.addCases_right]

theorem table_control (ht : 0<t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (tag : Fin 4) :
    tablePrograms ht childReturn controls event
      (Fin.natAdd originalCount (Fin.castAdd schedule.length tag))=controls tag := by
  simp only [tablePrograms,tableProgramsWith,Fin.addCases_right,Fin.addCases_left]

def tableEdgesWith (returns : Fin N → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (returnEdges : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (controlEdges : ∀ pc,Fin (controls pc).1 → Option (Fin (N+(4+length)+2)))
    (eventEdges : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2))) :
    ∀ pc,Fin (tableProgramsWith returns controls events pc).1 → Option (Fin (N+(4+length)+2)) := by
  intro pc
  induction pc using Fin.addCases with
  | left address => simpa only [tableProgramsWith,Fin.addCases_left] using returnEdges address
  | right rest =>
    induction rest using Fin.addCases with
    | left tag => simpa only [tableProgramsWith,Fin.addCases_right,Fin.addCases_left] using controlEdges tag
    | right event => simpa only [tableProgramsWith,Fin.addCases_right] using eventEdges event

/-- Entry, stopped, nonleaf and final-return controls use fixed extra PCs. -/
def controlPCFor (N length : ℕ) (tag : Fin 4) : Fin (N+(4+length)+2) :=
  GuardedFiniteReturnExtraFlow.extraPC (Fin.castAdd length tag)

private def firstPCFor (N length : ℕ) : Fin (N+(4+length)+2) :=
  if h : 0<length then GuardedFiniteReturnExtraFlow.extraPC (Fin.natAdd 4 (⟨0,h⟩ : Fin length))
  else controlPCFor N length 3

/-- Only the terminal entry classifier is variable; the other control edges
are fixed: stopped/final-return to the guard and nonleaf setup to first event. -/
def controlEdgesWith (controls : Fin 4 → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) :
    ∀ tag,Fin (controls tag).1 → Option (Fin (N+(4+length)+2)) :=
  Fin.cases (fun st => some (if isStopped st then controlPCFor N length 1 else controlPCFor N length 2))
    (Fin.cases (fun _ => some 0)
      (Fin.cases (fun _ => some (firstPCFor N length))
        (Fin.cases (fun _ => some 0) (fun i => Fin.elim0 i))))

def returnDestination (address : Fin originalCount) :
    Option (Fin (originalCount+(4+schedule.length)+2)) :=
  match decodeCall address with
  | some c => some (callNextPC c)
  | none => none

theorem returnDestination_actual (c : ComplexRecursiveCallSchema.Call) :
    returnDestination (callAddress c)=some (callNextPC c) := by
  simp only [returnDestination,CompactComplexScheduledPCDecode.decodeCall_actual]

private def destinationWith {P : ℕ} (e : Event) (next entry : Fin P) : Option (Fin P) :=
  match e with
  | .scalar _ => some next
  | .child _ => some entry

/-- A scalar block advances along this node; a child prefix back-edges to the
same shared recursive entry. Both edges preserve the local endpoint bank. -/
def eventDestination (i : Fin schedule.length) :=
  destinationWith (schedule.get i) (nextPC i) (controlPCFor originalCount schedule.length 0)

theorem eventDestination_scalar (i : Fin schedule.length)
    (g : CompactComplexScalarIntegerRows.GroupIndex) (hi : schedule.get i=Event.scalar g) :
    eventDestination i=some (nextPC i) :=
  congrArg (fun e => destinationWith e (nextPC i) (controlPCFor originalCount schedule.length 0)) hi

theorem eventDestination_child (i : Fin schedule.length)
    (c : ComplexRecursiveCallSchema.Call) (hi : schedule.get i=Event.child c) :
    eventDestination i=some (controlPCFor originalCount schedule.length 0) :=
  congrArg (fun e => destinationWith e (nextPC i) (controlPCFor originalCount schedule.length 0)) hi

theorem stopped_edge (controls : Fin 4 → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) (st : Fin (controls 1).1) :
    controlEdgesWith (N:=N) (length:=length) controls isStopped 1 st=some 0 := rfl

theorem final_return_edge (controls : Fin 4 → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) (st : Fin (controls 3).1) :
    controlEdgesWith (N:=N) (length:=length) controls isStopped 3 st=some 0 := rfl

def fixedProgramWith {k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (returns : Fin N → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (returnEdges : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (isStopped : Fin (controls 0).1 → Bool)
    (eventEdges : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2))) :=
  let programs := tableProgramsWith returns controls events
  let states := fun pc => (programs pc).1
  let blocks := fun pc => (programs pc).2
  let edges := tableEdgesWith returns controls events returnEdges
    (controlEdgesWith (N:=N) (length:=length) controls isStopped) eventEdges
  GuardedFiniteReturnExtraFlow.program (N:=N) (extra:=4+length) hN stack states blocks edges
    (controlPCFor N length 0)

def fixedProgram (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) :=
  fixedProgramWith (N:=originalCount) (length:=schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (returnPrograms ht childReturn) controls (fun i => event (schedule.get i))
    (fun address _ => returnDestination address) isStopped (fun i _ => eventDestination i)

end
end IntegerMultBounds.Machine.CompactComplexFixedNodeTable
