import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedActualTable
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedEntry
import IntegerMultBounds.Machine.CompactComplexSourceReadySinkCorrections
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinal

/-! A fixed controller table with actual source and sink correction routines.
The entry classifier, stopped branch, child programs and saved-return port are
the original oriented actual machinery. This identifies the transition table;
it does not assert a recursive execution invariant or its total runtime. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedActualTable
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles tapes)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites CompactComplexCompletedLiveLower.schedule
  CompactComplexRolePhaseSite.roleCount
  CompactComplexSourceReadyCorrectedEntry.program
  CompactComplexSourceReadySinkCorrections.program
  CompactComplexSourceReadyNonleafOrientedFinal.program

/-- Sink corrections precede the physical contraction, rejoin and saved-call
post-orientation already performed by the original final branch. -/
def final (pcStack : Fin s) : Σ q,Program (tapes s roles) q 2 :=
  ProgramPairSequence.pair (CompactComplexSourceReadySinkCorrections.program (s:=s))
    (CompactComplexSourceReadyNonleafOrientedFinal.program (c:=roles) pcStack)

theorem final_eq (pcStack : Fin s) : final pcStack=
    ProgramPairSequence.pair (CompactComplexSourceReadySinkCorrections.program (s:=s))
      (CompactComplexSourceReadyNonleafOrientedFinal.program (c:=roles) pcStack) := rfl

theorem final_program_eq (pcStack : Fin s) : final pcStack=
    CompactComplexSourceReadyCorrectedFinal.program pcStack := rfl

def controls (pcStack : Fin s) : Fin 4 → Σ q,Program (tapes s roles) q 2 :=
  ![CompactComplexSourceReadyOrientedControls.entry pcStack,
    CompactComplexSourceReadyOrientedControls.stopped pcStack,
    CompactComplexSourceReadyCorrectedEntry.program,
    final pcStack]

@[simp] theorem control_entry (pcStack : Fin s) : controls pcStack 0=
    CompactComplexSourceReadyOrientedControls.entry (c:=roles) pcStack := rfl
@[simp] theorem control_stopped (pcStack : Fin s) : controls pcStack 1=
    CompactComplexSourceReadyOrientedControls.stopped (c:=roles) pcStack := rfl
@[simp] theorem control_split (pcStack : Fin s) : controls pcStack 2=
    CompactComplexSourceReadyCorrectedEntry.program (s:=s) := rfl
@[simp] theorem control_final (pcStack : Fin s) : controls pcStack 3=
    ProgramPairSequence.pair (CompactComplexSourceReadySinkCorrections.program (s:=s))
      (CompactComplexSourceReadyNonleafOrientedFinal.program (c:=roles) pcStack) := rfl

/-- Original stopping markers still determine the entry branch. -/
def classify (pcStack : Fin s) : Fin (controls pcStack 0).1 → Bool :=
  CompactComplexSourceReadyOrientedControls.isStopped (c:=roles) pcStack

theorem classify_stopped (pcStack : Fin s) : classify pcStack
    (CompactComplexSourceReadyOrientedControls.stoppedState (c:=roles) pcStack)=true :=
  CompactComplexSourceReadyOrientedControls.classify_stopped pcStack

theorem classify_nonleaf (pcStack : Fin s) : classify pcStack
    (CompactComplexSourceReadyOrientedControls.nonleafState (c:=roles) pcStack)=false :=
  CompactComplexSourceReadyOrientedControls.classify_nonleaf pcStack

def savedStackSlot (pcStack : Fin s) : Fin (tapes s roles) :=
  CompactComplexSourceReadyActualTable.savedStackSlot pcStack

/-- The guard reads the same physical saved-PC port as actual child entry. -/
theorem savedStackSlot_eq (pcStack : Fin s) : savedStackSlot pcStack=
    Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch
      (CompactComplexSourceReadyOrientationInvariants.savedSlot (c:=roles) pcStack) := rfl

/-- A fixed actual program, parameterized only by its permanent stack slots. -/
def program (headerStack pcStack liveStack : Fin s) : Σ q,Program (tapes s roles) q 2 :=
  CompactComplexSourceReadyActualTable.program headerStack pcStack liveStack
    (controls pcStack) (classify pcStack)

theorem program_actual (headerStack pcStack liveStack : Fin s) :
    program headerStack pcStack liveStack=
      CompactComplexSourceReadyActualTable.programWithStack (savedStackSlot pcStack)
        headerStack pcStack liveStack (controls pcStack) (classify pcStack) := rfl

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedActualTable
