import IntegerMultBounds.Machine.CompactComplexSourceReadyActualTable
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsEntry
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStoppedSemantics
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStoppedRoot
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafTargetSplit
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedFinal

/-! One canonical fixed machine instantiates all four controls with genuine
physical routines: pre-orientation and original stopping test, forward stopped
body and post-orientation, target/count and split, contraction/rejoin and
post-orientation. Scalar, child and saved-return tables are the original actual
programs. Its only arguments choose permanent controller stack slots. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedActualTable
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles tapes)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites CompactComplexCompletedLiveLower.schedule
  CompactComplexRolePhaseSite.roleCount

def controls (pcStack : Fin s) : Fin 4 → Σ q,Program (tapes s roles) q 2 :=
  ![CompactComplexSourceReadyOrientedControls.entry pcStack,
    CompactComplexSourceReadyOrientedControls.stopped pcStack,
    CompactComplexSourceReadyNonleafTargetSplit.fullProgram,
    CompactComplexSourceReadyNonleafOrientedFinal.program pcStack]

@[simp] theorem control_entry (pcStack : Fin s) : controls pcStack 0=
    CompactComplexSourceReadyOrientedControls.entry (c:=roles) pcStack := rfl
@[simp] theorem control_stopped (pcStack : Fin s) : controls pcStack 1=
    CompactComplexSourceReadyOrientedControls.stopped (c:=roles) pcStack := rfl
@[simp] theorem control_split (pcStack : Fin s) : controls pcStack 2=
    CompactComplexSourceReadyNonleafTargetSplit.fullProgram (s:=s) (c:=roles) := rfl
@[simp] theorem control_final (pcStack : Fin s) : controls pcStack 3=
    CompactComplexSourceReadyNonleafOrientedFinal.program (c:=roles) pcStack := rfl

/-- Genuine stopping markers shifted through pre-orientation supply the
classifier; no separately supplied control decision enters the machine. -/
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

/-- Exactly the saved-PC port written by original child entry, widened over
its fixed scalar suffix; the cyclic return guard uses the same physical port. -/
theorem savedStackSlot_eq (pcStack : Fin s) : savedStackSlot pcStack=
    Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch
      (CompactComplexSourceReadyOrientationInvariants.savedSlot (c:=roles) pcStack) := rfl

/-- Canonical complete transition table, with no supplied local machine,
execution proof, direction, control family, classifier or saved-PC map. -/
def program (headerStack pcStack liveStack : Fin s) : Σ q,Program (tapes s roles) q 2 :=
  CompactComplexSourceReadyActualTable.program headerStack pcStack liveStack
    (controls pcStack) (classify pcStack)

theorem program_actual (headerStack pcStack liveStack : Fin s) :
    program headerStack pcStack liveStack=
      CompactComplexSourceReadyActualTable.programWithStack (savedStackSlot pcStack)
        headerStack pcStack liveStack (controls pcStack) (classify pcStack) := rfl

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedActualTable
