import IntegerMultBounds.Machine.CompactComplexSourceReadyFullChildPaths
import IntegerMultBounds.Machine.CompactComplexScalarSegmentRows
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientationInvariants

/-! The original event schedule populated by actual full-bank scalar and child
programs. Return blocks execute the complete physical parent continuation.
Nonleaf target/contraction and orientation controls remain fixed parameters
until their actual finalization programs are assembled. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyActualTable
noncomputable section
open Networks.ComplexRecursiveCallSchema (Call)
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexSourceReadyScalarWorkspace (roles tapes scratch)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount

/-- Count setup borrows one of the ten reclaimed denominator-work slots. -/
def countHeader : Fin (10+s) := ⟨0,by omega⟩
theorem countHeader_ne_live : (countHeader (s:=s)).val≠7 := by simp [countHeader]

def scalar (g : CompactComplexScalarIntegerRows.GroupIndex) :
    Σ q,Program (tapes s roles) q 2 :=
  CompactComplexSourceReadyScalarWorkspace.program countHeader countHeader_ne_live
    (CompactComplexScalarSegmentRows.block g)

def child (headerStack pcStack liveStack : Fin s) (call : Call) :
    Σ q,Program (tapes s roles) q 2 :=
  ⟨_,extend (CompactComplexSourceReadyChildEntryPath.program headerStack pcStack liveStack call) scratch⟩

def childReturn (headerStack liveStack : Fin s) (call : Call) :
    Σ q,Program (tapes s roles) q 2 :=
  ⟨_,extend (CompactComplexSourceReadyChildReturnPath.program
    (CompactComplexRolePhaseSite.role call.site) headerStack liveStack) scratch⟩

def event (headerStack pcStack liveStack : Fin s) : Event → Σ q,Program (tapes s roles) q 2
  | .scalar g => scalar g
  | .child call => child headerStack pcStack liveStack call

@[simp] theorem event_scalar (headerStack pcStack liveStack : Fin s)
    (g : CompactComplexScalarIntegerRows.GroupIndex) :
    event headerStack pcStack liveStack (.scalar g)=scalar g := rfl

@[simp] theorem event_child (headerStack pcStack liveStack : Fin s) (call : Call) :
    event headerStack pcStack liveStack (.child call)=
      ⟨_,extend (CompactComplexSourceReadyChildEntryPath.program headerStack pcStack liveStack call) scratch⟩ := rfl

@[simp] theorem return_child (headerStack liveStack : Fin s) (call : Call) :
    childReturn headerStack liveStack call=
      ⟨_,extend (CompactComplexSourceReadyChildReturnPath.program
        (CompactComplexRolePhaseSite.role call.site) headerStack liveStack) scratch⟩ := rfl

private def assemble {t : ℕ} (ht : 0<t) (stack : Fin t)
    (returns : Call → Σ q,Program t q 2) (ctrl : Fin 4 → Σ q,Program t q 2)
    (events : Event → Σ q,Program t q 2) (classify : Fin (ctrl 0).1 → Bool) :
    Σ q,Program t q 2 :=
  ⟨_,CompactComplexFixedNodeTable.fixedProgram ht stack returns ctrl events classify⟩

/-- One fixed cyclic machine uses the actual grouped scalar blocks, actual
child entry and actual decoded return. None depend on recursion depth. -/
def programWithStack (stack : Fin (tapes s roles)) (headerStack pcStack liveStack : Fin s)
    (ctrl : Fin 4 → Σ q,Program (tapes s roles) q 2)
    (classify : Fin (ctrl 0).1 → Bool) : Σ q,Program (tapes s roles) q 2 :=
  assemble (Nat.zero_lt_of_lt stack.isLt) stack (childReturn headerStack liveStack)
    ctrl (event headerStack pcStack liveStack) classify

/-- The controller reads the same physical saved-PC port written by actual
child entry and retained by both orientation wrappers. -/
def savedStackSlot (pcStack : Fin s) : Fin (tapes s roles) :=
  Fin.castAdd scratch (CompactComplexSourceReadyOrientationInvariants.savedSlot (c:=roles) pcStack)

/-- Canonical assembly derives the return-stack wiring from the child-entry
PC slot, rather than accepting a second independently supplied stack port. -/
def program (headerStack pcStack liveStack : Fin s)
    (ctrl : Fin 4 → Σ q,Program (tapes s roles) q 2)
    (classify : Fin (ctrl 0).1 → Bool) : Σ q,Program (tapes s roles) q 2 :=
  programWithStack (savedStackSlot pcStack) headerStack pcStack liveStack ctrl classify

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyActualTable
