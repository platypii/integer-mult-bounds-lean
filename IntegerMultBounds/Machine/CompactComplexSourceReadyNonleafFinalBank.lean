import IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeCurrentBudget
import IntegerMultBounds.Machine.CompactComplexControllerExactReturnBudget

/-! Actual permanent-bank projections used between contraction and merging. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalBank
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open ActiveRepairRankHeadersCommands (State)
variable {s c : ℕ}

theorem headers (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) (frame : Tapes 2 2) :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      ((bank control queue scalar stage tail storage payload).append frame)=
      ActiveRepairRankHeadersCommands.bank stage := by
  rw [CompactComplexNonleafRoleEntry.headerPlacement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    bank,CompactComplexNativeRoleBridge.bank,CompactComplexNativeRoleBridge.native,
    CompactComplexControllerNativeFrame.bank,CompactComplexControllerNativeFrame.nativeSlot,
    Tapes.append,Fin.addCases_left,Fin.addCases_right]
  all_goals rfl

theorem role (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) (frame : Tapes 2 2)
    (j : Fin c) :
    ((bank control queue scalar stage tail storage payload).append frame).head
        (CompactComplexNonleafRoleEntry.roleTape j)=payload.head (Fin.natAdd 1 j) ∧
    ((bank control queue scalar stage tail storage payload).append frame).tape
        (CompactComplexNonleafRoleEntry.roleTape j)=payload.tape (Fin.natAdd 1 j) := by
  simp only [CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNativeRoleBridge.roleSlot,bank,CompactComplexNativeRoleBridge.bank,
    CompactNativeRoleSourcePorts.roles,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  have hi : (⟨j.val+1,by omega⟩ : Fin (1+c))=Fin.natAdd 1 j := by apply Fin.ext; simp [Nat.add_comm]
  rw [hi]
  exact ⟨rfl,rfl⟩


theorem source (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) (frame : Tapes 2 2) :
    ((bank control queue scalar stage tail storage payload).append frame).head
        CompactComplexNonleafRoleEntry.source=payload.head 0 ∧
    ((bank control queue scalar stage tail storage payload).append frame).tape
        CompactComplexNonleafRoleEntry.source=payload.tape 0 := by
  have h65 : (65 : Fin 66)=Fin.natAdd 43 (Fin.natAdd 22 (0 : Fin 1)) := rfl
  simp only [CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    bank,CompactComplexNativeRoleBridge.bank,CompactComplexNativeRoleBridge.native,
    CompactComplexControllerNativeFrame.bank,CompactComplexControllerNativeFrame.nativeSlot,
    Tapes.append,Fin.addCases_left,Fin.addCases_right,h65,CompactComplexNativeRoleBridge.single,and_self]

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalBank
