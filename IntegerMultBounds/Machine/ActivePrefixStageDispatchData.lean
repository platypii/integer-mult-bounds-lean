import IntegerMultBounds.Machine.ActivePrefixStageDispatchCommon
import IntegerMultBounds.Machine.ActivePrefixStageFullEarlyRun
import IntegerMultBounds.Machine.ActivePrefixStageFullLateRun

/-! A separate permanent flag follows original thirteen numeric words and raw
array. Its bit is computed from source/target words, never supplied as input. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageDispatchData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
open ActiveRepairLayoutRecordsData (Array)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {s : Shape}

def caller (d : Inputs s) (x : Array s d.rows) := (original d x).append (SharedBank.empty 1 prime)
def flag : Fin 67 := 66
def compareSlots : Fin 3 → Fin 67 := ![11,12,66]
theorem compareSlots_injective : Function.Injective compareSlots := by decide

def flagged (d : Inputs s) (x : Array s d.rows) := setTape (caller d x) flag
  (BinaryDescriptorCompare.result (RecursiveChildQuotientsConstant.bits d.stage.source.val)
    (RecursiveChildQuotientsConstant.bits d.stage.target.val)) 0

theorem caller_compare (d : Inputs s) (x : Array s d.rows) :
    SharedBank.payload (caller d x) compareSlots=ActivePrefixStageOrderCompare.input d.stage := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

theorem compare_set (d : Inputs s) :
    setTape (ActivePrefixStageOrderCompare.input (a:=prime) d.stage) 2
      (BinaryDescriptorCompare.result (RecursiveChildQuotientsConstant.bits d.stage.source.val)
        (RecursiveChildQuotientsConstant.bits d.stage.target.val)) 0=
          ActivePrefixStageOrderCompare.output d.stage := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem flagged_compare (d : Inputs s) (x : Array s d.rows) :
    SharedBank.payload (flagged d x) compareSlots=ActivePrefixStageOrderCompare.output d.stage := by
  unfold flagged
  rw [show flag=compareSlots 2 from rfl,CompactGadgetReservationPlacement.payload_set _ _ compareSlots_injective,
    caller_compare,compare_set]

theorem caller_payload (d : Inputs s) (x : Array s d.rows) :
    SharedBank.payload (caller d x) (Fin.castAdd 1)=original d x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [caller,Tapes.append,Fin.addCases_left]
  all_goals rfl

theorem flagged_payload (d : Inputs s) (x : Array s d.rows) :
    SharedBank.payload (flagged d x) (Fin.castAdd 1)=original d x := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have hi : (Fin.castAdd 1 i : Fin 67)≠flag := by
      intro h; have hv := congrArg Fin.val h; have := i.isLt; change i.val=66 at hv; omega
    simp only [flagged,setTape,Function.update_of_ne hi]
    simp only [caller,Tapes.append,Fin.addCases_left]
    rfl

theorem flagged_set (d : Inputs s) (x y : Array s d.rows) :
    setTape (flagged d x) (Fin.castAdd 1 (65:Fin 66)) (ActiveTargetRotation.word y) 0=flagged d y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem caller_flag_blank (d : Inputs s) (x : Array s d.rows) :
    (caller d x).head flag=0 ∧ (caller d x).tape flag=(fun _ => blank) := ⟨rfl,rfl⟩

theorem erase_flag (d : Inputs s) (x : Array s d.rows) :
    setTape (flagged d x) flag (fun _ => blank) 0=caller d x := by
  simp only [flagged,SharedPlacementAlphabet.setTape_setTape]
  have h := caller_flag_blank d x
  rw [←h.1,←h.2,SharedPlacementAlphabet.setTape_self]

def result (d : Inputs s) (x : Array s d.rows) :=
  if h : d.stage.source.val<d.stage.target.val then earlyResult d h x
  else lateResult d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h) x

end
end IntegerMultBounds.Machine.ActivePrefixStageDispatchData
