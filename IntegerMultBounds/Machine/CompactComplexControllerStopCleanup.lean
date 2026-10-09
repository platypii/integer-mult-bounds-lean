import IntegerMultBounds.Machine.CompactComplexControllerStopSetup
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.DescriptorStackControl

/-! Physically reclaim every stop-workspace cell after the runtime decision.
The retained native bank and all appended persistent tapes are framed exactly. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerStopCleanup
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {a w r : ℕ}

def descriptors : List (Fin 10) := [6,7,9]
def words (B D e : ℕ) : Fin 10 → List Bool := fun i =>
  if i=6 then RecursiveChildQuotientsConstant.bits D
  else if i=7 then FixedBasePowerUntil.counter (Nat.clog B D)
  else RecursiveChildQuotientsConstant.bits e

def flagEraseAction (sy : Fin 10 → Fin (a+4)) (i : Fin 10) : Fin (a+4) × Move :=
  (if i=8 then blank else sy i,.stay)
def flagErase : Program 10 2 a := DescriptorStackControl.once (by decide) flagEraseAction

def cleaned (B D e : ℕ) : Tapes 10 a :=
  BinaryDescriptorCleanupList.cleared descriptors
    (CompactComplexStopRun.output B D
      (RecursiveChildQuotientsConstant.bits D) (RecursiveChildQuotientsConstant.bits e))

def program : Program 10 15 a := seq
  (BinaryDescriptorCleanupList.program (by decide) descriptors) flagErase

theorem cleanup (B D e : ℕ) :
    HoareTime (program (a := a))
      (fun v => v=CompactComplexStopRun.output B D
        (RecursiveChildQuotientsConstant.bits D) (RecursiveChildQuotientsConstant.bits e))
      (fun v => v=SharedBank.empty 10 a)
      (BinaryDescriptorCleanupList.cost descriptors (words B D e)+2) := by
  have hc := BinaryDescriptorCleanupList.cleanup_hoare (a := a) (by decide : 0<10)
    descriptors (by decide) (words B D e)
    (CompactComplexStopRun.output B D
      (RecursiveChildQuotientsConstant.bits D) (RecursiveChildQuotientsConstant.bits e)) (by
      intro i hi
      simp [descriptors] at hi
      rcases hi with rfl | rfl | rfl <;> constructor
      all_goals rfl)
  have hf := DescriptorStackControl.once_hoare (by decide : 0<10) flagEraseAction
    (cleaned (a := a) B D e)
  have hclean : cleaned (a := a) B D e=setTape (SharedBank.empty 10 a) 8
      (CompactComplexStopCompare.result (RecursiveChildQuotientsConstant.bits e)
        (FixedBasePowerUntil.counter (Nat.clog B D))) 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have he : DescriptorStackControl.after (cleaned (a := a) B D e) flagEraseAction=SharedBank.empty 10 a := by
    rw [hclean]
    apply congrArg₂ Tapes.mk
    · funext i
      simp [flagEraseAction,setTape,SharedBank.empty,Move.offset]
    · funext i z
      by_cases hi : i=8
      · subst i
        by_cases hz : z=0 <;>
          simp [flagEraseAction,setTape,SharedBank.empty,
            CompactComplexStopCompare.result,hz]
      · simp [flagEraseAction,setTape,SharedBank.empty,hi]
  rw [he] at hf
  exact hc.seq hf

/-- Cleanup is linear in the original dimension and live exponent. -/
theorem cost_le (B D e : ℕ) (hB : 2≤B) :
    BinaryDescriptorCleanupList.cost descriptors (words B D e)+2 ≤ 4*D+2*e+23 := by
  have hd := GrowingCounterData.canonical_width (RecursiveChildQuotientsConstant.bits D)
    (RecursiveChildQuotientsConstant.bits_canonical D)
  have he := GrowingCounterData.canonical_width (RecursiveChildQuotientsConstant.bits e)
    (RecursiveChildQuotientsConstant.bits_canonical e)
  rw [RecursiveChildQuotientsConstant.bits_value] at hd he
  have hr := GrowingCounterData.canonical_width (FixedBasePowerUntil.counter (Nat.clog B D))
    (FixedBasePowerUntil.counter_canonical (Nat.clog B D))
  rw [FixedBasePowerUntil.counter_value] at hr
  have hcl : Nat.clog B D ≤ D := Nat.clog_le_of_le_pow
    (show D ≤ B^D from (FixedBasePowerDescriptor.depth_le_power B D hB).trans' (by omega))
  have hld := Nat.log2_le_self D
  have hle := Nat.log2_le_self e
  have hlr := Nat.log2_le_self (Nat.clog B D)
  simp only [BinaryDescriptorCleanupList.cost,descriptors,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,words,Fin.reduceEq,ite_true,ite_false]
  omega

def placed : Program (CompactComplexControllerStopSetup.tapes w r) 15 a :=
  ContiguousBankPlacement.program program

theorem placed_cleanup (caller : Tapes (110+w) a) (persist : Tapes r a) (B D e : ℕ) :
    HoareTime (placed (a := a))
      (fun v => v=CompactComplexControllerStopSetup.bank caller
        (CompactComplexStopRun.output B D
          (RecursiveChildQuotientsConstant.bits D) (RecursiveChildQuotientsConstant.bits e)) persist)
      (fun v => v=CompactComplexControllerStopSetup.bank caller (SharedBank.empty 10 a) persist)
      (BinaryDescriptorCleanupList.cost descriptors (words B D e)+2) :=
  ContiguousBankPlacement.runs (cleanup B D e) caller persist

end
end IntegerMultBounds.Machine.CompactComplexControllerStopCleanup
