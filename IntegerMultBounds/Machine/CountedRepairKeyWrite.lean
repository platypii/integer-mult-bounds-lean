import IntegerMultBounds.Machine.CountedRepairKeyAppend

/-! The physical conditional key writer placed in the thirty-tape repair bank. -/
namespace IntegerMultBounds.Machine.CountedRepairKeyWrite
noncomputable section
open SharedPlacementAlphabet
open CountedRepairKeyBank
open CountedGuardGadgetRecord (word)
open CountedRankSplitBank (placed_exact)

def place : Fin (4+26) ≃ Fin 30 where
  toFun := ![28,27,29,6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
  invFun := ![4,5,6,7,8,9,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,1,0,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def program := Placement.placed CountedRepairKeyAppend.program place

def output (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :=
  setTape (setTape (toggled q b hb hbq V W Z cs hs) 28 (word [flag q b V W Z]) 0)
    27 (FlagCopy.keyTape (FlagCopy.keyWord (flag q b V W Z)
      (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z ++ PackedInverse.w q b hb hbq V W Z))) 0

theorem input_view (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active place (toggled q b hb hbq V W Z cs hs)=CountedRepairKeyAppend.input
      (flag q b V W Z) (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z) (PackedInverse.w q b hb hbq V W Z) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem output_view (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active place (output q b hb hbq V W Z cs hs)=CountedRepairKeyAppend.output
      (flag q b V W Z) (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z) (PackedInverse.w q b hb hbq V W Z) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem extra_view (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.extra place (toggled q b hb hbq V W Z cs hs)=Placement.extra place (output q b hb hbq V W Z cs hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b) :
    HoareTime program (fun v => v=toggled q b hb hbq V W Z cs hs)
      (fun v => v=output q b hb hbq V W Z cs hs) (20*((Z.length+1)*(q+b+1))) := by
  have h := placed_exact place _ _ _ _ (input_view q b hb hbq V W Z cs hs)
    (output_view q b hb hbq V W Z cs hs) (extra_view q b hb hbq V W Z cs hs)
    (CountedRepairKeyAppend.runs (flag q b V W Z) (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z)
      (PackedInverse.w q b hb hbq V W Z))
  obtain ⟨_,_,_,_,_,_,_,hw,_,hv⟩ := PackedInverse.lengths q b hb hbq V W Z hV hW
  refine h.consequence (fun _ h => h) (fun _ h => h) ?_
  rw [CountedIdealToggle.word_length q _ Z (by omega) hv,hv,hw]
  nlinarith

end
end IntegerMultBounds.Machine.CountedRepairKeyWrite
