import IntegerMultBounds.Machine.ActiveRepairRankFieldsPlaced
import IntegerMultBounds.Machine.SelectedSourceBitsPlaced

/-! One caller bank for actual counter parsing and source-bit extraction:
counter, four fields, selected controls, eight start/width headers, and the
original four selected-source headers. The nine private tapes are shared. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankFieldsBank
noncomputable section
open SharedPlacementAlphabet (setTape)
open SelectedSourceBitsScan (word)

def bank (cs : List Bool) (ws : Fin 5 → List Bool) (hs : Fin 8 → List Bool)
    (ss : Fin 4 → List Bool) : Tapes 18 1 :=
  ⟨![1,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1],
    ![RepairScan.ctrTape cs,word (ws 0),word (ws 1),word (ws 2),word (ws 3),word (ws 4),
      RadixZeroFill.encodedBinary (hs 0),RadixZeroFill.encodedBinary (hs 1),
      RadixZeroFill.encodedBinary (hs 2),RadixZeroFill.encodedBinary (hs 3),
      RadixZeroFill.encodedBinary (hs 4),RadixZeroFill.encodedBinary (hs 5),
      RadixZeroFill.encodedBinary (hs 6),RadixZeroFill.encodedBinary (hs 7),
      RadixZeroFill.encodedBinary (ss 0),RadixZeroFill.encodedBinary (ss 1),
      RadixZeroFill.encodedBinary (ss 2),RadixZeroFill.encodedBinary (ss 3)]⟩

def offsetSlot (i : Fin 4) : Fin 8 := ⟨2*i.val,by omega⟩
def widthSlot (i : Fin 4) : Fin 8 := ⟨2*i.val+1,by omega⟩
def localHeaders (hs : Fin 8 → List Bool) (i : Fin 4) : Fin 2 → List Bool :=
  ![hs (offsetSlot i),hs (widthSlot i)]

def focus (i : Fin 4) : Fin 4 → Fin 18 :=
  ![0,⟨i.val+1,by omega⟩,⟨6+2*i.val,by omega⟩,⟨7+2*i.val,by omega⟩]

theorem focus_injective (i : Fin 4) : Function.Injective (focus i) := by fin_cases i <;> decide

def stage (i : Fin 4) := ActiveRepairRankFieldsPlaced.program (focus i) (focus_injective i)

theorem stage_sources (cs : List Bool) (ws : Fin 5 → List Bool) (hs : Fin 8 → List Bool)
    (ss : Fin 4 → List Bool) (i : Fin 4) (hi : ws (Fin.castAdd 1 i)=[]) :
    SharedBank.payload (bank cs ws hs ss) (focus i)=
      ActiveRepairRankFieldsPlaced.sources cs (fun _ => blank) (localHeaders hs i) := by
  fin_cases i
  all_goals apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j
  all_goals first | rfl | exact congrArg (word (a := 1)) hi

theorem result_eq (cs : List Bool) (ws : Fin 5 → List Bool) (hs : Fin 8 → List Bool)
    (ss : Fin 4 → List Bool) (i : Fin 4) (xs : List Bool) :
    setTape (bank cs ws hs ss) (focus i 1) (word xs) 0=
      bank cs (Function.update ws (Fin.castAdd 1 i) xs) hs ss := by
  fin_cases i
  all_goals apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j
  all_goals simp [bank,focus,Function.update]

theorem field_runs (cs : List Bool) (ws : Fin 5 → List Bool) (hs : Fin 8 → List Bool)
    (ss : Fin 4 → List Bool) (i : Fin 4) (hi : ws (Fin.castAdd 1 i)=[]) (start width : ℕ)
    (hv0 : Counter.value (hs (offsetSlot i))=start)
    (hv1 : Counter.value (hs (widthSlot i))=width)
    (hc0 : GrowingCounterData.Canonical (hs (offsetSlot i)))
    (hc1 : GrowingCounterData.Canonical (hs (widthSlot i))) :
    HoareTime (stage i) (fun v => v=CleanSubbank.bank (s := 9) (bank cs ws hs ss))
      (fun v => v=CleanSubbank.bank (s := 9)
        (bank cs (Function.update ws (Fin.castAdd 1 i) (Gather.field cs start width)) hs ss))
      (200*(start+width+1)) := by
  have h := ActiveRepairRankFieldsPlaced.runs_linear (bank cs ws hs ss) (focus i) (focus_injective i)
    (fun _ => blank) cs (localHeaders hs i) start width (stage_sources cs ws hs ss i hi) hv0 hv1
    (by intro j; fin_cases j; exact hc0; exact hc1)
  have he := result_eq cs ws hs ss i (Gather.field cs start width)
  change setTape (bank cs ws hs ss) (focus i 1)
    (putWord (fun _ => blank) 0 ((Gather.field cs start width).map bitSymbol)) 0=_ at he
  unfold ActiveRepairRankFieldsPlaced.result at h
  rw [he] at h
  exact h

end
end IntegerMultBounds.Machine.ActiveRepairRankFieldsBank
