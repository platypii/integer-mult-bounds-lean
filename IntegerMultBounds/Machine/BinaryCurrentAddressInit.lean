import IntegerMultBounds.Machine.BinaryCurrentAddress
import IntegerMultBounds.Machine.BinaryAddressTableFill

/-! Physically initialize a live address counter and its raw readout from the
original binary width descriptor. No address word is prepared externally. -/
namespace IntegerMultBounds.Machine.BinaryCurrentAddressInit
noncomputable section
open CountedLoopReuseAlphabet (encoding binary)
open BinaryAddressTableData (row)
variable {a : ℕ}

def bank (counter addr : ℤ → Fin (a+4)) (pc : ℤ) (ws : List Bool) : Tapes 4 a :=
  ⟨![pc,0,0,1],![counter,addr,(fun _ => blank),binary ws]⟩
def input (ws : List Bool) := bank (a := a) (fun _ => blank) (fun _ => blank) 0 ws
def ready (ws : List Bool) (W : ℕ) :=
  bank (a := a) (binary (List.replicate W false)) (fun _ => blank) 1 ws
def output (ws : List Bool) (W : ℕ) :=
  bank (a := a) (binary (row W 0)) (SelectedSourceBitsScan.word (row W 0)) 1 ws
def placement : Fin (3+1) ≃ Fin 4 where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def fill := Placement.placed (Alphabet.program (encoding a) BinaryAddressTableFill.program) placement
def readout := extend (BinaryCurrentAddress.copyProgram (a := a)) 2
def program := seq (fill (a := a)) readout

theorem fill_runs (ws : List Bool) (W : ℕ) (hw : Counter.value ws=W) :
    HoareTime (fill (a := a)) (fun v => v=input ws) (fun v => v=ready ws W)
      (8*W+7*ws.length+39) := by
  have hsmall := Alphabet.map_hoare (encoding a) (BinaryAddressTableFill.runs ws W hw)
  have ha : Placement.active placement (input (a := a) ws)=
      Alphabet.mapTapes (encoding a) (BinaryAddressTableFill.input ws) := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i
      · rfl
      · rfl
      · exact congrFun (CountedLoopReuseAlphabet.encoding_binary ws).symm z
  have hb : Placement.active placement (ready (a := a) ws W)=
      Alphabet.mapTapes (encoding a) (BinaryAddressTableFill.output ws W) := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i
      · exact congrFun (CountedLoopReuseAlphabet.encoding_binary (List.replicate W false)).symm z
      · rfl
      · exact congrFun (CountedLoopReuseAlphabet.encoding_binary ws).symm z
  have hs : HoareTime (Alphabet.program (encoding a) BinaryAddressTableFill.program)
      (fun v => v=Placement.active placement (input ws))
      (fun v => v=Placement.active placement (ready ws W)) (8*W+7*ws.length+39) := by
    apply hsmall.consequence _ _ le_rfl
    · rintro v rfl; exact ⟨_,rfl,ha⟩
    · rintro v ⟨original,rfl,rfl⟩; exact hb.symm
  apply (Placement.hoare_at hs placement (input ws) rfl).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  have hf : Placement.extra placement (input (a := a) ws)=Placement.extra placement (ready ws W) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [Placement.replace,hf]
  exact Placement.view placement (ready ws W)

theorem readout_runs (ws : List Bool) (W : ℕ) :
    HoareTime (readout (a := a)) (fun v => v=ready ws W) (fun v => v=output ws W) (3*W+7) := by
  have h := hoare_extend_eq (BinaryCurrentAddress.copies_blank (a := a) (List.replicate W false))
    (⟨![0,1],![(fun _ => blank),binary ws]⟩ : Tapes 2 a)
  have he0 : (Copy.tapes (binary (a := a) (List.replicate W false)) (fun _ => blank) 1 0).append
      (⟨![0,1],![(fun _ => blank),binary ws]⟩ : Tapes 2 a)=ready ws W := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have he1 : (BinaryCurrentAddress.bank (a := a) (List.replicate W false) (List.replicate W false)).append
      (⟨![0,1],![(fun _ => blank),binary ws]⟩ : Tapes 2 a)=output ws W := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [readout,he0,he1,List.length_replicate] using h

theorem runs (ws : List Bool) (W : ℕ) (hw : Counter.value ws=W)
    (hc : GrowingCounterData.Canonical ws) :
    HoareTime (program (a := a)) (fun v => v=input ws) (fun v => v=output ws W) (65*(W+1)) := by
  have hh := (fill_runs (a := a) ws W hw).seq (readout_runs ws W)
  have hl := GrowingCounterData.canonical_width ws hc
  rw [hw] at hl
  have hlog := Nat.log2_le_self W
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryCurrentAddressInit
