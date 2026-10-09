import IntegerMultBounds.Machine.ActiveRepairLateSourceRun
import IntegerMultBounds.Machine.ActiveRepairLateKeyPatch
import IntegerMultBounds.Machine.ActiveRepairLateKeyAppend
import IntegerMultBounds.Machine.ActiveRepairLateKeyCleanup

/-! The actual full-rank later key bank. Only original counter and runtime
descriptors are inputs; every address-dependent word is computed internally. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateKeyData
noncomputable section
open SharedPlacementAlphabet (setTape)

structure Data where
  cs : List Bool
  starts : Fin 4 → ℕ
  widths : Fin 4 → ℕ
  hs : Fin 8 → List Bool
  ss : Fin 4 → List Bool
  bs : List Bool
  ph : Fin 7 → List Bool
  q : ℕ
  b : ℕ
  rho : ℕ
  n : ℕ
  f : ℕ
  A : ℕ
  sv : ℕ
  st : ℕ
  su : ℕ
  hb : 1≤b
  hbq : b+1≤q

namespace Data
def V (d : Data) := Gather.field d.cs (d.starts 0) (d.widths 0)
def T (d : Data) := Gather.field d.cs (d.starts 1) (d.widths 1)
def U (d : Data) := Gather.field d.cs (d.starts 2) (d.widths 2)
def X (d : Data) := Gather.field d.cs (d.starts 3) (d.widths 3)
def Z (d : Data) := SelectedSourceBitsData.selected d.X d.q d.rho d.n
def recoveredT (d : Data) := CountedLateRepairInverse.temp d.q d.b d.hb d.hbq d.V d.T d.U d.Z
def recoveredU (d : Data) := CountedLateRepairInverse.restored d.b d.hb d.U d.Z
def target (d : Data) := CountedIdealToggle.word d.q
  (CountedLateRepairInverse.target d.q d.b d.hb d.hbq d.V d.T d.U d.Z) d.Z
def flag (d : Data) := CountedLateRepairGuard.flag d.q d.b d.V d.T d.Z ||
  CountedLateRepairGuard.flag d.q d.b d.V d.U d.Z
def destination (d : Data) := ActiveRepairDestinationPatchRun.destination d.cs
  d.target d.recoveredT d.recoveredU d.A d.sv d.st d.su

def extra (hs : Fin 7 → List Bool) (g K : ℤ → Fin 5) : Tapes 10 1 :=
  ⟨![1,1,1,1,1,1,1,0,0,0],
    ![RadixZeroFill.encodedBinary (hs 0),RadixZeroFill.encodedBinary (hs 1),
      RadixZeroFill.encodedBinary (hs 2),RadixZeroFill.encodedBinary (hs 3),
      RadixZeroFill.encodedBinary (hs 4),RadixZeroFill.encodedBinary (hs 5),
      RadixZeroFill.encodedBinary (hs 6),g,K,fun _ => blank]⟩

def sourceInput (d : Data) := ActiveRepairLateSourceRun.bank d.cs
  ActiveRepairRankFieldsRun.empty d.hs d.ss d.bs
def sourceOutput (d : Data) :=
  setTape (setTape (setTape (setTape
    (ActiveRepairLateSourceRun.parsed d.cs d.starts d.widths d.q d.rho d.n d.hs d.ss d.bs)
    19 (CountedGuardGadgetRecord.word d.recoveredT) 0)
    20 (CountedGuardGadgetRecord.word d.recoveredU) 0)
    21 (CountedLateRepairFlag.key d.flag) 1)
    22 (CountedGuardGadgetRecord.word d.target) 0

theorem sourceOutput_real (d : Data) : d.sourceOutput=ActiveRepairLateFieldsPlaced.result
  (ActiveRepairLateSourceRun.parsed d.cs d.starts d.widths d.q d.rho d.n d.hs d.ss d.bs)
  ActiveRepairLateSourceRun.repairFocus d.q d.b d.hb d.hbq d.V d.T d.U d.Z := rfl

def input (d : Data) := d.sourceInput.append (extra d.ph (fun _ => blank) (FlagCopy.keyTape []))
def computed (d : Data) := d.sourceOutput.append (extra d.ph (fun _ => blank) (FlagCopy.keyTape []))
def patched (d : Data) := setTape d.computed 30
  (CountedGuardGadgetRecord.word d.destination) 0
def written (d : Data) := setTape (setTape d.patched 21
  (CountedGuardGadgetRecord.word [d.flag]) 0) 31
  (FlagCopy.keyTape (FlagCopy.keyWord d.flag d.destination)) 0
def output (d : Data) := setTape d.input 31
  (FlagCopy.keyTape (FlagCopy.keyWord d.flag d.destination)) 0
end Data
open Data

def sourceFocus : Fin 23 → Fin 33 := Fin.castAdd 10
def patchFocus : Fin 12 → Fin 33 := ![0,30,22,19,20,23,24,25,26,27,28,29]
def appendFocus : Fin 4 → Fin 33 := ![21,31,30,32]
theorem source_injective : Function.Injective sourceFocus := Fin.castAdd_injective _ _
theorem patch_injective : Function.Injective patchFocus := by decide
theorem append_injective : Function.Injective appendFocus := by decide

theorem source_payload (d : Data) : SharedBank.payload d.input sourceFocus=d.sourceInput :=
  SharedBankFrames.payload_append_left _ _ id

private theorem patch_payload_raw (cs : List Bool) (ws : Fin 5 → List Bool)
    (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool) (bs v t u : List Bool)
    (fl : Bool) (ph : Fin 7 → List Bool) :
    SharedBank.payload
      ((setTape (setTape (setTape (setTape (ActiveRepairLateSourceRun.bank cs ws hs ss bs)
        19 (CountedGuardGadgetRecord.word t) 0) 20 (CountedGuardGadgetRecord.word u) 0)
        21 (CountedLateRepairFlag.key fl) 1) 22 (CountedGuardGadgetRecord.word v) 0).append
        (extra ph (fun _ => blank) (FlagCopy.keyTape []))) patchFocus=
      ActiveRepairDestinationPatchRun.bank cs v t u (fun _ => blank) ph := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem patch_payload (d : Data) : SharedBank.payload d.computed patchFocus=
    ActiveRepairDestinationPatchRun.bank d.cs d.target d.recoveredT d.recoveredU (fun _ => blank) d.ph :=
  patch_payload_raw _ _ _ _ _ _ _ _ _ _

theorem patched_install (d : Data) : ActiveRepairEarlyKeyPlacement.install d.computed patchFocus
    (ActiveRepairDestinationPatchRun.bank d.cs d.target d.recoveredT d.recoveredU
      (ActiveRepairDestinationPatchRun.word d.destination) d.ph)=d.patched := by
  apply ActiveRepairEarlyKeyPlacement.install_eq
  · unfold patched
    change SharedBank.payload (setTape d.computed (patchFocus 1) _ _) patchFocus = _
    rw [CompactGadgetReservationPlacement.payload_set _ _ patch_injective,patch_payload]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · unfold patched
    change SharedBank.strip d.computed patchFocus=
      SharedBank.strip (setTape d.computed (patchFocus 1) _ _) patchFocus
    rw [CompactGadgetReservationPlacement.strip_set]

theorem append_payload (d : Data) : SharedBank.payload d.patched appendFocus=
    CountedRepairKeyAppend.input d.flag d.destination [] := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem written_install (d : Data) : ActiveRepairEarlyKeyPlacement.install d.patched appendFocus
    (CountedRepairKeyAppend.output d.flag d.destination [])=d.written := by
  apply ActiveRepairEarlyKeyPlacement.install_eq
  · simp only [CountedRepairKeyAppend.output,List.append_nil]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · unfold written
    change SharedBank.strip d.patched appendFocus=
      SharedBank.strip (setTape (setTape d.patched (appendFocus 0) _ _)
        (appendFocus 1) _ _) appendFocus
    rw [CompactGadgetReservationPlacement.strip_set,CompactGadgetReservationPlacement.strip_set]

def Data.words (d : Data) : Fin 33 → List Bool := fun i =>
  if i=1 then d.V else if i=2 then d.T else if i=3 then d.U else if i=4 then d.X
  else if i=5 then d.Z else if i=19 then d.recoveredT else if i=20 then d.recoveredU else if i=21 then [d.flag]
  else if i=22 then d.target else if i=30 then d.destination else []

private theorem cleanup_tape_22 (d : Data) :
    d.written.tape 22=CountedGuardGadgetRecord.word (d.words 22) := by
  have hw : d.words 22=d.target := rfl
  rw [hw]
  simp only [written,patched,setTape,Function.update_apply]
  norm_num only [Fin.reduceEq,ite_true,ite_false]
  rw [show (22 : Fin 33)=Fin.castAdd 10 (22 : Fin 23) from rfl]
  simp only [computed,Tapes.append,Fin.addCases_left,sourceOutput,setTape,Function.update_apply,ite_true]

theorem cleanup_tapes (d : Data) (i : Fin 33) (hi : i∈ActiveRepairLateKeyCleanup.slots) :
    d.written.tape i=CountedGuardGadgetRecord.word (d.words i) := by
  simp only [ActiveRepairLateKeyCleanup.slots,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact cleanup_tape_22 d
  · rfl

theorem cleanup_heads (d : Data) (i : Fin 33) (hi : i∈ActiveRepairLateKeyCleanup.slots) :
    d.written.head i=0 := by
  simp only [ActiveRepairLateKeyCleanup.slots,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem cleanup_output (d : Data) :
    ActiveRepairLateKeyCleanup.execute ActiveRepairLateKeyCleanup.slots d.written=d.output := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActiveRepairLateKeyData
