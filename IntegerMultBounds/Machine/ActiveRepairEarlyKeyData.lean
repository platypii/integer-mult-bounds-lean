import IntegerMultBounds.Machine.ActiveRepairEarlyKeyPatch
import IntegerMultBounds.Machine.ActiveRepairEarlyKeyAppend
import IntegerMultBounds.Machine.ActiveRepairEarlyKeyCleanup

/-! The actual full-rank early key bank. Only original counter and runtime
descriptors are inputs; every address-dependent word is computed internally. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyData
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
def recoveredT (d : Data) := PackedInverse.w d.q d.b d.hb d.hbq d.V d.T d.Z
def target (d : Data) := CountedIdealToggle.word d.q
  (PackedInverse.v d.q d.b d.hb d.hbq d.V d.T d.Z) d.Z
def flags (d : Data) := CountedGuardGadget.flags d.q d.b d.Z.length d.V d.T
  (CountedGuardConstantsData.c1 d.q d.b) (CountedGuardConstantsData.c2 d.q d.b)
  (CountedGuardConstantsData.c3 d.b)
def flag (d : Data) := d.flags.any id
def destination (d : Data) := ActiveRepairDestinationPatchRun.destination d.cs
  d.target d.recoveredT d.U d.A d.sv d.st d.su

def extra (hs : Fin 7 → List Bool) (g K : ℤ → Fin 5) : Tapes 10 1 :=
  ⟨![1,1,1,1,1,1,1,0,0,0],
    ![RadixZeroFill.encodedBinary (hs 0),RadixZeroFill.encodedBinary (hs 1),
      RadixZeroFill.encodedBinary (hs 2),RadixZeroFill.encodedBinary (hs 3),
      RadixZeroFill.encodedBinary (hs 4),RadixZeroFill.encodedBinary (hs 5),
      RadixZeroFill.encodedBinary (hs 6),g,K,fun _ => blank]⟩

def sourceInput (d : Data) := ActiveRepairEarlySourceRun.bank d.cs
  ActiveRepairRankFieldsRun.empty d.hs d.ss d.bs
def sourceOutput (d : Data) := ActiveRepairEarlyFieldsPlaced.result
  (ActiveRepairEarlySourceRun.parsed d.cs d.starts d.widths d.q d.rho d.n d.hs d.ss d.bs)
  ActiveRepairEarlySourceRun.repairFocus d.q d.b d.hb d.hbq d.V d.T d.Z

def input (d : Data) := d.sourceInput.append (extra d.ph (fun _ => blank) (FlagCopy.keyTape []))
def computed (d : Data) := d.sourceOutput.append (extra d.ph (fun _ => blank) (FlagCopy.keyTape []))
def patched (d : Data) := setTape d.computed 29
  (CountedGuardGadgetRecord.word d.destination) 0
def written (d : Data) := setTape (setTape d.patched 20
  (CountedGuardGadgetRecord.word [d.flag]) 0) 30
  (FlagCopy.keyTape (FlagCopy.keyWord d.flag d.destination)) 0
def output (d : Data) := setTape d.input 30
  (FlagCopy.keyTape (FlagCopy.keyWord d.flag d.destination)) 0
end Data
open Data

def sourceFocus : Fin 22 → Fin 32 := Fin.castAdd 10
def patchFocus : Fin 12 → Fin 32 := ![0,29,21,19,3,22,23,24,25,26,27,28]
def appendFocus : Fin 4 → Fin 32 := ![20,30,29,31]
theorem source_injective : Function.Injective sourceFocus := Fin.castAdd_injective _ _
theorem patch_injective : Function.Injective patchFocus := by decide
theorem append_injective : Function.Injective appendFocus := by decide

theorem source_payload (d : Data) : SharedBank.payload d.input sourceFocus=d.sourceInput :=
  SharedBankFrames.payload_append_left _ _ id

theorem patch_payload (d : Data) : SharedBank.payload d.computed patchFocus=
    ActiveRepairDestinationPatchRun.bank d.cs d.target d.recoveredT d.U (fun _ => blank) d.ph := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem patched_install (d : Data) : ActiveRepairEarlyKeyPlacement.install d.computed patchFocus
    (ActiveRepairDestinationPatchRun.bank d.cs d.target d.recoveredT d.U
      (ActiveRepairDestinationPatchRun.word d.destination) d.ph)=d.patched := by
  apply ActiveRepairEarlyKeyPlacement.install_eq
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
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

def Data.words (d : Data) : Fin 32 → List Bool := fun i =>
  if i=1 then d.V else if i=2 then d.T else if i=3 then d.U else if i=4 then d.X
  else if i=5 then d.Z else if i=19 then d.recoveredT else if i=20 then [d.flag]
  else if i=21 then d.target else if i=29 then d.destination else []

theorem cleanup_tapes (d : Data) (i : Fin 32) (hi : i∈ActiveRepairEarlyKeyCleanup.slots) :
    d.written.tape i=CountedGuardGadgetRecord.word (d.words i) := by
  simp only [ActiveRepairEarlyKeyCleanup.slots,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem cleanup_heads (d : Data) (i : Fin 32) (hi : i∈ActiveRepairEarlyKeyCleanup.slots) :
    d.written.head i=0 := by
  simp only [ActiveRepairEarlyKeyCleanup.slots,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem cleanup_output (d : Data) :
    ActiveRepairEarlyKeyCleanup.execute ActiveRepairEarlyKeyCleanup.slots d.written=d.output := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyData
