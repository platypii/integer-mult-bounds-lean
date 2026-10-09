import IntegerMultBounds.Machine.CompactComplexChildHeadersData
import IntegerMultBounds.Machine.CompactChildHeadersStack

/-! The concrete original sixty-six-tape caller saves exactly its three
changed child-node headers, using tape sixty-four for generic binary frames.
The raw payload at sixty-five and every other tape are preserved. -/
namespace IntegerMultBounds.Machine.CompactComplexChildHeaderFrames
noncomputable section
open SharedPlacementAlphabet ActivePrefixStageParameters
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageHeadersData (initial)
open ActiveRepairRankHeadersCommands (bank caller)
open RecursiveChildQuotientsConstant (bits)

variable {a : ℕ}
def focus : Fin 3 → Fin 66 := ![7,8,9]
def stack : Fin 66 := 64
theorem focus_injective : Function.Injective focus := by decide
theorem distinct : ∀ i, focus i ≠ stack := by decide

def saveProgram := CompactChildHeadersStack.saveProgram (a := a) focus stack distinct
def restoreProgram := CompactChildHeadersStack.restoreProgram (a := a) focus stack distinct

def data {s : Shape} (v : Stage s) : Fin 3 → List Bool := ![bits v.f,bits v.left,bits v.right]
def input {s : Shape} (v : Stage s) (rows : ℕ) (tail : Tapes 23 a) := (bank (initial v rows)).append tail

def saved {s : Shape} (v : Stage s) (rows : ℕ) (tail : Tapes 23 a) :=
  setTape (input v rows tail) stack
    (CompactChildHeadersStack.frames ((input v rows tail).tape stack)
      ((input v rows tail).head stack) (data v))
    (CompactChildHeadersStack.top ((input v rows tail).head stack) (data v))

theorem save {s : Shape} (v : Stage s) (rows : ℕ) (tail : Tapes 23 a) :
    HoareTime saveProgram (fun w => w=input v rows tail) (fun w => w=saved v rows tail)
      (CompactChildHeadersStack.cost (data v)) := by
  apply CompactChildHeadersStack.save
  · intro i
    fin_cases i <;>
      simp [input,focus,bank,CleanSubbank.bank,Tapes.append,Fin.addCases,caller,initial,
        ActivePrefixStageHeadersData.originalValues,data,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  · intro i
    fin_cases i <;>
      simp [input,focus,bank,CleanSubbank.bank,Tapes.append,Fin.addCases,caller,initial,
        ActivePrefixStageHeadersData.originalValues]

/-- Generic restoration on the concrete original bank after its changed
headers have been erased. This theorem retains every other physical tape. -/
theorem restore (v : Tapes 66 a) (f : ℤ → Fin (a+4)) (p : ℤ) (words : Fin 3 → List Bool)
    (ht : v.tape stack = CompactChildHeadersStack.frames f p words)
    (hp : v.head stack = CompactChildHeadersStack.top p words)
    (hd : ∀ i, v.tape (focus i) = fun _ => blank) (hh : ∀ i, v.head (focus i) = 0)
    (hblank : ∀ z, p ≤ z → f z = blank) :
    HoareTime restoreProgram (fun w => w=v)
      (fun w => w=setTape (setTape (setTape (setTape v stack f p)
        (focus 2) (BinaryDescriptorStack.descriptor (words 2)) 1)
        (focus 1) (BinaryDescriptorStack.descriptor (words 1)) 1)
        (focus 0) (BinaryDescriptorStack.descriptor (words 0)) 1)
      (CompactChildHeadersStack.cost words) :=
  CompactChildHeadersStack.restore focus focus_injective stack distinct v f p words ht hp hd hh hblank


def cleanupSchedule : List CompactChildHeadersArithmetic.Op :=
  [.existing (.command (.erase 7)),.existing (.command (.erase 8)),.existing (.command (.erase 9))]
def cleared (st : ActiveRepairRankHeadersCommands.State) :=
  Function.update (Function.update (Function.update st 7 none) 8 none) 9 none

def cleanupProgram := extend (CompactChildHeadersArithmetic.compile (a := a) cleanupSchedule).2 23

/-- Child descriptors are physically erased before their saved parent values
are popped; erase and sequence-transition costs are both included. -/
theorem cleanup (st : ActiveRepairRankHeadersCommands.State) (width left right : ℕ)
    (h7 : st 7 = some width) (h8 : st 8 = some left) (h9 : st 9 = some right)
    (tail : Tapes 23 a) : HoareTime cleanupProgram
      (fun w => w=(bank st).append tail) (fun w => w=(bank (cleared st)).append tail)
      (100*(width+left+right+3)+3) := by
  have hv : CompactChildHeadersArithmetic.validSchedule cleanupSchedule st := by
    simp [cleanupSchedule,CompactChildHeadersArithmetic.validSchedule,
      CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
      ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
      h7,h8,h9,Function.update]
  have he : CompactChildHeadersArithmetic.execute cleanupSchedule st = cleared st := rfl
  have hc : CompactChildHeadersArithmetic.scheduleCost cleanupSchedule st =
      100*(width+left+right+3)+3 := by
    simp [cleanupSchedule,CompactChildHeadersArithmetic.scheduleCost,
      CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
      ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
      h7,h8,h9,Function.update]
    omega
  have h := CompactChildHeadersArithmetic.schedule_runs (a := a) cleanupSchedule st hv
  rw [he,hc] at h
  exact hoare_extend_eq h tail


/-- Private stack frames occupy the original caller's tape sixty-four. -/
def savedTail {s : Shape} (v : Stage s) (tail : Tapes 23 a) :=
  setTape tail 21 (CompactChildHeadersStack.frames (tail.tape 21) (tail.head 21) (data v))
    (CompactChildHeadersStack.top (tail.head 21) (data v))

theorem saved_eq {s : Shape} (v : Stage s) (rows : ℕ) (tail : Tapes 23 a) :
    saved v rows tail = (bank (initial v rows)).append (savedTail v tail) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals fin_cases i <;> simp [input,savedTail,stack,setTape,Tapes.append,Fin.addCases]

/-- Only the three changed fields are cleared; equal retained parent/child
fields therefore give exactly the same clean restoration input. -/
theorem cleared_initial_eq {s : Shape} (old new : Stage s) (rows : ℕ)
    (hslots : old.slots = new.slots) (hrho : old.rho = new.rho)
    (hsrc : old.source.val = new.source.val) (htarget : old.target.val = new.target.val) :
    cleared (initial new rows) = cleared (initial old rows) := by
  funext i
  fin_cases i <;> simp [cleared,initial,ActivePrefixStageHeadersData.originalValues,
    Function.update,hslots,hrho,hsrc,htarget]

private theorem setTape_append_right {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p = v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; omega

private theorem restore_state {s : Shape} (old : Stage s) (rows : ℕ) :
    ActiveRepairRankHeadersCommands.put (ActiveRepairRankHeadersCommands.put
      (ActiveRepairRankHeadersCommands.put (cleared (initial old rows)) 9 old.right) 8 old.left) 7 old.f =
      initial old rows := by
  funext i
  fin_cases i <;> simp [cleared,ActiveRepairRankHeadersCommands.put,initial,
    ActivePrefixStageHeadersData.originalValues,Function.update]

private theorem restored_eq {s : Shape} (old : Stage s) (rows : ℕ) (tail : Tapes 23 a) :
    setTape (setTape (setTape (setTape
      ((bank (cleared (initial old rows))).append (savedTail old tail)) stack (tail.tape 21) (tail.head 21))
      (focus 2) (BinaryDescriptorStack.descriptor (data old 2)) 1)
      (focus 1) (BinaryDescriptorStack.descriptor (data old 1)) 1)
      (focus 0) (BinaryDescriptorStack.descriptor (data old 0)) 1 = input old rows tail := by
  change setTape (setTape (setTape (setTape
      ((bank (cleared (initial old rows))).append (savedTail old tail))
      (Fin.natAdd 43 (21 : Fin 23)) (tail.tape 21) (tail.head 21))
      (Fin.castAdd 23 (Fin.castAdd 15 (9 : Fin 28))) (BinaryDescriptorStack.descriptor (bits old.right)) 1)
      (Fin.castAdd 23 (Fin.castAdd 15 (8 : Fin 28))) (BinaryDescriptorStack.descriptor (bits old.left)) 1)
      (Fin.castAdd 23 (Fin.castAdd 15 (7 : Fin 28))) (BinaryDescriptorStack.descriptor (bits old.f)) 1 = _
  rw [setTape_append_right]
  simp only [savedTail,setTape_setTape,setTape_self]
  rw [setTape_append_left,setTape_append_left,setTape_append_left]
  simp only [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  unfold bank CleanSubbank.bank
  rw [setTape_append_left,setTape_append_left,setTape_append_left]
  rw [← ActiveRepairRankHeadersCommands.put_caller,
    ← ActiveRepairRankHeadersCommands.put_caller,← ActiveRepairRankHeadersCommands.put_caller,
    restore_state]
  rfl

/-- Popping the saved descriptors after cleanup returns the entire original
parent bank, including the exact stack tape and head and raw role payload. -/
theorem restore_parent {s : Shape} (old : Stage s) (rows : ℕ) (tail : Tapes 23 a)
    (hblank : ∀ z, tail.head 21 ≤ z → tail.tape 21 z = blank) :
    HoareTime restoreProgram
      (fun w => w=(bank (cleared (initial old rows))).append (savedTail old tail))
      (fun w => w=input old rows tail) (CompactChildHeadersStack.cost (data old)) := by
  have h := restore ((bank (cleared (initial old rows))).append (savedTail old tail))
    (tail.tape 21) (tail.head 21) (data old)
    (by simp [stack,savedTail,setTape,Tapes.append,Fin.addCases])
    (by simp [stack,savedTail,setTape,Tapes.append,Fin.addCases])
    (by intro i; fin_cases i <;> simp [focus,bank,CleanSubbank.bank,caller,
      cleared,Tapes.append,Fin.addCases,Function.update])
    (by intro i; fin_cases i <;> simp [focus,bank,CleanSubbank.bank,caller,
      cleared,Tapes.append,Fin.addCases,Function.update]) hblank
  apply h.consequence (fun _ h => h) _ le_rfl
  intro w hw
  rw [hw]
  exact restored_eq old rows tail

end
end IntegerMultBounds.Machine.CompactComplexChildHeaderFrames
