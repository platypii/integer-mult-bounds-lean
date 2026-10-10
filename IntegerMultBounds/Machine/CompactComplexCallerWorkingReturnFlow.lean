import IntegerMultBounds.Machine.CompactComplexCallerReturnFlow

/-! The fixed guarded return controller on the literal caller plus blank workspace.
Every permanent role and the immutable original scalar43 bank remain present
through PC decoding. Continuation blocks may back-edge into the same entry;
this placement alone does not establish the complete recursive execution. -/
namespace IntegerMultBounds.Machine.CompactComplexCallerWorkingReturnFlow
noncomputable section
open CompactComplexNativeCodecFrame (permanentTapes)

open CompactComplexCallReturn (addressCount addressWidth roomFor)
open ActiveRepairRankHeadersCommands (State)
variable {s c w siteCount base : ℕ}
abbrev workingTapes (s c w : ℕ) := permanentTapes s c+w

def workingBank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    Tapes (workingTapes s c w) 2 :=
  (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage payload).append
    (SharedBank.empty w 2)

def stackSlot (stack : Fin s) : Fin (workingTapes s c w) :=
  Fin.castAdd w (CompactComplexSpectatorTargetBank.oldSlot stack)

private theorem working_old_bank (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+c) 2) (stack : Fin s) :
    (workingBank (w:=w) control queue scalar stage tail storage payload).head (stackSlot stack)=storage.head stack ∧
    (workingBank (w:=w) control queue scalar stage tail storage payload).tape (stackSlot stack)=storage.tape stack := by
  simpa only [workingBank,stackSlot,Tapes.append,Fin.addCases_left] using
    CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage payload stack

abbrev PCs := Fin (addressCount siteCount base+2)

def program (stack : Fin s) (states : Fin (addressCount siteCount base) → ℕ)
    (blocks : ∀ pc,Program (workingTapes s c w) (states pc) 2)
    (edges : ∀ pc,Fin (states pc) → Option (PCs (siteCount:=siteCount) (base:=base)))
    (entry : PCs (siteCount:=siteCount) (base:=base)) :=
  GuardedFiniteReturnFlow.program (roomFor siteCount base) (stackSlot stack) states blocks edges entry

private theorem workingBank_set (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ) :
    SharedPlacementAlphabet.setTape (workingBank (w:=w) control queue scalar stage tail storage payload)
      (stackSlot stack) f p=
    workingBank (w:=w) control queue scalar stage tail (SharedPlacementAlphabet.setTape storage stack f p) payload := by
  unfold stackSlot workingBank CompactComplexSpectatorTargetBank.oldSlot
    CompactComplexNativeCodecFrame.bank CompactComplexNativeRoleBridge.bank
    CompactComplexControllerNativeFrame.storageSlot CompactComplexControllerNativeFrame.bank
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_left]

private theorem restored (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+c) 2) (stack : Fin s)
    (site : Fin siteCount) (coordinate : Fin base) :
    SharedPlacementAlphabet.setTape
      (workingBank (w:=w) control queue scalar stage tail
        (CompactComplexControllerReturnStack.saved storage stack site coordinate) payload)
      (stackSlot stack) (storage.tape stack) (storage.head stack)=
      workingBank (w:=w) control queue scalar stage tail storage payload := by
  rw [workingBank_set]
  simp only [CompactComplexControllerReturnStack.saved,
    SharedPlacementAlphabet.setTape_setTape,SharedPlacementAlphabet.setTape_self]

/-- Actual saved site/coordinate bits decode the continuation on the full
caller bank, retaining live7, all role payloads and original scalar metadata. -/
theorem return_ready (stack : Fin s) (states : Fin (addressCount siteCount base) → ℕ)
    (blocks : ∀ pc,Program (workingTapes s c w) (states pc) 2)
    (edges : ∀ pc,Fin (states pc) → Option (PCs (siteCount:=siteCount) (base:=base)))
    (entry : PCs (siteCount:=siteCount) (base:=base))
    (site : Fin siteCount) (coordinate : Fin base)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2)
    (hw : 0<addressWidth siteCount base)
    (hb : ∀ j<addressWidth siteCount base,storage.tape stack (storage.head stack+j)=blank) :
    let before := workingBank (w:=w) control queue scalar stage tail
      (CompactComplexControllerReturnStack.saved storage stack site coordinate) payload
    let after := workingBank (w:=w) control queue scalar stage tail storage payload
    let pc := CompactComplexControllerReturnStack.pc site coordinate
    run (program stack states blocks edges entry) (addressWidth siteCount base+5)
      ((before.start (FiniteReturnGuard.program (stackSlot stack))).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) 0))=
      some ((after.start (blocks pc)).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) pc.succ.succ)) := by
  dsimp only
  let saved := CompactComplexControllerReturnStack.saved storage stack site coordinate
  have hworkingBank := working_old_bank (w:=w) control queue scalar stage tail saved payload stack
  have hr := GuardedFiniteReturnFlow.return_ready (roomFor siteCount base) hw (stackSlot stack)
    states blocks edges entry (CompactComplexControllerReturnStack.pc site coordinate)
    (workingBank (w:=w) control queue scalar stage tail saved payload) (storage.tape stack) (storage.head stack)
    (hworkingBank.2.trans (by simp only [saved,CompactComplexControllerReturnStack.saved,
      SharedPlacementAlphabet.setTape,Function.update_self];rfl))
    (hworkingBank.1.trans (by simp only [saved,CompactComplexControllerReturnStack.saved,
      SharedPlacementAlphabet.setTape,Function.update_self])) hb
  rw [restored] at hr
  exact hr

/-- The empty original root PC stack halts the same fixed controller. -/
theorem root_halt (stack : Fin s) (states : Fin (addressCount siteCount base) → ℕ)
    (blocks : ∀ pc,Program (workingTapes s c w) (states pc) 2)
    (edges : ∀ pc,Fin (states pc) → Option (PCs (siteCount:=siteCount) (base:=base)))
    (entry : PCs (siteCount:=siteCount) (base:=base))
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2)
    (hb : storage.tape stack (storage.head stack-1)=blank) :
    let v := workingBank (w:=w) control queue scalar stage tail storage payload
    run (program stack states blocks edges entry) 2
      ((v.start (FiniteReturnGuard.program (stackSlot stack))).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) 0))=
      some ((FiniteReturnGuard.terminal v true).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) 0)) ∧
    step (program stack states blocks edges entry)
      ((FiniteReturnGuard.terminal v true).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) 0))=none := by
  have hworkingBank := working_old_bank (w:=w) control queue scalar stage tail storage payload stack
  exact GuardedFiniteReturnFlow.root_halt (roomFor siteCount base) (stackSlot stack) states blocks edges entry
    _ (by rw [hworkingBank.1,hworkingBank.2];exact hb)

/-- A real terminal continuation may re-enter the same fixed recursive entry
or the return guard, paying one tape-preserving transition. -/
theorem continuation_jump (stack : Fin s) (states : Fin (addressCount siteCount base) → ℕ)
    (blocks : ∀ pc,Program (workingTapes s c w) (states pc) 2)
    (edges : ∀ pc,Fin (states pc) → Option (PCs (siteCount:=siteCount) (base:=base)))
    (entry : PCs (siteCount:=siteCount) (base:=base))
    (pc : Fin (addressCount siteCount base)) (dest : PCs (siteCount:=siteCount) (base:=base))
    (v : Tapes (workingTapes s c w) 2) (n : ℕ) (out : Config (workingTapes s c w) (states pc) 2)
    (hr : run (blocks pc) n (v.start (blocks pc))=some out)
    (hh : step (blocks pc) out=none) (he : edges pc out.state=some dest) :
    run (program stack states blocks edges entry) (n+1)
      ((v.start (blocks pc)).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) pc.succ.succ))=
      some ((out.tapes.start (GuardedFiniteReturnFlow.family (stackSlot stack) states blocks dest)).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) dest)) :=
  GuardedFiniteReturnFlow.continuation_jump (roomFor siteCount base) (stackSlot stack)
    states blocks edges entry pc dest v n out hr hh he

end
end IntegerMultBounds.Machine.CompactComplexCallerWorkingReturnFlow
