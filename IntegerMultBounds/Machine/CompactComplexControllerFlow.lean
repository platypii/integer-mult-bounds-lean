import IntegerMultBounds.Machine.GuardedFiniteReturnFlow
import IntegerMultBounds.Machine.CompactComplexControllerReturnStack

/-! Guarded cyclic control on the actual controller43/queue1/native66 bank.
The return PC lives in appended storage, outside every original native tape;
fixed continuation blocks may back-edge into the same shared recursive entry.
Concrete role-block execution remains an explicit integration obligation. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerFlow
noncomputable section
open CompactComplexControllerNativeFrame
open CompactComplexCallReturn (addressCount addressWidth roomFor codeFor)
variable {a s siteCount base : ℕ}
abbrev addresses := addressCount siteCount base
abbrev PCs := Fin (addresses (siteCount := siteCount) (base := base)+2)
/-- At least two fixed return addresses give the necessary observable PC bit. -/
theorem width_positive (h : 2≤addressCount siteCount base) : 0<addressWidth siteCount base :=
  Nat.clog_pos (by decide) (by omega)

def program (stack : Fin s) (states : Fin (addressCount siteCount base) → ℕ)
    (blocks : ∀ pc, Program (tapes s) (states pc) a)
    (edges : ∀ pc, Fin (states pc) → Option (PCs (siteCount := siteCount) (base := base)))
    (entry : PCs (siteCount := siteCount) (base := base)) :=
  GuardedFiniteReturnFlow.program (roomFor siteCount base) (storageSlot stack) states blocks edges entry

private theorem setTape_append_right {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    SharedPlacementAlphabet.setTape (v.append w) (Fin.natAdd l i) f p=
      v.append (SharedPlacementAlphabet.setTape w i f p) := by
  unfold SharedPlacementAlphabet.setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; omega

private theorem restore_snapshot (control : Tapes 43 a) (queue : Tapes 1 a)
    (native : Tapes 66 a) (storage : Tapes s a) (stack : Fin s)
    (site : Fin siteCount) (coordinate : Fin base) :
    SharedPlacementAlphabet.setTape
      (bank control queue native (CompactComplexControllerReturnStack.saved storage stack site coordinate))
      (storageSlot stack) (storage.tape stack) (storage.head stack)=bank control queue native storage := by
  unfold bank storageSlot
  rw [setTape_append_right,setTape_append_right,setTape_append_right]
  simp only [CompactComplexControllerReturnStack.saved,SharedPlacementAlphabet.setTape_setTape,
    SharedPlacementAlphabet.setTape_self]

/-- Actual saved occurrence/coordinate bits select the continuation start and
restore the whole older storage snapshot in exactly width+5 transitions. -/
theorem return_ready (stack : Fin s) (states : Fin (addressCount siteCount base) → ℕ)
    (blocks : ∀ pc, Program (tapes s) (states pc) a)
    (edges : ∀ pc, Fin (states pc) → Option (PCs (siteCount := siteCount) (base := base)))
    (entry : PCs (siteCount := siteCount) (base := base))
    (site : Fin siteCount) (coordinate : Fin base)
    (control : Tapes 43 a) (queue : Tapes 1 a) (native : Tapes 66 a) (storage : Tapes s a)
    (hw : 0<addressWidth siteCount base)
    (hb : ∀ j<addressWidth siteCount base, storage.tape stack (storage.head stack+j)=blank) :
    let before := bank control queue native (CompactComplexControllerReturnStack.saved storage stack site coordinate)
    let after := bank control queue native storage
    let pc := CompactComplexControllerReturnStack.pc site coordinate
    run (program stack states blocks edges entry) (addressWidth siteCount base+5)
      ((before.start (FiniteReturnGuard.program (storageSlot stack))).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) 0))=
      some ((after.start (blocks pc)).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) pc.succ.succ)) := by
  dsimp only
  have ht : (bank control queue native (CompactComplexControllerReturnStack.saved storage stack site coordinate)).tape
      (storageSlot stack)=FiniteReturnStack.wordPart (storage.tape stack) (storage.head stack)
        (FiniteReturnStack.address (roomFor siteCount base) (CompactComplexControllerReturnStack.pc site coordinate))
          (addressWidth siteCount base) le_rfl := by
    simp only [storageSlot,bank,Tapes.append,Fin.addCases_right,
      CompactComplexControllerReturnStack.saved,SharedPlacementAlphabet.setTape,Function.update_self]
    rfl
  have hh : (bank control queue native (CompactComplexControllerReturnStack.saved storage stack site coordinate)).head
      (storageSlot stack)=storage.head stack+addressWidth siteCount base := by
    simp only [storageSlot,bank,Tapes.append,Fin.addCases_right,
      CompactComplexControllerReturnStack.saved,SharedPlacementAlphabet.setTape,Function.update_self]
  have hr := GuardedFiniteReturnFlow.return_ready (roomFor siteCount base) hw (storageSlot stack)
    states blocks edges entry (CompactComplexControllerReturnStack.pc site coordinate)
    (bank control queue native (CompactComplexControllerReturnStack.saved storage stack site coordinate))
    (storage.tape stack) (storage.head stack) ht hh hb
  rw [restore_snapshot] at hr
  exact hr

/-- Empty root return really halts and preserves all original banks and storage. -/
theorem root_halt (stack : Fin s) (states : Fin (addressCount siteCount base) → ℕ)
    (blocks : ∀ pc, Program (tapes s) (states pc) a)
    (edges : ∀ pc, Fin (states pc) → Option (PCs (siteCount := siteCount) (base := base)))
    (entry : PCs (siteCount := siteCount) (base := base))
    (control : Tapes 43 a) (queue : Tapes 1 a) (native : Tapes 66 a) (storage : Tapes s a)
    (hb : storage.tape stack (storage.head stack-1)=blank) :
    let v := bank control queue native storage
    run (program stack states blocks edges entry) 2
      ((v.start (FiniteReturnGuard.program (storageSlot stack))).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) 0))=
      some ((FiniteReturnGuard.terminal v true).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) 0)) ∧
    step (program stack states blocks edges entry)
      ((FiniteReturnGuard.terminal v true).mapState
        (FiniteFlow.embed (GuardedFiniteReturnFlow.states states) 0))=none := by
  exact GuardedFiniteReturnFlow.root_halt (roomFor siteCount base) (storageSlot stack)
    states blocks edges entry _
    (by simpa only [storageSlot,bank,Tapes.append,Fin.addCases_right] using hb)

end
end IntegerMultBounds.Machine.CompactComplexControllerFlow
