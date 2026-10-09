import IntegerMultBounds.Machine.CompactComplexControllerHeaderStack
import IntegerMultBounds.Machine.CompactComplexCallReturn

/-! Packed occurrence/coordinate return PCs live on a chosen appended storage
tape. Actual binary-pop dispatch selects the continuation, restoring exactly
the older complete stack while framing the native66 and root controller. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerReturnStack
noncomputable section
open CompactComplexControllerNativeFrame
open CompactComplexCallReturn (addressCount addressWidth codeFor roomFor)
open SharedPlacementAlphabet (setTape)
variable {a s siteCount base : ℕ}

def pc (site : Fin siteCount) (coordinate : Fin base) : Fin (addressCount siteCount base) :=
  ⟨site.val*base+coordinate.val,by
    have hm := Nat.mul_le_mul_right base (Nat.succ_le_of_lt site.isLt)
    rw [Nat.succ_mul] at hm
    have hc := coordinate.isLt
    unfold addressCount
    omega⟩

def saved (storage : Tapes s a) (stack : Fin s) (site : Fin siteCount) (coordinate : Fin base) :=
  setTape storage stack
    (FiniteReturnStack.wordPart (storage.tape stack) (storage.head stack) (codeFor site coordinate)
      (addressWidth siteCount base) le_rfl) (storage.head stack+addressWidth siteCount base)

def pushProgram (stack : Fin s) (site : Fin siteCount) (coordinate : Fin base) :=
  FiniteReturnStackAt.pushProgram (a := a) (storageSlot stack) (codeFor site coordinate)

private theorem setTape_append_right {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p=v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; omega

private theorem update_storage (control : Tapes 43 a) (queue : Tapes 1 a)
    (native : Tapes 66 a) (storage : Tapes s a) (i : Fin s) (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (bank control queue native storage) (storageSlot i) f p=
      bank control queue native (setTape storage i f p) := by
  unfold bank storageSlot
  rw [setTape_append_right,setTape_append_right,setTape_append_right]

theorem push (stack : Fin s) (site : Fin siteCount) (coordinate : Fin base)
    (control : Tapes 43 a) (queue : Tapes 1 a) (native : Tapes 66 a) (storage : Tapes s a) :
    HoareTime (pushProgram stack site coordinate) (fun v => v=bank control queue native storage)
      (fun v => v=bank control queue native (saved storage stack site coordinate))
      (addressWidth siteCount base) := by
  have h := FiniteReturnStackAt.push_hoare (a := a) (storageSlot stack) (codeFor site coordinate)
    (bank control queue native storage)
  apply h.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  unfold FiniteReturnStackAt.pushed
  simp only [storageSlot,bank,Tapes.append,Fin.addCases_right]
  exact update_storage control queue native storage stack _ _

def dispatcher (stack : Fin s) (states : Fin (addressCount siteCount base) → ℕ)
    (family : ∀ p, Program (tapes s) (states p) a) :=
  CompactComplexCallReturn.dispatcher (storageSlot stack) states family

/-- The actual retained bits choose their literal occurrence and residual
coordinate continuation; no return choice is supplied as a runtime input. -/
theorem dispatch (stack : Fin s) (states : Fin (addressCount siteCount base) → ℕ)
    (family : ∀ p, Program (tapes s) (states p) a) (site : Fin siteCount) (coordinate : Fin base)
    (control : Tapes 43 a) (queue : Tapes 1 a) (native : Tapes 66 a) (storage : Tapes s a)
    (B : ℕ) (post : TapePred (tapes s) a)
    (hb : ∀ j<addressWidth siteCount base, storage.tape stack (storage.head stack+j)=blank)
    (hc : HoareTime (family (pc site coordinate))
      (fun v => v=bank control queue native storage) post B) :
    HoareTime (dispatcher stack states family).2
      (fun v => v=bank control queue native (saved storage stack site coordinate)) post
      (addressWidth siteCount base+2+B) := by
  have hcode : codeFor site coordinate=FiniteReturnStack.address (roomFor siteCount base) (pc site coordinate) := rfl
  apply FiniteReturnStackAt.dispatch_hoare (roomFor siteCount base) (storageSlot stack) states family (pc site coordinate)
    (bank control queue native (saved storage stack site coordinate))
    (storage.tape stack) (storage.head stack) B post
    (by simp only [storageSlot,bank,Tapes.append,Fin.addCases_right,saved,setTape,Function.update_self,hcode])
    (by simp only [storageSlot,bank,Tapes.append,Fin.addCases_right,saved,setTape,Function.update_self]) hb
  rw [update_storage]
  simpa only [saved,SharedPlacementAlphabet.setTape_setTape,SharedPlacementAlphabet.setTape_self] using hc

end
end IntegerMultBounds.Machine.CompactComplexControllerReturnStack
