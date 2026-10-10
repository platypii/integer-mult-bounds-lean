import IntegerMultBounds.Machine.CompactComplexControllerDenominator
import IntegerMultBounds.Machine.CompactComplexControllerChildBudget

/-! Certified target-stack bookkeeping composed with the actual physical
child-call prefix. The target descriptor must represent the return exponent
established by a semantic Grid policy. Its physical synthesis from geometry
and the numerical whole-stream child callback remain separate obligations. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerDenominatorEntry
noncomputable section
open CompactComplexControllerNativeFrame (bank tapes storageSlot)
open CompactComplexControllerDenominator (size target stack saveProgram)
open SharedPlacementAlphabet (setTape)
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open CompactComplexControllerChildPrefix (native saved)
open ActiveRepairRankHeadersCommands (State put)
open RecursiveChildQuotientsConstant (bits)
variable {s siteCount : ℕ}

def targets (storage : Tapes (10+s) 2) (n : ℕ) :=
  setTape (setTape storage (⟨9,by omega⟩ : Fin (10+s))
    (BinaryDescriptorStack.frame (storage.tape ⟨9,by omega⟩) (storage.head ⟨9,by omega⟩) (bits n))
    (storage.head ⟨9,by omega⟩+1+(bits n).length)) ⟨8,by omega⟩ (fun _ => blank) 0

private theorem entered_bank (control : Tapes 43 2) (queue : Tapes 1 2) (native : Tapes 66 2)
    (storage : Tapes (10+s) 2) (n : ℕ) :
    CompactComplexControllerDenominator.entered (bank control queue native storage) n=
      bank control queue native (targets storage n) := by
  unfold CompactComplexControllerDenominator.entered CompactComplexControllerDenominator.saved
    CompactComplexControllerDenominator.stack CompactComplexControllerDenominator.target bank storageSlot targets
  rw [SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right]
  simp only [Tapes.append,Fin.addCases_right]

def program (headerStack pcStack : Fin s) (site : Fin siteCount) (slot : Fin arity) :=
  seq (saveProgram (s:=s)) (CompactComplexControllerChildPrefix.program (Fin.natAdd 10 headerStack) (Fin.natAdd 10 pcStack) site slot).2

/-- Save the actual certified denominator target once per child call, then
execute the existing paid original-header child prefix. No stream callback is
assumed, and no semantic choice of target is hidden in the control. -/
theorem entry {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (rows : ℕ)
    (headerStack pcStack : Fin s) (site : Fin siteCount) (st : State)
    (h1 : st 1=some (k+2)) (queue : Tapes 1 2) (tail : Tapes 23 2)
    (storage : Tapes (10+s) 2) (targetN : ℕ)
    (ht : storage.tape ⟨8,by omega⟩=BinaryDescriptorStack.descriptor (bits targetN))
    (hh : storage.head ⟨8,by omega⟩=1) :
    HoareTime (program headerStack pcStack site slot)
      (fun v => v=bank (ActiveRepairRankHeadersCommands.bank st) queue
        (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage)
      (fun v => v=bank (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
        (native (CompactComplexChildHeadersData.child rho visit hactive pair slot) rows tail)
        (saved (targets storage targetN) (Fin.natAdd 10 headerStack) (Fin.natAdd 10 pcStack) site slot
          (CompactComplexChildHeadersData.parent rho visit hactive pair)))
      (4*(bits targetN).length+13+
        CompactComplexControllerChildBudget.entryCost siteCount rho visit hactive pair slot rows) := by
  have h0 := CompactComplexControllerDenominator.save
    (bank (ActiveRepairRankHeadersCommands.bank st) queue
      (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage) targetN
    (by simpa [target,storageSlot,bank,Tapes.append,Fin.addCases] using ht)
    (by simpa [target,storageSlot,bank,Tapes.append,Fin.addCases] using hh)
  rw [entered_bank] at h0
  have h1 := CompactComplexControllerChildPrefix.runs rho visit hactive pair slot rows (Fin.natAdd 10 headerStack) (Fin.natAdd 10 pcStack)
    site st h1 queue tail (targets storage targetN)
  apply (h0.seq h1).consequence (fun _ h => h) (fun _ h => h)
  unfold CompactComplexControllerChildBudget.entryCost
  omega

def restored (storage : Tapes (10+s) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ) :=
  setTape (setTape storage (⟨9,by omega⟩ : Fin (10+s)) f p) ⟨8,by omega⟩
    (BinaryDescriptorStack.descriptor (bits n)) 1

private theorem restored_bank (control : Tapes 43 2) (queue : Tapes 1 2) (native : Tapes 66 2)
    (storage : Tapes (10+s) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ) :
    setTape (setTape (bank control queue native storage) stack f p) target
      (BinaryDescriptorStack.descriptor (bits n)) 1=bank control queue native (restored storage f p n) := by
  unfold stack target bank storageSlot restored
  rw [SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right]

/-- Actual child-header return restores geometry first, then pops the saved
certified semantic target. The computed coefficient payload and live true
denominator survive both operations, ready for the subsequent gap return. -/
def returnProgram (headerStack : Fin s) := seq
  (CompactComplexControllerChildReturn.program (a:=2) (Fin.natAdd 10 headerStack)).2
  (CompactComplexControllerDenominator.restoreProgram (s:=s))

theorem return_restore {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (rows : ℕ)
    (headerStack : Fin s) (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 2) (tail : Tapes 23 2) (storage : Tapes (10+s) 2)
    (hb : ∀ z,storage.head (Fin.natAdd 10 headerStack)≤z → storage.tape (Fin.natAdd 10 headerStack) z=blank)
    (f : ℤ → Fin 6) (p : ℤ) (targetN : ℕ)
    (ht : storage.tape ⟨9,by omega⟩=BinaryDescriptorStack.frame f p (bits targetN))
    (hh : storage.head ⟨9,by omega⟩=p+1+(bits targetN).length)
    (hd : storage.tape ⟨8,by omega⟩=fun _ => blank) (hp : storage.head ⟨8,by omega⟩=0)
    (hf : ∀ z,p≤z → z<p+1+(bits targetN).length → f z=blank) :
    HoareTime (returnProgram headerStack)
      (fun v => v=bank (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
        (native (CompactComplexChildHeadersData.child rho visit hactive pair slot) rows tail)
        (CompactComplexControllerHeaderStack.saved storage (Fin.natAdd 10 headerStack)
          (CompactComplexControllerChildPrefix.data (CompactComplexChildHeadersData.parent rho visit hactive pair))))
      (fun v => v=bank (ActiveRepairRankHeadersCommands.bank st) queue
        (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail)
        (restored storage f p targetN))
      (CompactComplexControllerChildBudget.returnCost rho visit hactive pair slot+2*(bits targetN).length+8) := by
  have h0 := CompactComplexControllerChildReturn.runs rho visit hactive pair slot rows
    (Fin.natAdd 10 headerStack) st h1 queue tail storage hb
  have h2 := CompactComplexControllerDenominator.restore
    (bank (ActiveRepairRankHeadersCommands.bank st) queue
      (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage)
    f p targetN
    (by simpa [stack,storageSlot,bank,Tapes.append,Fin.addCases] using ht)
    (by simpa [stack,storageSlot,bank,Tapes.append,Fin.addCases] using hh)
    (by simpa [target,storageSlot,bank,Tapes.append,Fin.addCases] using hd)
    (by simpa [target,storageSlot,bank,Tapes.append,Fin.addCases] using hp) hf
  rw [restored_bank] at h2
  apply (h0.seq h2).consequence (fun _ h => h) (fun _ h => h)
  unfold CompactComplexControllerChildBudget.returnCost
  omega

end
end IntegerMultBounds.Machine.CompactComplexControllerDenominatorEntry
