import IntegerMultBounds.Machine.CompactComplexControllerHeaderStack
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Exact appended-stack parent-header return. Changed child descriptors are
physically erased before the saved parent words are popped; every controller,
payload and stack cell/head outside these three headers is retained literally. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerHeaderReturn
noncomputable section
open CompactComplexControllerNativeFrame
open CompactComplexControllerHeaderStack (focus saved)
open SharedPlacementAlphabet (setTape)
variable {a s : ℕ}

def clear (native : Tapes 66 a) :=
  setTape (setTape (setTape native 7 (fun _ => blank) 0) 8 (fun _ => blank) 0) 9 (fun _ => blank) 0

def clearProgram : Program (tapes s) 12 a :=
  seq (seq (BinaryDescriptorCleanupList.oneProgram (focus 0))
    (BinaryDescriptorCleanupList.oneProgram (focus 1))) (BinaryDescriptorCleanupList.oneProgram (focus 2))

private theorem setTape_append_right {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p=v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; omega

private theorem update_native (control : Tapes 43 a) (queue : Tapes 1 a)
    (native : Tapes 66 a) (storage : Tapes s a) (i : Fin 66) (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (bank control queue native storage) (nativeSlot i) f p=
      bank control queue (setTape native i f p) storage := by
  unfold bank nativeSlot
  rw [setTape_append_right,setTape_append_right,SharedPlacementAlphabet.setTape_append_left]

private theorem update_storage (control : Tapes 43 a) (queue : Tapes 1 a)
    (native : Tapes 66 a) (storage : Tapes s a) (i : Fin s) (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (bank control queue native storage) (storageSlot i) f p=
      bank control queue native (setTape storage i f p) := by
  unfold bank storageSlot
  rw [setTape_append_right,setTape_append_right,setTape_append_right]

/-- Each child's obsolete descriptor cell and marker is physically removed. -/
theorem cleanup (control : Tapes 43 a) (queue : Tapes 1 a) (native : Tapes 66 a)
    (storage : Tapes s a) (words : Fin 3 → List Bool)
    (ht : ∀ i, native.tape (![7,8,9] i)=BinaryDescriptorStack.descriptor (words i))
    (hh : ∀ i, native.head (![7,8,9] i)=1) :
    HoareTime clearProgram (fun v => v=bank control queue native storage)
      (fun v => v=bank control queue (clear native) storage)
      (2*((words 0).length+(words 1).length+(words 2).length)+14) := by
  have h0 := BinaryDescriptorCleanupList.one_hoare (focus (s := s) 0)
    (bank control queue native storage) (words 0)
    (by simpa only [focus,nativeSlot,bank,Tapes.append,Fin.addCases_right,Fin.addCases_left] using ht 0)
    (by simpa only [focus,nativeSlot,bank,Tapes.append,Fin.addCases_right,Fin.addCases_left] using hh 0)
  have h1 := BinaryDescriptorCleanupList.one_hoare (focus (s := s) 1)
    (bank control queue (setTape native 7 (fun _ => blank) 0) storage) (words 1)
    (by simpa [focus,nativeSlot,bank,Tapes.append,setTape] using ht 1)
    (by simpa [focus,nativeSlot,bank,Tapes.append,setTape] using hh 1)
  have h2 := BinaryDescriptorCleanupList.one_hoare (focus (s := s) 2)
    (bank control queue (setTape (setTape native 7 (fun _ => blank) 0) 8 (fun _ => blank) 0) storage) (words 2)
    (by simpa [focus,nativeSlot,bank,Tapes.append,setTape] using ht 2)
    (by simpa [focus,nativeSlot,bank,Tapes.append,setTape] using hh 2)
  simp only [focus] at h0 h1 h2
  rw [update_native] at h0 h1 h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

private theorem native_restored (native : Tapes 66 a) (words : Fin 3 → List Bool)
    (ht : ∀ i, native.tape (![7,8,9] i)=BinaryDescriptorStack.descriptor (words i))
    (hh : ∀ i, native.head (![7,8,9] i)=1) :
    setTape (setTape (setTape (clear native) 9 (BinaryDescriptorStack.descriptor (words 2)) 1)
      8 (BinaryDescriptorStack.descriptor (words 1)) 1)
      7 (BinaryDescriptorStack.descriptor (words 0)) 1=native := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases h7 : i=7
    · subst i; simpa [clear,setTape] using (hh 0).symm
    by_cases h8 : i=8
    · subst i; simpa [clear,setTape] using (hh 1).symm
    by_cases h9 : i=9
    · subst i; simpa [clear,setTape] using (hh 2).symm
    simp [clear,setTape,Function.update,h7,h8,h9]
  · funext i
    by_cases h7 : i=7
    · subst i; simpa [clear,setTape] using (ht 0).symm
    by_cases h8 : i=8
    · subst i; simpa [clear,setTape] using (ht 1).symm
    by_cases h9 : i=9
    · subst i; simpa [clear,setTape] using (ht 2).symm
    simp [clear,setTape,Function.update,h7,h8,h9]

/-- Restore the entire desired native bank and exact older storage snapshot.
The desired bank may already contain the child's computed payload result. -/
theorem restore_parent (stack : Fin s) (control : Tapes 43 a) (queue : Tapes 1 a)
    (native : Tapes 66 a) (storage : Tapes s a) (words : Fin 3 → List Bool)
    (ht : ∀ i, native.tape (![7,8,9] i)=BinaryDescriptorStack.descriptor (words i))
    (hh : ∀ i, native.head (![7,8,9] i)=1)
    (hb : ∀ z, storage.head stack≤z → storage.tape stack z=blank) :
    HoareTime (CompactComplexControllerHeaderStack.restoreProgram stack)
      (fun v => v=bank control queue (clear native) (saved storage stack words))
      (fun v => v=bank control queue native storage) (CompactChildHeadersStack.cost words) := by
  have hp := CompactComplexControllerHeaderStack.restore stack
    (bank control queue (clear native) (saved storage stack words)) (storage.tape stack) (storage.head stack) words
    (by simp only [storageSlot,bank,Tapes.append,Fin.addCases_right,saved,setTape,Function.update_self])
    (by simp only [storageSlot,bank,Tapes.append,Fin.addCases_right,saved,setTape,Function.update_self])
    (by intro i; simp only [focus,nativeSlot,bank,Tapes.append,Fin.addCases_right,Fin.addCases_left];
        fin_cases i <;> simp [clear,setTape])
    (by intro i; simp only [focus,nativeSlot,bank,Tapes.append,Fin.addCases_right,Fin.addCases_left];
        fin_cases i <;> simp [clear,setTape]) hb
  apply hp.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv,update_storage]
  simp only [saved,SharedPlacementAlphabet.setTape_setTape,SharedPlacementAlphabet.setTape_self,focus]
  rw [update_native,update_native,update_native]
  exact congrArg (fun restored => bank control queue restored storage) (native_restored native words ht hh)

end
end IntegerMultBounds.Machine.CompactComplexControllerHeaderReturn
