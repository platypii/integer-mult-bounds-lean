import IntegerMultBounds.Machine.CompactComplexControllerNativeFrame

/-! Persistent descriptor frames live on appended recursion-storage tapes,
strictly after the complete native66 bank. Saving/restoring them retains the
whole controller, native payload and every other persistent storage tape. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerHeaderStack
noncomputable section
open CompactComplexControllerNativeFrame
open SharedPlacementAlphabet (setTape)
variable {a s : ℕ}

def focus : Fin 3 → Fin (tapes s) := fun i => nativeSlot (![7,8,9] i)
theorem focus_injective : Function.Injective (focus (s := s)) := by
  intro i j h
  have hn := native_injective h
  fin_cases i <;> fin_cases j <;> simp_all

theorem distinct (stack : Fin s) : ∀ i, focus (s := s) i≠storageSlot stack := by
  intro i h
  have hv := congrArg Fin.val h
  simp only [focus,nativeSlot,storageSlot,Fin.val_natAdd,Fin.val_castAdd] at hv
  have hi : (![7,8,9] i : Fin 66).val<66 := (![7,8,9] i : Fin 66).isLt
  omega

def saveProgram (stack : Fin s) :=
  CompactChildHeadersStack.saveProgram (a := a) focus (storageSlot stack) (distinct stack)
def restoreProgram (stack : Fin s) :=
  CompactChildHeadersStack.restoreProgram (a := a) focus (storageSlot stack) (distinct stack)

def saved (storage : Tapes s a) (stack : Fin s) (data : Fin 3 → List Bool) :=
  setTape storage stack (CompactChildHeadersStack.frames (storage.tape stack) (storage.head stack) data)
    (CompactChildHeadersStack.top (storage.head stack) data)

private theorem setTape_append_right {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p=v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; omega

private theorem saved_bank (control : Tapes 43 a) (queue : Tapes 1 a) (native : Tapes 66 a)
    (storage : Tapes s a) (stack : Fin s) (data : Fin 3 → List Bool) :
    setTape (bank control queue native storage) (storageSlot stack)
      (CompactChildHeadersStack.frames (storage.tape stack) (storage.head stack) data)
      (CompactChildHeadersStack.top (storage.head stack) data)=bank control queue native (saved storage stack data) := by
  unfold bank storageSlot saved
  rw [setTape_append_right,setTape_append_right,setTape_append_right]

/-- The native scratch bank is unchanged, so the saved parent descriptors
survive arbitrary intervening native stage routines. -/
theorem save (stack : Fin s) (control : Tapes 43 a) (queue : Tapes 1 a)
    (native : Tapes 66 a) (storage : Tapes s a) (data : Fin 3 → List Bool)
    (ht : ∀ i, native.tape (![7,8,9] i)=BinaryDescriptorStack.descriptor (data i))
    (hh : ∀ i, native.head (![7,8,9] i)=1) :
    HoareTime (saveProgram stack) (fun v => v=bank control queue native storage)
      (fun v => v=bank control queue native (saved storage stack data)) (CompactChildHeadersStack.cost data) := by
  have hp := CompactChildHeadersStack.save focus (storageSlot stack) (distinct stack)
    (bank control queue native storage) data
    (by intro i; simpa only [focus,nativeSlot,bank,Tapes.append,Fin.addCases_right,Fin.addCases_left] using ht i)
    (by intro i; simpa only [focus,nativeSlot,bank,Tapes.append,Fin.addCases_right,Fin.addCases_left] using hh i)
  apply hp.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  simpa only [storageSlot,bank,Tapes.append,Fin.addCases_right] using saved_bank control queue native storage stack data

/-- After the changed header destinations have been physically erased, pop
all three actual saved descriptors. No native private tape stores a frame. -/
theorem restore (stack : Fin s) (v : Tapes (tapes s) a) (f : ℤ → Fin (a+4))
    (p : ℤ) (data : Fin 3 → List Bool)
    (ht : v.tape (storageSlot stack)=CompactChildHeadersStack.frames f p data)
    (hh : v.head (storageSlot stack)=CompactChildHeadersStack.top p data)
    (hd : ∀ i, v.tape (focus i)=fun _ => blank) (hp : ∀ i, v.head (focus i)=0)
    (hb : ∀ z, p≤z → f z=blank) :
    HoareTime (restoreProgram stack) (fun w => w=v)
      (fun w => w=setTape (setTape (setTape (setTape v (storageSlot stack) f p)
        (focus 2) (BinaryDescriptorStack.descriptor (data 2)) 1)
        (focus 1) (BinaryDescriptorStack.descriptor (data 1)) 1)
        (focus 0) (BinaryDescriptorStack.descriptor (data 0)) 1)
      (CompactChildHeadersStack.cost data) :=
  CompactChildHeadersStack.restore focus focus_injective (storageSlot stack) (distinct stack)
    v f p data ht hh hd hp hb

end
end IntegerMultBounds.Machine.CompactComplexControllerHeaderStack
