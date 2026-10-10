import IntegerMultBounds.Machine.CompactComplexControllerNativeFrame
import IntegerMultBounds.Machine.CompactComplexExponentStep
import IntegerMultBounds.Machine.BinaryDescriptorStackAt
import IntegerMultBounds.Machine.NativeSignedGapHeadersReturn

/-! True coefficient denominator storage, separate from geometric controller k
and signed-width metadata. Storage7 is live, storage8 is the certified return
target, and storage9 is its nested stack. Slots0..8 exactly match the source43
return adapter suffix. Target policy must come from an actual Grid theorem;
saving parent input precision alone is not generally a valid return policy. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerDenominator
noncomputable section
open CompactComplexControllerNativeFrame (tapes storageSlot nativeSlot)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s : ℕ}

abbrev size (s : ℕ) := tapes (10+s)
def current : Fin (size s) := storageSlot ⟨7,by omega⟩
def target : Fin (size s) := storageSlot ⟨8,by omega⟩
def stack : Fin (size s) := storageSlot ⟨9,by omega⟩
private theorem current_target : (current : Fin (size s))≠target := by
  intro h
  have hh := congrArg Fin.val h
  simp [current,target,storageSlot] at hh
private theorem target_stack : (target : Fin (size s))≠stack := by
  intro h
  have hh := congrArg Fin.val h
  simp [target,stack,storageSlot] at hh

/-- One increment belongs at whole-scalar-gate completion, outside its record
loop. No coefficient-stream execution or numerical callback is asserted here. -/
def incrementProgram := CompactComplexExponentStep.ascendProgram (a:=2) (current (s:=s))
theorem increment (v : Tapes (size s) 2) (n : ℕ)
    (ht : v.tape current=BinaryDescriptorStack.descriptor (bits n)) (hh : v.head current=1) :
    HoareTime incrementProgram (fun w => w=v)
      (fun w => w=setTape v current (BinaryDescriptorStack.descriptor (bits (n+1))) 1) (2*(n+2)) :=
  CompactComplexExponentStep.ascend current v n ht hh

def saved (v : Tapes (size s) 2) (n : ℕ) :=
  setTape v stack (BinaryDescriptorStack.frame (v.tape stack) (v.head stack) (bits n))
    (v.head stack+1+(bits n).length)
def entered (v : Tapes (size s) 2) (n : ℕ) := setTape (saved v n) target (fun _ => blank) 0

def saveProgram := seq (BinaryDescriptorStackAt.pushProgram (a:=2) (target (s:=s)) stack target_stack)
  (BinaryDescriptorCleanupList.oneProgram (a:=2) target)

/-- Push the already certified return target and clear its port for nested
children. The live denominator and every caller/native tape are retained. -/
theorem save (v : Tapes (size s) 2) (n : ℕ)
    (ht : v.tape target=BinaryDescriptorStack.descriptor (bits n)) (hh : v.head target=1) :
    HoareTime saveProgram (fun w => w=v) (fun w => w=entered v n) (4*(bits n).length+12) := by
  have h0 := BinaryDescriptorStackAt.push_hoare target stack target_stack v (bits n) ht hh
  have h1 := BinaryDescriptorCleanupList.one_hoare target (saved v n) (bits n)
    (by simp only [saved,setTape,Function.update_of_ne target_stack,ht])
    (by simp only [saved,setTape,Function.update_of_ne target_stack,hh])
  apply (h0.seq h1).consequence (fun _ h => h) (fun _ h => h)
  omega

def restoreProgram := BinaryDescriptorStackAt.popProgram (a:=2) (stack (s:=s)) target (Ne.symm target_stack)

/-- Pop exactly the saved semantic target after arbitrary child denominator
progression. Popping changes no live denominator or native coefficient tape. -/
theorem restore (v : Tapes (size s) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ)
    (ht : v.tape stack=BinaryDescriptorStack.frame f p (bits n))
    (hh : v.head stack=p+1+(bits n).length)
    (hd : v.tape target=fun _ => blank) (hp : v.head target=0)
    (hf : ∀ z,p≤z → z<p+1+(bits n).length → f z=blank) :
    HoareTime restoreProgram (fun w => w=v)
      (fun w => w=setTape (setTape v stack f p) target (BinaryDescriptorStack.descriptor (bits n)) 1)
      (2*(bits n).length+7) :=
  BinaryDescriptorStackAt.pop_hoare stack target (Ne.symm target_stack) v f p (bits n) ht hh hd hp hf

def copySlots : Fin 2 → Fin (size s) := ![target,current]
private theorem copy_injective : Function.Injective (copySlots (s:=s)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copySlots,current_target,Ne.symm current_target]
def commitProgram := seq (BinaryDescriptorCleanupList.oneProgram (a:=2) (current (s:=s)))
  (seq (BinaryDescriptorCopyPlaced.program (a:=2) copySlots copy_injective)
    (BinaryDescriptorCleanupList.oneProgram (a:=2) target))
def committed (v : Tapes (size s) 2) (n : ℕ) :=
  setTape (setTape v current (RadixZeroFill.encodedBinary (bits n)) 1) target (fun _ => blank) 0

/-- Install a certified target only after the coefficient return. This theorem
is descriptor mechanics; it does not itself assert numerical normalization. -/
theorem commit (v : Tapes (size s) 2) (n targetN : ℕ)
    (hc : v.tape current=BinaryDescriptorStack.descriptor (bits n)) (hch : v.head current=1)
    (ht : v.tape target=BinaryDescriptorStack.descriptor (bits targetN)) (hth : v.head target=1) :
    HoareTime commitProgram (fun w => w=v) (fun w => w=committed v targetN)
      (2*(bits n).length+4*(bits targetN).length+15) := by
  let erased := setTape v current (fun _ => blank) 0
  let copied := setTape erased current (RadixZeroFill.encodedBinary (bits targetN)) 1
  have h0 := BinaryDescriptorCleanupList.one_hoare current v (bits n) hc hch
  have h1 := BinaryDescriptorCopyPlaced.copies erased copySlots copy_injective (bits targetN) (by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals dsimp only [BinaryDescriptorCopy.encodedInput]
    all_goals simp [erased,copySlots,setTape,Ne.symm current_target,ht,hth,
      Copy.cfg,BinaryDescriptorStackRoundtrip.descriptor_encoded])
  have h2 := BinaryDescriptorCleanupList.one_hoare target copied (bits targetN)
    (by simp [copied,erased,setTape,Ne.symm current_target,ht])
    (by simp [copied,erased,setTape,Ne.symm current_target,hth])
  apply (h0.seq (h1.seq h2)).consequence (fun _ h => h) _ (by omega)
  rintro w rfl
  simp only [copied,erased,SharedPlacementAlphabet.setTape_setTape,committed]

/-- The return adapter's source43 and appended73/74 map to the actual root
native source and storage7/8. Storage9 and all older stacks are outside it. -/
def returnSlots : Fin 10 → Fin (size s) := fun i =>
  if i.val=0 then nativeSlot 43 else storageSlot ⟨i.val-1,by have := i.isLt; omega⟩
private theorem return_injective : Function.Injective (returnSlots (s:=s)) := by
  intro i j h
  have hv := congrArg Fin.val h
  unfold returnSlots at hv
  split_ifs at hv
  all_goals simp only [nativeSlot,storageSlot,Fin.val_natAdd,Fin.val_castAdd] at hv
  all_goals apply Fin.ext; omega

def returnPlacement := InjectivePlacement.placement (returnSlots (s:=s)) return_injective
  (by unfold size tapes; omega : 10+(size s-10)=size s)
def returnProgram := Placement.placed NativeSignedGapHeadersReturn.program (returnPlacement (s:=s))
def returned (v : Tapes (size s) 2) (ws : List RadixSignedShiftRight.Word) (n targetN : ℕ) (ls : List Bool) :=
  Placement.replace returnPlacement v (NativeSignedGapHeadersReturn.output ws n targetN ls)
def returnCommitProgram := seq (returnProgram (s:=s)) commitProgram

private theorem returned_current (v : Tapes (size s) 2)
    (ws : List RadixSignedShiftRight.Word) (n targetN : ℕ) (ls : List Bool) :
    (returned v ws n targetN ls).tape current=BinaryDescriptorStack.descriptor (bits n) ∧
    (returned v ws n targetN ls).head current=1 := by
  have ht := InjectivePlacement.replace_tape_slot returnSlots return_injective
    (show 10+(size s-10)=size s by unfold size tapes; omega) v
    (NativeSignedGapHeadersReturn.output ws n targetN ls) (8:Fin 10)
  have hh := InjectivePlacement.replace_head_slot returnSlots return_injective
    (show 10+(size s-10)=size s by unfold size tapes; omega) v
    (NativeSignedGapHeadersReturn.output ws n targetN ls) (8:Fin 10)
  constructor
  · change (returned v ws n targetN ls).tape (returnSlots 8)=_
    change (Placement.replace (InjectivePlacement.placement returnSlots return_injective _) v
      (NativeSignedGapHeadersReturn.output ws n targetN ls)).tape (returnSlots _) = _
    rw [ht]
    change RadixZeroFill.encodedBinary _=_
    rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  · exact hh

private theorem returned_target (v : Tapes (size s) 2)
    (ws : List RadixSignedShiftRight.Word) (n targetN : ℕ) (ls : List Bool) :
    (returned v ws n targetN ls).tape target=BinaryDescriptorStack.descriptor (bits targetN) ∧
    (returned v ws n targetN ls).head target=1 := by
  have ht := InjectivePlacement.replace_tape_slot returnSlots return_injective
    (show 10+(size s-10)=size s by unfold size tapes; omega) v
    (NativeSignedGapHeadersReturn.output ws n targetN ls) (9:Fin 10)
  have hh := InjectivePlacement.replace_head_slot returnSlots return_injective
    (show 10+(size s-10)=size s by unfold size tapes; omega) v
    (NativeSignedGapHeadersReturn.output ws n targetN ls) (9:Fin 10)
  constructor
  · change (returned v ws n targetN ls).tape (returnSlots 9)=_
    change (Placement.replace (InjectivePlacement.placement returnSlots return_injective _) v
      (NativeSignedGapHeadersReturn.output ws n targetN ls)).tape (returnSlots _) = _
    rw [ht]
    change RadixZeroFill.encodedBinary _=_
    rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  · exact hh

/-- The target becomes live only after the physical precision-return pass.
The coefficient Grid premise for value preservation is supplied separately by
actual semantic return theorems; target selection is never identified with n. -/
theorem return_commit (v : Tapes (size s) 2) (ws : List RadixSignedShiftRight.Word)
    (n targetN : ℕ) (hle : targetN≤n) (hd : ∀ w∈ws,n-targetN≤w.length) (hn : ws≠[])
    (ls : List Bool) (hlen : Counter.value ls=NativeSignedReturnStream.volume ws)
    (hl : GrowingCounterData.Canonical ls)
    (ha : Placement.active returnPlacement v=NativeSignedGapHeadersReturn.input ws n targetN ls) :
    HoareTime returnCommitProgram (fun w => w=v)
      (fun w => w=committed (returned v ws n targetN ls) targetN)
      (NativeSignedGapHeadersReturn.cost ws n targetN+2*(bits n).length+4*(bits targetN).length+16) := by
  have h0 := NativeSignedGapHeadersReturn.runs_at returnPlacement v ws n targetN hle hd hn ls hlen hl ha
  have hc := returned_current v ws n targetN ls
  have ht := returned_target v ws n targetN ls
  have h1 := commit (returned v ws n targetN ls) n targetN hc.1 hc.2 ht.1 ht.2
  apply (h0.seq h1).consequence (fun _ h => h) (fun _ h => h)
  omega

end
end IntegerMultBounds.Machine.CompactComplexControllerDenominator
