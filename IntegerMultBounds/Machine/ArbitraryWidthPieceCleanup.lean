import IntegerMultBounds.Machine.ArbitraryWidthPieceSetup

/-! Every final marked digit-dispatcher control is physically erased. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPieceCleanup
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitraryWidthConsumePlacement (S T parent)
open ArbitraryWidthPieceSetup (bare input offsetSlot offsetGlobal remainingSlot)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

def globalSlot (slot : Fin S) : Fin T := Fin.natAdd 14 (Fin.castAdd 6 slot)

theorem set_middle (ns : List Bool) (slice : Tapes S prime) (level : Tapes 6 prime)
    (slot : Fin S) (f : ℤ → Fin (prime+4)) (p : ℤ) :
    setTape (parent ns slice level) (globalSlot slot) f p = parent ns (setTape slice slot f p) level := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    have hn : Fin.castAdd (S+6) i ≠ globalSlot slot := by
      intro he
      have hh := congrArg Fin.val he
      simp only [globalSlot,Fin.val_natAdd,Fin.val_castAdd] at hh
      have := i.isLt
      omega
    simp only [setTape,parent,Tapes.append,Fin.addCases_left,Function.update_of_ne hn]
  | right i =>
    induction i using Fin.addCases with
    | left i =>
      by_cases hi : i = slot
      · subst i
        simp only [setTape,parent,globalSlot,Tapes.append,Fin.addCases_right,
          Fin.addCases_left,Function.update_self]
      · have hn : Fin.natAdd 14 (Fin.castAdd 6 i) ≠ globalSlot slot := by
          intro he
          apply hi
          exact Fin.ext (by simpa only [globalSlot,Fin.val_natAdd,Fin.val_castAdd,
            Nat.add_left_cancel_iff] using congrArg Fin.val he)
        simp only [setTape,parent,Tapes.append,Fin.addCases_right,Fin.addCases_left,
          Function.update_of_ne hn,Function.update_of_ne hi]
    | right i =>
      have hn : Fin.natAdd 14 (Fin.natAdd S i) ≠ globalSlot slot := by
        intro he
        have hh := congrArg Fin.val he
        simp only [globalSlot,Fin.val_natAdd,Fin.val_castAdd] at hh
        have := slot.isLt
        omega
      simp only [setTape,parent,Tapes.append,Fin.addCases_right,Function.update_of_ne hn]

theorem erase_middle (ns : List Bool) (slice : Tapes S prime) (level : Tapes 6 prime)
    (slot : Fin S) (xs : List Bool) (ht : slice.tape slot = RadixZeroFill.encodedBinary xs)
    (hh : slice.head slot = 1) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram (globalSlot slot))
      (fun z => z = parent ns slice level)
      (fun z => z = parent ns (setTape slice slot (fun _ => blank) 0) level) (2*xs.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (globalSlot slot) (parent ns slice level) xs
    (by simpa only [parent,globalSlot,Tapes.append,Fin.addCases_right,Fin.addCases_left] using ht.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded xs).symm)
    (by simpa only [parent,globalSlot,Tapes.append,Fin.addCases_right,Fin.addCases_left] using hh)
  rw [set_middle] at h
  exact h

theorem cleared_slice (root : Tapes ArbitrarySliceCall.rootCount prime) (frame : Tapes 1 prime)
    (ts bs : List Bool) :
    setTape (setTape (root.append (SliceHeaderPlacement.tail ts bs frame))
      ArbitraryWidthLevelPlacement.widthSlot (fun _ => blank) 0)
      offsetSlot (fun _ => blank) 0 = bare root frame := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    have ho : Fin.castAdd 12 i ≠ offsetSlot := by
      intro he
      have hh := congrArg Fin.val he
      simp only [offsetSlot,Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero] at hh
      have := i.isLt
      omega
    have hw : Fin.castAdd 12 i ≠ ArbitraryWidthLevelPlacement.widthSlot := by
      intro he
      have hh := congrArg Fin.val he
      simp only [ArbitraryWidthLevelPlacement.widthSlot,Fin.val_castAdd,Fin.val_natAdd,Fin.val_one] at hh
      have := i.isLt
      omega
    simp only [setTape,Tapes.append,Fin.addCases_left,
      Function.update_of_ne ho,Function.update_of_ne hw]
  | right i =>
    fin_cases i
    all_goals simp [setTape,offsetSlot,ArbitraryWidthLevelPlacement.widthSlot,
      Tapes.append,SliceHeaderPlacement.tail,SharedBank.empty]; rfl

theorem erased_remaining (ns : List Bool) (slice : Tapes S prime) :
    setTape (parent ns slice (SharedBank.empty 6 prime)) remainingSlot (fun _ => blank) 0 =
      ArbitraryWidthPieceSetup.input slice := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    fin_cases i <;> simp [setTape,parent,remainingSlot,ArbitraryWidthPieceCounter.input,Tapes.append]; rfl
  | right i =>
    have hn : Fin.natAdd 14 i ≠ remainingSlot := by
      intro he
      have hh := congrArg Fin.val he
      simp only [remainingSlot,Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero] at hh
      omega
    simp only [parent,Tapes.append,Fin.addCases_right,Function.update_of_ne hn]

def program := seq (seq ArbitraryWidthLevelLifecycle.finish
  (BinaryDescriptorCleanupList.oneProgram offsetGlobal))
  (BinaryDescriptorCleanupList.oneProgram remainingSlot)

theorem cleans (B j : ℕ) (hB : 2 ≤ B) (ns ts : List Bool)
    (root : Tapes ArbitrarySliceCall.rootCount prime) (frame : Tapes 1 prime) :
    HoareTime program
      (fun z => z = parent ns (root.append (SliceHeaderPlacement.tail ts
        (FixedBasePowerStep.bits B j) frame)) (ArbitraryWidthLevelPlacement.extras B j))
      (fun z => z = ArbitraryWidthPieceSetup.input (bare root frame))
      ((2*(bits B).length+20)*B^j+2*ts.length+2*ns.length+10) := by
  let slice := root.append (SliceHeaderPlacement.tail ts (FixedBasePowerStep.bits B j) frame)
  have hw : slice.tape ArbitraryWidthLevelPlacement.widthSlot =
      RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B j) := by
    simp only [slice,ArbitraryWidthLevelPlacement.widthSlot,Tapes.append,Fin.addCases_right]; rfl
  have hh : slice.head ArbitraryWidthLevelPlacement.widthSlot = 1 := by
    simp only [slice,ArbitraryWidthLevelPlacement.widthSlot,Tapes.append,Fin.addCases_right]; rfl
  have hl := ArbitraryWidthLevelLifecycle.cleans B j hB ns slice hw hh
  let slice' := setTape slice ArbitraryWidthLevelPlacement.widthSlot (fun _ => blank) 0
  have ht : slice'.tape offsetSlot = RadixZeroFill.encodedBinary ts := by
    simp [slice',slice,setTape,offsetSlot,ArbitraryWidthLevelPlacement.widthSlot,Tapes.append,SliceHeaderPlacement.tail]
    rfl
  have hh' : slice'.head offsetSlot = 1 := by
    simp [slice',slice,setTape,offsetSlot,ArbitraryWidthLevelPlacement.widthSlot,Tapes.append,SliceHeaderPlacement.tail]
    rfl
  have ho := erase_middle ns slice' (SharedBank.empty 6 prime) offsetSlot ts ht hh'
  change HoareTime _ _ (fun z => z = parent ns
    (setTape (setTape (root.append (SliceHeaderPlacement.tail ts (FixedBasePowerStep.bits B j) frame))
      ArbitraryWidthLevelPlacement.widthSlot (fun _ => blank) 0) offsetSlot (fun _ => blank) 0)
      (SharedBank.empty 6 prime)) (2*ts.length+4) at ho
  rw [cleared_slice] at ho
  have hn := BinaryDescriptorCleanupList.one_hoare remainingSlot
    (parent ns (bare root frame) (SharedBank.empty 6 prime)) ns
    (by simp only [parent,remainingSlot,Tapes.append,Fin.addCases_left]
        change BinaryDescriptorStack.descriptor ns = _
        rfl)
    (by simp only [parent,remainingSlot,Tapes.append,Fin.addCases_left]; rfl)
  rw [erased_remaining] at hn
  exact ((hl.seq ho).seq hn).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ArbitraryWidthPieceCleanup
