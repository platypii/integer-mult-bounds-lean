import IntegerMultBounds.Machine.ArbitraryWidthLevelLifecycle

/-! Install the digit dispatcher's remaining-width and offset controls from
retained parent headers and blank private storage. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPieceSetup
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitraryWidthConsumePlacement (S T parent)
open ArbitrarySliceCall (rootBank headerSlot)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

def bare (root : Tapes ArbitrarySliceCall.rootCount prime) (frame : Tapes 1 prime) : Tapes S prime :=
  root.append ((SharedBank.empty 11 prime).append frame)
def input (slice : Tapes S prime) : Tapes T prime :=
  (SharedBank.empty 14 prime).append (slice.append (SharedBank.empty 6 prime))
def widthSource : Fin T := Fin.natAdd 14 (Fin.castAdd 6
  (Fin.castAdd 12 (headerSlot 3)))
def remainingSlot : Fin T := Fin.castAdd (S+6) (0 : Fin 14)
def offsetSlot : Fin S := Fin.natAdd ArbitrarySliceCall.rootCount (0 : Fin 12)
def offsetGlobal : Fin T := Fin.natAdd 14 (Fin.castAdd 6 offsetSlot)

theorem distinct : widthSource ≠ remainingSlot := by
  intro he
  have hh := congrArg Fin.val he
  simp only [widthSource,remainingSlot,Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero] at hh
  omega

theorem root_header (data : Tapes Shared50NodeSegments.payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (i : Fin 6) :
    (rootBank data hs f p node scalar st).head (headerSlot i) = 1 ∧
    (rootBank data hs f p node scalar st).tape (headerSlot i) = RadixZeroFill.encodedBinary (hs i) := by
  have hinside : (headerSlot i).val < ArbitrarySliceCall.commonCount :=
    (RecursiveCallBank.headerSlot i).isLt
  unfold rootBank SharedBankStageInput.raw
  simp only [dite_eq_left hinside]
  change (Shared50RecursiveBank.bank data hs f p node scalar (SharedBank.empty 0 prime) st).head
      (RecursiveCallBank.headerSlot i) = 1 ∧
    (Shared50RecursiveBank.bank data hs f p node scalar (SharedBank.empty 0 prime) st).tape
      (RecursiveCallBank.headerSlot i) = RadixZeroFill.encodedBinary (hs i)
  simp only [Shared50RecursiveBank.bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,
    RecursiveCallBank.headerSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,RecursiveShiftRoleBank.headers]
  constructor <;> first | rfl | trivial

theorem install_output (slice : Tapes S prime) (ns : List Bool) :
    setTape (input slice) remainingSlot (RadixZeroFill.encodedBinary ns) 1 =
      parent ns slice (SharedBank.empty 6 prime) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    fin_cases i <;> simp [setTape,input,remainingSlot,Tapes.append,
      ArbitraryWidthPieceCounter.input,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  | right i =>
    have hn : Fin.natAdd 14 i ≠ remainingSlot := by
      intro he
      have hh := congrArg Fin.val he
      simp only [remainingSlot,Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero] at hh
      omega
    simp only [input,Tapes.append,Fin.addCases_right,Function.update_of_ne hn]

def copyWidth := BinaryDescriptorInstall.program prime widthSource remainingSlot distinct

theorem copies_width (data : Tapes Shared50NodeSegments.payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :
    HoareTime copyWidth (fun z => z = input (bare (rootBank data hs f p node scalar st) frame))
      (fun z => z = parent (hs 3) (bare (rootBank data hs f p node scalar st) frame)
        (SharedBank.empty 6 prime)) (2*(hs 3).length+5) := by
  let slice := bare (rootBank data hs f p node scalar st) frame
  have hs0 : (input slice).tape widthSource = RadixZeroFill.encodedBinary (hs 3) := by
    simp only [input,bare,slice,widthSource,Tapes.append,Fin.addCases_right,Fin.addCases_left]
    exact (root_header data hs f p node scalar st 3).2
  have hh0 : (input slice).head widthSource = 1 := by
    simp only [input,bare,slice,widthSource,Tapes.append,Fin.addCases_right,Fin.addCases_left]
    exact (root_header data hs f p node scalar st 3).1
  have hd : (input slice).tape remainingSlot = fun _ => blank := by
    simp only [input,remainingSlot,Tapes.append,Fin.addCases_left]; rfl
  have hdh : (input slice).head remainingSlot = 0 := by
    simp only [input,remainingSlot,Tapes.append,Fin.addCases_left]; rfl
  have h := BinaryDescriptorInstall.install_hoare widthSource remainingSlot distinct
    (input slice) (hs 3) hs0 hh0 hd hdh
  rw [install_output] at h
  exact h

def initializeOffset := Placement.placed (RecursiveChildQuotientsConstant.program (a := prime) 0)
  (FiniteReturnStackAt.placement offsetGlobal)

theorem initializes_offset (ns : List Bool) (root : Tapes ArbitrarySliceCall.rootCount prime)
    (frame : Tapes 1 prime) :
    HoareTime initializeOffset (fun z => z = parent ns (bare root frame) (SharedBank.empty 6 prime))
      (fun z => z = parent ns (setTape (bare root frame) offsetSlot
        (RadixZeroFill.encodedBinary (bits 0)) 1) (SharedBank.empty 6 prime))
      (RecursiveChildQuotientsConstant.cost 0) := by
  let v := parent ns (bare root frame) (SharedBank.empty 6 prime)
  have ha : Placement.active (FiniteReturnStackAt.placement offsetGlobal) v =
      SharedBank.empty 1 prime := by
    rw [FiniteReturnStackAt.active_bank]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp only [v,parent,bare,offsetGlobal,offsetSlot,Tapes.append,
      Fin.addCases_right,Fin.addCases_left]
    all_goals rfl
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := prime) 0)
    (FiniteReturnStackAt.placement offsetGlobal) v ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    have hn : Fin.castAdd (S+6) i ≠ offsetGlobal := by
      intro he
      have hh := congrArg Fin.val he
      simp only [offsetGlobal,Fin.val_natAdd,Fin.val_castAdd] at hh
      have := i.isLt
      omega
    simp only [setTape,v,parent,Tapes.append,Fin.addCases_left,Function.update_of_ne hn]
  | right i =>
    induction i using Fin.addCases with
    | left i =>
      by_cases hi : i = offsetSlot
      · subst i
        simp only [setTape,v,parent,offsetGlobal,Tapes.append,Fin.addCases_right,
          Fin.addCases_left,Function.update_self]
      · have hn : Fin.natAdd 14 (Fin.castAdd 6 i) ≠ offsetGlobal := by
          intro he
          apply hi
          exact Fin.ext (by simpa only [offsetGlobal,Fin.val_natAdd,Fin.val_castAdd,
            Nat.add_left_cancel_iff] using congrArg Fin.val he)
        simp only [setTape,v,parent,Tapes.append,Fin.addCases_right,Fin.addCases_left,
          Function.update_of_ne hn,Function.update_of_ne hi]
    | right i =>
      have hn : Fin.natAdd 14 (Fin.natAdd S i) ≠ offsetGlobal := by
        intro he
        have hh := congrArg Fin.val he
        simp only [offsetGlobal,Fin.val_natAdd,Fin.val_castAdd] at hh
        have := offsetSlot.isLt
        omega
      simp only [setTape,v,parent,Tapes.append,Fin.addCases_right,Function.update_of_ne hn]

theorem controls_bank (root : Tapes ArbitrarySliceCall.rootCount prime) (frame : Tapes 1 prime)
    (bs : List Bool) :
    setTape (setTape (bare root frame) offsetSlot (RadixZeroFill.encodedBinary (bits 0)) 1)
      ArbitraryWidthLevelPlacement.widthSlot (RadixZeroFill.encodedBinary bs) 1 =
        root.append (SliceHeaderPlacement.tail (bits 0) bs frame) := by
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
    simp only [setTape,bare,Tapes.append,Fin.addCases_left,
      Function.update_of_ne ho,Function.update_of_ne hw]
  | right i =>
    fin_cases i
    all_goals simp [setTape,bare,offsetSlot,ArbitraryWidthLevelPlacement.widthSlot,
      Tapes.append,SliceHeaderPlacement.tail,SharedBank.empty]; rfl

def program := seq (seq copyWidth initializeOffset) (ArbitraryWidthLevelLifecycle.setup 125000)

theorem sets_up (v : RecursiveInterchangeLayout.Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs)
    (data : Tapes Shared50NodeSegments.payloadCount prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :
    HoareTime program (fun z => z = input (bare (rootBank data hs f p node scalar st) frame))
      (fun z => z = parent (bits v.width)
        (ArbitrarySliceCall.bank data hs (bits 0) (FixedBasePowerStep.bits 125000 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras 125000 0))
      (2*(hs 3).length+RecursiveChildQuotientsConstant.cost 125000+
        RecursiveChildQuotientsConstant.cost 1+2*RecursiveChildQuotientsConstant.cost 0+9) := by
  have hb : hs 3 = bits v.width := BinaryCanonicalData.value_injective _ _ (hv.2 3)
    (RecursiveChildQuotientsConstant.bits_canonical _) (by
      rw [RecursiveChildQuotientsConstant.bits_value]
      exact hv.1 3)
  have hc := copies_width data hs f p node scalar st frame
  have ho := initializes_offset (hs 3) (rootBank data hs f p node scalar st) frame
  let slice := setTape (bare (rootBank data hs f p node scalar st) frame) offsetSlot
    (RadixZeroFill.encodedBinary (bits 0)) 1
  have ht : slice.tape ArbitraryWidthLevelPlacement.widthSlot = fun _ => blank := by
    simp [slice,setTape,bare,offsetSlot,ArbitraryWidthLevelPlacement.widthSlot,Tapes.append,SharedBank.empty]
    rfl
  have hh : slice.head ArbitraryWidthLevelPlacement.widthSlot = 0 := by
    simp [slice,setTape,bare,offsetSlot,ArbitraryWidthLevelPlacement.widthSlot,Tapes.append,SharedBank.empty]
    rfl
  have hl := ArbitraryWidthLevelLifecycle.initializes 125000 (hs 3) slice ht hh
  change HoareTime _ _ (fun z => z = parent (hs 3)
    (setTape (setTape (bare (rootBank data hs f p node scalar st) frame) offsetSlot
      (RadixZeroFill.encodedBinary (bits 0)) 1) ArbitraryWidthLevelPlacement.widthSlot
      (RadixZeroFill.encodedBinary (FixedBasePowerStep.bits 125000 0)) 1)
      (ArbitraryWidthLevelPlacement.extras 125000 0))
    (RecursiveChildQuotientsConstant.cost 125000+RecursiveChildQuotientsConstant.cost 1+
      RecursiveChildQuotientsConstant.cost 0+2) at hl
  rw [controls_bank] at hl
  have hrun := (hc.seq ho).seq hl
  rw [hb] at hrun
  exact hrun.consequence (fun _ h => h) (fun _ h => h) (by
    have hlen := congrArg List.length hb
    omega)

end
end IntegerMultBounds.Machine.ArbitraryWidthPieceSetup
