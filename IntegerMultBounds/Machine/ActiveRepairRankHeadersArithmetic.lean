import IntegerMultBounds.Machine.BinaryDescriptorAdvance
import IntegerMultBounds.Machine.BinaryDescriptorCopyPlaced
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCore

/-! Physical retained-header addition in the existing clean fifteen-tape
workspace. Unary-counted increments have an amortized, paid linear bound. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankHeadersArithmetic
noncomputable section
open CompactGadgetReservationHeadersCore
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a : ℕ}

def addPorts : Fin 2 → Fin 15 := ![0,2]
theorem add_injective : Function.Injective addPorts := by decide
def addCore := extend (BinaryDescriptorAdvance.program (q := a)) 12
def addProgram (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :=
  placed (addCore (a := a)) addPorts focus hf

theorem adds (caller : Tapes t a) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (xs ys : List Bool) (cx : GrowingCounterData.Canonical xs)
    (hx : caller.tape (focus 0)=RadixZeroFill.encodedBinary xs) (px : caller.head (focus 0)=1)
    (hy : caller.tape (focus 1)=RadixZeroFill.encodedBinary ys) (py : caller.head (focus 1)=1) :
    HoareTime (addProgram focus hf) (fun v => v=bank caller)
      (fun v => v=bank (setTape caller (focus 0)
        (RadixZeroFill.encodedBinary (bits (Counter.value xs+Counter.value ys))) 1))
      (10*Counter.value ys+2*xs.length+7*ys.length+28) := by
  let X := (BinaryDescriptorAdvance.input (q := a) xs ys).append (SharedBank.empty 12 a)
  have hr := hoare_extend_eq (BinaryDescriptorAdvance.advances_hoare (q := a) xs ys
    (Counter.value ys) rfl) (SharedBank.empty 12 a)
  have he : GrowingCounterData.advance (Counter.value ys) xs=bits (Counter.value xs+Counter.value ys) :=
    canonical_bits _ _ (BinaryDescriptorAdvance.canonical xs _ cx) (BinaryDescriptorAdvance.value xs _)
  rw [he] at hr
  have ho : BinaryDescriptorAdvance.input (q := a) (bits (Counter.value xs+Counter.value ys)) ys=
      setTape (BinaryDescriptorAdvance.input xs ys) 0
        (RadixZeroFill.encodedBinary (bits (Counter.value xs+Counter.value ys))) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact BinaryDescriptorStackRoundtrip.descriptor_encoded _
  rw [ho,←SharedPlacementAlphabet.setTape_append_left] at hr
  apply single (addCore (a := a)) addPorts add_injective focus hf caller X 0 _ _ ?_ ?_ hr
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,addPorts,BinaryDescriptorAdvance.input,BinaryDescriptorAdvance.bank,
      BinaryDescriptorIncrement.bank,CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,
      Tapes.append,Fin.addCases,hx,hy,px,py,BinaryDescriptorStackRoundtrip.descriptor_encoded,encoded_binary]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,addPorts,BinaryDescriptorAdvance.input,BinaryDescriptorAdvance.bank,
      BinaryDescriptorIncrement.bank,CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,
      Tapes.append,Fin.addCases,Fin.exists_fin_succ,SharedBank.empty]

end
end IntegerMultBounds.Machine.ActiveRepairRankHeadersArithmetic
