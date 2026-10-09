import IntegerMultBounds.Machine.UnitPhaseCountHeaders
import IntegerMultBounds.Machine.UnitPhaseStreamInit
import IntegerMultBounds.Machine.BinaryDescriptorCopyPlaced

/-! Physically transfer derived coefficient count24 to persistent count59,
then erase24 so sparse phase offset derivation may reuse it. All other tapes,
including original rows4 and complete width22, are retained. -/
namespace IntegerMultBounds.Machine.UnitPhaseCountTransfer
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ActiveRepairRankHeadersCommands (bank)
open SharedPlacementAlphabet (setTape)
variable {s : Shape}

def focus : Fin 2 → Fin 60 := ![24,59]
theorem injective : Function.Injective focus := by decide
def copy := BinaryDescriptorCopyPlaced.program (a := 2) focus injective
def erase := BinaryDescriptorCleanupList.oneProgram (a := 2) (24 : Fin 60)
def program := seq copy erase
def input (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (tail : Tapes 4 2) :=
  (bank (a := 2) (UnitPhaseCountHeaders.finished order v rows axis)).append
    (UnitPhaseStreamInit.privateEmpty.append tail)
def tailCount (tail : Tapes 4 2) (n : ℕ) :=
  setTape tail 3 (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n)) 1
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (tail : Tapes 4 2) :=
  UnitPhaseStreamInit.prepared order v rows axis (tailCount tail (rows*2^s.bits))

private theorem endpoint (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (tail : Tapes 4 2) :
    setTape (setTape (input order v rows axis tail) 59
      (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (rows*2^s.bits))) 1)
        24 (fun _ => blank) 0=output order v rows axis tail := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (tail : Tapes 4 2)
    (hn : tail.tape 3=(fun _ => blank) ∧ tail.head 3=0) :
    HoareTime program (fun z => z=input order v rows axis tail) (fun z => z=output order v rows axis tail)
      (4*(RecursiveChildQuotientsConstant.bits (rows*2^s.bits)).length+10) := by
  let z := input order v rows axis tail
  let bs := RecursiveChildQuotientsConstant.bits (rows*2^s.bits)
  have ha : SharedBank.payload z focus=BinaryDescriptorCopy.encodedInput 2 bs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    · rfl
    · exact hn.2
    · rfl
    · exact hn.1
  have h0 := BinaryDescriptorCopyPlaced.copies z focus injective bs ha
  have h1 := BinaryDescriptorCleanupList.one_hoare (24 : Fin 60)
    (setTape z 59 (RadixZeroFill.encodedBinary bs) 1) bs
    (by change RadixZeroFill.encodedBinary bs=BinaryDescriptorStack.descriptor bs
        exact (BinaryDescriptorStackRoundtrip.descriptor_encoded bs).symm)
    (by rfl)
  exact (h0.seq h1).consequence (fun _ h => h)
    (fun _ h => h.trans (endpoint order v rows axis tail)) (by dsimp [bs]; omega)

end
end IntegerMultBounds.Machine.UnitPhaseCountTransfer
