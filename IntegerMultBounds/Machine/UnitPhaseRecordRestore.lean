import IntegerMultBounds.Machine.UnitPhaseRecordFull

/-! Exact restored caller state after a complete phase record iteration.
The next coefficient context is arbitrary because all numerator/control
workspace is physically blank; only the actual streams and counter advance. -/
namespace IntegerMultBounds.Machine.UnitPhaseRecordRestore
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open SharedPlacementAlphabet (setTape)
open BinaryAddressTableData (row)
variable {s : Shape}

def nextTail (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (i : ℕ) (a : Context 2) (tail : Tapes 4 2) :=
  let p := UnitPhaseRecordKernel.exponent v axis m ws (row s.bits i)
  let re := UnitPhaseNumerator.words p 0 (UnitPhaseRecordRead.sources a)
  let im := UnitPhaseNumerator.words p 1 (UnitPhaseRecordRead.sources a)
  setTape (UnitPhaseRecordRead.advanced a (UnitPhaseRecordFull.advanced s.bits i tail)) 2
    (putWord (tail.tape 2) (tail.head 2) (DelimitedRadixRecord.complex re im))
    (tail.head 2+re.length+im.length+2)

theorem restored (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (a b : Context 2) (tail : Tapes 4 2) :
    UnitPhaseRecordFull.output order v rows axis m ws i a tail=
      UnitPhaseRecordRead.initial order v rows axis (row s.bits i) b (nextTail v axis m ws i a tail) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl

end
end IntegerMultBounds.Machine.UnitPhaseRecordRestore
