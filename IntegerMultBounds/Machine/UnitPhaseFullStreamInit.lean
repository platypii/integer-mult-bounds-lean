import IntegerMultBounds.Machine.UnitPhaseCountTransfer

/-! Full-address coefficient stream initialization from original headers:
physically derive bits, synthesize count rows*2^bits, transfer count to59,
initialize live counter/readout, and erase generated numeric workspace.
Original row header4 is preserved throughout. -/
namespace IntegerMultBounds.Machine.UnitPhaseFullStreamInit
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open SharedPlacementAlphabet (setTape)
open CountedLoopReuseAlphabet (binary)
open BinaryAddressTableData (row)
variable {s : Shape}

def derive := extend (UnitPhaseAddressHeaders.program (a := 2)) 17
def count := extend UnitPhaseCountHeaders.program 17
def program := seq (seq (seq derive count) UnitPhaseCountTransfer.program) UnitPhaseAddressInitAt.program
def readyTail (rows : ℕ) (tail : Tapes 4 2) :=
  setTape (UnitPhaseCountTransfer.tailCount tail (rows*2^s.bits)) 1 (binary (row s.bits 0)) 1
def input := @UnitPhaseStreamInit.input
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (a : Context 2) (tail : Tapes 4 2) :=
  UnitPhaseRecordRead.initial order v rows axis (row s.bits 0) a (readyTail (s := s) rows tail)
def cost (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :=
  CompactChildHeadersArithmetic.scheduleCost UnitPhaseAddressHeaders.schedule
    (UnitPhaseAddressHeaders.initial order v rows axis)+UnitPhaseCountHeaders.cost order v rows axis+
    4*(RecursiveChildQuotientsConstant.bits (rows*2^s.bits)).length+
    65*(s.bits+1)+2*(RecursiveChildQuotientsConstant.bits s.bits).length+18

private theorem endpoint (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (a : Context 2) (tail : Tapes 4 2) :
    UnitPhaseAddressInitAt.output (UnitPhaseCountTransfer.output order v rows axis tail)
      (RecursiveChildQuotientsConstant.bits s.bits) s.bits=output order v rows axis a tail := by
  rw [UnitPhaseAddressInitAt.output_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (a : Context 2) (tail : Tapes 4 2)
    (hc : tail.tape 1=(fun _ => blank) ∧ tail.head 1=0)
    (hn : tail.tape 3=(fun _ => blank) ∧ tail.head 3=0) :
    HoareTime program (fun z => z=input order v rows axis tail)
      (fun z => z=output order v rows axis a tail) (cost order v rows axis) := by
  have h0 := hoare_extend_eq (UnitPhaseAddressHeaders.runs (a := 2) order v rows axis)
    (UnitPhaseStreamInit.privateEmpty.append tail)
  have h1 := hoare_extend_eq (UnitPhaseCountHeaders.runs order v rows axis)
    (UnitPhaseStreamInit.privateEmpty.append tail)
  have h2 := UnitPhaseCountTransfer.runs order v rows axis tail hn
  have h3 := UnitPhaseAddressInitAt.runs (UnitPhaseCountTransfer.output order v rows axis tail)
    (RecursiveChildQuotientsConstant.bits s.bits) s.bits
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (by constructor
        · change RadixZeroFill.encodedBinary _=binary _; exact CountedLoopReuseAlphabet.encoding_binary _
        · rfl)
    (by simpa [UnitPhaseCountTransfer.output,UnitPhaseStreamInit.prepared,UnitPhaseStreamInit.privateEmpty,
        UnitPhaseCountTransfer.tailCount,setTape,Tapes.append,Fin.addCases] using hc)
    (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩)
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h)
    (fun _ h => h.trans (endpoint order v rows axis a tail)) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.UnitPhaseFullStreamInit
