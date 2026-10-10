import IntegerMultBounds.Machine.AllAxisPhaseFlagsCaller
import IntegerMultBounds.Machine.AllAxisCountTransfer

/-! Full-address coefficient stream initialization from original headers:
physically derive bits, synthesize count rows*2^bits, transfer count to59,
initialize live counter/readout, and erase generated numeric workspace.
Original row header4 is preserved throughout. -/
namespace IntegerMultBounds.Machine.AllAxisFullStreamInit
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open SharedPlacementAlphabet (setTape)
open CountedLoopReuseAlphabet (binary)
open BinaryAddressTableData (row)
variable {s : Shape}

def derive := extend (AllAxisAddressHeaders.program (a := 2)) 17
def count := extend AllAxisCountHeaders.program 17
def program := seq (seq (seq derive count) AllAxisCountTransfer.program) UnitPhaseAddressInitAt.program
def readyTail (rows : ℕ) (tail : Tapes 4 2) :=
  setTape (AllAxisCountTransfer.tailCount tail (rows*2^s.bits)) 1 (binary (row s.bits 0)) 1
def input := @AllAxisPhaseStreamInit.input
def output (order : Order) (v : Stage s) (rows : ℕ) (_a : Context 2) (tail : Tapes 4 2) :=
  (AllAxisPhaseFlagsCaller.input order v rows (row s.bits 0) (SharedBank.empty 6 2)).append
    (readyTail (s := s) rows tail)
def cost (order : Order) (v : Stage s) (rows : ℕ) :=
  CompactChildHeadersArithmetic.scheduleCost AllAxisAddressHeaders.schedule
    (AllAxisAddressHeaders.initial order v rows)+AllAxisCountHeaders.cost order v rows+
    4*(RecursiveChildQuotientsConstant.bits (rows*2^s.bits)).length+
    65*(s.bits+1)+2*(RecursiveChildQuotientsConstant.bits s.bits).length+18

private theorem endpoint (order : Order) (v : Stage s) (rows : ℕ)
    (a : Context 2) (tail : Tapes 4 2) :
    UnitPhaseAddressInitAt.output (AllAxisCountTransfer.output order v rows tail)
      (RecursiveChildQuotientsConstant.bits s.bits) s.bits=output order v rows a tail := by
  rw [UnitPhaseAddressInitAt.output_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (a : Context 2) (tail : Tapes 4 2)
    (hc : tail.tape 1=(fun _ => blank) ∧ tail.head 1=0)
    (hn : tail.tape 3=(fun _ => blank) ∧ tail.head 3=0) :
    HoareTime program (fun z => z=input order v rows tail)
      (fun z => z=output order v rows a tail) (cost order v rows) := by
  have h0 := hoare_extend_eq (AllAxisAddressHeaders.runs (a := 2) order v rows)
    (AllAxisPhaseStreamInit.privateEmpty.append tail)
  have h1 := hoare_extend_eq (AllAxisCountHeaders.runs order v rows)
    (AllAxisPhaseStreamInit.privateEmpty.append tail)
  have h2 := AllAxisCountTransfer.runs order v rows tail hn
  have h3 := UnitPhaseAddressInitAt.runs (AllAxisCountTransfer.output order v rows tail)
    (RecursiveChildQuotientsConstant.bits s.bits) s.bits
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (by constructor
        · change RadixZeroFill.encodedBinary _=binary _; exact CountedLoopReuseAlphabet.encoding_binary _
        · rfl)
    (by simpa [AllAxisCountTransfer.output,AllAxisPhaseStreamInit.prepared,AllAxisPhaseStreamInit.privateEmpty,
        AllAxisCountTransfer.tailCount,setTape,Tapes.append,Fin.addCases] using hc)
    (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩)
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h)
    (fun _ h => h.trans (endpoint order v rows a tail)) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.AllAxisFullStreamInit
