import IntegerMultBounds.Machine.UnitPhaseAddressHeaders
import IntegerMultBounds.Machine.UnitPhaseAddressInitAt

/-! Complete live counter initialization from the original node/global
headers. The address width is derived physically, used to fill the counter
and readout, then its generated header is erased. Streams are spectators. -/
namespace IntegerMultBounds.Machine.UnitPhaseStreamInit
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ActiveRepairRankHeadersCommands (bank)
open SharedPlacementAlphabet (setTape)
open DelimitedRadixRecord (Context)
open BinaryAddressTableData (row)
open CountedLoopReuseAlphabet (binary)
variable {s : Shape}

def privateEmpty := SharedBank.empty 13 2
def input (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (tail : Tapes 4 2) :=
  (bank (UnitPhaseAddressHeaders.initial order v rows axis)).append (privateEmpty.append tail)
def prepared (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (tail : Tapes 4 2) :=
  (bank (UnitPhaseAddressHeaders.finished order v rows axis)).append (privateEmpty.append tail)
def ready (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (a : Context 2) (tail : Tapes 4 2) :=
  UnitPhaseRecordRead.initial order v rows axis (row s.bits 0) a
    (setTape tail 1 (binary (row s.bits 0)) 1)
def derive := extend (UnitPhaseAddressHeaders.program (a := 2)) 17
def program := seq derive UnitPhaseAddressInitAt.program

def cost (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :=
  CompactChildHeadersArithmetic.scheduleCost UnitPhaseAddressHeaders.schedule
    (UnitPhaseAddressHeaders.initial order v rows axis)+65*(s.bits+1)+
      2*(RecursiveChildQuotientsConstant.bits s.bits).length+6

private theorem endpoint (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (a : Context 2) (tail : Tapes 4 2) :
    UnitPhaseAddressInitAt.output (prepared order v rows axis tail)
      (RecursiveChildQuotientsConstant.bits s.bits) s.bits=ready order v rows axis a tail := by
  rw [UnitPhaseAddressInitAt.output_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (a : Context 2) (tail : Tapes 4 2)
    (hc : tail.tape 1=(fun _ => blank) ∧ tail.head 1=0) :
    HoareTime program (fun z => z=input order v rows axis tail)
      (fun z => z=ready order v rows axis a tail) (cost order v rows axis) := by
  have h0 := hoare_extend_eq (UnitPhaseAddressHeaders.runs (a := 2) order v rows axis)
    (privateEmpty.append tail)
  have h1 := UnitPhaseAddressInitAt.runs (prepared order v rows axis tail)
    (RecursiveChildQuotientsConstant.bits s.bits) s.bits
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (by constructor
        · change RadixZeroFill.encodedBinary _=binary _
          exact CountedLoopReuseAlphabet.encoding_binary _
        · rfl)
    (by simpa [prepared,privateEmpty,Tapes.append,Fin.addCases] using hc)
    (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩)
  exact (h0.seq h1).consequence (fun _ h => h)
    (fun _ h => h.trans (endpoint order v rows axis a tail)) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.UnitPhaseStreamInit
