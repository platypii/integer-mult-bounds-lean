import IntegerMultBounds.Machine.UnitPhaseRecord
import IntegerMultBounds.Machine.UnitPhaseRecordAddress

/-! Physical sixty-tape record body including the live address counter.
Every iteration reads the current counter, increments it, reads one actual
serialized coefficient, applies its header-derived unit phase, emits the
result and resets the complete local phase workspace. -/
namespace IntegerMultBounds.Machine.UnitPhaseRecordFull
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open SharedPlacementAlphabet (setTape)
open BinaryAddressTableData (row)
open CountedLoopReuseAlphabet (binary)
variable {s : Shape}

def program (m : ℕ) (ws : List (ZMod 4)) :=
  seq UnitPhaseRecordAddress.program (UnitPhaseRecord.program m ws)
def advanced (W i : ℕ) (tail : Tapes 4 2) :=
  setTape tail 1 (binary (row W (i+1))) 1
abbrev initial := @UnitPhaseRecordRead.initial

def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (a : Context 2) (tail : Tapes 4 2) :=
  UnitPhaseRecord.output order v rows axis m ws (row s.bits i) a (advanced s.bits i tail)
def cost (v : Stage s) (axis : Fin v.f) (m w i : ℕ) :=
  5*s.bits+UnitPhaseRecord.cost v axis m w (row s.bits i)+11

private theorem addressed (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (old : List Bool) (a : Context 2) (tail : Tapes 4 2) (i : ℕ) :
    UnitPhaseRecordAddress.output (initial order v rows axis old a tail) s.bits i=
      initial order v rows axis (row s.bits i) a (advanced s.bits i tail) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (old : List Bool) (hold : old.length=s.bits) (i : ℕ)
    (a : Context 2) (w : ℕ) (hr : a.re.length=w) (hi : a.im.length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) (tail : Tapes 4 2)
    (ht : tail.tape 0=a.tape ∧ tail.head 0=a.start)
    (hc : tail.tape 1=binary (row s.bits i) ∧ tail.head 1=1) :
    HoareTime (program m ws) (fun z => z=initial order v rows axis old a tail)
      (fun z => z=output order v rows axis m ws i a tail) (cost v axis m w i) := by
  have h0 := UnitPhaseRecordAddress.runs (initial order v rows axis old a tail) s.bits i old hold
    (by simpa [UnitPhaseRecordRead.initial,UnitPhaseRecordKernel.initial,setTape,Tapes.append,Fin.addCases] using hc)
    (by exact ⟨rfl,rfl⟩)
  have h1 := UnitPhaseRecord.runs order v rows axis m ws hm hslots hl (row s.bits i) a w hr hi
    (by simpa only [BinaryAddressTableData.row_length] using hspan)
    (BinaryAddressTableData.row_length _ _) hrecord (advanced s.bits i tail)
    (by simpa [advanced,setTape] using ht)
  rw [addressed order v rows axis old a tail i] at h0
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.UnitPhaseRecordFull
