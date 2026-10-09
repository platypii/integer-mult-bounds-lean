import IntegerMultBounds.Machine.SparsePhaseUnitCaller
import IntegerMultBounds.Machine.UnitPhaseRecordIO
import IntegerMultBounds.Machine.UnitPhaseLocalReset

/-! Physical phase application, emission and complete local workspace reset
for one sixty-tape coefficient record. Numeric sparse descriptors are derived
inside the caller, and the emitted phase result is consumed before cleanup. -/
namespace IntegerMultBounds.Machine.UnitPhaseRecordKernel
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open UnitPhaseNumerator (words)
variable {s : Shape}

def phase (m : ℕ) (ws : List (ZMod 4)) := extend (SparsePhaseUnitCaller.program m ws) 4
def program (m : ℕ) (ws : List (ZMod 4)) :=
  seq (seq (phase m ws) UnitPhaseRecordIO.emitProgram) UnitPhaseLocalReset.program
def selected (v : Stage s) (axis : Fin v.f) (m : ℕ) (addr : List Bool) :=
  SparseWeightedUnitPhase.selected addr (v.f*s.chunk) (SparsePhaseHeadersData.offset v axis m) (m-1)
def exponent (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4)) (addr : List Bool) :=
  WeightedPhaseAccumulator.accumulate 0 ws (selected v axis m addr)
def initial (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (addr : List Bool) (xs : ℕ → List (Fin 2)) (tail : Tapes 4 2) :=
  (SparsePhaseUnitCaller.input order v rows axis addr xs).append tail
def applied (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (xs : ℕ → List (Fin 2)) (tail : Tapes 4 2) :=
  (SparsePhaseUnitCaller.output order v rows axis m ws addr xs).append tail
def emitted (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (xs : ℕ → List (Fin 2)) (tail : Tapes 4 2) :=
  UnitPhaseRecordIO.emitOutput (applied order v rows axis m ws addr xs tail)
    (words (exponent v axis m ws addr) 0 xs) (words (exponent v axis m ws addr) 1 xs)
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (xs : ℕ → List (Fin 2)) (tail : Tapes 4 2) :=
  UnitPhaseLocalReset.output (emitted order v rows axis m ws addr xs tail)
def headerWords (v : Stage s) (axis : Fin v.f) (m : ℕ) : Fin 60 → List Bool :=
  fun i => if i=22 then SparsePhaseUnitCaller.headers v axis m 0
    else if i=23 then SparsePhaseUnitCaller.headers v axis m 1
    else if i=24 then SparsePhaseUnitCaller.headers v axis m 2 else []
def cost (v : Stage s) (axis : Fin v.f) (m w : ℕ) (addr : List Bool) :=
  10400*s.payload+2*m+20*w+(selected v axis m addr).length+
    BinaryDescriptorCleanupList.cost UnitPhaseLocalReset.headerSlots (headerWords v axis m)+78

private theorem applied_real (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (xs : ℕ → List (Fin 2)) (tail : Tapes 4 2) :
    (applied order v rows axis m ws addr xs tail).tape 52=
      MarkedWordCleanup.word ((words (exponent v axis m ws addr) 0 xs).map RadixDigits.digitSymbol) ∧
      (applied order v rows axis m ws addr xs tail).head 52=0 := by
  exact ⟨rfl,rfl⟩
private theorem applied_imag (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (xs : ℕ → List (Fin 2)) (tail : Tapes 4 2) :
    (applied order v rows axis m ws addr xs tail).tape 54=
      MarkedWordCleanup.word ((words (exponent v axis m ws addr) 1 xs).map RadixDigits.digitSymbol) ∧
      (applied order v rows axis m ws addr xs tail).head 54=0 := by
  exact ⟨rfl,rfl⟩

theorem private_blank (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (xs : ℕ → List (Fin 2)) (tail : Tapes 4 2)
    (i : Fin 12) :
    (output order v rows axis m ws addr xs tail).tape ⟨44+i.val,by change 44+i.val<60; omega⟩=(fun _ => blank) ∧
      (output order v rows axis m ws addr xs tail).head ⟨44+i.val,by change 44+i.val<60; omega⟩=0 := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem address_retained (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (xs : ℕ → List (Fin 2)) (tail : Tapes 4 2) :
    (output order v rows axis m ws addr xs tail).tape 43=SelectedSourceBitsScan.word addr ∧
      (output order v rows axis m ws addr xs tail).head 43=0 := ⟨rfl,rfl⟩

theorem counter_retained (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (xs : ℕ → List (Fin 2)) (tail : Tapes 4 2) :
    (output order v rows axis m ws addr xs tail).tape 57=tail.tape 1 ∧
      (output order v rows axis m ws addr xs tail).head 57=tail.head 1 := ⟨rfl,rfl⟩

theorem stream_emitted (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (xs : ℕ → List (Fin 2)) (tail : Tapes 4 2) :
    (output order v rows axis m ws addr xs tail).tape 58=
      putWord (tail.tape 2) (tail.head 2)
        (DelimitedRadixRecord.complex (words (exponent v axis m ws addr) 0 xs)
          (words (exponent v axis m ws addr) 1 xs)) ∧
      (output order v rows axis m ws addr xs tail).head 58=
        tail.head 2+(words (exponent v axis m ws addr) 0 xs).length+
          (words (exponent v axis m ws addr) 1 xs).length+2 := ⟨rfl,rfl⟩

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (addr : List Bool) (xs : ℕ → List (Fin 2)) (w : ℕ) (hw : ∀ j,(xs j).length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<addr.length)
    (ha : addr.length=s.bits) (hrecord : s.bits+1≤s.payload) (tail : Tapes 4 2) :
    HoareTime (program m ws) (fun z => z=initial order v rows axis addr xs tail)
      (fun z => z=output order v rows axis m ws addr xs tail) (cost v axis m w addr) := by
  have h0 := hoare_extend_eq (SparsePhaseUnitCaller.runs order v rows axis m ws hm hslots hl
    addr xs w hw hspan ha hrecord) tail
  have h1 := UnitPhaseRecordIO.emit_runs (applied order v rows axis m ws addr xs tail)
    (words (exponent v axis m ws addr) 0 xs) (words (exponent v axis m ws addr) 1 xs)
    (applied_real order v rows axis m ws addr xs tail) (applied_imag order v rows axis m ws addr xs tail)
  have h2 := UnitPhaseLocalReset.runs (emitted order v rows axis m ws addr xs tail) xs
    (selected v axis m addr) (exponent v axis m ws addr) (headerWords v axis m)
    (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩)
    (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩) (by
      intro i hi
      simp only [UnitPhaseLocalReset.headerSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl
      all_goals constructor
      all_goals first | rfl | skip
      all_goals simp [emitted,UnitPhaseRecordIO.emitOutput,SharedPlacementAlphabet.setTape,
        applied,SparsePhaseUnitCaller.output,SparsePhaseHeadersData.finished,
        ActiveRepairRankHeadersCommands.bank,ActiveRepairRankHeadersCommands.put,
        headerWords,SparsePhaseUnitCaller.headers,CleanSubbank.bank,
        Tapes.append,Fin.addCases,ActiveRepairRankHeadersCommands.caller,
        BinaryDescriptorStackRoundtrip.descriptor_encoded]
      )
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by
    simp only [UnitPhaseNumerator.words_length _ _ xs w hw,UnitPhaseLocalReset.cost,hw]
    unfold cost
    omega)

end
end IntegerMultBounds.Machine.UnitPhaseRecordKernel
