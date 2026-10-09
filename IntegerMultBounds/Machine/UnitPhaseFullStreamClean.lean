import IntegerMultBounds.Machine.UnitPhaseFullStreamArray
import IntegerMultBounds.Machine.UnitPhaseStreamAddressReset

/-! Full literal-array phase stream with final live address/counter erasure.
At the endpoint every generated phase/count/address workspace is blank;
streams remain available for the enclosing native coefficient converter. -/
namespace IntegerMultBounds.Machine.UnitPhaseFullStreamClean
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient full)
open SharedPlacementAlphabet (setTape)
open BinaryAddressTableData (row)
open CountedLoopReuseAlphabet (binary)
variable {s : Shape}

def program (m : ℕ) (ws : List (ZMod 4)) :=
  seq (UnitPhaseFullStream.program m ws) (extend UnitPhaseStreamAddressReset.program 2)
def beforeCleanup (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (rows*2^s.bits) → Coefficient) :=
  setTape (UnitPhaseStreamLoop.state order v rows axis m ws (UnitPhaseStreamData.contexts f p xs)
    (UnitPhaseFullStreamInit.readyTail (s := s) rows (UnitPhaseFullStreamArray.tail f g p r xs)) (rows*2^s.bits))
      59 (fun _ => blank) 0
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (rows*2^s.bits) → Coefficient) :=
  (UnitPhaseStreamAddressReset.output (beforeCleanup order v rows axis m ws f g p r xs)
    (row s.bits (rows*2^s.bits-1))).append (SharedBank.empty 2 2)

private theorem prepared_eq (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (rows*2^s.bits) → Coefficient) :
    UnitPhaseFullStreamArray.output order v rows axis m ws f g p r xs=
      (beforeCleanup order v rows axis m ws f g p r xs).append (SharedBank.empty 2 2) :=
  SharedPlacementAlphabet.setTape_append_left _ _ (59 : Fin 60) _ _

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (rows*2^s.bits) → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    HoareTime (program m ws)
      (fun z => z=UnitPhaseFullStreamArray.input order v rows axis f g p r xs)
      (fun z => z=output order v rows axis m ws f g p r xs)
      ((rows*2^s.bits)*((FixedBasePowerDescriptor.constant 2+13100)*s.payload+24*w)) := by
  have h0 := UnitPhaseFullStreamArray.runs order v rows hr axis m ws hm hslots hl f g p r xs w hw hspan hrecord
  have hc := UnitPhaseStreamLoop.counter v axis m ws (UnitPhaseStreamData.contexts f p xs)
    (UnitPhaseFullStreamInit.readyTail (s := s) rows (UnitPhaseFullStreamArray.tail f g p r xs))
    (by exact ⟨rfl,rfl⟩) (rows*2^s.bits)
  have h1 := UnitPhaseStreamAddressReset.runs (beforeCleanup order v rows axis m ws f g p r xs)
    (row s.bits (rows*2^s.bits-1)) (row s.bits (rows*2^s.bits))
    (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩)
    (by exact hc)
  simp only [BinaryAddressTableData.row_length] at h1
  have he := hoare_extend_eq h1 (SharedBank.empty 2 2)
  rw [prepared_eq order v rows axis m ws f g p r xs] at h0
  apply (h0.seq he).consequence (fun _ h => h) (fun _ h => h) _
  have hn : 1≤rows*2^s.bits := Nat.mul_pos hr (by positivity)
  have hp : 1≤s.payload := by omega
  have hnp := Nat.mul_le_mul_left (rows*2^s.bits) hp
  nlinarith

theorem endpoint (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (rows*2^s.bits) → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    (output order v rows axis m ws f g p r xs).tape 58=full g r (UnitPhaseStreamEndpoint.result v axis m ws xs) ∧
      (output order v rows axis m ws f g p r xs).head 58=r+(rows*2^s.bits)*(2*(w+1)) := by
  have h := UnitPhaseFullStreamArray.endpoint order v rows axis m ws f g p r xs w hw
  change (beforeCleanup order v rows axis m ws f g p r xs).tape 58=_ ∧
    (beforeCleanup order v rows axis m ws f g p r xs).head 58=_ at h
  simpa [output,UnitPhaseStreamAddressReset.output_eq,setTape,Tapes.append,Fin.addCases] using h

end
end IntegerMultBounds.Machine.UnitPhaseFullStreamClean
