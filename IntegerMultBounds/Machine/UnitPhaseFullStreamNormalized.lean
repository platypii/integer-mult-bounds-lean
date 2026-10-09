import IntegerMultBounds.Machine.UnitPhaseSourceEndpoint
import IntegerMultBounds.Machine.BlankWordReturnAt

/-! Native-bridge endpoint for a literal phase coefficient array: input and
output streams are both physically rewound to0, every generated phase/count/
address workspace is erased, and output words have exact stored signed width. -/
namespace IntegerMultBounds.Machine.UnitPhaseFullStreamNormalized
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient)
open SharedPlacementAlphabet (setTape)
open UnitPhaseStreamEndpoint (result)
variable {s : Shape} {n : ℕ}

def serialized (xs : Fin n → Coefficient) := (List.ofFn (fun i => ButterflyStreamData.encoded (xs i))).flatten

theorem encoded_nonblank (a : Coefficient) : ∀ x∈ButterflyStreamData.encoded a,x≠(blank : Fin 6) := by
  intro x hx
  simp only [ButterflyStreamData.encoded,DelimitedRadixRecord.complex,DelimitedRadixRecord.field,List.mem_append] at hx
  rcases hx with (hm | hm) | (hm | hm)
  all_goals first
    | obtain ⟨d,_,rfl⟩ := List.mem_map.mp hm; fin_cases d <;> decide
    | have hx : x=separator := List.mem_singleton.mp hm; subst x; decide

theorem nonblank (xs : Fin n → Coefficient) : ∀ x∈serialized xs,x≠(blank : Fin 6) := by
  intro x hx
  obtain ⟨ys,hys,hx⟩ := List.mem_flatten.mp hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hys
  exact encoded_nonblank (xs i) x hx

theorem length (xs : Fin n → Coefficient) (w : ℕ) (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    (serialized xs).length=n*(2*(w+1)) := by
  have h := CyclicRowSplit.prefix_length (fun i => ButterflyStreamData.encoded (xs i)) (2*(w+1))
    (fun i => DelimitedRadixRecord.complex_length _ _ _ (hw i).1 (hw i).2) n le_rfl
  simpa only [CyclicRowCycle.prefix_all,serialized] using h

def rewinds := seq (BlankWordReturnAt.program (a := 2) (56 : Fin 62)) (BlankWordReturnAt.program (a := 2) (58 : Fin 62))
def program (m : ℕ) (ws : List (ZMod 4)) := seq (UnitPhaseFullStreamClean.program m ws) rewinds

def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (xs : Fin (rows*2^s.bits) → Coefficient) :=
  setTape (setTape (UnitPhaseFullStreamClean.output order v rows axis m ws (fun _ => blank) (fun _ => blank) 0 0 xs)
    56 (putWord (fun _ => blank) 0 (serialized xs)) 0)
    58 (putWord (fun _ => blank) 0 (serialized (result v axis m ws xs))) 0

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (xs : Fin (rows*2^s.bits) → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    HoareTime (program m ws)
      (fun z => z=UnitPhaseFullStreamArray.input order v rows axis (fun _ => blank) (fun _ => blank) 0 0 xs)
      (fun z => z=output order v rows axis m ws xs)
      ((rows*2^s.bits)*((FixedBasePowerDescriptor.constant 2+13200)*s.payload+28*w)) := by
  let z := UnitPhaseFullStreamClean.output order v rows axis m ws (fun _ => blank) (fun _ => blank) 0 0 xs
  have h0 := UnitPhaseFullStreamClean.runs order v rows hr axis m ws hm hslots hl
    (fun _ => blank) (fun _ => blank) 0 0 xs w hw hspan hrecord
  have hs := UnitPhaseSourceEndpoint.clean order v rows hr axis m ws (fun _ => blank) (fun _ => blank) 0 0 xs w hw
  have ho := UnitPhaseFullStreamClean.endpoint order v rows axis m ws (fun _ => blank) (fun _ => blank) 0 0 xs w hw
  have h1 := BlankWordReturnAt.runs z (56 : Fin 62) (serialized xs) (nonblank xs) hs.1
    (by rw [length xs w hw]; simpa using hs.2)
  have h2 := BlankWordReturnAt.runs (setTape z 56 (putWord (fun _ => blank) 0 (serialized xs)) 0)
    (58 : Fin 62) (serialized (result v axis m ws xs)) (nonblank _)
    (by exact ho.1)
    (by rw [length _ w (UnitPhaseFullStreamArray.result_width v axis m ws xs w hw)]
        simpa [setTape] using ho.2)
  apply (h0.seq (h1.seq h2)).consequence (fun _ h => h) (fun _ h => h) _
  rw [length xs w hw,length _ w (UnitPhaseFullStreamArray.result_width v axis m ws xs w hw)]
  have hn : 1≤rows*2^s.bits := Nat.mul_pos hr (by positivity)
  have hp : 1≤s.payload := by omega
  have hnp := Nat.mul_le_mul_left (rows*2^s.bits) hp
  nlinarith

end
end IntegerMultBounds.Machine.UnitPhaseFullStreamNormalized
