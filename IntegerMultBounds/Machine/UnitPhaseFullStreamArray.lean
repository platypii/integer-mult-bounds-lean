import IntegerMultBounds.Machine.UnitPhaseStreamEndpoint
import IntegerMultBounds.Machine.ButterflyStreamEndpoint

/-! Full phase stream theorem on literal finite coefficient arrays. The
input tape and all record contexts are derived from one serialized array;
the output is exactly its pointwise runtime-address phase serialization. -/
namespace IntegerMultBounds.Machine.UnitPhaseFullStreamArray
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient full position)
open UnitPhaseStreamEndpoint (result)
variable {s : Shape}

def tail (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (rows*2^s.bits) → Coefficient) : Tapes 4 2 :=
  ⟨![p,0,r,0],![full f p xs,(fun _ => blank),g,(fun _ => blank)]⟩
def input (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (rows*2^s.bits) → Coefficient) :=
  UnitPhaseFullStream.input order v rows axis (tail f g p r xs)
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (rows*2^s.bits) → Coefficient) :=
  UnitPhaseFullStream.output order v rows axis m ws (UnitPhaseStreamData.contexts f p xs) (tail f g p r xs)

theorem result_width (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (xs : Fin n → Coefficient) (w : ℕ) (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (i : Fin n) : (result v axis m ws xs i).1.length=w ∧ (result v axis m ws xs i).2.length=w := by
  have hc : ∀ j,(UnitPhaseStreamEndpoint.components (xs i) j).length=w := by
    intro j
    unfold UnitPhaseStreamEndpoint.components
    split_ifs <;> first | exact (hw i).1 | exact (hw i).2
  exact ⟨UnitPhaseNumerator.words_length _ _ _ w hc,UnitPhaseNumerator.words_length _ _ _ w hc⟩

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (rows*2^s.bits) → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    HoareTime (UnitPhaseFullStream.program m ws) (fun z => z=input order v rows axis f g p r xs)
      (fun z => z=output order v rows axis m ws f g p r xs)
      ((rows*2^s.bits)*((FixedBasePowerDescriptor.constant 2+13000)*s.payload+24*w)) := by
  have hn : 0<rows*2^s.bits := Nat.mul_pos hr (by positivity)
  apply UnitPhaseFullStream.runs order v rows hr axis m ws hm hslots hl
    (UnitPhaseStreamData.contexts f p xs) w (UnitPhaseStreamData.widths f p xs w hw) hspan hrecord
    (tail f g p r xs)
  · change full f p xs=(UnitPhaseStreamData.contexts f p xs 0).tape ∧
      p=(UnitPhaseStreamData.contexts f p xs 0).start
    rw [UnitPhaseStreamData.tape _ _ _ _ hn,UnitPhaseStreamData.start _ _ _ _ hn]
    simp [position,CyclicRowCycle.rowPrefix]
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact UnitPhaseStreamData.adjacent f p xs

theorem endpoint (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (rows*2^s.bits) → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    (output order v rows axis m ws f g p r xs).tape 58=full g r (result v axis m ws xs) ∧
      (output order v rows axis m ws f g p r xs).head 58=r+(rows*2^s.bits)*(2*(w+1)) := by
  have h := UnitPhaseStreamEndpoint.output_prefix v axis m ws f g p r xs
    (UnitPhaseFullStreamInit.readyTail (s := s) rows (tail f g p r xs)) (by exact ⟨rfl,rfl⟩)
    (rows*2^s.bits) le_rfl
  change _=_ ∧ _=_ at h
  rw [ButterflyStreamData.prefixTape,CyclicRowCycle.prefix_all] at h
  rw [ButterflyStreamEndpoint.position_all r (result v axis m ws xs) w (result_width v axis m ws xs w hw)] at h
  exact h

end
end IntegerMultBounds.Machine.UnitPhaseFullStreamArray
