import IntegerMultBounds.Machine.UnitPhaseFullStreamInitBudget
import IntegerMultBounds.Machine.UnitPhaseFullStreamLoop

/-! Complete physical full-address coefficient phase stream. Original rows4
and geometric headers produce the actual count rows*2^bits on59 and initialize
the live counter; every actual coefficient is processed and all generated
numeric/count/loop controls are erased, with a linear paid runtime bound. -/
namespace IntegerMultBounds.Machine.UnitPhaseFullStream
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open SharedPlacementAlphabet (setTape)
variable {s : Shape}

def program (m : ℕ) (ws : List (ZMod 4)) :=
  seq (extend UnitPhaseFullStreamInit.program 2) (UnitPhaseFullStreamLoop.program m ws)
def input (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (tail : Tapes 4 2) :=
  CountedLoopHeaderClean.bank (UnitPhaseFullStreamInit.input order v rows axis tail)
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → Context 2) (tail : Tapes 4 2) :=
  setTape (CountedLoopHeaderClean.bank (UnitPhaseStreamLoop.state order v rows axis m ws ctx
    (UnitPhaseFullStreamInit.readyTail (s := s) rows tail) (rows*2^s.bits))) 59 (fun _ => blank) 0

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (ctx : ℕ → Context 2) (w : ℕ)
    (hw : ∀ i<rows*2^s.bits,(ctx i).re.length=w ∧ (ctx i).im.length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) (tail : Tapes 4 2)
    (ht : tail.tape 0=(ctx 0).tape ∧ tail.head 0=(ctx 0).start)
    (hc : tail.tape 1=(fun _ => blank) ∧ tail.head 1=0)
    (hn : tail.tape 3=(fun _ => blank) ∧ tail.head 3=0)
    (hnext : ∀ i,i+1<rows*2^s.bits →(ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2) :
    HoareTime (program m ws) (fun z => z=input order v rows axis tail)
      (fun z => z=output order v rows axis m ws ctx tail)
      ((rows*2^s.bits)*((FixedBasePowerDescriptor.constant 2+13000)*s.payload+24*w)) := by
  have h0 := hoare_extend_eq (UnitPhaseFullStreamInit.runs order v rows axis (ctx 0) tail hc hn)
    (SharedBank.empty 2 2)
  have h1 := UnitPhaseFullStreamLoop.runs order v rows (rows*2^s.bits) axis m ws hm hslots hl ctx w hw hspan hrecord
    (UnitPhaseFullStreamInit.readyTail (s := s) rows tail)
    (by simpa [UnitPhaseFullStreamInit.readyTail,UnitPhaseCountTransfer.tailCount,setTape] using ht)
    (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩) hnext
  have hready : UnitPhaseFullStreamInit.output order v rows axis (ctx 0) tail=
      UnitPhaseStreamLoop.state order v rows axis m ws ctx (UnitPhaseFullStreamInit.readyTail (s := s) rows tail) 0 := rfl
  rw [hready] at h0
  apply (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) _
  have hi := UnitPhaseFullStreamInitBudget.cost_payload order v rows axis hr hrecord
  have hn' : 1≤rows*2^s.bits := Nat.mul_pos hr (by positivity)
  have hp : 1≤s.payload := by omega
  have hnp := Nat.mul_le_mul_left (rows*2^s.bits) hp
  nlinarith

end
end IntegerMultBounds.Machine.UnitPhaseFullStream
