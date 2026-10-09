import IntegerMultBounds.Machine.UnitPhaseRecordRestore
import IntegerMultBounds.Machine.CountedLoopHeaderClean

/-! Complete counted coefficient stream phase loop. The count is physically
copied from original node header4; every iteration advances the live address
counter and actual streams and restores all phase workspace. Generated loop
controls are physically erased at the endpoint. -/
namespace IntegerMultBounds.Machine.UnitPhaseStreamLoop
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open BinaryAddressTableData (row)
open CountedLoopReuseAlphabet (binary)
variable {s : Shape}

def tails (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (ctx : ℕ → Context 2) (tail : Tapes 4 2) : ℕ → Tapes 4 2
  | 0 => tail
  | i+1 => UnitPhaseRecordRestore.nextTail v axis m ws i (ctx i) (tails v axis m ws ctx tail i)
def state (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → Context 2) (tail : Tapes 4 2) (i : ℕ) :=
  UnitPhaseRecordRead.initial order v rows axis (row s.bits (i-1)) (ctx i)
    (tails v axis m ws ctx tail i)
def program (m : ℕ) (ws : List (ZMod 4)) :=
  CountedLoopHeaderClean.program (UnitPhaseRecordFull.program m ws) (4 : Fin 60)
def bodyCost (v : Stage s) (axis : Fin v.f) (m w : ℕ) (i : ℕ) :=
  UnitPhaseRecordFull.cost v axis m w i

theorem counter (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (ctx : ℕ → Context 2) (tail : Tapes 4 2)
    (hc : tail.tape 1=binary (row s.bits 0) ∧ tail.head 1=1) (i : ℕ) :
    (tails v axis m ws ctx tail i).tape 1=binary (row s.bits i) ∧
      (tails v axis m ws ctx tail i).head 1=1 := by
  cases i with
  | zero => exact hc
  | succ i => exact ⟨rfl,rfl⟩

theorem source (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (ctx : ℕ → Context 2) (tail : Tapes 4 2) (n : ℕ)
    (ht : tail.tape 0=(ctx 0).tape ∧ tail.head 0=(ctx 0).start)
    (hnext : ∀ i<n,(ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2)
    (i : ℕ) (hi : i≤n) :
    (tails v axis m ws ctx tail i).tape 0=(ctx i).tape ∧
      (tails v axis m ws ctx tail i).head 0=(ctx i).start := by
  cases i with
  | zero => exact ht
  | succ i =>
    have h := hnext i (by omega)
    exact ⟨h.1.symm,h.2.symm⟩

theorem body (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (ctx : ℕ → Context 2) (w : ℕ)
    (hw : ∀ i<rows,(ctx i).re.length=w ∧ (ctx i).im.length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) (tail : Tapes 4 2)
    (ht : tail.tape 0=(ctx 0).tape ∧ tail.head 0=(ctx 0).start)
    (hc : tail.tape 1=binary (row s.bits 0) ∧ tail.head 1=1)
    (hnext : ∀ i<rows,(ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2)
    (i : ℕ) (hi : i<rows) :
    HoareTime (UnitPhaseRecordFull.program m ws)
      (fun z => z=state order v rows axis m ws ctx tail i)
      (fun z => z=state order v rows axis m ws ctx tail (i+1)) (bodyCost v axis m w i) := by
  have h := UnitPhaseRecordFull.runs order v rows axis m ws hm hslots hl (row s.bits (i-1))
    (BinaryAddressTableData.row_length _ _) i (ctx i) w (hw i hi).1 (hw i hi).2 hspan hrecord
    (tails v axis m ws ctx tail i) (source v axis m ws ctx tail rows ht hnext i hi.le)
    (counter v axis m ws ctx tail hc i)
  apply h.consequence (fun _ h => h) _ le_rfl
  intro z hz
  rw [UnitPhaseRecordRestore.restored order v rows axis m ws i (ctx i) (ctx (i+1))] at hz
  simpa only [state,tails,Nat.add_sub_cancel] using hz

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (ctx : ℕ → Context 2) (w : ℕ)
    (hw : ∀ i<rows,(ctx i).re.length=w ∧ (ctx i).im.length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) (tail : Tapes 4 2)
    (ht : tail.tape 0=(ctx 0).tape ∧ tail.head 0=(ctx 0).start)
    (hc : tail.tape 1=binary (row s.bits 0) ∧ tail.head 1=1)
    (hnext : ∀ i<rows,(ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2) :
    HoareTime (program m ws)
      (fun z => z=CountedLoopHeaderClean.bank (state order v rows axis m ws ctx tail 0))
      (fun z => z=CountedLoopHeaderClean.bank (state order v rows axis m ws ctx tail rows))
      (CountedLoopHeaderClean.cost rows (RecursiveChildQuotientsConstant.bits rows) (bodyCost v axis m w)) := by
  apply CountedLoopHeaderClean.runs (UnitPhaseRecordFull.program m ws) (4 : Fin 60)
    (RecursiveChildQuotientsConstant.bits rows) rows (state order v rows axis m ws ctx tail)
    (bodyCost v axis m w)
  · exact ⟨rfl,rfl⟩
  · exact RecursiveChildQuotientsConstant.bits_value rows
  · exact body order v rows axis m ws hm hslots hl ctx w hw hspan hrecord tail ht hc hnext

end
end IntegerMultBounds.Machine.UnitPhaseStreamLoop
