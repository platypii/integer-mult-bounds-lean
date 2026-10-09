import IntegerMultBounds.Machine.UnitPhaseStreamBudget

/-! Count the entire coefficient stream using generated descriptor59, while
preserving original node row header4. The supplied count is read physically;
all loop controls and the generated count descriptor are erased afterwards. -/
namespace IntegerMultBounds.Machine.UnitPhaseFullStreamLoop
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open CountedLoopReuseAlphabet (binary)
open BinaryAddressTableData (row)
open SharedPlacementAlphabet (setTape)
variable {s : Shape}

def loop (m : ℕ) (ws : List (ZMod 4)) :=
  CountedLoopHeaderClean.program (UnitPhaseRecordFull.program m ws) (59 : Fin 60)
def cleanup := BinaryDescriptorCleanupList.oneProgram (a := 2) (59 : Fin 62)
def program (m : ℕ) (ws : List (ZMod 4)) := seq (loop m ws) cleanup

theorem retained_count (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (ctx : ℕ → Context 2) (tail : Tapes 4 2) (i : ℕ) :
    (UnitPhaseStreamLoop.tails v axis m ws ctx tail i).tape 3=tail.tape 3 ∧
      (UnitPhaseStreamLoop.tails v axis m ws ctx tail i).head 3=tail.head 3 := by
  induction i with
  | zero => exact ⟨rfl,rfl⟩
  | succ i ih => exact ih

theorem source (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (ctx : ℕ → Context 2) (tail : Tapes 4 2) (n : ℕ)
    (ht : tail.tape 0=(ctx 0).tape ∧ tail.head 0=(ctx 0).start)
    (hnext : ∀ i,i+1<n → (ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2)
    (i : ℕ) (hi : i<n) :
    (UnitPhaseStreamLoop.tails v axis m ws ctx tail i).tape 0=(ctx i).tape ∧
      (UnitPhaseStreamLoop.tails v axis m ws ctx tail i).head 0=(ctx i).start := by
  cases i with
  | zero => exact ht
  | succ i =>
    have h := hnext i hi
    exact ⟨h.1.symm,h.2.symm⟩

theorem runs (order : Order) (v : Stage s) (rows n : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (ctx : ℕ → Context 2) (w : ℕ)
    (hw : ∀ i<n,(ctx i).re.length=w ∧ (ctx i).im.length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) (tail : Tapes 4 2)
    (ht : tail.tape 0=(ctx 0).tape ∧ tail.head 0=(ctx 0).start)
    (hc : tail.tape 1=binary (row s.bits 0) ∧ tail.head 1=1)
    (hn : tail.tape 3=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n) ∧ tail.head 3=1)
    (hnext : ∀ i,i+1<n →(ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2) :
    HoareTime (program m ws)
      (fun z => z=CountedLoopHeaderClean.bank (UnitPhaseStreamLoop.state order v rows axis m ws ctx tail 0))
      (fun z => z=setTape (CountedLoopHeaderClean.bank
        (UnitPhaseStreamLoop.state order v rows axis m ws ctx tail n)) 59 (fun _ => blank) 0)
      (n*(10630*s.payload+24*w)+53) := by
  have hbody : ∀ i<n,HoareTime (UnitPhaseRecordFull.program m ws)
      (fun z => z=UnitPhaseStreamLoop.state order v rows axis m ws ctx tail i)
      (fun z => z=UnitPhaseStreamLoop.state order v rows axis m ws ctx tail (i+1))
      (UnitPhaseStreamLoop.bodyCost v axis m w i) := by
    intro i hi
    have h := UnitPhaseRecordFull.runs order v rows axis m ws hm hslots hl (row s.bits (i-1))
      (BinaryAddressTableData.row_length _ _) i (ctx i) w (hw i hi).1 (hw i hi).2 hspan hrecord
      (UnitPhaseStreamLoop.tails v axis m ws ctx tail i)
      (source v axis m ws ctx tail n ht hnext i hi)
      (UnitPhaseStreamLoop.counter v axis m ws ctx tail hc i)
    apply h.consequence (fun _ h => h) _ le_rfl
    intro z hz
    rw [UnitPhaseRecordRestore.restored order v rows axis m ws i (ctx i) (ctx (i+1))] at hz
    simpa only [UnitPhaseStreamLoop.state,UnitPhaseStreamLoop.tails,Nat.add_sub_cancel] using hz
  have h0 := CountedLoopHeaderClean.runs (UnitPhaseRecordFull.program m ws) (59 : Fin 60)
    (RecursiveChildQuotientsConstant.bits n) n (UnitPhaseStreamLoop.state order v rows axis m ws ctx tail)
    (UnitPhaseStreamLoop.bodyCost v axis m w)
    (by change tail.head 3=1 ∧ tail.tape 3=_; exact ⟨hn.2,hn.1⟩)
    (RecursiveChildQuotientsConstant.bits_value _) hbody
  have hcount := retained_count v axis m ws ctx tail n
  have h1 := BinaryDescriptorCleanupList.one_hoare (59 : Fin 62)
    (CountedLoopHeaderClean.bank (UnitPhaseStreamLoop.state order v rows axis m ws ctx tail n))
    (RecursiveChildQuotientsConstant.bits n)
    (by change (UnitPhaseStreamLoop.tails v axis m ws ctx tail n).tape 3=_
        rw [hcount.1,hn.1,BinaryDescriptorStackRoundtrip.descriptor_encoded])
    (by change (UnitPhaseStreamLoop.tails v axis m ws ctx tail n).head 3=1; rw [hcount.2,hn.2])
  apply (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) _
  have hb := UnitPhaseStreamBudget.loop_bound v axis m w n hm hslots hspan hrecord
  have hs := ActiveRepairRankHeadersCommands.bits_length n
  have hp : 1≤s.payload := by omega
  have hx := Nat.mul_le_mul_left n hp
  nlinarith

end
end IntegerMultBounds.Machine.UnitPhaseFullStreamLoop
