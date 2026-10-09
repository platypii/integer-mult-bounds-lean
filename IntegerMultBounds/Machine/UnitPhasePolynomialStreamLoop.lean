import IntegerMultBounds.Machine.UnitPhasePolynomialAdvance

/-! The outer physically counted address loop runs one phase preparation per
address and a complete inner coefficient loop. Original row metadata and
polynomial multiplicity persist; both outer loop-work tapes are erased. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialStreamLoop
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open CountedLoopReuseAlphabet (binary)
open BinaryAddressTableData (row)
variable {s : Shape}

def loop (m : ℕ) (ws : List (ZMod 4)) :=
  CountedLoopHeaderClean.program (UnitPhasePolynomialFull.program m ws) (59 : Fin 63)
def tails (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R : ℕ) : ℕ → Tapes 4 2
  | 0 => z
  | i+1 => UnitPhasePolynomialFull.nextTail order v rows axis m ws i
      (tails order v rows axis m ws ctx z R i) (ctx i) R

def state (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R i : ℕ) :=
  UnitPhasePolynomialRecord.initial order v rows axis (row s.bits (i-1))
    (tails order v rows axis m ws ctx z R i) R

theorem counter (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R : ℕ)
    (hc : z.tape 1=binary (row s.bits 0) ∧ z.head 1=1) (i : ℕ) :
    (tails order v rows axis m ws ctx z R i).tape 1=binary (row s.bits i) ∧
    (tails order v rows axis m ws ctx z R i).head 1=1 := by
  cases i with
  | zero => exact hc
  | succ i => exact UnitPhasePolynomialAdvance.counter _ _ _ _ _ _ _ _ _ _

theorem count (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R i : ℕ) :
    (tails order v rows axis m ws ctx z R i).tape 3=z.tape 3 ∧
    (tails order v rows axis m ws ctx z R i).head 3=z.head 3 := by
  induction i with
  | zero => exact ⟨rfl,rfl⟩
  | succ i ih =>
    have h := UnitPhasePolynomialAdvance.count order v rows axis m ws i
      (tails order v rows axis m ws ctx z R i) (ctx i) R
    exact ⟨h.1.trans ih.1,h.2.trans ih.2⟩

theorem source (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R N : ℕ) (hR : 0<R)
    (hs : z.tape 0=(ctx 0 0).tape ∧ z.head 0=(ctx 0 0).start)
    (hb : ∀ i,i+1<N → (ctx (i+1) 0).tape=(ctx i (R-1)).tape ∧
      (ctx (i+1) 0).start=(ctx i (R-1)).start+(ctx i (R-1)).re.length+(ctx i (R-1)).im.length+2)
    (i : ℕ) (hi : i<N) :
    (tails order v rows axis m ws ctx z R i).tape 0=(ctx i 0).tape ∧
    (tails order v rows axis m ws ctx z R i).head 0=(ctx i 0).start := by
  cases i with
  | zero => exact hs
  | succ i =>
    have h := UnitPhasePolynomialAdvance.source order v rows axis m ws i
      (tails order v rows axis m ws ctx z R i) (ctx i) R hR
    have hnext := hb i hi
    exact ⟨h.1.trans hnext.1.symm,h.2.trans hnext.2.symm⟩

def bodyCost (v : Stage s) (axis : Fin v.f) (m R w i : ℕ) :=
  5*s.bits+10 + (10400*(s.bits+1)+2*m+4 +
    (R*(24*w+89)+11*(RecursiveChildQuotientsConstant.bits R).length+35) +
    UnitPhaseControlReset.cost (UnitPhaseRecordKernel.selected v axis m (row s.bits i))
      (UnitPhaseRecordKernel.headerWords v axis m)+2)+1

theorem runs (order : Order) (v : Stage s) (rows N : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R w : ℕ) (hR : 0<R)
    (hw : ∀ i<N,∀ j<R,(ctx i j).re.length=w ∧ (ctx i j).im.length=w)
    (hs : z.tape 0=(ctx 0 0).tape ∧ z.head 0=(ctx 0 0).start)
    (hc : z.tape 1=binary (row s.bits 0) ∧ z.head 1=1)
    (hn : z.tape 3=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits N) ∧ z.head 3=1)
    (hnext : ∀ i<N,∀ j,j+1<R → (ctx i (j+1)).tape=(ctx i j).tape ∧
      (ctx i (j+1)).start=(ctx i j).start+(ctx i j).re.length+(ctx i j).im.length+2)
    (hb : ∀ i,i+1<N → (ctx (i+1) 0).tape=(ctx i (R-1)).tape ∧
      (ctx (i+1) 0).start=(ctx i (R-1)).start+(ctx i (R-1)).re.length+(ctx i (R-1)).im.length+2) :
    HoareTime (loop m ws)
      (fun t => t=CountedLoopHeaderClean.bank (state order v rows axis m ws ctx z R 0))
      (fun t => t=CountedLoopHeaderClean.bank (state order v rows axis m ws ctx z R N))
      (CountedLoopHeaderClean.cost N (RecursiveChildQuotientsConstant.bits N) (bodyCost v axis m R w)) := by
  have hbody : ∀ i<N,HoareTime (UnitPhasePolynomialFull.program m ws)
      (fun t => t=state order v rows axis m ws ctx z R i)
      (fun t => t=state order v rows axis m ws ctx z R (i+1)) (bodyCost v axis m R w i) := by
    intro i hi
    have h := UnitPhasePolynomialFull.runs order v rows axis m ws hm hslots hl
      (row s.bits (i-1)) (BinaryAddressTableData.row_length _ _) i hspan
      (tails order v rows axis m ws ctx z R i) (ctx i) R w (hw i hi)
      (source order v rows axis m ws ctx z R N hR hs hb i hi)
      (counter order v rows axis m ws ctx z R hc i) (hnext i hi)
    apply h.consequence (fun _ h => h) _ le_rfl
    intro t ht
    rw [UnitPhasePolynomialFull.restored] at ht
    simpa only [state,tails,Nat.add_sub_cancel] using ht
  exact CountedLoopHeaderClean.runs (UnitPhasePolynomialFull.program m ws) (59 : Fin 63)
    (RecursiveChildQuotientsConstant.bits N) N (state order v rows axis m ws ctx z R)
    (bodyCost v axis m R w) ⟨hn.2,hn.1⟩ (RecursiveChildQuotientsConstant.bits_value _) hbody

end
end IntegerMultBounds.Machine.UnitPhasePolynomialStreamLoop
