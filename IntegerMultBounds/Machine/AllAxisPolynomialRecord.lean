import IntegerMultBounds.Machine.AllAxisPhaseFlagsEndpoint
import IntegerMultBounds.Machine.UnitPhasePolynomialFrame
import IntegerMultBounds.Machine.UnitPhaseControlReset
import IntegerMultBounds.Machine.UnitPhaseRecordKernel

/-! Actual once-per-address polynomial phase application: derive and scan
one sparse address phase, apply its retained flags to a physically counted
coefficient stream, then erase phase controls/descriptors once. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialRecord
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open AllAxisPhaseFlagsCaller (controls phase)
open AllAxisPhaseFlagsEndpoint (headerWords)
open MarkedWordCleanup (one)
variable {s : Shape}

def multiplicity (R : ℕ) : Tapes 1 2 := one (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits R)) 1
def tail (z : Tapes 4 2) (R : ℕ) := z.append ((multiplicity R).append (SharedBank.empty 2 2))
def initial (order : Order) (v : Stage s) (rows : ℕ)
    (addr : List Bool) (z : Tapes 4 2) (R : ℕ) :=
  (AllAxisPhaseFlagsCaller.input order v rows addr (SharedBank.empty 6 2)).append (tail z R)
def prepared (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) :=
  (AllAxisPhaseFlagsCaller.output order v rows m ws addr (SharedBank.empty 6 2)).append z

def prepare (m : ℕ) (ws : List (ZMod 4)) := extend (AllAxisPhaseFlagsCaller.program m ws) 7
def cleanup := extend UnitPhaseControlReset.program 3
def program (m : ℕ) (ws : List (ZMod 4)) := seq (seq (prepare m ws) UnitPhasePolynomialLoop.program) cleanup

def finished (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :=
  UnitPhasePolynomialLoop.state (prepared order v rows m ws addr z) ctx (phase v m ws addr) R
def output (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :=
  CountedLoopHeaderClean.bank ((UnitPhaseControlReset.output (finished order v rows m ws addr z ctx R)).append (multiplicity R))

theorem reassociate (b : Tapes 56 2) (z : Tapes 4 2) (R : ℕ) :
    b.append (tail z R)=CountedLoopHeaderClean.bank ((b.append z).append (multiplicity R)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem prepared_flags (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) :
    UnitPhasePolynomialLoop.flagsAt (prepared order v rows m ws addr z) (phase v m ws addr) := AllAxisPhaseFlagsEndpoint.flags order v rows m ws addr (SharedBank.empty 6 2) z

theorem prepared_core (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) :
    UnitPhasePolynomialLoop.coreBlank (prepared order v rows m ws addr z) := AllAxisPhaseFlagsEndpoint.core order v rows m ws addr z

theorem reassociate60 (x : Tapes 60 2) (R : ℕ) :
    x.append ((multiplicity R).append (SharedBank.empty 2 2))=
      CountedLoopHeaderClean.bank (x.append (multiplicity R)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem prepared_headers (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) :
    ∀ i ∈ UnitPhaseControlReset.headerSlots,(prepared order v rows m ws addr z).head i=1 ∧
      (prepared order v rows m ws addr z).tape i=BinaryDescriptorStack.descriptor (headerWords v m i) := AllAxisPhaseFlagsEndpoint.headers order v rows m ws addr (SharedBank.empty 6 2) z

theorem prepare_runs (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (addr : List Bool) (ha : addr.length=s.bits)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<addr.length)
    (z : Tapes 4 2) (R : ℕ) :
    HoareTime (prepare m ws) (fun t => t=initial order v rows addr z R)
      (fun t => t=CountedLoopHeaderClean.bank ((prepared order v rows m ws addr z).append (multiplicity R)))
      (10400*(s.bits+1)+ws.length*(7*v.f+11*(RecursiveChildQuotientsConstant.bits v.f).length+36)+4) := by
  have h := hoare_extend_eq (AllAxisPhaseFlagsCaller.runs order v rows m ws hm hslots hl addr (SharedBank.empty 6 2) ha (by simpa only [ha] using hspan)) (tail z R)
  apply h.consequence (fun _ h => h) _ le_rfl
  intro t ht
  exact ht.trans (reassociate _ _ _)

theorem cleanup_finished (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :
    HoareTime UnitPhaseControlReset.program
      (fun t => t=finished order v rows m ws addr z ctx R)
      (fun t => t=UnitPhaseControlReset.output (finished order v rows m ws addr z ctx R))
      (UnitPhaseControlReset.cost (controls v m addr) (headerWords v m)) := by
  let b := prepared order v rows m ws addr z
  let p := phase v m ws addr
  have hf := prepared_flags order v rows m ws addr z
  have hc := prepared_core order v rows m ws addr z
  have fr := UnitPhasePolynomialFrame.frame b ctx p hf hc
  apply UnitPhaseControlReset.runs _ _ p (headerWords v m)
  · have h := fr 44 (by decide) R
    change (UnitPhasePolynomialLoop.state b ctx p R).tape 44=SelectedSourceBitsScan.word (controls v m addr) ∧
      (UnitPhasePolynomialLoop.state b ctx p R).head 44=(controls v m addr).length
    rw [h.1,h.2]
    exact ⟨(AllAxisPhaseFlagsEndpoint.control order v rows m ws addr (SharedBank.empty 6 2)).2,
      (AllAxisPhaseFlagsEndpoint.control order v rows m ws addr (SharedBank.empty 6 2)).1⟩
  · have h := UnitPhasePolynomialLoop.state_flags b ctx p hf R 0
    exact ⟨h.2,h.1⟩
  · have h := UnitPhasePolynomialLoop.state_flags b ctx p hf R 1
    exact ⟨h.2,h.1⟩
  · intro i hi
    have h := fr i (by
      simp only [UnitPhaseControlReset.headerSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide) R
    change (UnitPhasePolynomialLoop.state b ctx p R).head i=1 ∧
      (UnitPhasePolynomialLoop.state b ctx p R).tape i=_
    rw [h.1,h.2]
    exact prepared_headers order v rows m ws addr z i hi

theorem cleanup_runs (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :
    HoareTime cleanup
      (fun t => t=CountedLoopHeaderClean.bank ((finished order v rows m ws addr z ctx R).append (multiplicity R)))
      (fun t => t=output order v rows m ws addr z ctx R)
      (UnitPhaseControlReset.cost (controls v m addr) (headerWords v m)) := by
  have h := hoare_extend_eq (cleanup_finished order v rows m ws addr z ctx R)
    ((multiplicity R).append (SharedBank.empty 2 2))
  apply h.consequence _ _ le_rfl
  · intro t ht
    exact ht.trans (reassociate60 _ _).symm
  · intro t ht
    exact ht.trans (reassociate60 _ _)

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (addr : List Bool) (ha : addr.length=s.bits)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<addr.length)
    (z : Tapes 4 2) (ctx : ℕ → Context 2) (R w : ℕ)
    (hw : ∀ i<R,(ctx i).re.length=w ∧ (ctx i).im.length=w)
    (hs : z.tape 0=(ctx 0).tape ∧ z.head 0=(ctx 0).start)
    (hnext : ∀ i,i+1<R → (ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2) :
    HoareTime (program m ws) (fun b => b=initial order v rows addr z R)
      (fun b => b=output order v rows m ws addr z ctx R)
      (10400*(s.bits+1)+ws.length*(7*v.f+11*(RecursiveChildQuotientsConstant.bits v.f).length+36)+4 + (R*(24*w+89)+11*(RecursiveChildQuotientsConstant.bits R).length+35) +
        UnitPhaseControlReset.cost (controls v m addr) (headerWords v m)+2) := by
  have h0 := prepare_runs order v rows m ws hm hslots hl addr ha hspan z R
  have h1 := UnitPhasePolynomialLoop.runs (prepared order v rows m ws addr z) ctx (phase v m ws addr) R w hw
    (prepared_flags order v rows m ws addr z) (prepared_core order v rows m ws addr z) hs hnext
  have h2 := cleanup_runs order v rows m ws addr z ctx R
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.AllAxisPolynomialRecord
