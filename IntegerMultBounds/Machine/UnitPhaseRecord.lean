import IntegerMultBounds.Machine.UnitPhaseRecordRead
import IntegerMultBounds.Machine.UnitPhaseSigned

/-! One complete coefficient stream iteration after address readout: actual
record read, phase flag initialization, header-derived phase arithmetic,
result emission, and complete workspace reset, with a paid time bound. -/
namespace IntegerMultBounds.Machine.UnitPhaseRecord
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
variable {s : Shape}

def program (m : ℕ) (ws : List (ZMod 4)) :=
  seq UnitPhaseRecordRead.program (UnitPhaseRecordKernel.program m ws)
abbrev initial := @UnitPhaseRecordRead.initial

def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (a : Context 2) (tail : Tapes 4 2) :=
  UnitPhaseRecordKernel.output order v rows axis m ws addr (UnitPhaseRecordRead.sources a)
    (UnitPhaseRecordRead.advanced a tail)
def cost (v : Stage s) (axis : Fin v.f) (m w : ℕ) (addr : List Bool) :=
  UnitPhaseRecordKernel.cost v axis m w addr+4*w+16

theorem source_width (a : Context 2) (w : ℕ) (hr : a.re.length=w) (hi : a.im.length=w) :
    ∀ j,(UnitPhaseRecordRead.sources a j).length=w := by
  intro j
  unfold UnitPhaseRecordRead.sources
  split_ifs <;> assumption

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (addr : List Bool) (a : Context 2) (w : ℕ) (hr : a.re.length=w) (hi : a.im.length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<addr.length)
    (ha : addr.length=s.bits) (hrecord : s.bits+1≤s.payload) (tail : Tapes 4 2)
    (ht : tail.tape 0=a.tape ∧ tail.head 0=a.start) :
    HoareTime (program m ws) (fun z => z=initial order v rows axis addr a tail)
      (fun z => z=output order v rows axis m ws addr a tail) (cost v axis m w addr) := by
  have h0 := UnitPhaseRecordRead.runs order v rows axis addr a tail ht
  have h1 := UnitPhaseRecordKernel.runs order v rows axis m ws hm hslots hl addr
    (UnitPhaseRecordRead.sources a) w (source_width a w hr hi) hspan ha hrecord
    (UnitPhaseRecordRead.advanced a tail)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem signed_phase (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (addr : List Bool) (a : Context 2) (b n : ℕ)
    (hr : a.re.length=b+1) (hi : a.im.length=b+1)
    (hguard : ∀ j : Fin 2,|ButterflySigned.signedValue b (UnitPhaseRecordRead.sources a j.val)|<(2^b : ℕ)) :
    ButterflySigned.complexValue
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words (UnitPhaseRecordKernel.exponent v axis m ws addr) 0
        (UnitPhaseRecordRead.sources a)))
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words (UnitPhaseRecordKernel.exponent v axis m ws addr) 1
        (UnitPhaseRecordRead.sources a))) n=
      Networks.BinaryPhase.phase ((UnitPhaseRecordKernel.exponent v axis m ws addr).val : ZMod 4)*
        ButterflySigned.complexValue (ButterflySigned.signedValue b a.re) (ButterflySigned.signedValue b a.im) n := by
  simpa only [UnitPhaseRecordRead.sources,ite_true,show (1 : ℕ) ≠ 0 by decide,ite_false] using
    UnitPhaseSigned.words_phase (UnitPhaseRecordKernel.exponent v axis m ws addr)
      (UnitPhaseRecordRead.sources a) b n (source_width a (b+1) hr hi) hguard

end
end IntegerMultBounds.Machine.UnitPhaseRecord
