import IntegerMultBounds.Machine.UnitPhaseRecordKernel

/-! Read one physical coefficient and prepare its two phase flags before the
header-derived phase caller. Stream advancement is exactly the serialized
word size; every spectator tape is retained. -/
namespace IntegerMultBounds.Machine.UnitPhaseRecordRead
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open SharedPlacementAlphabet (setTape)
open DelimitedRadixRecord (Context)
variable {s : Shape}

def sources (a : Context 2) : ℕ → List (Fin 2) := fun j => if j=0 then a.re else a.im

def initial (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (addr : List Bool) (a : Context 2) (tail : Tapes 4 2) :=
  let z := UnitPhaseRecordKernel.initial order v rows axis addr (sources a) tail
  setTape (setTape (setTape (setTape z 50 (fun _ => blank) 0) 51 (fun _ => blank) 0)
    48 (fun _ => blank) 0) 49 (fun _ => blank) 0

def advanced (a : Context 2) (tail : Tapes 4 2) :=
  setTape tail 0 a.tape (a.start+a.re.length+a.im.length+2)

def prepare := TwoTapeAt.program UnitPhaseFlagsLifecycle.prepare (48 : Fin 60) 49 (by decide)
def program := seq UnitPhaseRecordIO.readProgram prepare

def ready (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (addr : List Bool) (a : Context 2) (tail : Tapes 4 2) :=
  UnitPhaseRecordKernel.initial order v rows axis addr (sources a) (advanced a tail)

private theorem prepares (z : Tapes 60 2)
    (hl : z.tape 48=(fun _ => blank) ∧ z.head 48=0)
    (hh : z.tape 49=(fun _ => blank) ∧ z.head 49=0) :
    HoareTime prepare (fun w => w=z)
      (fun w => w=TwoTapeAt.result z 48 49
        (putWord (fun _ => blank) 0 [bitSymbol false])
        (putWord (fun _ => blank) 0 [bitSymbol false]) 0 0) 1 := by
  have hs : SharedBank.empty 2 2=Copy.tapes (fun _ => blank) (fun _ => blank) 0 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hp : UnitPhaseNumerator.flags 0=Copy.tapes
      (putWord (fun _ => blank) 0 [bitSymbol false])
      (putWord (fun _ => blank) 0 [bitSymbol false]) 0 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := UnitPhaseFlagsLifecycle.prepares
  rw [hs,hp] at h
  exact TwoTapeAt.runs UnitPhaseFlagsLifecycle.prepare (48 : Fin 60) 49 (by decide)
    z _ _ _ _ _ _ _ _ hl hh h

private theorem ready_eq (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (addr : List Bool) (a : Context 2) (tail : Tapes 4 2) :
    TwoTapeAt.result (UnitPhaseRecordIO.readOutput (initial order v rows axis addr a tail) a)
      48 49 (putWord (fun _ => blank) 0 [bitSymbol false])
        (putWord (fun _ => blank) 0 [bitSymbol false]) 0 0=ready order v rows axis addr a tail := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (addr : List Bool) (a : Context 2) (tail : Tapes 4 2)
    (ht : tail.tape 0=a.tape ∧ tail.head 0=a.start) :
    HoareTime program (fun z => z=initial order v rows axis addr a tail)
      (fun z => z=ready order v rows axis addr a tail) (2*(a.re.length+a.im.length)+15) := by
  have h0 := UnitPhaseRecordIO.read_runs (initial order v rows axis addr a tail) a
    (by simpa [initial,setTape,UnitPhaseRecordKernel.initial,Tapes.append,Fin.addCases] using ht)
    (by simp [initial,setTape]) (by simp [initial,setTape])
  have h1 := prepares (UnitPhaseRecordIO.readOutput (initial order v rows axis addr a tail) a)
    (by simp [UnitPhaseRecordIO.readOutput,UnitPhaseRecordIO.readFirst,TwoTapeAt.result,initial,setTape])
    (by simp [UnitPhaseRecordIO.readOutput,UnitPhaseRecordIO.readFirst,TwoTapeAt.result,initial,setTape])
  exact (h0.seq h1).consequence (fun _ h => h)
    (fun _ h => h.trans (ready_eq order v rows axis addr a tail)) (by omega)

end
end IntegerMultBounds.Machine.UnitPhaseRecordRead
