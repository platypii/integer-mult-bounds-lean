import IntegerMultBounds.Machine.ButterflyRecordEmit

/-! Two-field physical record IO on the shared phase caller. Stream56 is read
into marked radix controls50/51; result52/54 is consumed into stream58. All other
sixty-bank tapes, including address/counter/flags, are retained literally. -/
namespace IntegerMultBounds.Machine.UnitPhaseRecordIO
noncomputable section
open RadixDigits
open SharedPlacementAlphabet (setTape)
open DelimitedRadixRecord (Context field complex)

abbrev count := 60

def readReal := TwoTapeAt.program (DelimitedRadixRead.program (q:=2)) (56:Fin count) 50 (by decide)
def readImag := TwoTapeAt.program (DelimitedRadixRead.program (q:=2)) (56:Fin count) 51 (by decide)
def readProgram := seq readReal readImag

def readFirst (v : Tapes count 2) (a : Context 2) :=
  TwoTapeAt.result v 56 50 a.tape (MarkedWordCleanup.marked (a.re.map digitSymbol))
    (a.start+a.re.length+1) 1

def readOutput (v : Tapes count 2) (a : Context 2) :=
  TwoTapeAt.result (readFirst v a) 56 51 a.tape (MarkedWordCleanup.marked (a.im.map digitSymbol))
    (a.start+a.re.length+a.im.length+2) 1

theorem read_runs (v : Tapes count 2) (a : Context 2)
    (hs : v.tape 56=a.tape ∧ v.head 56=a.start)
    (hr : v.tape 50=(fun _ => blank) ∧ v.head 50=0)
    (hi : v.tape 51=(fun _ => blank) ∧ v.head 51=0) :
    HoareTime readProgram (fun z => z=v) (fun z => z=readOutput v a)
      (2*(a.re.length+a.im.length)+13) := by
  have h0 := TwoTapeAt.runs DelimitedRadixRead.program (56:Fin count) 50 (by decide) v
    _ _ _ _ _ _ _ _ hs hr (DelimitedRadixRecord.read_real a)
  have h1 := TwoTapeAt.runs DelimitedRadixRead.program (56:Fin count) 51 (by decide) (readFirst v a)
    _ _ _ _ _ _ _ _ (by simp [readFirst,TwoTapeAt.result,setTape])
    (by simpa [readFirst,TwoTapeAt.result,setTape] using hi)
    (DelimitedRadixRecord.read_imaginary a)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

def emitReal := TwoTapeAt.program (DelimitedRadixEmit.program (q:=2)) (52:Fin count) 58 (by decide)
def emitImag := TwoTapeAt.program (DelimitedRadixEmit.program (q:=2)) (54:Fin count) 58 (by decide)
def emitProgram := seq emitReal emitImag

def emitFirst (v : Tapes count 2) (re : List (Fin 2)) :=
  TwoTapeAt.result v 52 58 (fun _ => blank) (putWord (v.tape 58) (v.head 58) (field re))
    0 (v.head 58+re.length+1)

def emitOutput (v : Tapes count 2) (re im : List (Fin 2)) :=
  setTape (setTape (setTape v 52 (fun _ => blank) 0) 54 (fun _ => blank) 0) 58
    (putWord (v.tape 58) (v.head 58) (complex re im)) (v.head 58+re.length+im.length+2)

private theorem emit_endpoint (v : Tapes count 2) (re im : List (Fin 2)) :
    TwoTapeAt.result (emitFirst v re) 54 58 (fun _ => blank)
      (putWord (putWord (v.tape 58) (v.head 58) (field re)) (v.head 58+re.length+1) (field im))
      0 (v.head 58+re.length+1+im.length+1)=emitOutput v re im := by
  rw [ButterflyRecordEmit.append_fields]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases h52 : i=52
  all_goals by_cases h54 : i=54
  all_goals by_cases h58 : i=58
  all_goals simp [TwoTapeAt.result,emitFirst,setTape,h52,h54,h58] <;> omega

theorem emit_runs (v : Tapes count 2) (re im : List (Fin 2))
    (hr : v.tape 52=MarkedWordCleanup.word (re.map digitSymbol) ∧ v.head 52=0)
    (hi : v.tape 54=MarkedWordCleanup.word (im.map digitSymbol) ∧ v.head 54=0) :
    HoareTime emitProgram (fun z => z=v) (fun z => z=emitOutput v re im)
      (2*(re.length+im.length)+13) := by
  have h0 := TwoTapeAt.runs DelimitedRadixEmit.program (52:Fin count) 58 (by decide) v
    _ _ _ _ _ _ _ _ hr ⟨rfl,rfl⟩ (DelimitedRadixRecord.emit_field (v.tape 58) (v.head 58) re)
  have h1 := TwoTapeAt.runs DelimitedRadixEmit.program (54:Fin count) 58 (by decide) (emitFirst v re)
    _ _ _ _ _ _ _ _ (by simpa [emitFirst,TwoTapeAt.result,setTape] using hi)
    (by simp [emitFirst,TwoTapeAt.result,setTape])
    (DelimitedRadixRecord.emit_field (putWord (v.tape 58) (v.head 58) (field re)) (v.head 58+re.length+1) im)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h.trans (emit_endpoint v re im)) (by omega)

end
end IntegerMultBounds.Machine.UnitPhaseRecordIO
