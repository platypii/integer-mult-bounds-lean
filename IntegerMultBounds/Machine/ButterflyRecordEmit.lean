import IntegerMultBounds.Machine.ButterflyRecordOutputData

/-! Emit all four physical butterfly outputs to their two coefficient streams.
Each result word is consumed and its private tape restored literally blank. -/
namespace IntegerMultBounds.Machine.ButterflyRecordEmit
noncomputable section
open DelimitedRadixRecord (field complex)
open ButterflyRecordOutputData (work block)
open RadixLinearCombinationBootstrap (empty)
open SharedPlacementAlphabet (setTape)

abbrev count := 52

def nextStreams (v : Tapes 4 2) (zs : Fin 4 → List (Fin 2)) : Tapes 4 2 :=
  setTape (setTape v 2 (putWord (v.tape 2) (v.head 2) (complex (zs 0) (zs 1)))
    (v.head 2+(zs 0).length+(zs 1).length+2))
    3 (putWord (v.tape 3) (v.head 3) (complex (zs 2) (zs 3)))
    (v.head 3+(zs 2).length+(zs 3).length+2)

def input := ButterflyRecordOutputData.output
def output (v : Tapes 4 2) (zs : Fin 4 → List (Fin 2)) : Tapes count 2 :=
  (nextStreams v zs).append (empty 48)

def p0 := TwoTapeAt.program (DelimitedRadixEmit.program (q:=2)) (8:Fin count) 2 (by decide)
def p1 := TwoTapeAt.program (DelimitedRadixEmit.program (q:=2)) (19:Fin count) 2 (by decide)
def p2 := TwoTapeAt.program (DelimitedRadixEmit.program (q:=2)) (30:Fin count) 3 (by decide)
def p3 := TwoTapeAt.program (DelimitedRadixEmit.program (q:=2)) (41:Fin count) 3 (by decide)
def program := seq (seq (seq p0 p1) p2) p3

def state1 (v : Tapes 4 2) (zs : Fin 4 → List (Fin 2)) :=
  TwoTapeAt.result (input v zs) 8 2 (fun _ => blank) (putWord (v.tape 2) (v.head 2) (field (zs 0)))
    0 (v.head 2+(zs 0).length+1)
def state2 (v : Tapes 4 2) (zs : Fin 4 → List (Fin 2)) :=
  TwoTapeAt.result (state1 v zs) 19 2 (fun _ => blank)
    (putWord (putWord (v.tape 2) (v.head 2) (field (zs 0))) (v.head 2+(zs 0).length+1) (field (zs 1)))
    0 (v.head 2+(zs 0).length+1+(zs 1).length+1)
def state3 (v : Tapes 4 2) (zs : Fin 4 → List (Fin 2)) :=
  TwoTapeAt.result (state2 v zs) 30 3 (fun _ => blank) (putWord (v.tape 3) (v.head 3) (field (zs 2)))
    0 (v.head 3+(zs 2).length+1)
def state4 (v : Tapes 4 2) (zs : Fin 4 → List (Fin 2)) :=
  TwoTapeAt.result (state3 v zs) 41 3 (fun _ => blank)
    (putWord (putWord (v.tape 3) (v.head 3) (field (zs 2))) (v.head 3+(zs 2).length+1) (field (zs 3)))
    0 (v.head 3+(zs 2).length+1+(zs 3).length+1)

theorem append_fields (f : ℤ → Fin 6) (p : ℤ) (a b : List (Fin 2)) :
    putWord (putWord f p (field a)) (p+a.length+1) (field b)=putWord f p (complex a b) := by
  have he : p+a.length+1=p+(field a).length := by rw [DelimitedRadixRecord.field_length]; push_cast; omega
  rw [he,putWord_append_forward]
  rfl

theorem endpoint (v : Tapes 4 2) (zs : Fin 4 → List (Fin 2)) : state4 v zs=output v zs := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using (Fin.addCases (m:=4) (n:=48)) with
  | left i =>
    fin_cases i <;> simp [state3,state2,state1,TwoTapeAt.result,setTape,input,
      ButterflyRecordOutputData.output,nextStreams,Tapes.append,append_fields,Fin.addCases]
    all_goals omega
  | right i =>
    fin_cases i <;> simp [state3,state2,state1,TwoTapeAt.result,setTape,input,
      ButterflyRecordOutputData.output,nextStreams,Tapes.append,work,block,empty,
      MarkedWordCleanup.one] <;> rfl

/-- All emitted components appear in coefficient order with their original widths. -/
theorem runs (v : Tapes 4 2) (zs : Fin 4 → List (Fin 2)) :
    HoareTime program (fun z => z=input v zs) (fun z => z=output v zs)
      (2*((zs 0).length+(zs 1).length+(zs 2).length+(zs 3).length)+27) := by
  have h0 := TwoTapeAt.runs DelimitedRadixEmit.program (8:Fin count) 2 (by decide) (input v zs)
    _ _ _ _ _ _ _ _
    (by constructor <;> rfl) (by constructor <;> rfl)
    (DelimitedRadixRecord.emit_field (v.tape 2) (v.head 2) (zs 0))
  have h1 := TwoTapeAt.runs DelimitedRadixEmit.program (19:Fin count) 2 (by decide) (state1 v zs)
    _ _ _ _ _ _ _ _
    (by simp [state1,TwoTapeAt.result,setTape]; constructor <;> rfl)
    (by simp [state1,TwoTapeAt.result,setTape])
    (DelimitedRadixRecord.emit_field (putWord (v.tape 2) (v.head 2) (field (zs 0))) (v.head 2+(zs 0).length+1) (zs 1))
  have h2 := TwoTapeAt.runs DelimitedRadixEmit.program (30:Fin count) 3 (by decide) (state2 v zs)
    _ _ _ _ _ _ _ _
    (by simp [state2,state1,TwoTapeAt.result,setTape]; constructor <;> rfl)
    (by simp [state2,state1,TwoTapeAt.result,setTape]; constructor <;> rfl)
    (DelimitedRadixRecord.emit_field (v.tape 3) (v.head 3) (zs 2))
  have h3 := TwoTapeAt.runs DelimitedRadixEmit.program (41:Fin count) 3 (by decide) (state3 v zs)
    _ _ _ _ _ _ _ _
    (by simp [state3,state2,state1,TwoTapeAt.result,setTape]; constructor <;> rfl)
    (by simp [state3,TwoTapeAt.result,setTape])
    (DelimitedRadixRecord.emit_field (putWord (v.tape 3) (v.head 3) (field (zs 2))) (v.head 3+(zs 2).length+1) (zs 3))
  have hh := ((h0.seq h1).seq h2).seq h3
  apply hh.consequence (fun _ h => h) ?_ (by omega)
  intro z hz
  exact hz.trans (endpoint v zs)

end
end IntegerMultBounds.Machine.ButterflyRecordEmit
