import IntegerMultBounds.Machine.DelimitedRadixRecord
import IntegerMultBounds.Machine.TwoTapeAt
import IntegerMultBounds.Machine.ButterflyNumerator

/-! Read four actual coefficient fields from two aligned record streams into
the physical butterfly controls. Both source streams and output streams are
framed, with source heads advanced by one complete complex coefficient. -/
namespace IntegerMultBounds.Machine.ButterflyRecordRead
noncomputable section
open DelimitedRadixRecord (Context)
open RadixDigits
open SharedPlacementAlphabet (setTape)

abbrev count := 52

def components (a b : Context 2) : ℕ → List (Fin 2)
  | 0 => a.re
  | 1 => a.im
  | 2 => b.re
  | _ => b.im

def streams (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) : Tapes 4 2 :=
  ⟨![a.start,b.start,pos 0,pos 1],![a.tape,b.tape,out 0,out 1]⟩

def afterStreams (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) : Tapes 4 2 :=
  ⟨![a.start+a.re.length+a.im.length+2,b.start+b.re.length+b.im.length+2,pos 0,pos 1],
    ![a.tape,b.tape,out 0,out 1]⟩

def input (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) : Tapes count 2 :=
  (streams a b out pos).append (RadixLinearCombinationBootstrap.empty 48)

def output (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) : Tapes count 2 :=
  (afterStreams a b out pos).append (ButterflyNumerator.input (components a b))

def p0 := TwoTapeAt.program (DelimitedRadixRead.program (q:=2)) (0:Fin count) 4 (by decide)
def p1 := TwoTapeAt.program (DelimitedRadixRead.program (q:=2)) (0:Fin count) 5 (by decide)
def p2 := TwoTapeAt.program (DelimitedRadixRead.program (q:=2)) (1:Fin count) 6 (by decide)
def p3 := TwoTapeAt.program (DelimitedRadixRead.program (q:=2)) (1:Fin count) 7 (by decide)
def program := seq (seq (seq p0 p1) p2) p3

def state1 (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) :=
  TwoTapeAt.result (input a b out pos) 0 4 a.tape (MarkedWordCleanup.marked (a.re.map digitSymbol))
    (a.start+a.re.length+1) 1
def state2 (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) :=
  TwoTapeAt.result (state1 a b out pos) 0 5 a.tape (MarkedWordCleanup.marked (a.im.map digitSymbol))
    (a.start+a.re.length+a.im.length+2) 1
def state3 (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) :=
  TwoTapeAt.result (state2 a b out pos) 1 6 b.tape (MarkedWordCleanup.marked (b.re.map digitSymbol))
    (b.start+b.re.length+1) 1
def state4 (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) :=
  TwoTapeAt.result (state3 a b out pos) 1 7 b.tape (MarkedWordCleanup.marked (b.im.map digitSymbol))
    (b.start+b.re.length+b.im.length+2) 1

theorem endpoint (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) :
    state4 a b out pos=output a b out pos := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using (Fin.addCases (m:=4) (n:=48)) with
  | left i => fin_cases i <;> simp [state3,state2,state1,TwoTapeAt.result,setTape,input,
      streams,afterStreams,Tapes.append] <;> rfl
  | right i =>
    induction i using (Fin.addCases (m:=4) (n:=44)) with
    | left i => fin_cases i <;> simp [state3,state2,state1,TwoTapeAt.result,setTape,input,
        ButterflyNumerator.input,RadixLinearCombinationRefresh.controls,MarkedRadixRefresh.source,
        streams,afterStreams,Tapes.append,components] <;> rfl
    | right i =>
      have h0 : (Fin.natAdd 4 (Fin.natAdd 4 i) : Fin count)≠0 := by intro h; have := congrArg Fin.val h; simp at this
      have h1 : (Fin.natAdd 4 (Fin.natAdd 4 i) : Fin count)≠1 := by intro h; have := congrArg Fin.val h; simp at this; omega
      have h4 : (Fin.natAdd 4 (Fin.natAdd 4 i) : Fin count)≠4 := by intro h; have := congrArg Fin.val h; simp at this
      have h5 : (Fin.natAdd 4 (Fin.natAdd 4 i) : Fin count)≠5 := by intro h; have := congrArg Fin.val h; simp at this; omega
      have h6 : (Fin.natAdd 4 (Fin.natAdd 4 i) : Fin count)≠6 := by intro h; have := congrArg Fin.val h; simp at this; omega
      have h7 : (Fin.natAdd 4 (Fin.natAdd 4 i) : Fin count)≠7 := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [state3,state2,state1,TwoTapeAt.result,setTape,input,
        ButterflyNumerator.input,Tapes.append,RadixLinearCombinationBootstrap.empty,h0,h1,h4,h5,h6,h7]

/-- All four field reads are actual fixed-control subroutines with paid joins. -/
theorem runs (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) :
    HoareTime program (fun v => v=input a b out pos) (fun v => v=output a b out pos)
      (2*(a.re.length+a.im.length+b.re.length+b.im.length)+27) := by
  have h0 := TwoTapeAt.runs DelimitedRadixRead.program (0:Fin count) 4 (by decide) (input a b out pos)
    _ _ _ _ _ _ _ _ (by simp [input,streams,Tapes.append]; constructor <;> rfl)
    (by simp [input,Tapes.append,RadixLinearCombinationBootstrap.empty]; constructor <;> rfl) (DelimitedRadixRecord.read_real a)
  have h1 := TwoTapeAt.runs DelimitedRadixRead.program (0:Fin count) 5 (by decide) (state1 a b out pos)
    _ _ _ _ _ _ _ _ (by simp [state1,TwoTapeAt.result,setTape])
    (by simp [state1,TwoTapeAt.result,setTape,input,Tapes.append,RadixLinearCombinationBootstrap.empty]; constructor <;> rfl)
    (DelimitedRadixRecord.read_imaginary a)
  have h2 := TwoTapeAt.runs DelimitedRadixRead.program (1:Fin count) 6 (by decide) (state2 a b out pos)
    _ _ _ _ _ _ _ _ (by simp [state2,state1,TwoTapeAt.result,setTape,input,streams,Tapes.append]; constructor <;> rfl)
    (by simp [state2,state1,TwoTapeAt.result,setTape,input,Tapes.append,RadixLinearCombinationBootstrap.empty]; constructor <;> rfl)
    (DelimitedRadixRecord.read_real b)
  have h3 := TwoTapeAt.runs DelimitedRadixRead.program (1:Fin count) 7 (by decide) (state3 a b out pos)
    _ _ _ _ _ _ _ _ (by simp [state3,TwoTapeAt.result,setTape])
    (by simp [state3,state2,state1,TwoTapeAt.result,setTape,input,Tapes.append,RadixLinearCombinationBootstrap.empty]; constructor <;> rfl)
    (DelimitedRadixRecord.read_imaginary b)
  have hh := ((h0.seq h1).seq h2).seq h3
  apply hh.consequence (fun _ h => h) ?_ (by omega)
  intro v hv
  exact hv.trans (endpoint a b out pos)

end
end IntegerMultBounds.Machine.ButterflyRecordRead
