import IntegerMultBounds.Machine.RawLinearCombination
import IntegerMultBounds.Machine.ExactFrame
import IntegerMultBounds.Machine.TwoTapeAt
import IntegerMultBounds.Machine.DelimitedRadixRecord

/-! A fixed expression computes a field, emits its literal radix digits and
separator, and returns all arithmetic workspace to blank storage. The marked
source fields remain available for other output wires of the same scalar row. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationFieldEmit
noncomputable section
open RadixLinearCombinationRefresh (Expr Size controls)
open SharedPlacementAlphabet (setTape)
open RadixDigits
variable {c q : ℕ} [Fact q.Prime]

abbrev count (e : Expr c) := (c+Size e)+1

def resultSlot (e : Expr c) : Fin (count e) := Fin.castAdd 1 (Fin.natAdd c (Fin.castAdd (RadixLinearCombination.AuxTapes e.erase) 0))
def destSlot (e : Expr c) : Fin (count e) := Fin.natAdd (c+Size e) 0

theorem distinct (e : Expr c) : resultSlot e≠destSlot e := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [resultSlot,destSlot] at hv
  unfold Size RadixLinearCombination.TapeCount at hv
  omega

def input (e : Expr c) (xs : ℕ → List (Fin q)) (f : ℤ → Fin (q+4)) (p : ℤ) :=
  (RawLinearCombination.input e xs).append (MarkedWordCleanup.one f p)

def output (e : Expr c) (xs : ℕ → List (Fin q)) (f : ℤ → Fin (q+4)) (p : ℤ) :=
  input e xs (putWord f p (DelimitedRadixRecord.field (RadixLinearCombination.result e.erase xs)))
    (p+(RadixLinearCombination.result e.erase xs).length+1)

def emitProgram (e : Expr c) :=
  TwoTapeAt.program (DelimitedRadixEmit.program (q:=q)) (resultSlot e) (destSlot e) (distinct e)

def program (e : Expr c) := seq (extend (RawLinearCombination.program (q:=q) e) 1) (emitProgram e)

private theorem emitted (e : Expr c) (xs : ℕ → List (Fin q)) (f : ℤ → Fin (q+4)) (p : ℤ) :
    TwoTapeAt.result ((RawLinearCombination.output e xs).append (MarkedWordCleanup.one f p))
      (resultSlot e) (destSlot e) (fun _ => blank)
      (putWord f p (DelimitedRadixRecord.field (RadixLinearCombination.result e.erase xs)))
      0 (p+(RadixLinearCombination.result e.erase xs).length+1)=output e xs f p := by
  apply Placement.Tapes.ext'
  · intro i
    induction i using Fin.addCases (m:=c+Size e) (n:=1) with
    | right i => fin_cases i; simp [TwoTapeAt.result,setTape,destSlot,resultSlot,output,input,MarkedWordCleanup.one,Tapes.append]
    | left i =>
      induction i using Fin.addCases (m:=c) (n:=Size e) with
      | left i =>
        have hi := i.isLt
        simp (disch := omega) [TwoTapeAt.result,setTape,Function.update_apply,Fin.ext_iff,Size,RadixLinearCombination.TapeCount,resultSlot,destSlot,output,input,RawLinearCombination.input,
          RawLinearCombination.output,Tapes.append]
        split_ifs <;> omega
      | right i =>
        induction i using Fin.addCases (m:=1) (n:=RadixLinearCombination.AuxTapes e.erase) with
        | left i => fin_cases i; simp (disch := omega) [TwoTapeAt.result,setTape,Function.update_apply,Fin.ext_iff,Size,RadixLinearCombination.TapeCount,resultSlot,destSlot,output,input,RawLinearCombination.input,
            RadixLinearCombinationBootstrap.empty,Tapes.append]
        | right i =>
          simp (disch := omega) [TwoTapeAt.result,setTape,Function.update_apply,Fin.ext_iff,Size,RadixLinearCombination.TapeCount,resultSlot,destSlot,output,input,RawLinearCombination.input,
            RawLinearCombination.output,RawLinearCombinationCleanup.clean,RadixLinearCombinationBootstrap.empty,Tapes.append]
          omega
  · intro i
    induction i using Fin.addCases (m:=c+Size e) (n:=1) with
    | right i => fin_cases i; simp [TwoTapeAt.result,setTape,destSlot,resultSlot,output,input,MarkedWordCleanup.one,Tapes.append]
    | left i =>
      induction i using Fin.addCases (m:=c) (n:=Size e) with
      | left i =>
        have hi := i.isLt
        simp (disch := omega) [TwoTapeAt.result,setTape,Function.update_apply,Fin.ext_iff,Size,RadixLinearCombination.TapeCount,resultSlot,destSlot,output,input,RawLinearCombination.input,
          RawLinearCombination.output,Tapes.append]
        split_ifs <;> first | omega | rfl
      | right i =>
        induction i using Fin.addCases (m:=1) (n:=RadixLinearCombination.AuxTapes e.erase) with
        | left i => fin_cases i; simp (disch := omega) [TwoTapeAt.result,setTape,Function.update_apply,Fin.ext_iff,Size,RadixLinearCombination.TapeCount,resultSlot,destSlot,output,input,RawLinearCombination.input,
            RadixLinearCombinationBootstrap.empty,Tapes.append]
        | right i =>
          simp (disch := omega) [TwoTapeAt.result,setTape,Function.update_apply,Fin.ext_iff,Size,RadixLinearCombination.TapeCount,resultSlot,destSlot,output,input,RawLinearCombination.input,
            RawLinearCombination.output,RawLinearCombinationCleanup.clean,RadixLinearCombinationBootstrap.empty,Tapes.append]
          omega

theorem runs (e : Expr c) (xs : ℕ → List (Fin q)) (b : ℕ)
    (hw : ∀ i,(xs i).length=b) (f : ℤ → Fin (q+4)) (p : ℤ) :
    HoareTime (program e) (fun v => v=input e xs f p) (fun v => v=output e xs f p)
      (RawLinearCombination.cost e b+2*b+7) := by
  have h0 := hoare_extend_eq (RawLinearCombination.runs e xs b hw) (MarkedWordCleanup.one f p)
  have h1 := TwoTapeAt.runs DelimitedRadixEmit.program (resultSlot e) (destSlot e) (distinct e)
    ((RawLinearCombination.output e xs).append (MarkedWordCleanup.one f p))
    _ _ _ _ _ _ _ _
    (by simp [resultSlot,RawLinearCombination.output,RawLinearCombinationCleanup.clean,Tapes.append,MarkedWordCleanup.one])
    (by simp [destSlot,Tapes.append,MarkedWordCleanup.one])
    (DelimitedRadixRecord.emit_field f p (RadixLinearCombination.result e.erase xs))
  have hl := RawLinearCombination.result_length e xs b hw
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h.trans (emitted e xs f p)) (by omega)

end
end IntegerMultBounds.Machine.RawLinearCombinationFieldEmit
