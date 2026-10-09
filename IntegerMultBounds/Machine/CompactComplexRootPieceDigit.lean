import IntegerMultBounds.Machine.CompactComplexRootPieceClock
import IntegerMultBounds.Machine.CompactComplexControllerTapeAssoc

/-! One fixed original-queue digit body: read the physical field, invoke the
piece clock, erase its canonical zero, and generate the next exponent/width.
The full appended native/controller bank is separate from all forty-four controller tapes. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceDigit
noncomputable section
open ActiveRepairRankHeadersCommands (State bank put)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexRootPieceNumbers
variable {a q t : ℕ}

def input (st : State) (f : ℤ → Fin (a+4)) (p : ℤ) (native : Tapes t a) : Tapes (43+(1+t)) a :=
  (bank st).append ((FiniteReturnStack.bank f p).append native)


def body (callback : Program (43+(1+t)) q a) (base : ℕ) : Σ k, Program (43+(1+t)) k a :=
  ⟨_,seq (seq (seq (CompactComplexControllerTapeAssoc.program (extend CompactComplexRootPieceQueue.program t))
    (CompactComplexRootPieceClock.program (t := t) callback))
      (extend (CompactChildHeadersArithmetic.compile clearClock).2 (1+t)))
        (extend (CompactChildHeadersArithmetic.compile (level base)).2 (1+t))⟩

def finished (st : State) (e left width digit base : ℕ) :=
  put (put (put st 1 (e+1)) 2 (left+digit*width)) 3 (width*base)

def digitCost (st : State) (left width digit base : ℕ) (callCost : ℕ → ℕ) :=
  2*(bits digit).length+6+
    (∑ j ∈ Finset.range digit, (callCost j+
      CompactChildHeadersArithmetic.scheduleCost piece
        (CompactComplexRootPieceClock.clock st (left+j*width) (digit-j))+3))+
    104+CompactChildHeadersArithmetic.scheduleCost (level base) (put st 2 (left+digit*width))

private theorem clock_initial (st : State) (left digit : ℕ) (h2 : st 2=some left) :
    CompactComplexRootPieceClock.clock st left digit=put st 4 digit := by
  unfold CompactComplexRootPieceClock.clock put
  have h : Function.update st 2 (some left)=st := by
    funext i
    by_cases hi : i=2
    · subst i; simpa using h2.symm
    · simp [Function.update,hi]
  rw [h]

private theorem clock_cleared (st : State) (left : ℕ) (h4 : st 4=none) :
    Function.update (CompactComplexRootPieceClock.clock st left 0) 4 none=put st 2 left := by
  funext i
  by_cases h2 : i=2
  · subst i; simp [CompactComplexRootPieceClock.clock,put,Function.update]
  by_cases hi4 : i=4
  · subst i; simp [put,Function.update,h4]
  simp [CompactComplexRootPieceClock.clock,put,Function.update,h2,hi4]

/-- All generated fields are paid physical state transitions. The sole
remaining parameter is the actual native callback's exact execution rule. -/
theorem runs (callback : Program (43+(1+t)) q a) (base : ℕ) (hb : 0<base)
    (st : State) (e left width digit : ℕ)
    (h1 : st 1=some e) (h2 : st 2=some left) (h3 : st 3=some width) (h4 : st 4=none)
    (h22 : st 22=none) (h23 : st 23=none) (h24 : st 24=none)
    (f : ℤ → Fin (a+4)) (p : ℤ) (ds : List ℕ)
    (native : ℕ → Tapes t a) (callCost : ℕ → ℕ)
    (hc : ∀ j<digit, HoareTime callback
      (fun v => v=CompactComplexRootPieceClock.input st (left+j*width) (digit-j)
        (FiniteReturnStack.bank (putWord f p (CompactComplexRootDigits.fields (digit::ds)))
          (p+(bits digit).length+1)) (native j))
      (fun v => v=CompactComplexRootPieceClock.input st (left+j*width) (digit-j)
        (FiniteReturnStack.bank (putWord f p (CompactComplexRootDigits.fields (digit::ds)))
          (p+(bits digit).length+1)) (native (j+1))) (callCost j)) :
    HoareTime (body callback base).2
      (fun v => v=input st (putWord f p (CompactComplexRootDigits.fields (digit::ds))) p (native 0))
      (fun v => v=input (finished st e left width digit base)
        (putWord f p (CompactComplexRootDigits.fields (digit::ds)))
        (p+(bits digit).length+1) (native digit))
      (digitCost st left width digit base callCost) := by
  let queue := FiniteReturnStack.bank (a := a)
    (putWord f p (CompactComplexRootDigits.fields (digit::ds))) (p+(bits digit).length+1)
  have hr := CompactComplexControllerTapeAssoc.hoare
    (CompactComplexRootPieceQueue.fields_runs_framed st h4 f p digit ds (native 0))
  have hc' := CompactComplexRootPieceClock.runs callback st left width digit h3 h22 h23 queue native callCost hc
  simp only [CompactComplexRootPieceClock.input,clock_initial st left digit h2] at hc'
  have he := hoare_extend_eq (clearClock_runs (a := a)
    (CompactComplexRootPieceClock.clock st (left+digit*width) 0)
    (by simp [CompactComplexRootPieceClock.clock,put])) (queue.append (native digit))
  rw [clock_cleared st _ h4] at he
  have hl := hoare_extend_eq (level_runs (a := a) (put st 2 (left+digit*width)) e width base hb
    (by simp [put,h1]) (by simp [put,h3]) (by simp [put,h22])
    (by simp [put,h23]) (by simp [put,h24])) (queue.append (native digit))
  have hend : levelDone (put st 2 (left+digit*width)) e width base=finished st e left width digit base := by
    funext i
    by_cases h1 : i=1
    · subst i; simp [levelDone,finished,put,Function.update]
    by_cases h2 : i=2
    · subst i; simp [levelDone,finished,put,Function.update]
    by_cases h3 : i=3
    · subst i; simp [levelDone,finished,put,Function.update]
    simp [levelDone,finished,put,Function.update,h1,h2,h3]
  rw [hend] at hl
  exact (((hr.seq hc').seq he).seq hl).consequence (fun _ h => h) (fun _ h => h) (by
    unfold digitCost
    omega)

end
end IntegerMultBounds.Machine.CompactComplexRootPieceDigit
