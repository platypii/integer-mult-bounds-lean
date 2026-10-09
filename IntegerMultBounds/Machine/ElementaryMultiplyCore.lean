import IntegerMultBounds.Machine.MultiplicationInputSplit
import IntegerMultBounds.Machine.BinaryMultiply
import IntegerMultBounds.Machine.Placement

/-! A fixed elementary multiplication core from the original packed input.
It splits/reverses both operands, positions their heads, and runs literal
Horner multiplication while preserving the original input. The accumulator
has exact product value; installing the final MSB output is separate. -/
namespace IntegerMultBounds.Machine.ElementaryMultiplyCore
noncomputable section
variable {a : ℕ}

def bank (f x y acc : ℤ → Fin (a+4)) (p px py pa : ℤ) : Tapes 4 a :=
  ⟨![p,px,py,pa],![f,x,y,acc]⟩
def input (x y : List Bool) :=
  (MultiplicationInputSplit.input (a := a) x y).append (MultiplicationInputSplit.single (fun _ => blank) 0)
def output (x y : List Bool) := bank (MultiplicationInputSplit.source (a := a) x y)
  (putWord (fun _ => blank) 0 (x.reverse.map bitSymbol))
  (putWord (fun _ => blank) 0 (y.reverse.map bitSymbol))
  (putWord (fun _ => blank) (-(y.length : ℤ))
    ((BinaryMultiply.horner x.reverse y.reverse).map bitSymbol)) x.length 0 (-1) (-(y.length : ℤ))

def rewindPlacement : Fin (1+3) ≃ Fin 4 := Equiv.swap 0 1
def shiftPlacement : Fin (1+3) ≃ Fin 4 where
  toFun := ![2,0,1,3]
  invFun := ![1,2,0,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def multiplyPlacement : Fin (3+1) ≃ Fin 4 where
  toFun := ![1,2,3,0]
  invFun := ![3,0,1,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def rewindPart := reindex (extend (ReturnOrigin.program (a := a)) 3) rewindPlacement
def shiftPart := reindex (extend (MultiplicationInputSplit.shift (a := a) .left) 3) shiftPlacement
def multiplyPart := reindex (extend (BinaryMultiply.program a) 1) multiplyPlacement
/-- Neither the program nor its number of states depends on the input widths. -/
def program (a : ℕ) := seq (seq (seq (extend (MultiplicationInputSplit.program a) 1)
  (rewindPart (a := a))) (shiftPart (a := a))) (multiplyPart (a := a))

def cost (x y : List Bool) := 4*x.length+2*y.length+
  y.length*(5*x.length+2*y.length+18)+18

theorem split_bank (f x y acc : ℤ → Fin (a+4)) (p px py pa : ℤ) :
    (MultiplicationInputSplit.bank f x y p px py).append (MultiplicationInputSplit.single acc pa) =
      bank f x y acc p px py pa := by
  unfold MultiplicationInputSplit.bank MultiplicationInputSplit.single bank Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem rewind_bank (f x y acc : ℤ → Fin (a+4)) (p px py pa : ℤ) :
    ((⟨fun _ => px,fun _ => x⟩ : Tapes 1 a).append (MultiplicationInputSplit.bank f y acc p py pa)).reindex
      rewindPlacement = bank f x y acc p px py pa := by
  unfold MultiplicationInputSplit.bank bank Tapes.append Tapes.reindex rewindPlacement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem shift_bank (f x y acc : ℤ → Fin (a+4)) (p px py pa : ℤ) :
    ((⟨fun _ => py,fun _ => y⟩ : Tapes 1 a).append (MultiplicationInputSplit.bank f x acc p px pa)).reindex
      shiftPlacement = bank f x y acc p px py pa := by
  unfold MultiplicationInputSplit.bank bank Tapes.append Tapes.reindex shiftPlacement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem multiply_bank (f x y acc : ℤ → Fin (a+4)) (p px py pa : ℤ) :
    ((BinaryMultiply.bank x y acc px py pa).append (MultiplicationInputSplit.single f p)).reindex
      multiplyPlacement = bank f x y acc p px py pa := by
  unfold BinaryMultiply.bank MultiplicationInputSplit.single bank Tapes.append Tapes.reindex multiplyPlacement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem runs (x y : List Bool) :
    HoareTime (program a) (fun v => v = input (a := a) x y)
      (fun v => v = output (a := a) x y) (cost x y) := by
  let F := MultiplicationInputSplit.source (a := a) x y
  let X := putWord (fun _ => blank) 0 (x.reverse.map (bitSymbol (a := a)))
  let Y := putWord (fun _ => blank) 0 (y.reverse.map (bitSymbol (a := a)))
  have h1 := hoare_extend_eq (MultiplicationInputSplit.splits (a := a) x y)
    (MultiplicationInputSplit.single (fun _ => blank) 0)
  simp only [MultiplicationInputSplit.output] at h1
  rw [split_bank] at h1
  have h2 := hoare_place (ReturnOrigin.return_hoare_at (a := a) (fun _ => blank) 0
    (x.reverse.map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) rewindPlacement
    (MultiplicationInputSplit.bank F Y (fun _ => blank) x.length y.length 0)
  simp only [ReturnOrigin.cfg,Config.tapes] at h2
  rw [rewind_bank,rewind_bank] at h2
  simp only [List.length_map,List.length_reverse,zero_add] at h2
  have h3 := hoare_place (MultiplicationInputSplit.shifts (a := a) .left Y y.length) shiftPlacement
    (MultiplicationInputSplit.bank F X (fun _ => blank) x.length 0 0)
  rw [shift_bank,shift_bank] at h3
  simp only [Move.offset,Int.add_neg_one] at h3
  have h4 := hoare_place (BinaryMultiply.multiply_hoare x.reverse y.reverse (fun _ => blank)
    (fun _ => blank) 0 0 0 rfl rfl rfl) multiplyPlacement (MultiplicationInputSplit.single F x.length)
  rw [multiply_bank,multiply_bank] at h4
  simp only [List.length_reverse,zero_add,zero_sub] at h4
  have hbound := BinaryMultiply.cost_le x.reverse y.reverse
  simp only [List.length_reverse] at hbound
  have h4' := h4.consequence (fun _ h => h) (fun _ h => h) hbound
  apply ((h1.seq h2).seq h3).seq h4' |>.consequence (fun _ h => h) (fun _ h => h) _
  unfold cost
  omega

/-- Reverse bit order changes the representation convention, not the integer. -/
theorem value_reverse (x : List Bool) : Counter.value x.reverse = binaryValue x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    rw [List.reverse_cons,BinaryMultiply.value_append,ih]
    cases b <;> simp [Counter.value,binaryValue,List.length_reverse,Nat.add_comm]

theorem accumulator_value (x y : List Bool) :
    Counter.value (BinaryMultiply.horner x.reverse y.reverse) = binaryValue x*binaryValue y := by
  rw [BinaryMultiply.horner_value,value_reverse,value_reverse]

theorem equal_length_cost {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    cost x y ≤ 24*(n^2+n+1) := by
  unfold cost
  rw [hx,hy]
  nlinarith


/-- All four tapes start exactly as in the original multiplication statement. -/
theorem input_start (x y : List Bool) :
    (input (a := a) x y).start (program a) = Machine.input (program a) x y := by
  apply congrArg₂ (Config.mk (program a).start)
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [input,MultiplicationInputSplit.input,MultiplicationInputSplit.bank,
      MultiplicationInputSplit.single,Tapes.append,MultiplicationInputSplit.source_wordTape]
    all_goals rfl

/-- Actual halting execution from the original input, with an exact literal
accumulator word and its independently proved product value. -/
theorem runs_original_input (x y : List Bool) :
    ∃ k ≤ cost x y, ∃ c,
      run (program a) k (Machine.input (program a) x y) = some c ∧
      step (program a) c = none ∧ c.tapes = output (a := a) x y ∧
      Counter.value (BinaryMultiply.horner x.reverse y.reverse) = binaryValue x*binaryValue y := by
  obtain ⟨k,c,hk,hr,hh,hout⟩ := runs (a := a) x y _ rfl
  exact ⟨k,hk,c,by simpa only [input_start] using hr,hh,hout,accumulator_value x y⟩

/-- Uniform polynomial cost for every equal input length, including zero. -/
theorem runs_equal_length {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    HoareTime (program a) (fun v => v = input (a := a) x y)
      (fun v => v = output (a := a) x y) (24*(n^2+n+1)) :=
  (runs (a := a) x y).consequence (fun _ h => h) (fun _ h => h) (equal_length_cost hx hy)

end
end IntegerMultBounds.Machine.ElementaryMultiplyCore
