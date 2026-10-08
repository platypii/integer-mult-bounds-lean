import IntegerMultBounds.Machine.StackPop

/-! A fixed finite symbol operation applied pointwise to two streams. The first
stream is preserved; the second receives the operation's value at every counted
cell. Binary clock setup, real scanning, and clock cleanup are charged. -/
namespace IntegerMultBounds.Machine.PointwiseBinary
variable {a : ℕ}

def cell (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then
    some (1,fun i => (if i = 0 then sy i else op (sy 0) (sy 1),.right)) else none

def advance (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) (v : Tapes 2 a) : Tapes 2 a :=
  StackPop.bank (v.tape 0)
    (Function.update (v.tape 1) (v.head 1) (op (v.tape 0 (v.head 0)) (v.tape 1 (v.head 1))))
    (v.head 0+1) (v.head 1+1)

theorem cell_hoare (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) (v : Tapes 2 a) :
    HoareTime (cell op) (fun w => w = v) (fun w => w = advance op v) 1 := by
  intro w hw
  subst w
  refine ⟨1,⟨1,(advance op v).head,(advance op v).tape⟩,le_rfl,?_,by simp [step,cell],rfl⟩
  rw [run_one]
  simp only [step,cell,Tapes.start,↓reduceIte]
  congr 1
  congr 1
  · funext i
    fin_cases i <;> simp [advance,StackPop.bank,Move.offset]
  · funext i j
    fin_cases i <;> simp [advance,StackPop.bank,Function.update_apply,eq_comm]
    intro h
    rw [h]

def result (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) (v : Tapes 2 a) : ℕ → Tapes 2 a
  | 0 => v
  | n+1 => advance op (result op v n)

def program (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) := CountedLoopReuseAlphabet.program (cell op)

theorem apply_hoare (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) (v : Tapes 2 a)
    (bs : List Bool) (n : ℕ) (hc : Counter.value bs = n) :
    HoareTime (program op)
      (fun w => w = CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary bs) 1 1)
      (fun w => w = CountedLoopReuseAlphabet.bank (result op v n) CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary bs) 1 1)
      (7*n+7*bs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (cell op) bs n (result op v)
    (fun _ => 1) hc (fun i _ => cell_hoare op (result op v i))
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  omega

theorem heads (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) (v : Tapes 2 a) (n : ℕ) (i : Fin 2) :
    (result op v n).head i = v.head i+n := by
  induction n generalizing i with
  | zero => simp [result]
  | succ n ih => fin_cases i <;> simp [result,advance,StackPop.bank,ih] <;> omega

theorem source (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) (v : Tapes 2 a) (n : ℕ) :
    (result op v n).tape 0 = v.tape 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [result,advance,StackPop.bank,ite_true] using ih

theorem destination (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) (v : Tapes 2 a) (n : ℕ) (j : ℤ) :
    (result op v n).tape 1 j = if v.head 1 ≤ j ∧ j < v.head 1+n then
      op (v.tape 0 (v.head 0+(j-v.head 1))) (v.tape 1 j) else v.tape 1 j := by
  induction n generalizing j with
  | zero => simp [result]
  | succ n ih =>
    simp only [result,advance,StackPop.bank,show (1 : Fin 2) ≠ 0 by decide,ite_false,
      Function.update_apply,heads,source]
    rw [ih,ih]
    have hz : ¬ (v.head 1 ≤ v.head 1+(n : ℤ) ∧ v.head 1+n < v.head 1+n) := by omega
    simp only [hz,ite_false]
    by_cases hj : j = v.head 1+n
    · subst j
      rw [ite_eq_left rfl,ite_eq_left (by constructor <;> omega)]
      congr 2
      omega
    · rw [ite_eq_right hj]
      have he : (v.head 1 ≤ j ∧ j < v.head 1+(n : ℤ)) ↔
          (v.head 1 ≤ j ∧ j < v.head 1+((n+1 : ℕ) : ℤ)) := by omega
      simp only [he]

/-- XOR is a finite transition-table operation on encoded bits. -/
def xorSymbol (x y : Fin (a+4)) : Fin (a+4) :=
  if x = bitSymbol true then if y = bitSymbol true then bitSymbol false else bitSymbol true else y

theorem xorSymbol_bits (x y : Bool) :
    xorSymbol (a := a) (bitSymbol x) (bitSymbol y) = bitSymbol (Bool.xor x y) := by
  cases x <;> cases y <;> simp [xorSymbol,bitSymbol]

end IntegerMultBounds.Machine.PointwiseBinary
