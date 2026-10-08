import IntegerMultBounds.Machine.CountedLoopReuseAlphabet

/-! Destructive length-counted stack transfer. Source and destination heads start
on the final cells of their respective regions, move left together, and stop
just before those regions. Every alphabet symbol, including blank and separator,
is data; only the independent binary clock decides when to stop. Positioning and
constructing the immutable length descriptor are explicit caller obligations. -/
namespace IntegerMultBounds.Machine.StackPop
variable {a : ℕ}

def cell : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 0 then
    some (1,fun i => (if i = 0 then blank else symbols 0,.left)) else none

def bank (f g : ℤ → Fin (a+4)) (p q : ℤ) : Tapes 2 a :=
  ⟨fun i => if i = 0 then p else q, fun i => if i = 0 then f else g⟩

def advance (v : Tapes 2 a) : Tapes 2 a :=
  bank (Function.update (v.tape 0) (v.head 0) blank)
    (Function.update (v.tape 1) (v.head 1) (v.tape 0 (v.head 0)))
    (v.head 0-1) (v.head 1-1)

theorem cell_hoare (v : Tapes 2 a) :
    HoareTime cell (fun w => w = v) (fun w => w = advance v) 1 := by
  intro w hw
  subst w
  let c : Config 2 2 a := ⟨1,(advance v).head,(advance v).tape⟩
  refine ⟨1,c,le_rfl,?_,by simp [step,cell,c],rfl⟩
  rw [run_one]
  simp only [step,cell,Tapes.start,↓reduceIte]
  congr 1
  congr 1
  · funext i
    fin_cases i <;> simp [advance,bank,Move.offset,sub_eq_add_neg]
  · funext i j
    fin_cases i <;> simp [advance,bank,Function.update_apply,eq_comm]

/-- Semantic iteration of the actual destructive transfer cell. -/
def transfer (v : Tapes 2 a) : ℕ → Tapes 2 a
  | 0 => v
  | n+1 => advance (transfer v n)

def program : Program 4 (7+(2+5)+4) a := CountedLoopReuseAlphabet.program cell

/-- One fixed machine, reusable work clock, immutable descriptor, and exact
whole-bank output. No terminator condition is imposed on payload symbols. -/
theorem pop_hoare (v : Tapes 2 a) (bs : List Bool) (n : ℕ)
    (hcount : Counter.value bs = n) :
    HoareTime program
      (fun w => w = CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary bs) 1 1)
      (fun w => w = CountedLoopReuseAlphabet.bank (transfer v n) CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary bs) 1 1)
      (7*n+7*bs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare cell bs n (transfer v) (fun _ => 1)
    hcount (fun i _ => cell_hoare (transfer v i))
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  omega

theorem heads (v : Tapes 2 a) (n : ℕ) (i : Fin 2) :
    (transfer v n).head i = v.head i-n := by
  induction n generalizing i with
  | zero => simp [transfer]
  | succ n ih =>
    fin_cases i <;> simp [transfer,advance,bank,ih] <;> omega

/-- The popped stack interval is erased; no ancestor cell outside it changes. -/
theorem source (v : Tapes 2 a) (n : ℕ) (j : ℤ) :
    (transfer v n).tape 0 j =
      if v.head 0-(n : ℤ) < j ∧ j ≤ v.head 0 then blank else v.tape 0 j := by
  induction n with
  | zero => simp [transfer]
  | succ n ih =>
    simp only [transfer,advance,bank,ite_true,Function.update_apply,heads]
    rw [ih]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- Popping towards a destination's left end preserves the original order,
and every destination cell outside the written interval is retained. -/
theorem destination (v : Tapes 2 a) (n : ℕ) (j : ℤ) :
    (transfer v n).tape 1 j =
      if v.head 1-(n : ℤ) < j ∧ j ≤ v.head 1 then
        v.tape 0 (v.head 0+(j-v.head 1)) else v.tape 1 j := by
  induction n with
  | zero => simp [transfer]
  | succ n ih =>
    simp only [transfer,advance,bank,show (1 : Fin 2) ≠ 0 by decide,ite_false,
      Function.update_apply,heads]
    rw [source,ih]
    have hz : ¬ (v.head 0-(n : ℤ) < v.head 0-n ∧ v.head 0-n ≤ v.head 0) := by omega
    simp only [hz,ite_false]
    by_cases hj : j = v.head 1-n
    · subst j
      simp only [↓reduceIte]
      rw [ite_eq_left (by constructor <;> omega)]
      congr 1
      omega
    · rw [ite_eq_right hj]
      have he : (v.head 1-(n : ℤ) < j ∧ j ≤ v.head 1) ↔
          (v.head 1-((n+1 : ℕ) : ℤ) < j ∧ j ≤ v.head 1) := by omega
      simp only [he]

/-- Exact region form used when restoring a parked stream. The source head
ends at the previously saved stack top, one cell before the popped region. -/
theorem transfer_region (f g : ℤ → Fin (a+4)) (p q : ℤ) (n : ℕ) :
    transfer (bank f g (p+n-1) (q+n-1)) n =
      bank (fun j => if p ≤ j ∧ j < p+n then blank else f j)
        (fun j => if q ≤ j ∧ j < q+n then f (p+(j-q)) else g j) (p-1) (q-1) := by
  apply congrArg₂ Tapes.mk
  · funext i
    rw [heads]
    fin_cases i <;> simp [bank] <;> omega
  · funext i j
    fin_cases i
    · change (transfer (bank f g (p+n-1) (q+n-1)) n).tape 0 j =
        (if p ≤ j ∧ j < p+n then blank else f j)
      rw [source]
      simp only [bank,↓reduceIte]
      have he : p+(n : ℤ)-1-n < j ∧ j ≤ p+n-1 ↔ p ≤ j ∧ j < p+n := by omega
      simp only [he]
    · change (transfer (bank f g (p+n-1) (q+n-1)) n).tape 1 j =
        (if q ≤ j ∧ j < q+n then f (p+(j-q)) else g j)
      rw [destination]
      simp only [bank,show (1 : Fin 2) ≠ 0 by decide,↓reduceIte]
      have he : q+(n : ℤ)-1-n < j ∧ j ≤ q+n-1 ↔ q ≤ j ∧ j < q+n := by omega
      have hp : p+(n : ℤ)-1+(j-(q+n-1)) = p+(j-q) := by omega
      simp only [he,hp]

end IntegerMultBounds.Machine.StackPop
