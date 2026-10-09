import IntegerMultBounds.Machine.CounterTape
import IntegerMultBounds.Machine.GrowingCounterData

/-! The literal least-significant-bit-first words visited by a regular binary
address counter. Table rows increase in ordinary integer order. -/
namespace IntegerMultBounds.Machine.BinaryAddressTableData

def row (w i : ℕ) : List Bool := Counter.advance i (List.replicate w false)
def table (w n : ℕ) : List Bool := ((List.range n).map (row w)).flatten

theorem advance_succ (i : ℕ) (bs : List Bool) :
    Counter.advance (i+1) bs = Counter.increment (Counter.advance i bs) := by
  induction i generalizing bs with
  | zero => rfl
  | succ i ih => exact ih (Counter.increment bs)

@[simp] theorem advance_length (i : ℕ) (bs : List Bool) :
    (Counter.advance i bs).length = bs.length := by
  induction i generalizing bs with
  | zero => rfl
  | succ i ih => simpa only [Counter.advance,Counter.increment_length] using ih (Counter.increment bs)

@[simp] theorem row_length (w i : ℕ) : (row w i).length = w := by simp [row]

theorem row_succ (w i : ℕ) : row w (i+1) = Counter.increment (row w i) := advance_succ _ _

@[simp] theorem table_zero (w : ℕ) : table w 0 = [] := rfl

theorem table_succ (w n : ℕ) : table w (n+1) = table w n ++ row w n := by
  simp [table,List.range_succ]

@[simp] theorem table_length (w n : ℕ) : (table w n).length = n*w := by
  induction n with
  | zero => simp
  | succ n ih => rw [table_succ,List.length_append,ih,row_length]; ring

@[simp] theorem zeros_value (w : ℕ) : Counter.value (List.replicate w false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simpa only [List.replicate_succ,Counter.value,Bool.false_eq_true,ite_false,zero_add,mul_eq_zero] using Or.inr ih

theorem zero_word (xs : List Bool) (hx : Counter.value xs = 0) : xs = List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [Counter.value] at hx
    · simpa only [List.length_cons,List.replicate_succ] using congrArg (List.cons false) (ih (by omega))

theorem row_value (w i : ℕ) : Counter.value (row w i) = i % 2^w := by
  induction i with
  | zero => simp [row,Counter.advance]
  | succ i ih => rw [row_succ,Counter.increment_value,row_length,ih,Nat.mod_add_mod]

/-- Each physical row is the fixed-width binary representation of its rank. -/
theorem row_rank (w i : ℕ) (hi : i < 2^w) : Counter.value (row w i) = i := by
  rw [row_value,Nat.mod_eq_of_lt hi]

/-- A full traversal restores the precise initial zero word. -/
theorem row_wrap (w : ℕ) : row w (2^w) = List.replicate w false := by
  have hh := zero_word (row w (2^w)) (by rw [row_value,Nat.mod_self])
  simpa only [row_length] using hh

end IntegerMultBounds.Machine.BinaryAddressTableData
