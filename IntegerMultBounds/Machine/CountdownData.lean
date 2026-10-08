import IntegerMultBounds.Machine.Counter

/-! Fixed-width LSB-first binary countdown and its exact digit trace. Successful
calls include the borrow scan, head return, and one payload operation. A single
terminal underflow includes its full scan and return, with no payload operation. -/

namespace IntegerMultBounds.CountdownData

def decrement : List Bool → List Bool
  | [] => []
  | true :: bs => false :: bs
  | false :: bs => true :: decrement bs

def underflow : List Bool → Bool
  | [] => true
  | true :: _ => false
  | false :: bs => underflow bs

/-- Inspected digits, including the end blank precisely on underflow. -/
def borrowSteps : List Bool → ℕ
  | [] => 1
  | true :: _ => 1
  | false :: bs => borrowSteps bs + 1

abbrev scanSteps := borrowSteps

/-- Each propagated zero becomes one; the first one becomes zero. -/
def flips : List Bool → ℕ
  | [] => 0
  | true :: _ => 1
  | false :: bs => flips bs + 1

def zeroWeight : List Bool → ℕ
  | [] => 0
  | true :: bs => zeroWeight bs
  | false :: bs => zeroWeight bs + 1

@[simp] theorem decrement_length (bs : List Bool) : (decrement bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [decrement,ih]

theorem underflow_eq_true_iff (bs : List Bool) : underflow bs = true ↔ Counter.value bs = 0 := by
  induction bs with
  | nil => simp [underflow,Counter.value]
  | cons b bs ih => cases b <;> simp [underflow,Counter.value,ih]

theorem underflow_eq_false_iff (bs : List Bool) : underflow bs = false ↔ 0 < Counter.value bs := by
  constructor
  · intro hf
    have hn : Counter.value bs ≠ 0 := by
      intro hz
      have ht := (underflow_eq_true_iff bs).mpr hz
      simp [hf] at ht
    omega
  · intro hp
    cases hu : underflow bs with
    | false => rfl
    | true =>
      have hz := (underflow_eq_true_iff bs).mp hu
      omega

theorem decrement_value (bs : List Bool) (h : 0 < Counter.value bs) :
    Counter.value (decrement bs) + 1 = Counter.value bs := by
  induction bs with
  | nil => simp [Counter.value] at h
  | cons b bs ih =>
    cases b with
    | true => simp [decrement,Counter.value]; omega
    | false =>
      have hp : 0 < Counter.value bs := by simpa [Counter.value] using h
      have hi := ih hp
      simp only [decrement,Counter.value,Bool.false_eq_true,ite_false,ite_true,zero_add]
      omega

theorem decrement_zero (bs : List Bool) (h : Counter.value bs = 0) :
    decrement bs = List.replicate bs.length true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true => simp [Counter.value] at h
    | false =>
      have ht : Counter.value bs = 0 := by simpa [Counter.value] using h
      simp [decrement,ih ht,List.replicate_succ]

theorem zeroWeight_le_length (bs : List Bool) : zeroWeight bs ≤ bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [zeroWeight] <;> omega

theorem zeroWeight_of_zero (bs : List Bool) (h : Counter.value bs = 0) :
    zeroWeight bs = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true => simp [Counter.value] at h
    | false =>
      have ht : Counter.value bs = 0 := by simpa [Counter.value] using h
      simp [zeroWeight,ih ht]

theorem borrowSteps_bounds (bs : List Bool) :
    1 ≤ borrowSteps bs ∧ borrowSteps bs ≤ bs.length+1 ∧ borrowSteps bs ≤ flips bs+1 := by
  induction bs with
  | nil => simp [borrowSteps,flips]
  | cons b bs ih =>
    cases b <;> simp [borrowSteps,flips]
    omega

theorem borrowSteps_of_zero (bs : List Bool) (h : Counter.value bs = 0) :
    borrowSteps bs = bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true => simp [Counter.value] at h
    | false =>
      have ht : Counter.value bs = 0 := by simpa [Counter.value] using h
      simp [borrowSteps,ih ht]

theorem borrowSteps_of_pos (bs : List Bool) (h : 0 < Counter.value bs) :
    borrowSteps bs = flips bs := by
  induction bs with
  | nil => simp [Counter.value] at h
  | cons b bs ih =>
    cases b with
    | true => rfl
    | false =>
      have ht : 0 < Counter.value bs := by simpa [Counter.value] using h
      simp [borrowSteps,flips,ih ht]

/-- The actual visited-digit count telescopes against zero bits. -/
theorem decrement_potential (bs : List Bool) (h : 0 < Counter.value bs) :
    borrowSteps bs + zeroWeight (decrement bs) = 2+zeroWeight bs := by
  induction bs with
  | nil => simp [Counter.value] at h
  | cons b bs ih =>
    cases b with
    | true => simp [borrowSteps,decrement,zeroWeight]; omega
    | false =>
      have ht : 0 < Counter.value bs := by simpa [Counter.value] using h
      have hi := ih ht
      simp only [borrowSteps,decrement,zeroWeight]
      omega

/-- Includes return-to-marker movement and the one payload operation. -/
theorem successful_cost_potential (bs : List Bool) (h : 0 < Counter.value bs) :
    2*borrowSteps bs+1+2*zeroWeight (decrement bs) = 5+2*zeroWeight bs := by
  have hh := decrement_potential bs h
  omega

def advance : ℕ → List Bool → List Bool
  | 0, bs => bs
  | n+1, bs => advance n (decrement bs)

def totalCost : ℕ → List Bool → ℕ
  | 0, _ => 0
  | n+1, bs => 2*borrowSteps bs+1+totalCost n (decrement bs)

@[simp] theorem advance_length (n : ℕ) (bs : List Bool) : (advance n bs).length = bs.length := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => simp only [advance,ih,decrement_length]

theorem advance_value (n : ℕ) (bs : List Bool) (h : n ≤ Counter.value bs) :
    Counter.value (advance n bs)+n = Counter.value bs := by
  induction n generalizing bs with
  | zero => simp [advance]
  | succ n ih =>
    have hd := decrement_value bs (by omega)
    have hi := ih (decrement bs) (by omega)
    simp only [advance]
    omega

/-- No successful iteration underflows; its actual transition charges telescope. -/
theorem total_potential (n : ℕ) (bs : List Bool) (h : n ≤ Counter.value bs) :
    totalCost n bs + 2*zeroWeight (advance n bs) = 5*n+2*zeroWeight bs := by
  induction n generalizing bs with
  | zero => simp [totalCost,advance]
  | succ n ih =>
    have hd := decrement_value bs (by omega)
    have hc := successful_cost_potential bs (by omega)
    have hi := ih (decrement bs) (by omega)
    simp only [totalCost,advance]
    omega

theorem amortized_cost (n : ℕ) (bs : List Bool) (h : n ≤ Counter.value bs) :
    totalCost n bs ≤ 5*n+2*bs.length := by
  have hp := total_potential n bs h
  have hz := zeroWeight_le_length bs
  omega

theorem countdown_zero (bs : List Bool) : Counter.value (advance (Counter.value bs) bs) = 0 := by
  have h := advance_value (Counter.value bs) bs le_rfl
  omega

/-- All successful decrements, followed by one complete underflow scan and return. -/
def countdownCost (bs : List Bool) : ℕ :=
  totalCost (Counter.value bs) bs + 2*borrowSteps (advance (Counter.value bs) bs)

/-- Final zero potential absorbs the initial potential, leaving a linear bound
with only one final width charge for the actual zero-detecting underflow. -/
theorem countdown_cost (bs : List Bool) : countdownCost bs ≤ 5*Counter.value bs+2*bs.length+2 := by
  have hp := total_potential (Counter.value bs) bs le_rfl
  have hz := zeroWeight_of_zero _ (countdown_zero bs)
  have hs := borrowSteps_of_zero _ (countdown_zero bs)
  have hw := zeroWeight_le_length bs
  rw [advance_length] at hz hs
  dsimp only [countdownCost]
  omega

end IntegerMultBounds.CountdownData
