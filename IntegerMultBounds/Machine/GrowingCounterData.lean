import IntegerMultBounds.Machine.Counter

/-! Binary increment with a growing most-significant end. Carry into the end
creates a new true bit, so no width is supplied in advance. The exact scan
potential pays for both carry propagation and return to the left sentinel. -/

namespace IntegerMultBounds.GrowingCounterData

def increment : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::increment bs

def carrySteps : List Bool → ℕ
  | [] => 1
  | false::_ => 1
  | true::bs => carrySteps bs+1

def Canonical (bs : List Bool) : Prop := bs = [] ∨ bs.getLast? = some true

theorem increment_ne_nil (bs : List Bool) : increment bs ≠ [] := by
  cases bs with
  | nil => simp [increment]
  | cons b bs => cases b <;> simp [increment]

theorem increment_value (bs : List Bool) : Counter.value (increment bs) = Counter.value bs+1 := by
  induction bs with
  | nil => simp [increment,Counter.value]
  | cons b bs ih => cases b <;> simp [increment,Counter.value,ih] <;> omega

theorem increment_length (bs : List Bool) : bs.length ≤ (increment bs).length ∧
    (increment bs).length ≤ bs.length+1 := by
  induction bs with
  | nil => simp [increment]
  | cons b bs ih =>
    cases b <;> simp [increment]
    omega

private theorem last_cons (b : Bool) (bs : List Bool) (h : bs ≠ []) :
    (b::bs).getLast? = bs.getLast? := by cases bs <;> simp_all

/-- The newly represented integer has a highest one whenever its input is canonical. -/
theorem increment_last (bs : List Bool) (h : Canonical bs) : (increment bs).getLast? = some true := by
  induction bs with
  | nil => simp [increment]
  | cons b bs ih =>
    cases bs with
    | nil => cases b <;> simp [increment]
    | cons x xs =>
      have ht : Canonical (x::xs) := by
        rcases h with h | h
        · simp at h
        · exact Or.inr (by simpa only [List.getLast?_cons_cons] using h)
      cases b with
      | false => simpa only [increment,List.getLast?_cons_cons] using ht.resolve_left (by simp)
      | true => rw [increment,last_cons false _ (increment_ne_nil _)]; exact ih ht

theorem increment_canonical (bs : List Bool) (h : Canonical bs) : Canonical (increment bs) :=
  Or.inr (increment_last bs h)

private theorem high_bit_value (initialBits : List Bool) : 2^initialBits.length ≤ Counter.value (initialBits++[true]) := by
  induction initialBits with
  | nil => simp [Counter.value]
  | cons b bs ih => cases b <;> simp [Counter.value,pow_succ] <;> omega

/-- A canonical growing clock has logarithmic width, including the empty zero clock. -/
theorem canonical_width (bs : List Bool) (h : Canonical bs) : bs.length ≤ (Counter.value bs).log2+1 := by
  rcases h with rfl | hlast
  · simp
  obtain ⟨initialBits,rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hb := high_bit_value initialBits
  have hv : Counter.value (initialBits++[true]) ≠ 0 := by have := Nat.two_pow_pos initialBits.length; omega
  have hl := (Nat.le_log2 hv).mpr hb
  simpa using Nat.add_le_add_right hl 1

theorem carrySteps_bounds (bs : List Bool) : 1 ≤ carrySteps bs ∧ carrySteps bs ≤ bs.length+1 := by
  induction bs with
  | nil => simp [carrySteps]
  | cons b bs ih =>
    cases b <;> simp [carrySteps]
    omega

theorem carrySteps_le_output (bs : List Bool) : carrySteps bs ≤ (increment bs).length := by
  induction bs with
  | nil => simp [carrySteps,increment]
  | cons b bs ih =>
    cases b <;> simp [carrySteps,increment]
    omega

/-- Exact telescoping identity, including a newly allocated high bit. -/
theorem increment_potential (bs : List Bool) :
    carrySteps bs + Counter.weight (increment bs) = 2+Counter.weight bs := by
  induction bs with
  | nil => simp [carrySteps,increment,Counter.weight]
  | cons b bs ih => cases b <;> simp [carrySteps,increment,Counter.weight] <;> omega

def advance : ℕ → List Bool → List Bool
  | 0,bs => bs
  | n+1,bs => advance n (increment bs)

def totalCost : ℕ → List Bool → ℕ
  | 0,_ => 0
  | n+1,bs => 2*carrySteps bs+totalCost n (increment bs)

theorem advance_value (n : ℕ) (bs : List Bool) : Counter.value (advance n bs) = Counter.value bs+n := by
  induction n generalizing bs with
  | zero => simp [advance]
  | succ n ih => simp [advance,ih,increment_value]; omega

theorem advance_canonical (n : ℕ) (bs : List Bool) (h : Canonical bs) : Canonical (advance n bs) := by
  induction n generalizing bs with
  | zero => exact h
  | succ n ih => exact ih _ (increment_canonical bs h)

theorem total_potential (n : ℕ) (bs : List Bool) :
    totalCost n bs+2*Counter.weight (advance n bs) = 4*n+2*Counter.weight bs := by
  induction n generalizing bs with
  | zero => simp [totalCost,advance]
  | succ n ih =>
    have hs := increment_potential bs
    have ht := ih (increment bs)
    simp only [totalCost,advance]
    omega

theorem amortized_cost (n : ℕ) (bs : List Bool) : totalCost n bs ≤ 4*n+2*bs.length := by
  have hp := total_potential n bs
  have hw := Counter.weight_le_length bs
  omega

theorem empty_value (n : ℕ) : Counter.value (advance n []) = n := by simp [advance_value,Counter.value]

theorem empty_width (n : ℕ) : (advance n []).length ≤ n.log2+1 := by
  simpa only [empty_value] using canonical_width _ (advance_canonical n [] (Or.inl rfl))

end IntegerMultBounds.GrowingCounterData
