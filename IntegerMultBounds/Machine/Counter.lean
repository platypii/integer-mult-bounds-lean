import Mathlib.Tactic

/-! A finite-width ripple counter and its amortized flip bound.
`Machine/CounterTape.lean` implements this increment on literal tapes and
accounts for head returns and the transitions between repeated calls. -/

namespace IntegerMultBounds.Counter

/-- Least-significant bit first; overflow wraps at the fixed width. -/
def increment : List Bool → List Bool
  | [] => []
  | false :: bs => true :: bs
  | true :: bs => false :: increment bs

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * value bs

def weight : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + weight bs

def flips : List Bool → ℕ
  | [] => 0
  | false :: _ => 1
  | true :: bs => 1 + flips bs

theorem increment_length (bs : List Bool) : (increment bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [increment, ih]

theorem value_lt (bs : List Bool) : value bs < 2 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih => cases b <;> simp [value, pow_succ] <;> omega

theorem increment_value (bs : List Bool) :
    value (increment bs) = (value bs + 1) % 2 ^ bs.length := by
  induction bs with
  | nil => simp [increment, value]
  | cons b bs ih =>
    cases b with
    | false =>
      have hv := value_lt bs
      simp only [increment, value, Bool.false_eq_true, ↓reduceIte, zero_add,
        List.length_cons, pow_succ]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    | true =>
      simp only [increment, value, Bool.false_eq_true, ↓reduceIte, zero_add,
        List.length_cons, pow_succ, ih]
      have heq : 1 + 2 * value bs + 1 = 2 * (value bs + 1) := by omega
      rw [heq, Nat.mul_comm (2 ^ bs.length) 2, Nat.mul_mod_mul_left]

theorem increment_potential (bs : List Bool) :
    flips bs + weight (increment bs) ≤ weight bs + 2 := by
  induction bs with
  | nil => decide
  | cons b bs ih => cases b <;> simp [increment, flips, weight] <;> omega

theorem weight_le_length (bs : List Bool) : weight bs ≤ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih => cases b <;> simp [weight] <;> omega

def advance : ℕ → List Bool → List Bool
  | 0, bs => bs
  | n + 1, bs => advance n (increment bs)

def totalFlips : ℕ → List Bool → ℕ
  | 0, _ => 0
  | n + 1, bs => flips bs + totalFlips n (increment bs)

theorem total_potential (n : ℕ) (bs : List Bool) :
    totalFlips n bs + weight (advance n bs) ≤ 2 * n + weight bs := by
  induction n generalizing bs with
  | zero => simp [totalFlips, advance]
  | succ n ih =>
    have h₁ := increment_potential bs
    have h₂ := ih (increment bs)
    simp only [totalFlips, advance]
    omega

/-- Any run of `n` increments, from any initial counter value, flips at most
`2*n + width` bits. No zero-initialization assumption is needed. -/
theorem amortized_flips (n : ℕ) (bs : List Bool) :
    totalFlips n bs ≤ 2 * n + bs.length := by
  have h₁ := total_potential n bs
  have h₂ := weight_le_length bs
  omega

end IntegerMultBounds.Counter
