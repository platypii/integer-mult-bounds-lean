import IntegerMultBounds.Machine.RadixDigits
import IntegerMultBounds.Machine.GrowingCounterData

/-! Radix-q countdown data and amortized conversion cost. Long zero suffixes
are charged against zero-digit potential, never against the full width on each
iteration. The binary output is grown once per successful radix decrement. -/
namespace IntegerMultBounds.Machine.RadixToBinaryData

open RadixDigits
variable {q : ℕ}

def lastDigit (hq : 2 ≤ q) : Fin q := ⟨q-1,by omega⟩

def decrement (hq : 2 ≤ q) : List (Fin q) → List (Fin q)
  | [] => []
  | x::xs => if h : x.val = 0 then lastDigit hq::decrement hq xs
    else ⟨x.val-1,by have := x.isLt; omega⟩::xs

def underflow : List (Fin q) → Bool
  | [] => true
  | x::xs => if x.val = 0 then underflow xs else false

def borrowSteps : List (Fin q) → ℕ
  | [] => 1
  | x::xs => if x.val = 0 then borrowSteps xs+1 else 1

def zeroWeight : List (Fin q) → ℕ
  | [] => 0
  | x::xs => (if x.val = 0 then 1 else 0)+zeroWeight xs

@[simp] theorem decrement_length (hq : 2 ≤ q) (xs : List (Fin q)) :
    (decrement hq xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [decrement]; split_ifs <;> simp [ih]

theorem underflow_eq_true_iff (hq : 2 ≤ q) (xs : List (Fin q)) :
    underflow xs = true ↔ value xs = 0 := by
  induction xs with
  | nil => simp [underflow,value]
  | cons x xs ih =>
    by_cases hx : x.val = 0
    · simp [underflow,value,hx,ih,show q ≠ 0 by omega]
    · simp [underflow,value,hx]

theorem underflow_eq_false_iff (hq : 2 ≤ q) (xs : List (Fin q)) :
    underflow xs = false ↔ 0 < value xs := by
  constructor
  · intro hf
    have hn : value xs ≠ 0 := by
      intro hz
      have ht := (underflow_eq_true_iff hq xs).mpr hz
      simp [hf] at ht
    omega
  · intro hp
    cases hu : underflow xs with
    | false => rfl
    | true =>
      have hz := (underflow_eq_true_iff hq xs).mp hu
      omega

theorem decrement_value (hq : 2 ≤ q) (xs : List (Fin q)) (h : 0 < value xs) :
    value (decrement hq xs)+1 = value xs := by
  induction xs with
  | nil => simp [value] at h
  | cons x xs ih =>
    by_cases hx : x.val = 0
    · have hp : 0 < value xs := by simp only [value,hx,zero_add] at h; nlinarith
      have hi := ih hp
      simp only [decrement,hx,↓reduceDIte,value,lastDigit]
      have hqsub : q-1+1 = q := by omega
      nlinarith
    · simp only [decrement,hx,↓reduceDIte,value]
      omega

theorem decrement_zero (hq : 2 ≤ q) (xs : List (Fin q)) (h : value xs = 0) :
    decrement hq xs = List.replicate xs.length (lastDigit hq) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.val = 0 := by simp only [value] at h; omega
    have ht : value xs = 0 := by simp only [value] at h; nlinarith
    simp [decrement,hx,ih ht,List.replicate_succ]

theorem zeroWeight_le_length (xs : List (Fin q)) : zeroWeight xs ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [zeroWeight,List.length_cons]; split_ifs <;> omega

theorem zeroWeight_of_zero (hq : 2 ≤ q) (xs : List (Fin q)) (h : value xs = 0) :
    zeroWeight xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.val = 0 := by simp only [value] at h; omega
    have ht : value xs = 0 := by simp only [value] at h; nlinarith
    simp [zeroWeight,hx,ih ht,Nat.add_comm]

theorem borrowSteps_bounds (xs : List (Fin q)) : 1 ≤ borrowSteps xs ∧ borrowSteps xs ≤ xs.length+1 := by
  induction xs with
  | nil => simp [borrowSteps]
  | cons x xs ih => simp only [borrowSteps,List.length_cons]; split_ifs <;> omega

theorem borrowSteps_of_zero (hq : 2 ≤ q) (xs : List (Fin q)) (h : value xs = 0) :
    borrowSteps xs = xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.val = 0 := by simp only [value] at h; omega
    have ht : value xs = 0 := by simp only [value] at h; nlinarith
    simp [borrowSteps,hx,ih ht]

/-- Each propagated zero removes one potential unit; a terminating nonzero
digit creates at most one. The constant is independent of the radix. -/
theorem decrement_potential (hq : 2 ≤ q) (xs : List (Fin q)) (h : 0 < value xs) :
    borrowSteps xs+zeroWeight (decrement hq xs) ≤ 2+zeroWeight xs := by
  induction xs with
  | nil => simp [value] at h
  | cons x xs ih =>
    by_cases hx : x.val = 0
    · have hp : 0 < value xs := by simp only [value,hx,zero_add] at h; nlinarith
      have hi := ih hp
      simp only [borrowSteps,decrement,zeroWeight,hx,↓reduceIte,↓reduceDIte,lastDigit,
        show q-1 ≠ 0 by omega]
      omega
    · simp only [borrowSteps,decrement,zeroWeight,hx,↓reduceIte,↓reduceDIte]
      split_ifs <;> omega

def advance (hq : 2 ≤ q) : ℕ → List (Fin q) → List (Fin q)
  | 0,xs => xs
  | n+1,xs => advance hq n (decrement hq xs)

/-- Successful borrow and return, plus the two body-entry/return transitions. -/
def totalCost (hq : 2 ≤ q) : ℕ → List (Fin q) → ℕ
  | 0,_ => 0
  | n+1,xs => 2*borrowSteps xs+2+totalCost hq n (decrement hq xs)

@[simp] theorem advance_length (hq : 2 ≤ q) (n : ℕ) (xs : List (Fin q)) :
    (advance hq n xs).length = xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [advance,ih]

theorem advance_value (hq : 2 ≤ q) (n : ℕ) (xs : List (Fin q)) (h : n ≤ value xs) :
    value (advance hq n xs)+n = value xs := by
  induction n generalizing xs with
  | zero => simp [advance]
  | succ n ih =>
    have hd := decrement_value hq xs (by omega)
    have hi := ih (decrement hq xs) (by omega)
    simp only [advance]
    omega

theorem total_potential (hq : 2 ≤ q) (n : ℕ) (xs : List (Fin q)) (h : n ≤ value xs) :
    totalCost hq n xs+2*zeroWeight (advance hq n xs) ≤ 6*n+2*zeroWeight xs := by
  induction n generalizing xs with
  | zero => simp [totalCost,advance]
  | succ n ih =>
    have hd := decrement_value hq xs (by omega)
    have hc := decrement_potential hq xs (by omega)
    have hi := ih (decrement hq xs) (by omega)
    simp only [totalCost,advance]
    omega

theorem countdown_zero (hq : 2 ≤ q) (xs : List (Fin q)) :
    value (advance hq (value xs) xs) = 0 := by
  have := advance_value hq (value xs) xs le_rfl
  omega

/-- Add the unique terminal underflow and all binary increment carry scans. -/
def conversionCost (hq : 2 ≤ q) (xs : List (Fin q)) : ℕ :=
  totalCost hq (value xs) xs+2*borrowSteps (advance hq (value xs) xs)+
    GrowingCounterData.totalCost (value xs) []

theorem conversion_cost (hq : 2 ≤ q) (xs : List (Fin q)) :
    conversionCost hq xs ≤ 10*value xs+2*xs.length+2 := by
  have hp := total_potential hq (value xs) xs le_rfl
  have hz := zeroWeight_of_zero hq _ (countdown_zero hq xs)
  have hs := borrowSteps_of_zero hq _ (countdown_zero hq xs)
  have hw := zeroWeight_le_length xs
  have hb := GrowingCounterData.amortized_cost (value xs) []
  rw [advance_length] at hz hs
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at hb
  dsimp only [conversionCost]
  omega

theorem width_le_power (hq : 2 ≤ q) (b : ℕ) : b ≤ q^b := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ]; have := Nat.one_le_pow b q (by omega); nlinarith

theorem conversion_cost_power (hq : 2 ≤ q) (xs : List (Fin q)) :
    conversionCost hq xs ≤ 12*q^xs.length+2 := by
  have h := conversion_cost hq xs
  have hv := value_lt hq xs
  have hw := width_le_power hq xs.length
  omega

/-- The final grown binary word represents the source radix value exactly. -/
def output (xs : List (Fin q)) : List Bool := GrowingCounterData.advance (value xs) []

theorem output_value (xs : List (Fin q)) : Counter.value (output xs) = value xs :=
  GrowingCounterData.empty_value _

theorem output_canonical (xs : List (Fin q)) : GrowingCounterData.Canonical (output xs) :=
  GrowingCounterData.advance_canonical _ [] (Or.inl rfl)

end IntegerMultBounds.Machine.RadixToBinaryData
