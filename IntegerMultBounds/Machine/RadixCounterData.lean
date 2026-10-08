import IntegerMultBounds.Machine.RadixDigits

/-! Fixed-width prime-radix counter semantics. The carry potential counts only
maximal digits, so unrelated wide spectator counters are not rescanned per
increment. The radix need not be prime for these counter facts. -/
namespace IntegerMultBounds.Machine.RadixCounterData

open RadixDigits
variable {q : ℕ}

def zeroDigit (hq : 2 ≤ q) : Fin q := ⟨0,by omega⟩

def increment (hq : 2 ≤ q) : List (Fin q) → List (Fin q)
  | [] => []
  | x::xs => if h : x.val+1 < q then ⟨x.val+1,h⟩::xs
    else zeroDigit hq::increment hq xs

def carrySteps : List (Fin q) → ℕ
  | [] => 1
  | x::xs => if x.val+1 < q then 1 else carrySteps xs+1

def maxWeight : List (Fin q) → ℕ
  | [] => 0
  | x::xs => (if x.val+1 = q then 1 else 0)+maxWeight xs

@[simp] theorem increment_length (hq : 2 ≤ q) (xs : List (Fin q)) :
    (increment hq xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [increment]; split_ifs <;> simp [ih]

theorem carrySteps_bounds (xs : List (Fin q)) : 1 ≤ carrySteps xs ∧ carrySteps xs ≤ xs.length+1 := by
  induction xs with
  | nil => simp [carrySteps]
  | cons x xs ih => simp only [carrySteps,List.length_cons]; split_ifs <;> omega

theorem increment_value (hq : 2 ≤ q) (xs : List (Fin q)) :
    value (increment hq xs) = (value xs+1)%q^xs.length := by
  induction xs with
  | nil => simp [increment,value]
  | cons x xs ih =>
    have hv := value_lt hq xs
    by_cases hx : x.val+1 < q
    · simp only [increment,hx,↓reduceDIte,value,List.length_cons,pow_succ]
      rw [Nat.mod_eq_of_lt (by have := x.isLt; nlinarith)]
      omega
    · have hm : x.val+1 = q := by have := x.isLt; omega
      simp only [increment,hx,↓reduceDIte,value,zeroDigit,zero_add,List.length_cons,pow_succ,ih]
      have he : x.val+q*value xs+1 = q*(value xs+1) := by nlinarith
      rw [he,Nat.mul_comm (q^xs.length) q,Nat.mul_mod_mul_left]

/-- Propagating a carry removes a maximal digit; its last step creates at most
one. The bound also charges the end blank on a complete overflow. -/
theorem increment_potential (hq : 2 ≤ q) (xs : List (Fin q)) :
    carrySteps xs+maxWeight (increment hq xs) ≤ 2+maxWeight xs := by
  induction xs with
  | nil => simp [carrySteps,increment,maxWeight]
  | cons x xs ih =>
    by_cases hx : x.val+1 < q
    · simp only [carrySteps,increment,maxWeight,hx,↓reduceIte,↓reduceDIte]
      split_ifs <;> omega
    · have hm : x.val+1 = q := by have := x.isLt; omega
      simp only [carrySteps,increment,hx,↓reduceIte,↓reduceDIte]
      simp only [maxWeight,zeroDigit,zero_add,show 1 ≠ q by omega,hm,ite_false,ite_true]
      omega

theorem maxWeight_le_length (xs : List (Fin q)) : maxWeight xs ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [maxWeight,List.length_cons]; split_ifs <;> omega

def advance (hq : 2 ≤ q) : ℕ → List (Fin q) → List (Fin q)
  | 0,xs => xs
  | n+1,xs => advance hq n (increment hq xs)

@[simp] theorem advance_length (hq : 2 ≤ q) (n : ℕ) (xs : List (Fin q)) :
    (advance hq n xs).length = xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [advance,ih]

theorem advance_value (hq : 2 ≤ q) (n : ℕ) (xs : List (Fin q)) :
    value (advance hq n xs) = (value xs+n)%q^xs.length := by
  induction n generalizing xs with
  | zero => simp only [advance,Nat.add_zero]; exact (Nat.mod_eq_of_lt (value_lt hq xs)).symm
  | succ n ih =>
    simp only [advance,ih,increment_length,increment_value,Nat.mod_add_mod]
    congr 1
    omega

/-- Full physical increment cost plus the two fixed cycling-control steps. -/
def cycleTime (hq : 2 ≤ q) : ℕ → List (Fin q) → ℕ
  | 0,_ => 0
  | n+1,xs => 2*carrySteps xs+2+cycleTime hq n (increment hq xs)

theorem cycle_potential (hq : 2 ≤ q) (n : ℕ) (xs : List (Fin q)) :
    cycleTime hq n xs+2*maxWeight (advance hq n xs) ≤ 6*n+2*maxWeight xs := by
  induction n generalizing xs with
  | zero => simp [cycleTime,advance]
  | succ n ih =>
    have hs := increment_potential hq xs
    have hr := ih (increment hq xs)
    simp only [cycleTime,advance]
    omega

theorem cycle_amortized (hq : 2 ≤ q) (n : ℕ) (xs : List (Fin q)) :
    cycleTime hq n xs ≤ 6*n+2*xs.length := by
  have hp := cycle_potential hq n xs
  have hw := maxWeight_le_length xs
  omega

def zeros (hq : 2 ≤ q) (b : ℕ) : List (Fin q) := List.replicate b (zeroDigit hq)

@[simp] theorem zeros_length (hq : 2 ≤ q) (b : ℕ) : (zeros hq b).length = b := List.length_replicate ..

@[simp] theorem zeros_value (hq : 2 ≤ q) (b : ℕ) : value (zeros hq b) = 0 := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change value (zeroDigit hq::zeros hq b) = 0
    simp [value,zeroDigit,ih]

/-- Every earlier-control value occurs in increasing radix order. -/
theorem enumerate_value (hq : 2 ≤ q) (b n : ℕ) (hn : n < q^b) :
    value (advance hq n (zeros hq b)) = n := by
  rw [advance_value,zeros_value,zeros_length,Nat.zero_add,Nat.mod_eq_of_lt hn]

private theorem value_zero (hq : 2 ≤ q) (xs : List (Fin q)) (h : value xs = 0) :
    xs = zeros hq xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.val = 0 := by simp only [value] at h; omega
    have ht : value xs = 0 := by simp only [value] at h; nlinarith
    have he : x = zeroDigit hq := Fin.ext hx
    change x::xs = zeroDigit hq::zeros hq xs.length
    exact congrArg₂ List.cons he (ih ht)

theorem full_cycle (hq : 2 ≤ q) (b : ℕ) : advance hq (q^b) (zeros hq b) = zeros hq b := by
  have hv : value (advance hq (q^b) (zeros hq b)) = 0 := by simp [advance_value]
  have h := value_zero hq _ hv
  simpa only [advance_length,zeros_length] using h

theorem enumerate_injective (hq : 2 ≤ q) (b : ℕ) :
    Function.Injective (fun i : Fin (q^b) => advance hq i.val (zeros hq b)) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg value hij
  simpa only [enumerate_value hq b i.val i.isLt,enumerate_value hq b j.val j.isLt] using h

/-- A full field traversal absorbs the counter's one-time width term. -/
theorem full_cycle_cost (hq : 2 ≤ q) (b : ℕ) :
    cycleTime hq (q^b) (zeros hq b) ≤ 8*q^b := by
  have hw : b ≤ q^b := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [pow_succ]
      have := Nat.one_le_pow b q (by omega)
      nlinarith
  have h := cycle_amortized hq (q^b) (zeros hq b)
  rw [zeros_length] at h
  omega

end IntegerMultBounds.Machine.RadixCounterData
