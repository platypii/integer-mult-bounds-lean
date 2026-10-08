import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
A literal fixed-finite-alphabet, fixed-multitape machine model. One transition
can read/write just the scanned cell of each tape and move each head by at most
one. In particular, arithmetic on an unbounded register is not a primitive.

`EndToEnd` is the target proposition, NOT a proved theorem. No complexity
contract or oracle is built into the machine definition.
-/

namespace IntegerMultBounds
namespace Machine

inductive Move where
  | left | stay | right
  deriving DecidableEq

def Move.offset : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

theorem Move.unit (m : Move) : -1 ≤ m.offset ∧ m.offset ≤ 1 := by
  cases m <;> decide

/-- The finite transition table has no access to head indices or entire tapes. -/
structure Program (tapes states extraSymbols : ℕ) where
  tapes_pos : 0 < tapes
  start : Fin states
  transition : Fin states → (Fin tapes → Fin (extraSymbols + 4)) →
    Option (Fin states × (Fin tapes → Fin (extraSymbols + 4) × Move))

structure Config (tapes states extraSymbols : ℕ) where
  state : Fin states
  head : Fin tapes → ℤ
  tape : Fin tapes → ℤ → Fin (extraSymbols + 4)

variable {t q a : ℕ}

def step (M : Program t q a) (c : Config t q a) : Option (Config t q a) :=
  match M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => none
  | some (state, action) => some {
      state := state
      head := fun i => c.head i + (action i).2.offset
      tape := fun i j => if j = c.head i then (action i).1 else c.tape i j }

/-- Exactly `k` actual transitions; a halted configuration has no successor. -/
def run (M : Program t q a) : ℕ → Config t q a → Option (Config t q a)
  | 0, c => some c
  | k + 1, c => (step M c).bind (run M k)

def blank : Fin (a + 4) := ⟨0, by omega⟩
def bitSymbol (b : Bool) : Fin (a + 4) := ⟨if b then 2 else 1, by split <;> omega⟩
def separator : Fin (a + 4) := ⟨3, by omega⟩

def wordTape (word : List (Fin (a + 4))) (j : ℤ) : Fin (a + 4) :=
  if 0 ≤ j then (word[j.toNat]?).getD blank else blank

def input (M : Program t q a) (x y : List Bool) : Config t q a where
  state := M.start
  head := fun _ => 0
  tape := fun i => if i.val = 0 then
    wordTape (x.map bitSymbol ++ [separator] ++ y.map bitSymbol)
    else fun _ => blank

/-- Most-significant bit first, including any leading zeroes. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) * 2 ^ bs.length + binaryValue bs

theorem binaryValue_lt (bs : List Bool) : binaryValue bs < 2 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp only [binaryValue, List.length_cons, pow_succ,
      Bool.false_eq_true, ↓reduceIte, zero_mul, one_mul, zero_add] <;> omega

theorem product_fits {x y : List Bool} {n : ℕ}
    (hx : x.length = n) (hy : y.length = n) :
    binaryValue x * binaryValue y < 2 ^ (2 * n) := by
  have hx' := binaryValue_lt x
  have hy' := binaryValue_lt y
  rw [hx] at hx'
  rw [hy] at hy'
  calc
    _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_lt_of_lt hx' hy'
    _ = _ := by rw [← pow_add, two_mul]

def outputCorrect (M : Program t q a) (n : ℕ) (x y : List Bool)
    (c : Config t q a) : Prop :=
  ∃ out : List Bool, out.length = 2 * n ∧
    binaryValue out = binaryValue x * binaryValue y ∧
    c.tape ⟨0, M.tapes_pos⟩ = wordTape (out.map bitSymbol)

def lg (n : ℕ) : ℕ := max (Nat.clog 2 n) 1

noncomputable def targetTime (κ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (lg n : ℝ) ^ (1 - κ)

/-- Correct on *every* positive input length, with a uniform eventual time bound. -/
def ComputesWithin (M : Program t q a) (κ : ℝ) : Prop :=
  ∃ (C : ℝ) (n₀ : ℕ), 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (x y : List Bool), x.length = n → y.length = n →
      ∃ (k : ℕ) (c : Config t q a),
        run M k (input M x y) = some c ∧ step M c = none ∧
        outputCorrect M n x y c ∧
        (n₀ ≤ n → (k : ℝ) ≤ C * targetTime κ n)

/-- The requested theorem statement. Existence of such a program is still open here. -/
def EndToEnd : Prop :=
  ∃ (t q a : ℕ) (M : Program t q a), ComputesWithin M (83 / 10 ^ 12)

end Machine
end IntegerMultBounds
