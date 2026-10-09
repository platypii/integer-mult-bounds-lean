import IntegerMultBounds.Machine.SharedControlPair

/-! Four literal integer numerators of the complex butterfly. This program uses
four common radix-two inputs and disjoint private banks, performs all source
copies and cleanup, and retains four output words. Signed interpretation and
Gaussian dyadic scaling are proved separately. -/
namespace IntegerMultBounds.Machine.ButterflyNumerator
noncomputable section
open RadixLinearCombinationRefresh (Expr controls)

instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Input order is real(u), imaginary(u), real(v), imaginary(v). -/
def negative : Fin 4 → Fin 4 → Bool :=
  ![![false,true,false,false], ![false,false,true,false],
    ![false,false,false,true], ![true,false,false,false]]

def expression (i : Fin 4) : Expr 4 :=
  .add (.add (.term 0 (if negative i 0 then -1 else 1))
             (.term 1 (if negative i 1 then -1 else 1)))
       (.add (.term 2 (if negative i 2 then -1 else 1))
             (.term 3 (if negative i 3 then -1 else 1)))

def numerator {R : Type*} [Ring R] (x : Fin 4 → R) : Fin 4 → R :=
  ![x 0-x 1+x 2+x 3, x 0+x 1-x 2+x 3,
    x 0+x 1+x 2-x 3, -x 0+x 1+x 2+x 3]

def words (i : Fin 4) (xs : ℕ → List (Fin 2)) :=
  RadixLinearCombination.result (expression i).erase xs

def privateOutput (i : Fin 4) (xs : ℕ → List (Fin 2)) : Tapes 11 2 :=
  RawLinearCombinationCleanup.clean (expression i) (words i xs)

def input (xs : ℕ → List (Fin 2)) : Tapes 48 2 :=
  (controls xs).append (RadixLinearCombinationBootstrap.empty 44)

def output (xs : ℕ → List (Fin 2)) : Tapes 48 2 :=
  (controls xs).append
    (((privateOutput 0 xs).append (privateOutput 1 xs)).append
     ((privateOutput 2 xs).append (privateOutput 3 xs)))

def program := SharedControlPair.program
  (SharedControlPair.program (RawLinearCombination.program (q:=2) (expression 0))
    (RawLinearCombination.program (q:=2) (expression 1)))
  (SharedControlPair.program (RawLinearCombination.program (q:=2) (expression 2))
    (RawLinearCombination.program (q:=2) (expression 3)))

theorem expression_cost (i : Fin 4) (b : ℕ) :
    RawLinearCombination.cost (expression i) b=42*b+147 := by
  simp [RawLinearCombination.cost,expression,RadixLinearCombinationBootstrap.initCost,
    RawLinearCombination.refreshCost,RadixLinearCombinationRefresh.Expr.erase,
    RadixLinearCombination.runtime,RawLinearCombinationCleanup.cost]
  omega

/-- A fixed forty-eight-tape program, with six physical alphabet symbols,
computes the four numerator words in linear time and erases every private copy. -/
theorem runs (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ i,(xs i).length=b) :
    HoareTime program (fun v => v=input xs) (fun v => v=output xs) (168*b+591) := by
  have h (i : Fin 4) := RawLinearCombination.runs (expression i) xs b hw
  have h01 := SharedControlPair.runs _ _ (controls xs) _ _ _ _ (h 0) (h 1)
  have h23 := SharedControlPair.runs _ _ (controls xs) _ _ _ _ (h 2) (h 3)
  have hh := SharedControlPair.runs _ _ (controls xs) _ _ _ _ h01 h23
  simp only [RawLinearCombinationCleanup.empty_append,expression_cost] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem words_length (i : Fin 4) (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b) :
    (words i xs).length=b := RawLinearCombination.result_length _ _ _ hw

theorem valid (i : Fin 4) : RadixLinearCombination.Valid (q:=2) (expression i).erase := by
  fin_cases i <;> norm_num [expression,negative,RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.Valid]

/-- Exact numerator arithmetic in the represented residue ring. -/
theorem words_value (i : Fin 4) (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b) :
    (RadixDigits.value (words i xs) : ZMod (2^b))=
      numerator (fun j => (RadixDigits.value (xs j.val) : ZMod (2^b))) i := by
  rw [words,RawLinearCombination.result_value _ (valid i) xs b hw]
  fin_cases i <;>
    simp [expression,negative,numerator,RadixLinearCombinationRefresh.Expr.erase,
      RadixLinearCombination.valueMod,Swap.Modular.ratMod] <;> ring

/-- Integer signed inputs are handled by their residues; no positivity is assumed. -/
theorem words_integer (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b)
    (x : Fin 4 → ℤ) (hx : ∀ j : Fin 4,(RadixDigits.value (xs j.val) : ZMod (2^b))=(x j : ZMod (2^b)))
    (i : Fin 4) :
    (RadixDigits.value (words i xs) : ZMod (2^b))=((numerator x i : ℤ) : ZMod (2^b)) := by
  rw [words_value i xs b hw]
  have hh : (fun j : Fin 4 => (RadixDigits.value (xs j.val) : ZMod (2^b)))=fun j => (x j : ZMod (2^b)) := funext hx
  rw [hh]
  fin_cases i <;> simp [numerator]

end
end IntegerMultBounds.Machine.ButterflyNumerator
