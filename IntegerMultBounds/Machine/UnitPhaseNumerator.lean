import IntegerMultBounds.Machine.ButterflyNumerator
import IntegerMultBounds.Machine.ActivePrefixStageDispatchCommon

/-! A fixed runtime four-way Gaussian unit multiplier. Both phase bits and
real/imaginary sources are preserved, two width-exact outputs remain, and all
private source copies are erased in time linear in radix-word width. -/
namespace IntegerMultBounds.Machine.UnitPhaseNumerator
noncomputable section
open RadixLinearCombinationRefresh (Expr controls)
open MarkedWordCleanup (one word)
open RawLinearCombinationCleanup (prepend prepend_runs clean empty_append)

def source : Fin 4 → Fin 2 → Fin 2 := ![![0,1],![1,0],![0,1],![1,0]]
def negative : Fin 4 → Fin 2 → Bool := ![![false,false],![true,false],![true,true],![false,true]]
def expression (p : Fin 4) (i : Fin 2) : Expr 2 := .term (source p i) (if negative p i then -1 else 1)

def numerator {R : Type*} [Ring R] (p : Fin 4) (x : Fin 2 → R) (i : Fin 2) : R :=
  if negative p i then -x (source p i) else x (source p i)

def words (p : Fin 4) (i : Fin 2) (xs : ℕ → List (Fin 2)) :=
  RadixLinearCombination.result (expression p i).erase xs

def coreInput (xs : ℕ → List (Fin 2)) : Tapes 6 2 :=
  (controls xs).append (RadixLinearCombinationBootstrap.empty 4)
def coreOutput (p : Fin 4) (xs : ℕ → List (Fin 2)) : Tapes 6 2 :=
  (controls xs).append ((clean (expression p 0) (words p 0 xs)).append (clean (expression p 1) (words p 1 xs)))
def coreProgram (p : Fin 4) := SharedControlPair.program
  (RawLinearCombination.program (q:=2) (expression p 0))
  (RawLinearCombination.program (q:=2) (expression p 1))

def low (p : Fin 4) : Bool := decide (p.val%2=1)
def high (p : Fin 4) : Bool := decide (2≤p.val)
def flags (p : Fin 4) : Tapes 2 2 :=
  (one (putWord (fun _ => blank) 0 [bitSymbol (low p)]) 0).append
    (one (putWord (fun _ => blank) 0 [bitSymbol (high p)]) 0)
def input (p : Fin 4) (xs : ℕ → List (Fin 2)) := (flags p).append (coreInput xs)
def output (p : Fin 4) (xs : ℕ → List (Fin 2)) := (flags p).append (coreOutput p xs)
def selected (p : Fin 4) := prepend (coreProgram p) 2

def testLow (sy : Fin 8 → Fin 6) := decide (sy 0=bitSymbol true)
def testHigh (sy : Fin 8 → Fin 6) := decide (sy 1=bitSymbol true)
def program := branch testHigh (branch testLow (selected 3) (selected 2))
  (branch testLow (selected 1) (selected 0))

theorem expression_cost (p : Fin 4) (i : Fin 2) (b : ℕ) : RawLinearCombination.cost (expression p i) b=6*b+21 := by
  simp [RawLinearCombination.cost,expression,RadixLinearCombinationBootstrap.initCost,
    RawLinearCombination.refreshCost,RadixLinearCombinationRefresh.Expr.erase,
    RadixLinearCombination.runtime,RawLinearCombinationCleanup.cost]
  omega

theorem core_runs (p : Fin 4) (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b) :
    HoareTime (coreProgram p) (fun v => v=coreInput xs) (fun v => v=coreOutput p xs) (12*b+43) := by
  have h0 := RawLinearCombination.runs (expression p 0) xs b hw
  have h1 := RawLinearCombination.runs (expression p 1) xs b hw
  have hh := SharedControlPair.runs _ _ (controls xs) _ _ _ _ h0 h1
  simp only [empty_append,expression_cost] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem selected_runs (p : Fin 4) (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b) :
    HoareTime (selected p) (fun v => v=input p xs) (fun v => v=output p xs) (12*b+43) :=
  prepend_runs (coreProgram p) _ _ (flags p) (core_runs p xs b hw)

theorem low_flag (p : Fin 4) (xs : ℕ → List (Fin 2)) : testLow (input p xs).reads=low p := by
  change decide ((putWord (fun _ => blank) 0 [bitSymbol (low p)]) 0=bitSymbol true)=low p
  cases low p <;> simp [putWord,bitSymbol,Fin.ext_iff]

theorem high_flag (p : Fin 4) (xs : ℕ → List (Fin 2)) : testHigh (input p xs).reads=high p := by
  change decide ((putWord (fun _ => blank) 0 [bitSymbol (high p)]) 0=bitSymbol true)=high p
  cases high p <;> simp [putWord,bitSymbol,Fin.ext_iff]

/-- Both bits are read by transitions; no phase case is an external branch. -/
theorem runs (p : Fin 4) (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b) :
    HoareTime program (fun v => v=input p xs) (fun v => v=output p xs) (12*b+45) := by
  have hl := low_flag p xs
  have hh := high_flag p xs
  fin_cases p
  all_goals simp only [low,high,Nat.reduceMod,Nat.reduceLeDiff,decide_true,decide_false] at hl hh
  · exact ActivePrefixStageDispatchCommon.branch_false _ _ _ _ _ hh
      (ActivePrefixStageDispatchCommon.branch_false _ _ _ _ _ hl (selected_runs 0 xs b hw))
  · exact ActivePrefixStageDispatchCommon.branch_false _ _ _ _ _ hh
      (ActivePrefixStageDispatchCommon.branch_true _ _ _ _ _ hl (selected_runs 1 xs b hw))
  · exact ActivePrefixStageDispatchCommon.branch_true _ _ _ _ _ hh
      (ActivePrefixStageDispatchCommon.branch_false _ _ _ _ _ hl (selected_runs 2 xs b hw))
  · exact ActivePrefixStageDispatchCommon.branch_true _ _ _ _ _ hh
      (ActivePrefixStageDispatchCommon.branch_true _ _ _ _ _ hl (selected_runs 3 xs b hw))

theorem words_length (p : Fin 4) (i : Fin 2) (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b) :
    (words p i xs).length=b := RawLinearCombination.result_length (expression p i) xs b hw

theorem valid (p : Fin 4) (i : Fin 2) : RadixLinearCombination.Valid (q:=2) (expression p i).erase := by
  fin_cases p <;> fin_cases i <;> norm_num [expression,source,negative,RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.Valid]

theorem words_value (p : Fin 4) (i : Fin 2) (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b) :
    (RadixDigits.value (words p i xs) : ZMod (2^b))=
      numerator p (fun j => (RadixDigits.value (xs j.val) : ZMod (2^b))) i := by
  rw [words,RawLinearCombination.result_value _ (valid p i) xs b hw]
  fin_cases p <;> fin_cases i <;> simp [expression,source,negative,numerator,
    RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.valueMod,Swap.Modular.ratMod]

end
end IntegerMultBounds.Machine.UnitPhaseNumerator
