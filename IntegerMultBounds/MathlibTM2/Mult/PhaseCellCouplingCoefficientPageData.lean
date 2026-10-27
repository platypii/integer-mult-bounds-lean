module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingRowValue

/-! Sparse coefficient-page order follows the actual generated coupling guards. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def couplingCoefficientPageChunk (P q s t u band a b i : ℕ) : List GaussianInt :=
  if couplingSkipAt true s t band a b i then [] else spatialCouplingCoefficientWords P q s t u band i

def couplingCoefficientPage (P q s t u band a b N : ℕ) : List GaussianInt :=
  (List.range N).flatMap (couplingCoefficientPageChunk P q s t u band a b)

@[simp] theorem couplingCoefficientPage_zero (P q s t u band a b : ℕ) :
    couplingCoefficientPage P q s t u band a b 0 = [] := rfl

theorem couplingCoefficientPage_succ (P q s t u band a b N : ℕ) :
    couplingCoefficientPage P q s t u band a b (N+1) =
      couplingCoefficientPage P q s t u band a b N++couplingCoefficientPageChunk P q s t u band a b N := by
  simp [couplingCoefficientPage,List.range_succ]

@[simp] theorem couplingCoefficientPageChunk_length (P q s t u band a b i : ℕ) :
    (couplingCoefficientPageChunk P q s t u band a b i).length =
      if couplingSkipAt true s t band a b i then 0 else 2*band+1 := by
  unfold couplingCoefficientPageChunk
  split <;> simp

theorem couplingCoefficientPage_length_le (P q s t u band a b N : ℕ) :
    (couplingCoefficientPage P q s t u band a b N).length ≤ N*(2*band+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [couplingCoefficientPage_succ,List.length_append,couplingCoefficientPageChunk_length]
    split <;> nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
