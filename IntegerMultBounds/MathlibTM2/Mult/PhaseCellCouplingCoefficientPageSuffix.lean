module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageData

/-! Structural suffixes align the sparse page cursor with ambient coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds

def couplingCoefficientPageSuffix (P q s t u band a b i N : ℕ) : List GaussianInt :=
  (List.range (N-i)).flatMap (fun j => couplingCoefficientPageChunk P q s t u band a b (i+j))

@[simp] theorem couplingCoefficientPageSuffix_zero (P q s t u band a b N : ℕ) :
    couplingCoefficientPageSuffix P q s t u band a b 0 N = couplingCoefficientPage P q s t u band a b N := by
  simp [couplingCoefficientPageSuffix,couplingCoefficientPage]

@[simp] theorem couplingCoefficientPageSuffix_end (P q s t u band a b N : ℕ) :
    couplingCoefficientPageSuffix P q s t u band a b N N = [] := by simp [couplingCoefficientPageSuffix]

theorem couplingCoefficientPageSuffix_step (P q s t u band a b i N : ℕ) (hi : i < N) :
    couplingCoefficientPageSuffix P q s t u band a b i N =
      couplingCoefficientPageChunk P q s t u band a b i++
        couplingCoefficientPageSuffix P q s t u band a b (i+1) N := by
  unfold couplingCoefficientPageSuffix
  rw [show N-i = (N-(i+1))+1 by omega,List.range_succ_eq_map]
  simp [List.flatMap_map,Function.comp_def,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
