module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageData

/-! Restrict a retained coefficient page to consecutive ambient rows. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds

def couplingCoefficientPageInterval (P q s t u band a b origin L : ℕ) : List GaussianInt :=
  (List.range L).flatMap (fun j => couplingCoefficientPageChunk P q s t u band a b (origin+j))

@[simp] theorem couplingCoefficientPageInterval_zero (P q s t u band a b origin : ℕ) :
    couplingCoefficientPageInterval P q s t u band a b origin 0 = [] := rfl

theorem couplingCoefficientPageInterval_succ (P q s t u band a b origin L : ℕ) :
    couplingCoefficientPageInterval P q s t u band a b origin (L+1) =
      couplingCoefficientPageInterval P q s t u band a b origin L ++
        couplingCoefficientPageChunk P q s t u band a b (origin+L) := by
  simp [couplingCoefficientPageInterval,List.range_succ]

/-- Split by row ownership, rather than by a fixed number of encoded words:
skipped rows contribute no words. -/
theorem couplingCoefficientPage_split_interval (P q s t u band a b origin L : ℕ) :
    couplingCoefficientPage P q s t u band a b (origin+L) =
      couplingCoefficientPage P q s t u band a b origin ++
        couplingCoefficientPageInterval P q s t u band a b origin L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.add_succ,couplingCoefficientPage_succ,ih,couplingCoefficientPageInterval_succ]
    simp only [List.append_assoc]

/-- Consecutive row intervals concatenate even when some rows emit no words. -/
theorem couplingCoefficientPageInterval_add (P q s t u band a b origin M N : ℕ) :
    couplingCoefficientPageInterval P q s t u band a b origin (M+N) =
      couplingCoefficientPageInterval P q s t u band a b origin M ++
        couplingCoefficientPageInterval P q s t u band a b (origin+M) N := by
  simp [couplingCoefficientPageInterval,List.range_add,List.flatMap_map,Function.comp_def,Nat.add_assoc]

theorem couplingCoefficientPageInterval_length_le (P q s t u band a b origin L : ℕ) :
    (couplingCoefficientPageInterval P q s t u band a b origin L).length ≤ L*(2*band+1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [couplingCoefficientPageInterval_succ,List.length_append,couplingCoefficientPageChunk_length]
    split <;> nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
