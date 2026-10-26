module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientOffsetLoop
public import IntegerMultBounds.NLogN.PhaseCellCouplingOffsets

/-! Physical stream order for the exact alias-preserving coupling offsets. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def couplingCoefficientWords (P q s t u band i : ℕ) : List GaussianInt :=
  (PhaseCellMatrix.couplingOffsets band).reverse.map (fun δ =>
    rationalWord q (PhaseCellCrossCell.entry P s t u band i ((i : ℤ)+δ)))

theorem couplingCoefficientWords_split (P q s t u band i : ℕ) :
    couplingCoefficientWords P q s t u band i =
      offsetCoefficientWords true P q s t u band i band ++
      offsetCoefficientWords false P q s t u band i band ++
      [signedCoefficientWord false P q s t u band i 0] := by
  simp [couplingCoefficientWords,PhaseCellMatrix.couplingOffsets,offsetCoefficientWords,
    signedCoefficientWord,List.reverse_append,List.map_reverse,List.map_map,
    Function.comp_def,couplingOffset,List.append_assoc]

@[simp] theorem couplingCoefficientWords_length (P q s t u band i : ℕ) :
    (couplingCoefficientWords P q s t u band i).length = 2*band+1 := by
  simp [couplingCoefficientWords]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
