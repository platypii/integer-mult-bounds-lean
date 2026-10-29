module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCellRuntime

/-! The common native-bank state after retaining an actual boundary count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node

/-- Retain the actual boundary count beside the released native cell bank. -/
def countedReleasedCellBank {A : ℕ} (n : ℕ) (rhs borrowed result : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let B := releasedCellBank rhs borrowed result inp out
  {B with R := Function.update B.R 116 (List.replicate n tick)}

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
