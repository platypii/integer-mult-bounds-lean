module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInputBank

/-! Shared source/result updates for the ordinary numerical batch bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {A : ℕ}

theorem batchInputBank_prepend_rhs (precision stage q l s t u band L B : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    {batchInputBank precision stage q l s t u band L B lo [] borrowed outTail inp out with
      R := Function.update (batchInputBank precision stage q l s t u band L B lo [] borrowed outTail inp out).R
        110 (rhs++borrowed)} =
      batchInputBank precision stage q l s t u band L B lo rhs borrowed outTail inp out := by
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k = 110
  · subst k; simp [batchInputBank]
  · have hv : k.val ≠ 110 := by intro he; apply hk; exact Fin.ext he
    simp [batchInputBank,hk,hv]

theorem batchInputBank_update_result (precision stage q l s t u band L B : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed result result' : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    {batchInputBank precision stage q l s t u band L B lo rhs borrowed result inp out with
      R := Function.update (batchInputBank precision stage q l s t u band L B lo rhs borrowed result inp out).R
        93 result'} =
      batchInputBank precision stage q l s t u band L B lo rhs borrowed result' inp out := by
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k = 93
  · subst k; simp [batchInputBank]
  · have hv : k.val ≠ 93 := by intro he; apply hk; exact Fin.ext he
    simp [batchInputBank,hk,hv]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
