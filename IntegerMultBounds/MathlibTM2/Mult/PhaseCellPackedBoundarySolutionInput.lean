module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMoveCountedLine
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

/-! Isolate the owned boundary solution from the solver's borrowed output suffix.
The counted move restores all controls, so the factor page remains available
for inverse folding and the recovery solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

/-- Move exactly the boundary words from the publication port to the inverse-fold
input, without traversing or changing the caller's suffix. -/
def packedBoundarySolutionInput : Pr P 242 Q A U :=
  moveCountedLine 116 174 238 231 239 240 241 143

theorem packedBoundarySolutionInput_exec (w : ℕ) (solution : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 242 Q A U) (S : Stacks 242 A)
    (hcount : (S.R 116).length = solution.length) (hw : (S.R 174).length = w)
    (hsrc : S.R 238 = cstream A w solution ++ tail)
    (hclean : ∀ i ∈ ([231,239,240,241,143] : List (Fin 242)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ moveCountedLineCost solution.length w ∧
      Exec body packedBoundarySolutionInput (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 238 tail)
          231 (cstream A w solution))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := moveCountedLine_exec (body := body)
    116 174 238 231 239 240 241 143 (by decide) solution.length w
    (cstream A w solution) tail (by simp only [length_cstream]) v S hcount hw hsrc
    (hclean 239 (by simp)) (hclean 240 (by simp))
    (hclean 241 (by simp)) (hclean 143 (by simp))
  refine ⟨v',n,hu,hn,?_⟩
  simpa only [packedBoundarySolutionInput,hclean 231 (by simp),List.append_nil] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
