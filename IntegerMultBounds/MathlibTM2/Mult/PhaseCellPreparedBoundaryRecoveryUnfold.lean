module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryUnfold

/-! Start recovery by extending the proved solver endpoint with blank ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

theorem preparedBoundaryRecoveryUnfold_exec {Q A s : ℕ} [NeZero s] {P U : Type}
    {body : P → Pr P 248 Q A U} (hA : 4 ≤ A) (q w W : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (hlen : solution.length = B.card)
    (tail : List (Fin (A+4))) (v : HS 248 Q A U) (S : Stacks 242 A)
    (hbank : PackedPreparedBank q w W B.card S)
    (h143 : S.R 143 = []) (hcount : S.R 116 = List.replicate B.card tick)
    (hsrc : S.R 238 = cstream A w solution++tail) :
    let F := extendStacks (by decide : 242 ≤ 248) S
    ∃ v' n, v'.user = v.user ∧
      n ≤ ScalarPlacement.moveCountedLineCost B.card w+
        (generatedBoundaryUnfoldCost B.card w+B.card*(12*w+9)+12) ∧
      Exec body packedBoundarySolutionUnfold (mk v F) n
        (mk v' {F with R := (Function.update (Function.update (Function.update F.R
          238 tail) 231 []) 245
          (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}) := by
  apply packedBoundaryRecoveryUnfold_exec (body := body) hA q w W B solution hlen tail v
    (extendStacks (by decide) S)
  · simpa [packedBoundaryRecoveryBase] using hbank.workspace
  · simpa [packedBoundaryRecoveryBase] using hbank.ready
  · simpa [extendStacks] using h143
  · simpa [extendStacks] using hcount
  · simpa [extendStacks] using hsrc
  · intro i hi
    exact (extendStacks_fresh (by decide) S i hi).1
  · intro i hi
    exact (extendStacks_fresh (by decide) S i hi).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
