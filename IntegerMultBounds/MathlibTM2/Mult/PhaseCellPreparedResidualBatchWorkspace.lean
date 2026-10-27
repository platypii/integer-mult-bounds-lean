module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryBatchWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Eight private registers route a batch through one preserved prepared boundary bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def preparedResidualBatchStep (hQ : SS.states ≤ Q) : Pr P 234 Q A U :=
  .seq (copyPrefix 231 226 206 232 233)
    (.seq (transfer 231 226 227 233)
      (.seq (embProg preparedBoundaryBatchCoreReg id (preparedResidualSolve hQ))
        (transfer 231 224 228 233)))

def preparedResidualBatchStepCost (q w N W : ℕ) : ℕ :=
  preparedResidualSolveCost q w N W+18*N*w+18

noncomputable def preparedResidualBatch (hQ : SS.states ≤ Q) : Pr P 234 Q A U :=
  .seq (unaryProduct 192 160 231 232 233)
    (.seq (ucopy 229 230 233)
      (.seq (countedLoop 230 (preparedResidualBatchStep hQ))
        (.seq (moveR 227 226 id) (.seq (moveR 228 224 id) (uclear 231)))))

def preparedResidualBatchCost (q w N W replicas : ℕ) : ℕ :=
  N*(6*w+9)+16+replicas*(preparedResidualSolveCost q w N W+22*N*w+25)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
