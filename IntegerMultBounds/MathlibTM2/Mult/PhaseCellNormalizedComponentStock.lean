module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedComponentSolutions
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Pairing component streams has linear traffic and no numerical arithmetic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type}

def normalizedComponentSolutionsCost (L W N : ℕ) : ℕ :=
  (6*N+4)+((L*(4*W+9)+4)+(N*(16*(L*W)+9)+14)+(2*(L*W)+2))+(2*N+2)

def normalizedComponentSolutionsWorkspace (L W N : ℕ) : ℕ :=
  13*((N+1)*(L+1)*(40*W+100))

theorem normalizedComponentSolutionsCost_le (L W N : ℕ) :
    normalizedComponentSolutionsCost L W N ≤ (N+1)*(L+1)*(40*W+100) := by
  unfold normalizedComponentSolutionsCost
  nlinarith [Nat.zero_le (N*L*W),Nat.zero_le (N*W),Nat.zero_le (L*W),Nat.zero_le (N*L)]

theorem normalizedComponentSolutionsAssembly_native :
    mnNativePushBound 13 (normalizedComponentSolutionsAssembly (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [normalizedComponentSolutionsAssembly,halfCount,halfPairAct,normalizedCoreAssembly,
    pairComplexKey,pairComplexPrefix,pairComponents,pairComponentStep,countedLoop,countedLoopBody,
    unaryProduct,transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
