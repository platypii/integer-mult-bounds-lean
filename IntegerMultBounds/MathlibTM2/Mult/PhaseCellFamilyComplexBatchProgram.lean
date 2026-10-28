module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyComplexBatchFinish
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Node
variable {Q A : ℕ} {P U : Type}

noncomputable def familyComplexBatch (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq (unaryProduct 121 160 243 245 244)
    (.seq (ucopy 246 240 244)
      (.seq (countedLoop 240 (familyComplexBatchStep recovery hR hQ)) familyComplexBatchFinish))


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
