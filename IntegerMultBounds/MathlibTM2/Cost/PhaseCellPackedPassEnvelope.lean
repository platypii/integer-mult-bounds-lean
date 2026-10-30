module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedKeyCost

/-! One resource language for the initial and recovery interior passes. The
same polynomial envelope bounds both numeric formats and actual tape controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

structure PackedHaloPassEnvelope (p l s t u target rhsExp a b V Z : ℕ) : Prop where
  positive : 1 ≤ Z
  parameter : 2^15*p ≤ Z
  stage : executionStagePrecision p l target rhsExp+1 ≤ Z
  precision : executionPrecision p l target rhsExp ≤ Z
  ringLog : l ≤ Z
  exponent : u ≤ Z
  width : executionWidth p l target rhsExp ≤ Z
  band : PhaseCellBand.width p u ≤ Z
  workspace : V ≤ Z
  familyWorkspace : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
    (executionWidth p l target rhsExp) t u ≤ Z
  candidates : ∀ L ∈ haloLengthCandidates s t (PhaseCellBand.width p u) a b, L ≤ Z
  keys : ∀ L ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b,
    ∀ x ∈ packedHaloKeyDimensions p l s t u target rhsExp a b V L, x ≤ Z

end IntegerMultBounds.MathlibTM2.Cost
