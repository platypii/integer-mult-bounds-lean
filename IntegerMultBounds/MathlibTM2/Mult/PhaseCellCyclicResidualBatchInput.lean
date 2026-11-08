module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedCyclicResidualBatch

/-! Ordinary geometry, arithmetic and workspace prerequisites of cyclic factor
construction. Numerical residual rows and factor tables are not supplied here. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure CyclicResidualBatchInput {A : ℕ} (p l s t u target a n : ℕ) [NeZero s]
    (tail pageTail : List (Fin (A+4))) (S : Stacks 234 A) : Prop where
  rows : (S.R 116).length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
  pageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u)
  page : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
    ((bFoldOrder s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail
  arithmetic : LengthKeyReady (2^15*p)
    (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
    (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2)
    l s t u (PhaseCellBand.width p u) 0 0 tail
    (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg
      (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg S))))))
  origin : (S.R 144).length = a
  leftEnd : (S.R 145).length = a+min n (s-a)
  rightEnd : (S.R 146).length = n-min n (s-a)
  fresh : ∀ i ∈ [(0 : Fin 234),127,138,139,141,142,143,147,151,152,153], S.R i = []
  left : ∀ i : Fin 224, S.L (preparedBoundaryBatchCoreReg (preparedBoundaryCoreReg i)) = []
  new : ∀ i : Fin 224, 154 ≤ i.val → S.R (preparedBoundaryBatchCoreReg (preparedBoundaryCoreReg i)) = []
  privateFresh : ∀ i ∈ [(225 : Fin 234),227,228,230,231,232,233], S.R i = []

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
