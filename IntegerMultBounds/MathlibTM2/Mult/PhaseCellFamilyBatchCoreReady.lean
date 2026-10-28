module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseHeadersReady

/-! The generated batch core's readiness at the raw caller's fixed placement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

structure FamilyBatchCoreReady {A : ℕ} (recovery : Bool) (p u l target s t a b replicas : ℕ)
    [NeZero s] (input : List (Fin (A+4))) (S : Stacks 303 A) : Prop where
  native :
    let band := PhaseCellBand.width p u
    let E := inverseExecutionExponent p l target (haloBoundary s t band a b).card band
    LengthKeyReady (2^15*p) (2*E+1) (4*E) l s t u band 0 0 input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg
          (embStk familyBoundaryReg (embStk familyInverseCoreReg S)))))))
  couplingGuard : (embStk familyInverseCoreReg S).R (familyCouplingCachePort recovery 0) = []
  couplingWords : (embStk familyInverseCoreReg S).R (familyCouplingCachePort recovery 2) = []
  couplingRows : (embStk familyInverseCoreReg S).R (familyCouplingCachePort recovery 3) = []
  familyFresh : ∀ i ∈ ([(256 : Fin 263),257,258,259,260,261,262] : List (Fin 263)),
    (embStk familyInverseCoreReg S).R i = []
  left : ∀ i, (embStk familyBoundaryReg (embStk familyInverseCoreReg S)).L i = []
  aLength : ((embStk familyBoundaryReg (embStk familyInverseCoreReg S)).R 141).length = a
  bLength : ((embStk familyBoundaryReg (embStk familyInverseCoreReg S)).R 142).length = b
  lowerBlank : ∀ i ∈ ([109,115,116,0,106,139,127,138,143,147,151,153,152,94,131,134,135,136,140] : List (Fin 240)),
    (embStk familyBoundaryReg (embStk familyInverseCoreReg S)).R i = []
  upperBlank : ∀ i : Fin 240, 154 ≤ i.val →
    (embStk familyBoundaryReg (embStk familyInverseCoreReg S)).R i = []
  count : ((embStk familyInverseCoreReg S).R 246).length = replicas
  fresh : ∀ i ∈ ([240,241,242,243,244,245] : List (Fin 263)),
    (embStk familyInverseCoreReg S).R i = []
  extraBlank : (embStk familyBoundaryReg (embStk familyInverseCoreReg S)).R 137 = []

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
