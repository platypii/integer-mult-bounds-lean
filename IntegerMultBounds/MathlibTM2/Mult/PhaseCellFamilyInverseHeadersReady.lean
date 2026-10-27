module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseCallerWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseHeadersReady

/-! Scalar-generated headers supply the generated cached core readiness contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem familyInverseCoreView {A : ℕ} (S : Stacks 303 A) :
    embStk sharedPageRecoveryReg (embStk familyBoundaryReg (embStk familyInverseCoreReg S)) =
      embStk inverseCoreReg (embStk familyInverseSetupReg S) := by
  apply Stacks.ext
  · rfl
  · rfl
  · funext i
    exact congrArg S.L (familyInverseCoreReg_legacy i)
  · funext i
    exact congrArg S.R (familyInverseCoreReg_legacy i)

theorem familyInverseHeaders_ready {A p u l target s t a b : ℕ} [NeZero s]
    (S : Stacks 303 A) (input : List (Fin (A+4)))
    (hleft : ∀ k, S.L (familyInverseSetupReg (inverseCoreReg k)) = [])
    (hheaders : ∀ i, S.R (familyInverseSetupReg (inverseMasterPort i)) =
      List.replicate (inverseMasterValues p u l target s t a b i) Node.tick)
    (hblank : ∀ k, (∀ i, inverseMasterCorePort i ≠ k) → k ≠ 110 → k ≠ 132 →
      S.R (familyInverseSetupReg (inverseCoreReg k)) = [])
    (hsource : S.R (familyInverseSetupReg (inverseCoreReg 110)) = input) :
    let band := PhaseCellBand.width p u
    let N := (haloBoundary s t band a b).card
    let E := inverseExecutionExponent p l target N band
    LengthKeyReady (2^15*p) (2*E+1) (4*E) l s t u band 0 0 input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg
          (embStk sharedPageRecoveryReg (embStk familyBoundaryReg (embStk familyInverseCoreReg S))))))) := by
  rw [familyInverseCoreView]
  exact inverseHeaders_ready _ input hleft hheaders hblank hsource

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
