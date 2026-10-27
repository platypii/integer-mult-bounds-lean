module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedInverseWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseHeadersReady

/-! Scalar-generated headers supply the generated cached core readiness contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem generatedInverseCoreView {A : ℕ} (S : Stacks 296 A) :
    embStk sharedPageRecoveryReg (embStk couplingBoundaryReg (embStk generatedInverseCoreReg S)) =
      embStk inverseCoreReg (embStk generatedInverseSetupReg S) := by
  apply Stacks.ext
  · rfl
  · rfl
  · funext i
    exact congrArg S.L (generatedInverseCoreReg_legacy i)
  · funext i
    exact congrArg S.R (generatedInverseCoreReg_legacy i)

theorem generatedInverseHeaders_ready {A p u l target s t a b : ℕ} [NeZero s]
    (S : Stacks 296 A) (input : List (Fin (A+4)))
    (hleft : ∀ k, S.L (generatedInverseSetupReg (inverseCoreReg k)) = [])
    (hheaders : ∀ i, S.R (generatedInverseSetupReg (inverseMasterPort i)) =
      List.replicate (inverseMasterValues p u l target s t a b i) Node.tick)
    (hblank : ∀ k, (∀ i, inverseMasterCorePort i ≠ k) → k ≠ 110 → k ≠ 132 →
      S.R (generatedInverseSetupReg (inverseCoreReg k)) = [])
    (hsource : S.R (generatedInverseSetupReg (inverseCoreReg 110)) = input) :
    let band := PhaseCellBand.width p u
    let N := (haloBoundary s t band a b).card
    let E := inverseExecutionExponent p l target N band
    LengthKeyReady (2^15*p) (2*E+1) (4*E) l s t u band 0 0 input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg
          (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg (embStk generatedInverseCoreReg S))))))) := by
  rw [generatedInverseCoreView]
  exact inverseHeaders_ready _ input hleft hheaders hblank hsource

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
