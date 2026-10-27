module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedInverseCallerWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseHeadersReady

/-! Scalar-generated headers have the same view in the shared-page caller. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem sharedInverseCoreView {A : ℕ} (S : Stacks 280 A) :
    embStk sharedPageRecoveryReg (embStk sharedInverseCoreReg S) =
      embStk inverseCoreReg (embStk sharedInverseSetupReg S) := by
  apply Stacks.ext
  · rfl
  · rfl
  · funext i
    exact congrArg S.L (sharedInverseCoreReg_legacy i)
  · funext i
    exact congrArg S.R (sharedInverseCoreReg_legacy i)

theorem sharedInverseHeaders_ready {A p u l target s t a b : ℕ} [NeZero s]
    (S : Stacks 280 A) (input : List (Fin (A+4)))
    (hleft : ∀ k, S.L (sharedInverseSetupReg (inverseCoreReg k)) = [])
    (hheaders : ∀ i, S.R (sharedInverseSetupReg (inverseMasterPort i)) =
      List.replicate (inverseMasterValues p u l target s t a b i) Node.tick)
    (hblank : ∀ k, (∀ i, inverseMasterCorePort i ≠ k) → k ≠ 110 → k ≠ 132 →
      S.R (sharedInverseSetupReg (inverseCoreReg k)) = [])
    (hsource : S.R (sharedInverseSetupReg (inverseCoreReg 110)) = input) :
    let band := PhaseCellBand.width p u
    let N := (haloBoundary s t band a b).card
    let E := inverseExecutionExponent p l target N band
    LengthKeyReady (2^15*p) (2*E+1) (4*E) l s t u band 0 0 input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg
          (embStk sharedPageRecoveryReg (embStk sharedInverseCoreReg S)))))) := by
  rw [sharedInverseCoreView]
  exact inverseHeaders_ready _ input hleft hheaders hblank hsource

theorem sharedInverseOutput_frame {A : ℕ} (S : Stacks 280 A)
    (result : List (Fin (A+4))) :
    embOvr sharedInverseCoreReg
      ({(embStk sharedInverseCoreReg S) with R := (
        Function.update (embStk sharedInverseCoreReg S).R 132 (result++S.R 132))} : Stacks 240 A).get S =
      {S with R := Function.update S.R 132 (result++S.R 132)} := by
  rw [embOvr_updR sharedInverseCoreReg_injective, embOvr_stk]
  rfl

theorem sharedInverseOutput_scalars {A : ℕ} (S : Stacks 280 A)
    (result : List (Fin (A+4))) (r : Fast.TableVM.TblR 25) :
    ({S with R := Function.update S.R 132 (result++S.R 132)} : Stacks 280 A).R
      (sharedInverseSetupReg (inverseScalarReg r)) =
        S.R (sharedInverseSetupReg (inverseScalarReg r)) := by
  apply Function.update_of_ne
  exact sharedInverseScalarReg_core r 132

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
