module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBinaryRecoveryGuardInterval
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock

/-! The shared binary guard generator is closed; placement preserves its atomic bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main

def intervalGuardPush {Q A : ℕ} {U : Type} : ℕ :=
  mnProgPush (.seq (loadIntervalGuardBank (P := Empty) (Q := Q) (A := A) (U := U))
    (recoveryGuardIntervalHost true))

theorem placedBinaryRecoveryGuardInterval_native {P U : Type} {Q A : ℕ} :
    mnNativePushBound (intervalGuardPush (Q := Q) (A := A) (U := U))
      (placedBinaryRecoveryGuardInterval (P := P) (Q := Q) (A := A) (U := U) true) := by
  exact embProg_native intervalGuardPlacement Empty.elim _ (WordCmd.empty_native _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
