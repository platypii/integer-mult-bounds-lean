module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJointSourceRecoveryCouplingStock

/-! The paired recovery endpoint preserves stock. Both pieces exchange their
consumed field/RHS prefixes for equal-length saved/computed archives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "source" => CyclicRecoveryPlacement.bank 132
variable {s Q A : ℕ} [NeZero s] {U : Type}

theorem cyclicRecoveryCouplingRowState_stock (H K : ReplicaHaloProblem s)
    (C D B E : ZMod s → GaussianInt) (tail rhsL rhsR outputL outputR : List (Fin (A+4)))
    (houtputL : outputL.length = H.span*H.wordWidth) (houtputR : outputR.length = K.span*K.wordWidth)
    (v w : HS 840 Q A U) (S : Stacks 840 A)
    (hsource : S.R source = cstream A H.wordWidth (packedInterval H.origin H.span C)++
      (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail))
    (hrhsL : S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) =
      cstream A H.wordWidth (packedInterval H.origin H.span B)++rhsL)
    (hrhsR : S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) =
      cstream A K.wordWidth (packedInterval K.origin K.span E)++rhsR) :
    mnSize (mk w (cyclicRecoveryCouplingRowState H K C D tail rhsL rhsR outputL outputR S)) = mnSize (mk v S) := by
  let J := jointSourceRecoveryCouplingState H CyclicRecoveryPlacement.leftJob.coupling source C
    (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail) rhsL outputL S
  have hL := jointSourceRecoveryCouplingState_stock H CyclicRecoveryPlacement.leftJob.coupling source
    (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.bank i))
    (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.gather i)) C B _ rhsL outputL houtputL v w S hsource hrhsL
  have hsourceJ : J.R source = cstream A K.wordWidth (packedInterval K.origin K.span D)++tail := by
    dsimp only [J]
    rw [jointSourceRecoveryCouplingState_eq H CyclicRecoveryPlacement.leftJob.coupling source
      (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.bank i))
      (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.gather i))]
    simp [(CyclicRecoveryPlacement.source_left_disjoint _ (.bank 93)).symm,
      (CyclicRecoveryPlacement.source_left_disjoint _ (.bank 110)).symm,
      (CyclicRecoveryPlacement.source_left_disjoint _ (.gather 125)).symm]
  have hrhsJ : J.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) =
      cstream A K.wordWidth (packedInterval K.origin K.span E)++rhsR :=
    (cyclicRecoveryLeftPiece_frame H C _ rhsL outputL S _ (.bank 93)).trans hrhsR
  have hR := jointSourceRecoveryCouplingState_stock K CyclicRecoveryPlacement.rightJob.coupling source
    (fun i => CyclicRecoveryPlacement.source_right_disjoint _ (.bank i))
    (fun i => CyclicRecoveryPlacement.source_right_disjoint _ (.gather i)) D E tail rhsR outputR houtputR w w J hsourceJ hrhsJ
  exact hR.trans hL

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
