module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectRecoveryPrefixes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryOwnedFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBoundaryFrame

/-! Two separate archives for the batched second pass. Register 256 holds the
RHS archive, leaving the existing worker bank and loop counter untouched. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 257 Q A U}

def collectReplicaRecoveryRhs : Pr P 257 Q A U :=
  collectRecoveryPrefixes 251 110 132 256 125 104 105

def collectedReplicaRecoveryRhsState (S : Stacks 257 A)
    (rhsWords boundaryWords rhsTail boundaryTail : List (Fin (A+4))) : Stacks 257 A :=
  collectedRecoveryPrefixes S 110 132 256 125 rhsWords boundaryWords rhsTail boundaryTail

theorem collectedReplicaRecoveryRhsState_core (H : ReplicaHaloProblem s) (W : ℕ) (S : Stacks 257 A)
    (rhsWords boundaryWords rhsTail boundaryTail : List (Fin (A+4)))
    (h : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 257)) S)) :
    ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 257))
      (collectedReplicaRecoveryRhsState S rhsWords boundaryWords rhsTail boundaryTail)) := by
  apply ReplicaRecoveryCoreReady.of_owned_frame H W h
    (F := embStk (Fin.castLE (by decide : 248 ≤ 257))
      (collectedReplicaRecoveryRhsState S rhsWords boundaryWords rhsTail boundaryTail)) rfl
  intro k hk
  apply collectedRecoveryPrefixes_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE] at hk ⊢
  have hi := k.isLt
  norm_num at hk ⊢
  omega

theorem collectReplicaRecoveryRhs_exec_within (V : ℕ)
    (rhsWords originalWords boundaryWords rhsTail boundaryTail : List (Fin (A+4)))
    (hR : rhsWords.length = V) (hC : originalWords.length = V) (hY : boundaryWords.length = V)
    (v : HS 257 Q A U) (S : Stacks 257 A) (hV : (S.R 251).length = V)
    (hrhs : S.R 110 = rhsWords++(originalWords++rhsTail))
    (hboundary : S.R 132 = boundaryWords++boundaryTail)
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(18*V+18)) depth
        collectReplicaRecoveryRhs (mk v S) (18*V+18)
        (mk v' (collectedReplicaRecoveryRhsState S rhsWords boundaryWords rhsTail boundaryTail)) := by
  exact collectRecoveryPrefixes_exec_within 251 110 132 256 125 104 105 (by decide) V
    rhsWords originalWords boundaryWords rhsTail boundaryTail hR hC hY v S hV hrhs hboundary h104 h105 depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
