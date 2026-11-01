module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryOwnedFrame

/-! Physical preparation supplies the disposable part of recovery readiness;
the shared core is transported through the exact owned-input frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 255 Q A U}

theorem ReplicaRecoveryCoreReady.prepare_inputs (H : ReplicaHaloProblem s) (W : ℕ)
    (S : Stacks 255 A) (xs tail : List (Fin (A+4)))
    (h : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) S)) :
    ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) (preparedReplicaRecoveryInputState S xs tail)) := by
  apply ReplicaRecoveryCoreReady.of_owned_frame H W h
    (F := embStk (Fin.castLE (by decide : 248 ≤ 255)) (preparedReplicaRecoveryInputState S xs tail)) rfl
  intro k hk
  apply preparedReplicaRecoveryInputState_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE] at hk ⊢
  norm_num at hk ⊢
  tauto

theorem prepareReplicaRecoveryReady_exec (H : ReplicaHaloProblem s) (W : ℕ)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 255 Q A U) (S : Stacks 255 A)
    (hphysical : ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg S))
    (h : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) S))
    (hsource : S.R 93 = cstream A H.wordWidth (packedInterval H.origin H.span C)++tail)
    (h116 : S.R 116 = []) (h167 : S.R 167 = []) :
    let F := preparedReplicaRecoveryInputState S (cstream A H.wordWidth (packedInterval H.origin H.span C)) tail
    ∃ v', v'.user = v.user ∧
      Exec body prepareReplicaRecoveryInputs (mk v S) (replicaRecoveryInputsCost H) (mk v' F) ∧
      ReplicaRecoveryReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) := by
  dsimp only
  obtain ⟨v',hu,he,hbank,hcount,hmask⟩ := replicaRecoveryInputs_exec (body := body) H W C tail v S
    hphysical h.bank hsource h116 h167
  exact ⟨v',hu,he,⟨ReplicaRecoveryCoreReady.prepare_inputs H W S _ tail h,hcount,hmask⟩⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
