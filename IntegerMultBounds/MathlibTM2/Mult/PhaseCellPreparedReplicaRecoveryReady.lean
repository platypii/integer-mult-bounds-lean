module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryReady

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
  have hframe (k : Fin 248) (hk : k ∉ [93,110,116,132,167]) :
      (embStk (Fin.castLE (by decide : 248 ≤ 255)) (preparedReplicaRecoveryInputState S xs tail)).R k =
        (embStk (Fin.castLE (by decide : 248 ≤ 255)) S).R k := by
    apply preparedReplicaRecoveryInputState_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE] at hk ⊢
    norm_num at hk ⊢
    all_goals exact hk
  constructor
  · exact preparedBank_prepare_recovery_inputs S xs tail h.bank
  · exact (hframe 143 (by decide)).trans h.rhs
  · exact h.freshLeft
  · intro i hi
    rw [hframe i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
      norm_num
      omega)]
    exact h.freshRight i hi
  · exact couplingMasters_prepare_recovery_inputs S xs tail h.masters
  · rw [hframe 118 (by decide)]; exact h.stage
  · rw [hframe 120 (by decide)]; exact h.level
  · intro i h93 h110 h116
    rw [hframe ⟨i.val,by omega⟩ (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at h93 h110 h116 ⊢
      have hi := i.isLt
      omega)]
    exact h.native i h93 h110 h116
  · intro k hk
    rw [hframe k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
      norm_num at hk ⊢
      omega)]
    exact h.clean k hk
  · rw [hframe 140 (by decide)]; exact h.rows
  · exact (hframe 138 (by decide)).trans h.page
  · rw [hframe 139 (by decide)]; exact h.pageCount
  · exact couplingGeometry_prepare_recovery_inputs S xs tail h.geometry

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
