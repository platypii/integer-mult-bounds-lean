module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingRecoveryFrame

/-! The shared masters and factor extension are spectators of the interior
controller. Both stacks survive; native scratch is restored by its loop state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast

theorem replicaRecoveryCallerWorkerReg_high (k : Fin 255) (hk : 117 ≤ k.val) :
    249 ≤ (replicaRecoveryCallerWorkerReg k).val := by
  cases hs : recoveryBankSplit (recoveryPortOrder (Fin.castLE (by decide) k)) with
  | inl i =>
    have he : replicaRecoveryCallerWorkerReg k =
        Fin.castLE (by decide : 300 ≤ 389) (ReplicaCouplingPlacement.standard.bank i) := by
      change recoveryBankSum (recoveryBankSplit (recoveryPortOrder (Fin.castLE (by decide) k))) = _
      rw [hs]
      rfl
    have he' : (Fin.castLE (by decide : 255 ≤ 259) k) = Fin.castLE (by decide : 168 ≤ 259) i :=
      replicaRecoveryCallerReg_injective (he.trans (replicaRecoveryCallerReg_native i).symm)
    have hv := congrArg (fun i : Fin 259 => i.val) he'
    change k.val = i.val at hv
    rw [he]
    change 249 ≤ (ReplicaCouplingPlacement.standard.bank i).val
    unfold ReplicaCouplingPlacement.bank
    rw [dif_neg (by omega : ¬ i.val < 117)]
    change 249 ≤ 249+(i.val-117)
    omega
  | inr i =>
    cases i with
    | inl i =>
      have he : replicaRecoveryCallerWorkerReg k = (⟨300+i.val,by omega⟩ : Fin 389) := by
        change recoveryBankSum (recoveryBankSplit (recoveryPortOrder (Fin.castLE (by decide) k))) = _
        rw [hs]
        rfl
      rw [he]
      change 249 ≤ 300+i.val
      omega
    | inr i =>
      have he : replicaRecoveryCallerWorkerReg k = recoverySource i := by
        change recoveryBankSum (recoveryBankSplit (recoveryPortOrder (Fin.castLE (by decide) k))) = _
        rw [hs]
        rfl
      fin_cases i
      · exact False.elim (replicaRecoveryCallerReg_worker_gather_disjoint k 121 he)
      · exact False.elim (replicaRecoveryCallerReg_worker_gather_disjoint k 125 he)

theorem initializedReplicaHaloLoop_recovery_frame_at {Q A : ℕ} {P U : Type}
    {body : P → Pr P 389 Q A U} (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {v v' : HS 389 Q A U} {S F : Stacks 389 A} {n : ℕ}
    (he : Exec body (initializedReplicaHaloLoop replicaRecoveryCallerInterior 247 hR hQ) (mk v S) n (mk v' F))
    (outside : Fin 389) (hb : 249 ≤ outside.val) :
    F.L (outside) = S.L (outside) ∧
      F.R (outside) = S.R (outside) := by
  have hg (i : Fin 126) : replicaRecoveryCallerInterior.gather i ≠ outside := by
    intro he
    have hv := congrArg (fun i : Fin 389 => i.val) he
    change i.val = (outside).val at hv
    have hi := i.isLt
    omega
  have hs (i : Fin 121) : replicaRecoveryCallerInterior.solver i ≠ outside := by
    intro he
    have hv := congrArg (fun i : Fin 389 => i.val) he
    change 126+i.val = (outside).val at hv
    have hi := i.isLt
    omega
  have hd : (247 : Fin 389) ≠ outside := by
    intro he
    have hv := congrArg (fun i : Fin 389 => i.val) he
    change 247 = (outside).val at hv
    omega
  exact ⟨initializedReplicaHaloLoop_preserves_left _ _ _ hR hQ hg hs hd he,
    initializedReplicaHaloLoop_preserves_right _ _ _ hR hQ hg hs hd he⟩


theorem initializedReplicaHaloLoop_recovery_frame {Q A : ℕ} {P U : Type}
    {body : P → Pr P 389 Q A U} (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {v v' : HS 389 Q A U} {S F : Stacks 389 A} {n : ℕ}
    (he : Exec body (initializedReplicaHaloLoop replicaRecoveryCallerInterior 247 hR hQ) (mk v S) n (mk v' F))
    (k : Fin 255) (hk : 117 ≤ k.val) :
    F.L (replicaRecoveryCallerWorkerReg k) = S.L (replicaRecoveryCallerWorkerReg k) ∧
      F.R (replicaRecoveryCallerWorkerReg k) = S.R (replicaRecoveryCallerWorkerReg k) :=
  initializedReplicaHaloLoop_recovery_frame_at hR hQ he _ (replicaRecoveryCallerWorkerReg_high k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
