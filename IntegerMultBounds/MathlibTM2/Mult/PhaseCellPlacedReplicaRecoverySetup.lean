module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoveryPreparation

/-! Reuse the existing physical boundary setup in the enlarged recovery caller.
The retained native bank is unchanged, and the three new archive/control ports
are outside the embedded setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

def replicaRecoverySetupWorkerReg (i : Fin 255) : Fin 392 :=
  Fin.castLE (by decide : 389 ≤ 392) (replicaRecoveryCallerWorkerReg i)

theorem replicaRecoverySetupWorkerReg_eq (i : Fin 255) :
    replicaRecoverySetupWorkerReg i =
      replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 255 ≤ 257) i) :=
  (replicaRecoveryPreparationCallerReg_worker i).symm

def placedReplicaRecoverySetup : Pr P 392 Q A U :=
  embProg (Fin.castLE (by decide : 389 ≤ 392)) Empty.elim (replicaRecoveryCallerSetup (P := Empty))

theorem placedReplicaRecoverySetup_exec (H : ReplicaHaloProblem s) (W : ℕ) (hA : 4 ≤ A)
    (v : HS 392 Q A U) (S : Stacks 392 A)
    (hcore : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255))
      (embStk replicaRecoverySetupWorkerReg S)))
    (hvolume : (S.R 123).length = H.span*H.wordWidth)
    (hblank : ∀ i : Fin 255, 248 ≤ i.val → S.R (replicaRecoverySetupWorkerReg i) = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (4*(H.span*H.wordWidth)+4)+initializeReplicaBoundaryRhsCost H ∧
      Exec body placedReplicaRecoverySetup (mk v S) n (mk v' F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk replicaRecoverySetupWorkerReg F)) ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255))
        (embStk replicaRecoverySetupWorkerReg F)) ∧
      embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk replicaRecoverySetupWorkerReg F) =
        embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk replicaRecoverySetupWorkerReg S) ∧
      embStk replicaRecoveryBatchInterior.gather F = embStk replicaRecoveryBatchInterior.gather S ∧
      F.L = S.L ∧
      (∀ k : Fin 392, 389 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k) ∧
      (∀ k, (∀ i, replicaRecoverySetupWorkerReg i ≠ k) → F.R k = S.R k) := by
  let e : Fin 389 → Fin 392 := Fin.castLE (by decide)
  obtain ⟨vi,G,n,hu,hn,he,hphysical,hcoreG,hnative,hgather,hL,hframe⟩ :=
    replicaRecoveryCallerSetup_exec (body := fun f : Empty => nomatch f) H W hA
      (embDn e v) (embStk e S) hcore hvolume hblank
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    (Fin.castLE_injective (by decide : 389 ≤ 392)) (fun f : Empty => nomatch f) he v rfl S rfl
  let F := embOvr e G.get S
  have hview : embStk e F = G := embStk_ovr (Fin.castLE_injective _) G S
  have hworker : embStk replicaRecoverySetupWorkerReg F = embStk replicaRecoveryCallerWorkerReg G := by
    change embStk replicaRecoveryCallerWorkerReg (embStk e F) = _
    rw [hview]
  have hgatherF : embStk replicaRecoveryBatchInterior.gather F = embStk replicaRecoveryCallerInterior.gather G := by
    change embStk replicaRecoveryCallerInterior.gather (embStk e F) = _
    rw [hview]
  refine ⟨v',F,n,hu'.trans hu,hn,he',?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hworker]; exact hphysical
  · rw [hworker]; exact hcoreG
  · rw [hworker]; exact hnative
  · rw [hgatherF]; exact hgather
  · exact embOvr_left_of_eq S G hL
  · intro k hk
    apply embOvr_off G.get S
    intro i heq
    have hv : i.val = k.val := congrArg Fin.val heq
    have hi := i.isLt
    omega

  · intro k hk
    by_cases hlow : k.val < 389
    · let j : Fin 389 := ⟨k.val,hlow⟩
      have hj : e j = k := Fin.ext rfl
      have hh := congrArg (fun Z : Stacks 389 A => Z.R j) hview
      change F.R (e j) = G.R j at hh
      have hoff := hframe j (by
        intro i heq
        exact hk i ((congrArg e heq).trans hj))
      change G.R j = S.R (e j) at hoff
      rw [hj] at hh hoff
      exact hh.trans hoff
    · exact (embOvr_off G.get S (by
        intro i heq
        have hv : i.val = k.val := congrArg Fin.val heq
        have hi := i.isLt
        omega)).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
