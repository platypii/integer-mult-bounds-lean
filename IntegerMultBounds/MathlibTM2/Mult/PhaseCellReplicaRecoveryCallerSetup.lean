module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedReplicaBoundarySetup

/-! Copy the actual retained row-volume master once and generate the shared
boundary mask/counters. Both the recovery core and complete gather bank survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

def replicaRecoveryCallerWorkerReg (i : Fin 255) : Fin 389 :=
  replicaRecoveryCallerReg (Fin.castLE (by decide) i)

theorem replicaRecoveryCallerWorkerReg_injective : Function.Injective replicaRecoveryCallerWorkerReg :=
  replicaRecoveryCallerReg_injective.comp (Fin.castLE_injective _)

def replicaRecoveryCallerSetup : Pr P 389 Q A U :=
  .seq (ucopy 123 (replicaRecoveryCallerWorkerReg 251) (replicaRecoveryCallerWorkerReg 104))
    (embProg replicaRecoveryCallerWorkerReg Empty.elim (retainedReplicaBoundarySetup (P := Empty)))

theorem replicaRecoveryCallerSetup_exec (H : ReplicaHaloProblem s) W (hA : 4 ≤ A)
    (v : HS 389 Q A U) (G : Stacks 389 A)
    (hcore : ReplicaRecoveryCoreReady H W
      (embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk replicaRecoveryCallerWorkerReg G)))
    (hvolume : (G.R 123).length = H.span*H.wordWidth)
    (hblank : ∀ i : Fin 255, 248 ≤ i.val → G.R (replicaRecoveryCallerWorkerReg i) = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ (4*(H.span*H.wordWidth)+4)+initializeReplicaBoundaryRhsCost H ∧
      Exec body replicaRecoveryCallerSetup (mk v G) n (mk v' F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk replicaRecoveryCallerWorkerReg F)) ∧
      ReplicaRecoveryCoreReady H W
        (embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk replicaRecoveryCallerWorkerReg F)) ∧
      embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk replicaRecoveryCallerWorkerReg F) =
        embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk replicaRecoveryCallerWorkerReg G) ∧
      embStk replicaRecoveryCallerInterior.gather F = embStk replicaRecoveryCallerInterior.gather G ∧
      F.L = G.L ∧
      (∀ k, (∀ i, replicaRecoveryCallerWorkerReg i ≠ k) → F.R k = G.R k) := by
  let e := replicaRecoveryCallerWorkerReg
  have hinj : Function.Injective e := replicaRecoveryCallerWorkerReg_injective
  have h104 : G.R (e 104) = [] := hcore.native 104 (by decide) (by decide) (by decide)
  have hsrc (i : Fin 255) : e i ≠ 123 := replicaRecoveryCallerReg_worker_gather_disjoint i 123
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 123) (b := e 251) (t := e 104)
    (hsrc 251).symm (hsrc 104).symm (hinj.ne (by decide)) v G h104
  let J : Stacks 389 A := {G with R := Function.update G.R (e 251) (List.replicate (H.span*H.wordWidth) tick)}
  have h251 : G.R (e 251) = [] := hblank 251 (by decide)
  have he₁' : Exec body (ucopy 123 (e 251) (e 104)) (mk v G) (4*(H.span*H.wordWidth)+4) (mk v₁ J) := by
    simpa [J,hvolume,h251] using he₁
  have hnativeJ : embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk e J) =
      embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk e G) := by
    change embStk (fun i : Fin 248 => e (Fin.castLE (by decide) i)) J = _
    apply embStk_updateR_off
    intro i hi
    have hh := congrArg (fun k : Fin 255 => k.val) (hinj hi)
    change i.val = 251 at hh
    have hb := i.isLt
    omega
  have hcoreJ : ReplicaRecoveryCoreReady H W
      (embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk e J)) := by rw [hnativeJ]; exact hcore
  obtain ⟨vi,n,hu,hn,he,hphysical,hcoreF⟩ := retainedReplicaBoundarySetup_of_core_exec
    (body := fun z : Empty => nomatch z) H W hA (embDn e v₁) (embStk e J) hcoreJ
    (by change (J.R (e 251)).length = _; simp [J])
    (by
      intro k hk
      have hne : k ≠ 251 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      change Function.update G.R (e 251) _ (e k) = []
      rw [Function.update_of_ne (hinj.ne hne)]
      exact hblank k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    hinj (fun z => nomatch z) he v₁ rfl J rfl
  let B := retainedReplicaBoundarySetupState H (embStk e J)
  let F := embOvr e B.get J
  have hview : embStk e F = B := embStk_ovr hinj B J
  have hgather : embStk replicaRecoveryCallerInterior.gather F = embStk replicaRecoveryCallerInterior.gather G := by
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      exact (embOvr_off B.get J (fun k => replicaRecoveryCallerReg_worker_gather_disjoint k i)).1
    · funext i
      exact (embOvr_off B.get J (fun k => replicaRecoveryCallerReg_worker_gather_disjoint k i)).2.trans
        (Function.update_of_ne (replicaRecoveryCallerReg_worker_gather_disjoint 251 i).symm _ _)
  refine ⟨v',F,(4*(H.span*H.wordWidth)+4)+n,hu'.trans (hu.trans hu₁),by omega,
    Exec.seq he₁' he',?_,?_,?_,hgather,?_,?_⟩
  · rw [hview]; exact hphysical
  · rw [hview]; exact hcoreF
  · rw [hview,retainedReplicaBoundarySetupState_native,hnativeJ]
  · have hBL : B.L = (embStk e J).L := embOvr_left_of_eq (embStk e J)
      (initializedReplicaBoundaryRhsState H (embStk replicaBoundaryPhaseReg (embStk e J))) rfl
    exact embOvr_left_of_eq J B hBL
  · intro k hk
    exact (embOvr_off B.get J hk).2.trans (Function.update_of_ne (hk 251).symm _ _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
