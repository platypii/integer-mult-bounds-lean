module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseReplicaCouplingNative
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryCallerSetup

/-! Native coupling cleanup in the common caller. The exact released view and
one high-bank frame carry all retained recovery and gather data across cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 389 Q A U}

def replicaRecoveryCallerNativeReg (i : Fin 248) : Fin 389 :=
  replicaRecoveryCallerWorkerReg (Fin.castLE (by decide) i)

theorem replicaRecoveryCallerNativeReg_injective : Function.Injective replicaRecoveryCallerNativeReg :=
  replicaRecoveryCallerWorkerReg_injective.comp (Fin.castLE_injective _)

def releaseReplicaCouplingCaller : Pr P 389 Q A U :=
  embProg replicaRecoveryCallerNativeReg Empty.elim (releaseReplicaCouplingNative (P := Empty))

theorem releaseReplicaCouplingCaller_exec (v : HS 389 Q A U) (G : Stacks 389 A) :
    ∃ v' F, v'.user = v.user ∧
      Exec body releaseReplicaCouplingCaller (mk v G)
        (releaseReplicaCouplingNativeCost (embStk replicaRecoveryCallerNativeReg G)) (mk v' F) ∧
      embStk replicaRecoveryCallerNativeReg F = releasedReplicaCouplingNative (embStk replicaRecoveryCallerNativeReg G) ∧
      embStk replicaRecoveryCallerInterior.gather F = embStk replicaRecoveryCallerInterior.gather G ∧
      F.L = G.L ∧ F.inp = G.inp ∧ F.out = G.out ∧
      (∀ i : Fin 255, 117 ≤ i.val → F.R (replicaRecoveryCallerWorkerReg i) = G.R (replicaRecoveryCallerWorkerReg i)) ∧
      F.R (replicaRecoveryCallerWorkerReg 93) = G.R (replicaRecoveryCallerWorkerReg 93) ∧
      F.R (replicaRecoveryCallerWorkerReg 110) = G.R (replicaRecoveryCallerWorkerReg 110) ∧
      (∀ k, (∀ i, replicaRecoveryCallerNativeReg i ≠ k) → F.R k = G.R k) := by
  let e := replicaRecoveryCallerNativeReg
  have hinj : Function.Injective e := replicaRecoveryCallerNativeReg_injective
  obtain ⟨vi,hu,he⟩ := releaseReplicaCouplingNative_exec (body := fun z : Empty => nomatch z) (embDn e v) (embStk e G)
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    hinj (fun z => nomatch z) he v rfl G rfl
  let B := releasedReplicaCouplingNative (embStk e G)
  let F := embOvr e B.get G
  have hview : embStk e F = B := embStk_ovr hinj B G
  have hget (i : Fin 248) : F.R (e i) = B.R i := congrArg (fun S : Stacks 248 A => S.R i) hview
  have hoff (k : Fin 389) (hk : ∀ i, e i ≠ k) : F.R k = G.R k := (embOvr_off B.get G hk).2
  have hhigh (i : Fin 255) (hi : 117 ≤ i.val) : F.R (replicaRecoveryCallerWorkerReg i) = G.R (replicaRecoveryCallerWorkerReg i) := by
    by_cases hb : i.val < 248
    · exact (hget ⟨i.val,hb⟩).trans (releasedReplicaCouplingNative_high (embStk e G) ⟨i.val,hb⟩ hi)
    · apply hoff
      intro j hj
      have hh := congrArg (fun k : Fin 255 => k.val) (replicaRecoveryCallerWorkerReg_injective hj)
      change j.val = i.val at hh
      have hjb := j.isLt
      omega
  have hgather : embStk replicaRecoveryCallerInterior.gather F = embStk replicaRecoveryCallerInterior.gather G := by
    refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
    · exact (embOvr_off B.get G (fun k => replicaRecoveryCallerReg_worker_gather_disjoint (Fin.castLE (by decide) k) i)).1
    · exact hoff _ (fun k => replicaRecoveryCallerReg_worker_gather_disjoint (Fin.castLE (by decide) k) i)
  refine ⟨v',F,hu'.trans hu,he',hview,hgather,embOvr_left_of_eq G B rfl,rfl,rfl,hhigh,?_,?_,hoff⟩
  · exact (hget 93).trans (by simp [B,releasedReplicaCouplingNative,embStk,e,replicaRecoveryCallerNativeReg])
  · exact (hget 110).trans (by simp [B,releasedReplicaCouplingNative,embStk,e,replicaRecoveryCallerNativeReg])

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
