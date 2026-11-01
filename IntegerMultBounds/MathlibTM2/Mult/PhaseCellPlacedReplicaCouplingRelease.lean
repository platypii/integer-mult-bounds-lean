module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoverySharedBank

/-! Pay for native coupling cleanup once in the common caller. Shared generated
factors survive and the recovery core follows from the retained coupling bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

def replicaRecoveryPreparationNativeReg (i : Fin 248) : Fin 392 :=
  replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide) i)

theorem replicaRecoveryPreparationNativeReg_injective : Function.Injective replicaRecoveryPreparationNativeReg :=
  replicaRecoveryPreparationCallerReg_injective.comp
    ((Fin.castLE_injective _).comp (Fin.castLE_injective _))

def placedReplicaCouplingRelease : Pr P 392 Q A U :=
  embProg replicaRecoveryPreparationNativeReg Empty.elim (releaseReplicaCouplingNative (P := Empty))

theorem placedReplicaCouplingRelease_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (columns : List (ZMod s → GaussianInt)) (v : HS 392 Q A U) (S : Stacks 392 A)
    (hfactor : ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg S))
    (hshared : ReplicaRecoverySharedBank H (12*H.band+1) (embStk replicaRecoveryPreparationNativeReg S)) :
    ∃ v' F, v'.user = v.user ∧
      Exec body placedReplicaCouplingRelease (mk v S)
        (releaseReplicaCouplingNativeCost (embStk replicaRecoveryPreparationNativeReg S)) (mk v' F) ∧
      ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg F) ∧
      ReplicaRecoveryCoreReady H (12*H.band+1) (embStk replicaRecoveryPreparationNativeReg F) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k : Fin 248, 117 ≤ k.val ∨ k = 93 ∨ k = 110 → F.R (replicaRecoveryPreparationNativeReg k) = S.R (replicaRecoveryPreparationNativeReg k)) ∧
      (∀ k, (∀ i, replicaRecoveryPreparationNativeReg i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k) ∧
      F.R (replicaRecoveryPreparationNativeReg 116) = [] := by
  let e := replicaRecoveryPreparationNativeReg
  let B := embStk e S
  let G := releasedReplicaCouplingNative B
  have hdata : ReplicaBoundaryFactorData H target columns (embStk packedBoundaryRecoveryBase G) := by
    apply hfactor.of_recovery_frame H target columns (F := embStk packedBoundaryRecoveryBase G) rfl
    · intro i
      exact releasedReplicaCouplingNative_blank B ⟨i.val,by omega⟩
        (by intro he; have hv : i.val = 93 := congrArg (fun j : Fin 117 => j.val) he; have hi := i.isLt; omega)
        (by intro he; have hv : i.val = 110 := congrArg (fun j : Fin 117 => j.val) he; have hi := i.isLt; omega)
    · exact releasedReplicaCouplingNative_high B 119 (by decide)
    · intro k hk _
      exact releasedReplicaCouplingNative_high B (packedBoundaryRecoveryBase k) (by change 117 ≤ k.val; omega)
  obtain ⟨vi,hu,he⟩ := releaseReplicaCouplingNative_exec (body := fun f : Empty => nomatch f) (embDn e v) B
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    replicaRecoveryPreparationNativeReg_injective (fun f : Empty => nomatch f) he v rfl S rfl
  let F := embOvr e G.get S
  have hview : embStk e F = G := embStk_ovr replicaRecoveryPreparationNativeReg_injective G S
  refine ⟨v',F,hu'.trans hu,he',?_,?_,?_,rfl,rfl,?_,?_,?_⟩
  · change ReplicaBoundaryFactorData H target columns (embStk packedBoundaryRecoveryBase (embStk e F))
    rw [hview]
    exact hdata
  · rw [hview]
    exact hshared.released H (12*H.band+1) B
  · exact embOvr_left_of_eq S G rfl
  · intro k hk
    have hh := congrArg (fun Z : Stacks 248 A => Z.R k) hview
    apply hh.trans
    rcases hk with hk | rfl | rfl
    · exact releasedReplicaCouplingNative_high B k hk
    · simp [G,releasedReplicaCouplingNative,B,e,embStk]
    · simp [G,releasedReplicaCouplingNative,B,e,embStk]
  · intro k hk
    exact embOvr_off G.get S hk

  · have hh := congrArg (fun Z : Stacks 248 A => Z.R 116) hview
    exact hh.trans (releasedReplicaCouplingNative_blank B 116 (by decide) (by decide))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
