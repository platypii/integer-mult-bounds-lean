module

public import IntegerMultBounds.MathlibTM2.Host.OrderedMove
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryCursor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryOwnedFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBoundaryFrame

/-! Load owned residual and matching original-RHS queues by two ordered moves.
The queue sources are outside the worker, and its borrowed destination suffixes
are preserved. No total-volume header or per-replica transport is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 259 Q A U}

def recoveryQueueWorkerReg : Fin 255 → Fin 259 := Fin.castLE (by decide)

def loadReplicaRecoveryQueues : Pr P 259 Q A U :=
  .seq (moveRightOrdered 257 104 238) (moveRightOrdered 258 104 93)

def loadedReplicaRecoveryQueues (S : Stacks 259 A) : Stacks 259 A :=
  {S with R := Function.update (Function.update (Function.update (Function.update S.R 257 [])
    238 (S.R 257++S.R 238)) 258 []) 93 (S.R 258++S.R 93)}

theorem loadedReplicaRecoveryQueues_frame (S : Stacks 259 A) (k : Fin 259)
    (hk : k ∉ [257,238,258,93]) : (loadedReplicaRecoveryQueues S).R k = S.R k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  simp [loadedReplicaRecoveryQueues,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2]

theorem loadReplicaRecoveryQueues_exec (H : ReplicaHaloProblem s) W Good
    (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length)
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val])
    (v : HS 259 Q A U) (S : Stacks 259 A)
    (hres : S.R 257 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)))
    (hrhs : S.R 258 = H.Fs.flatMap (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R)))
    (hcore : ReplicaRecoveryCoreReady H W
      (embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk recoveryQueueWorkerReg S)))
    (hphysical : ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk recoveryQueueWorkerReg S))) :
    let F := loadedReplicaRecoveryQueues S
    ∃ v', v'.user = v.user ∧
      Exec body loadReplicaRecoveryQueues (mk v S) (8*(H.Fs.length*(H.span*H.wordWidth))+8) (mk v' F) ∧
      F.R 257 = [] ∧ F.R 258 = [] ∧
      ReplicaRecoveryCursor H Good (S.R 238) (S.R 93) (S.R 125) 0 (embStk recoveryQueueWorkerReg F) ∧
      ReplicaRecoveryCoreReady H W
        (embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk recoveryQueueWorkerReg F)) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk recoveryQueueWorkerReg F)) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df
          (embStk (Fin.castLE (by decide : 242 ≤ 255)) (embStk recoveryQueueWorkerReg S)) →
        PackedBoundaryFactorPages bo hf df
          (embStk (Fin.castLE (by decide : 242 ≤ 255)) (embStk recoveryQueueWorkerReg F))) := by
  dsimp only
  have h104 : S.R 104 = [] := hcore.native 104 (by decide) (by decide) (by decide)
  obtain ⟨v₁,hu₁,he₁⟩ := moveRightOrdered_exec (body := body) 257 104 238
    (by decide) (by decide) (by decide) v S h104
  let J : Stacks 259 A := {S with R := Function.update (Function.update S.R 257 []) 238 (S.R 257++S.R 238)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveRightOrdered_exec (body := body) 258 104 93
    (by decide) (by decide) (by decide) v₁ J (by simpa [J] using h104)
  have hlenRows (rows : List (ZMod s → GaussianInt)) :
      (rows.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).length =
        rows.length*(H.span*H.wordWidth) := by
    induction rows with
    | nil => simp
    | cons D rows ih => simp [List.flatMap_cons,length_cstream,packedInterval_length D H.span_fit,ih,Nat.succ_mul,Nat.add_comm,Nat.add_mul]
  have hlenRes : (S.R 257).length = H.Fs.length*(H.span*H.wordWidth) := by rw [hres,hlenRows,hlen]
  have hlenRhs : (J.R 258).length = H.Fs.length*(H.span*H.wordWidth) := by
    change ((Function.update (Function.update S.R 257 []) 238 (S.R 257++S.R 238)) 258).length = _
    simp only [Function.update_of_ne (by decide : (258 : Fin 259) ≠ 238),Function.update_of_ne (by decide : (258 : Fin 259) ≠ 257)]
    rw [hrhs,hlenRows]
  have he : Exec body loadReplicaRecoveryQueues (mk v S)
      (8*(H.Fs.length*(H.span*H.wordWidth))+8) (mk v₂ (loadedReplicaRecoveryQueues S)) := by
    apply (Exec.seq he₁ he₂).cast
    · rw [hlenRes,hlenRhs]; omega
    · apply congrArg (mk v₂)
      simp [J,loadedReplicaRecoveryQueues]
  have hcoreF : ReplicaRecoveryCoreReady H W
      (embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk recoveryQueueWorkerReg (loadedReplicaRecoveryQueues S))) := by
    apply ReplicaRecoveryCoreReady.of_owned_frame H W hcore
      (F := embStk (Fin.castLE (by decide : 248 ≤ 255))
        (embStk recoveryQueueWorkerReg (loadedReplicaRecoveryQueues S))) rfl
    intro k hk
    apply loadedReplicaRecoveryQueues_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE,recoveryQueueWorkerReg] at hk ⊢
    have hb := k.isLt
    norm_num at hk ⊢
    omega
  refine ⟨v₂,hu₂.trans hu₁,he,by simp [loadedReplicaRecoveryQueues],by simp [loadedReplicaRecoveryQueues],?_,hcoreF,?_,?_⟩
  · apply ReplicaRecoveryCursor.initial H Good (S.R 238) (S.R 93)
      (embStk recoveryQueueWorkerReg (loadedReplicaRecoveryQueues S)) Ds hlen
    · change (loadedReplicaRecoveryQueues S).R 238 = _
      simpa [loadedReplicaRecoveryQueues] using congrArg (fun xs => xs++S.R 238) hres
    · exact hgood
    · change (loadedReplicaRecoveryQueues S).R 93 = _
      simpa [loadedReplicaRecoveryQueues] using congrArg (fun xs => xs++S.R 93) hrhs
  · apply ReplicaBoundaryRhsReady.of_recovery_core H W hphysical hcoreF
    intro k hk
    apply loadedReplicaRecoveryQueues_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,recoveryQueueWorkerReg,Fin.castLE]
    have hb := k.isLt
    norm_num
    omega
  · intro bo hf df hpages
    apply hpages.of_solution_frame
    intro k hk h238
    apply loadedReplicaRecoveryQueues_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,recoveryQueueWorkerReg,Fin.castLE] at h238 ⊢
    have hb := k.isLt
    norm_num at h238 ⊢
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
