module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchFactorFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingRecoveryBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingRetainedHeaders

/-! Assemble recovery's retained shared bank from the first pass's restored
workspace, structural frames and generated coupling pages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

theorem ReplicaBoundaryFactorData.batch_first_pass_shared_bank (H : ReplicaHaloProblem s) (target : ℕ)
    (columns : List (ZMod s → GaussianInt)) {S F : Stacks 392 A}
    (h : ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg S))
    (raw : List (Fin (A+4)))
    (hnative : (embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver F)).L =
      (embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver S)).L)
    (hleft : ∀ k, (∀ i, replicaRecoveryBatchInterior.gather i ≠ k) →
      (∀ i, replicaRecoveryBatchInterior.solver i ≠ k) → (247 : Fin 392) ≠ k → F.L k = S.L k)
    (hright : ∀ k, (∀ i, replicaRecoveryBatchCoupling.bank i ≠ k) →
      (∀ i, replicaRecoveryBatchInterior.gather i ≠ k) →
      (∀ i, replicaRecoveryBatchInterior.solver i ≠ k) →
      (247 : Fin 392) ≠ k → (248 : Fin 392) ≠ k → F.R k = S.R k)
    (hready : RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) raw (embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver F)))
    (hshare : ∀ k : Fin 168, 117 ≤ k.val → k ∉ replicaCouplingSetupPorts →
      F.R (replicaRecoveryBatchCoupling.bank k) = S.R (replicaRecoveryBatchCoupling.bank k))
    (hwork : ReplicaFactoryWorkspace (embStk replicaRecoveryBoundaryFactoryReg S))
    (hheaders : PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
      H.origin (H.origin+H.span) H.metadataWidth H.wordWidth (embStk replicaRecoveryBatchCoupling.bank F))
    (hprivate : ∀ k : Fin 248, 242 ≤ k.val →
      S.L (replicaRecoveryPreparationNativeReg k) = [] ∧ S.R (replicaRecoveryPreparationNativeReg k) = [])
    (hfresh : ∀ k ∈ ([(127 : Fin 168),143,166,158,135,167]), F.R (replicaRecoveryBatchCoupling.bank k) = [])
    (hrows : (F.R (replicaRecoveryBatchCoupling.bank 140)).length = 2*H.band+1)
    (hpage : F.R (replicaRecoveryBatchCoupling.bank 138) = cstream A H.wordWidth
      (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span)
        H.origin H.span)++S.R (replicaRecoveryBatchCoupling.bank 138))
    (hcount : (F.R (replicaRecoveryBatchCoupling.bank 139)).length =
      (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span)
        H.origin H.span).length) :
    ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg F) ∧
      ReplicaRecoverySharedBank H (12*H.band+1) (embStk replicaRecoveryPreparationNativeReg F) := by
  have hheadersF : PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
      H.origin (H.origin+H.span) H.metadataWidth H.wordWidth
      (embStk packedRecoveryRuntimeReg (embStk replicaRecoveryPreparationNativeReg F)) := by
    rw [replicaRecoveryBatchCoupling_runtime_view]
    exact hheaders
  refine h.coupling_recovery_bank H target columns (F := embStk replicaRecoveryPreparationNativeReg F)
    (replicaRecoveryBatchCoupling_factor_left_frame hnative hleft) ?_ ?_ ?_ hheadersF ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [replicaRecoveryBatchCoupling_native_view F] at hready
    intro i
    exact (hready.clean i).2
  · change F.R (replicaRecoveryPreparationCallerWorkerReg 119) = S.R (replicaRecoveryPreparationCallerWorkerReg 119)
    have hh := hshare 119 (by decide) (by decide)
    norm_num only [replicaRecoveryBatchCoupling_bank,Fin.castLE] at hh
    exact hh
  · intro k hk _
    exact replicaRecoveryBatchCoupling_factor_extension_frame hright (Fin.castLE (by decide : 242 ≤ 257) k) hk
  · intro k hk
    have hl := replicaRecoveryBatchCoupling_worker_left_frame hleft
      (Fin.castLE (by decide : 248 ≤ 257) k) (by change 117 ≤ k.val; omega)
    have hr := replicaRecoveryBatchCoupling_factor_extension_frame hright
      (Fin.castLE (by decide : 248 ≤ 257) k) (by change 168 ≤ k.val; omega)
    exact ⟨hl.trans (hprivate k hk).1,hr.trans (hprivate k hk).2⟩
  · intro k hk
    apply hwork.scratch
    simp only [replicaFactoryScratchPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
    norm_num at hk ⊢
    omega
  · intro k hk
    have hlow : k.val < 168 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
      norm_num at hk
      omega
    have hh := hshare ⟨k.val,hlow⟩ (by
      change 117 ≤ k.val
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
      norm_num at hk
      omega) (by
      simp only [replicaCouplingSetupPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
      norm_num at hk ⊢
      omega)
    change F.R (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 242 ≤ 257) k)) =
      S.R (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 242 ≤ 257) k))
    norm_num only [replicaRecoveryBatchCoupling_bank,Fin.castLE] at hh
    exact hh
  · intro k hk
    have hlow : k.val < 168 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
      norm_num at hk
      omega
    have hh := hfresh ⟨k.val,hlow⟩ (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
      norm_num at hk ⊢
      omega)
    change F.R (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 248 ≤ 257) k)) = []
    norm_num only [replicaRecoveryBatchCoupling_bank,Fin.castLE] at hh
    exact hh
  · change (F.R (replicaRecoveryPreparationCallerWorkerReg 140)).length = _
    norm_num only [replicaRecoveryBatchCoupling_bank,Fin.castLE] at hrows
    exact hrows
  · have h138 : S.R (replicaRecoveryBatchCoupling.bank 138) = [] := by
      rw [replicaRecoveryBatchCoupling_bank]
      exact hwork.scratch 138 (by decide)
    rw [h138,List.append_nil] at hpage
    change F.R (replicaRecoveryPreparationCallerWorkerReg 138) = _
    norm_num only [replicaRecoveryBatchCoupling_bank,Fin.castLE] at hpage
    exact hpage
  · change (F.R (replicaRecoveryPreparationCallerWorkerReg 139)).length = _
    norm_num only [replicaRecoveryBatchCoupling_bank,Fin.castLE] at hcount
    exact hcount

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
