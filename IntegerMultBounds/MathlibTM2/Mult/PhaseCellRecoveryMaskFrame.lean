module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoveryPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBoundaryFrame

/-! Installing geometry mask caches preserves the retained arithmetic and geometry bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

theorem ReplicaRecoveryCoreReady.of_mask_frame (H : ReplicaHaloProblem s) (W : ℕ)
    {S F : Stacks 248 A} (h : ReplicaRecoveryCoreReady H W S) (hL : F.L = S.L)
    (hframe : ∀ k : Fin 248, k ∉ [159,161] → F.R k = S.R k) :
    ReplicaRecoveryCoreReady H W F := by
  have hfactor (k : Fin 242) (hk : k.val < 64 ∨ 168 ≤ k.val) (h238 : k ≠ 238) :
      F.R (packedBoundaryRecoveryBase k) = S.R (packedBoundaryRecoveryBase k) := by
    apply hframe
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,packedBoundaryRecoveryBase] at h238 ⊢
    norm_num at h238 ⊢
    omega
  constructor
  · apply h.bank.of_runtime_frame (F := embStk packedBoundaryRecoveryBase F)
    · exact congrArg (fun L => L ∘ packedBoundaryRecoveryBase) hL
    · intro k hk; exact hfactor k (Or.inl hk) (by intro he; have hv := congrArg Fin.val he; norm_num at hv; omega)
    · exact hframe 119 (by decide)
    · intro k hk h238; exact hfactor k (Or.inr hk) h238
  · exact (hframe 143 (by decide)).trans h.rhs
  · intro k hk; rw [hL]; exact h.freshLeft k hk
  · intro k hk
    rw [hframe k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
      norm_num
      omega)]
    exact h.freshRight k hk
  · apply h.masters.of_frame
    intro k hk
    apply hframe
    simp only [couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,packedRecoveryRuntimeReg] at hk ⊢
    norm_num at hk ⊢
    omega
  · rw [hframe 118 (by decide)]; exact h.stage
  · rw [hframe 120 (by decide)]; exact h.level
  · intro i h93 h110 h116
    rw [hframe ⟨i.val,by omega⟩ (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at h93 h110 h116 ⊢
      have hi := i.isLt
      norm_num at h93 h110 h116 ⊢
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
  · apply h.geometry.of_frame (hframe 163 (by decide))
    intro k hk
    apply hframe
    simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,packedRecoveryRuntimeReg] at hk ⊢
    norm_num at hk ⊢
    omega

/-- Installing the two caches leaves every preparation input and retained factor ready. -/
theorem ReplicaRecoveryPreparationReady.of_mask_frame (H : ReplicaHaloProblem s) (target : ℕ)
    (X : ℕ → ZMod s → ℝ) (columns : List (ZMod s → GaussianInt))
    (residualTail rhsTail boundaryTail recoveryTail : List (Fin (A+4)))
    {S F : Stacks 257 A}
    (h : ReplicaRecoveryPreparationReady H target X columns residualTail rhsTail boundaryTail recoveryTail S)
    (hL : F.L = S.L) (hframe : ∀ k : Fin 257, k ∉ [159,161] → F.R k = S.R k) :
    ReplicaRecoveryPreparationReady H target X columns residualTail rhsTail boundaryTail recoveryTail F := by
  have hcore : ReplicaRecoveryCoreReady H (12*H.band+1)
      (embStk (Fin.castLE (by decide : 248 ≤ 257)) F) := by
    apply h.core.of_mask_frame H (12*H.band+1)
      (congrArg (fun L => L ∘ Fin.castLE (by decide : 248 ≤ 257)) hL)
    intro k hk
    apply hframe
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE] at hk ⊢
    norm_num at hk ⊢
    exact hk
  refine ⟨?_,?_,?_,?_,hcore,?_,?_⟩
  · rcases h.cursor with ⟨hi,hr,hs,ha⟩
    refine ⟨hi,?_,?_,?_⟩
    · rcases hr with ⟨Ds,hlen,hres,hgood⟩
      exact ⟨Ds,hlen,(hframe 238 (by decide)).trans hres,hgood⟩
    · exact (hframe 93 (by decide)).trans hs
    · rcases ha with ⟨rows,hlen,h125,h256,hgood⟩
      exact ⟨rows,hlen,(hframe 125 (by decide)).trans h125,(hframe 256 (by decide)).trans h256,hgood⟩
  · apply h.factor.of_runtime_frame H target columns
      (congrArg (fun L => L ∘ Fin.castLE (by decide : 242 ≤ 257)) hL)
    · intro k hk
      apply hframe
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE]
      omega
    · exact hframe 119 (by decide)
    · intro k hk _
      apply hframe
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE]
      omega
  · intro i
    rw [hL]
    exact h.left i
  · have hc : ReplicaRecoveryCoreReady H (12*H.band+1)
        (embStk (Fin.castLE (by decide : 248 ≤ 255))
          (embStk (Fin.castLE (by decide : 255 ≤ 257)) F)) := hcore
    apply ReplicaBoundaryRhsReady.of_recovery_core H (12*H.band+1) h.physical hc
    intro k hk
    apply hframe
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE]
    omega
  · exact (hframe 116 (by decide)).trans h.count
  · exact (hframe 167 (by decide)).trans h.mask

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
