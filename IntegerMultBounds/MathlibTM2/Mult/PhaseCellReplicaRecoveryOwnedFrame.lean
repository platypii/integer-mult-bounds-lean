module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryReady

/-! Owned queue, RHS and output changes do not alter the shared recovery core.
This frame rule covers both input preparation and recovered-row retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

theorem ReplicaRecoveryCoreReady.of_owned_frame (H : ReplicaHaloProblem s) (W : ℕ)
    {S F : Stacks 248 A} (h : ReplicaRecoveryCoreReady H W S) (hL : F.L = S.L)
    (hframe : ∀ k : Fin 248, k ∉ [93,110,116,125,132,167,238] → F.R k = S.R k) :
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

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
