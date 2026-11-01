module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryPhasePlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace

/-! The displaced phase counters do not belong to numerical factor state.
The boundary and recovery views therefore share the same prepared factor bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

private theorem replicaBoundaryPhaseReg_factor_fixed (i : Fin 242) (hi : i.val < 64 ∨ 168 ≤ i.val) :
    replicaBoundaryPhaseReg i = Fin.castLE (by decide) i := by
  apply replicaBoundaryPhaseReg_fixed
  simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
  norm_num
  omega

theorem preparedBoundaryPhaseBank {A q w W N : ℕ} (S : Stacks 255 A)
    (h : PackedPreparedBank q w W N (embStk replicaBoundaryPhaseReg S))
    (hleft : ∀ i : Fin 242, S.L (Fin.castLE (by decide) i) = S.L (replicaBoundaryPhaseReg i)) :
    PackedPreparedBank q w W N (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) := by
  apply h.of_runtime_frame (F := embStk (Fin.castLE (by decide : 242 ≤ 255)) S)
  · funext i; exact hleft i
  · intro k hk
    change S.R (Fin.castLE (by decide) k) = S.R (replicaBoundaryPhaseReg k)
    rw [replicaBoundaryPhaseReg_factor_fixed k (Or.inl hk)]
  · change S.R 119 = S.R (replicaBoundaryPhaseReg 119)
    rw [replicaBoundaryPhaseReg_fixed _ (by decide)]
    rfl
  · intro k hk _
    change S.R (Fin.castLE (by decide) k) = S.R (replicaBoundaryPhaseReg k)
    rw [replicaBoundaryPhaseReg_factor_fixed k (Or.inr hk)]

theorem boundaryPhaseFactorPages {A : ℕ} (S : Stacks 255 A) {bo hf df : List (Fin (A+4))}
    (h : PackedBoundaryFactorPages bo hf df (embStk replicaBoundaryPhaseReg S)) :
    PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) := by
  apply h.of_solution_frame
  intro k hk _
  change S.R (Fin.castLE (by decide) k) = S.R (replicaBoundaryPhaseReg k)
  rw [replicaBoundaryPhaseReg_factor_fixed k (Or.inr hk)]

theorem preparedBoundaryPhaseBank_of_native {A q w W N : ℕ} (S : Stacks 255 A)
    (h : PackedPreparedBank q w W N (embStk (Fin.castLE (by decide : 242 ≤ 255)) S))
    (hleft : ∀ i : Fin 242, S.L (Fin.castLE (by decide) i) = S.L (replicaBoundaryPhaseReg i)) :
    PackedPreparedBank q w W N (embStk replicaBoundaryPhaseReg S) := by
  apply h.of_runtime_frame (F := embStk replicaBoundaryPhaseReg S)
  · funext i; exact (hleft i).symm
  · intro k hk
    change S.R (replicaBoundaryPhaseReg k) = S.R (Fin.castLE (by decide) k)
    rw [replicaBoundaryPhaseReg_factor_fixed k (Or.inl hk)]
  · change S.R (replicaBoundaryPhaseReg 119) = S.R 119
    rw [replicaBoundaryPhaseReg_fixed _ (by decide)]
    rfl
  · intro k hk _
    change S.R (replicaBoundaryPhaseReg k) = S.R (Fin.castLE (by decide) k)
    rw [replicaBoundaryPhaseReg_factor_fixed k (Or.inr hk)]

theorem boundaryPhaseFactorPages_of_native {A : ℕ} (S : Stacks 255 A) {bo hf df : List (Fin (A+4))}
    (h : PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S)) :
    PackedBoundaryFactorPages bo hf df (embStk replicaBoundaryPhaseReg S) := by
  apply h.of_solution_frame
  intro k hk _
  change S.R (replicaBoundaryPhaseReg k) = S.R (Fin.castLE (by decide) k)
  rw [replicaBoundaryPhaseReg_factor_fixed k (Or.inr hk)]

private theorem seedRecovery_factor_frame {A : ℕ} (S : Stacks 255 A) (k : Fin 242)
    (hk : k.val < 64 ∨ 168 ≤ k.val) :
    (seededReplicaRecoveryState S).R (Fin.castLE (by decide) k) = S.R (Fin.castLE (by decide) k) := by
  apply seededReplicaRecoveryState_frame
  all_goals intro he; have hv := congrArg Fin.val he; change k.val = _ at hv; omega

theorem preparedBank_seed_recovery {A q w W N : ℕ} (S : Stacks 255 A)
    (h : PackedPreparedBank q w W N (embStk (Fin.castLE (by decide : 242 ≤ 255)) S)) :
    PackedPreparedBank q w W N (embStk (Fin.castLE (by decide : 242 ≤ 255)) (seededReplicaRecoveryState S)) := by
  apply h.of_runtime_frame (F := embStk (Fin.castLE (by decide : 242 ≤ 255)) (seededReplicaRecoveryState S)) rfl
  · intro k hk; exact seedRecovery_factor_frame S k (Or.inl hk)
  · exact seededReplicaRecoveryState_frame S 119 (by decide) (by decide)
  · intro k hk _; exact seedRecovery_factor_frame S k (Or.inr hk)

theorem factorPages_seed_recovery {A : ℕ} (S : Stacks 255 A) {bo hf df : List (Fin (A+4))}
    (h : PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S)) :
    PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) (seededReplicaRecoveryState S)) := by
  apply h.of_solution_frame
  intro k hk _
  exact seedRecovery_factor_frame S k (Or.inr hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
