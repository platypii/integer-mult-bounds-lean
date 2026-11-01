module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaRecoveryInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingMasterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata

/-! Recovery input preparation changes owned data only. Shared numerical
factors, coupling masters and binary interval geometry retain their meanings. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

private theorem recoveryInputs_factor_frame {A : ℕ} (S : Stacks 255 A)
    (xs tail : List (Fin (A+4))) (k : Fin 242) (hk : k.val < 64 ∨ 168 ≤ k.val) :
    (preparedReplicaRecoveryInputState S xs tail).R (Fin.castLE (by decide) k) = S.R (Fin.castLE (by decide) k) := by
  apply preparedReplicaRecoveryInputState_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
  norm_num
  omega

theorem preparedBank_prepare_recovery_inputs {A q w W N : ℕ} (S : Stacks 255 A)
    (xs tail : List (Fin (A+4)))
    (h : PackedPreparedBank q w W N (embStk (Fin.castLE (by decide : 242 ≤ 255)) S)) :
    PackedPreparedBank q w W N
      (embStk (Fin.castLE (by decide : 242 ≤ 255)) (preparedReplicaRecoveryInputState S xs tail)) := by
  apply h.of_runtime_frame (F := embStk (Fin.castLE (by decide : 242 ≤ 255)) (preparedReplicaRecoveryInputState S xs tail)) rfl
  · intro k hk; exact recoveryInputs_factor_frame S xs tail k (Or.inl hk)
  · exact preparedReplicaRecoveryInputState_frame S xs tail 119 (by decide)
  · intro k hk _; exact recoveryInputs_factor_frame S xs tail k (Or.inr hk)

theorem factorPages_prepare_recovery_inputs {A : ℕ} (S : Stacks 255 A)
    (xs tail : List (Fin (A+4))) {bo hf df : List (Fin (A+4))}
    (h : PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S)) :
    PackedBoundaryFactorPages bo hf df
      (embStk (Fin.castLE (by decide : 242 ≤ 255)) (preparedReplicaRecoveryInputState S xs tail)) := by
  apply h.of_solution_frame
  intro k hk _
  exact recoveryInputs_factor_frame S xs tail k (Or.inr hk)

theorem couplingMasters_prepare_recovery_inputs {A P q w s t u band a b : ℕ}
    (S : Stacks 255 A) (xs tail : List (Fin (A+4)))
    (h : CouplingMasterHeaders P q w s t u band a b (embStk (Fin.castLE (by decide : 168 ≤ 255)) S)) :
    CouplingMasterHeaders P q w s t u band a b
      (embStk (Fin.castLE (by decide : 168 ≤ 255)) (preparedReplicaRecoveryInputState S xs tail)) := by
  apply h.of_frame
  intro k hk
  apply preparedReplicaRecoveryInputState_frame
  simp only [couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
  norm_num at hk ⊢
  omega

theorem couplingGeometry_prepare_recovery_inputs {A V s t band a b origin N : ℕ}
    (S : Stacks 255 A) (xs tail : List (Fin (A+4)))
    (h : CouplingIntervalMetadata V s t band a b origin N (embStk (Fin.castLE (by decide : 168 ≤ 255)) S)) :
    CouplingIntervalMetadata V s t band a b origin N
      (embStk (Fin.castLE (by decide : 168 ≤ 255)) (preparedReplicaRecoveryInputState S xs tail)) := by
  apply h.of_frame
  · exact preparedReplicaRecoveryInputState_frame S xs tail 163 (by decide)
  · intro k hk
    apply preparedReplicaRecoveryInputState_frame
    simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
    norm_num at hk ⊢
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
