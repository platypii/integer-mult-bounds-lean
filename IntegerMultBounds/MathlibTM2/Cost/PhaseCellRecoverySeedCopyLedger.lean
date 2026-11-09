module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedRecoveryBudgets
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryMasterValues

/-! Replica-count accounting for ordinary seed headers, independent of the
computed recovery schedule and its publication proofs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s : ℕ} [NeZero s]

theorem recoverySeedCopyCost_zero_eq (H : ReplicaHaloProblem s) (W : ℕ) :
    recoverySeedCopyCost H W 0 = 4*(List.ofFn (recoveryMasterValues H)).sum+4*H.p+4*W+53 := by
  simp [recoverySeedCopyCost,recoverySeedHeaderPorts,complexRecoveryHeaderPorts,derivedRecoveryHeaderPorts,
    recoverySeedHeader,complexRecoveryHeader,generatedRecoveryHeader,replicaFactoryHeaderValue,
    recoveryMasterValues,masterHeaderValues,List.ofFn_succ]
  ring

private theorem recoverySeedHeader_affine (H : ReplicaHaloProblem s) (W N : ℕ) (k : Fin 392) :
    recoverySeedHeader H W N k = recoverySeedHeader H W 0 k+(if k = 390 then N else 0) := by
  by_cases hk : k = 390
  · subst k; simp [recoverySeedHeader,derivedRecoveryHeaderPorts,complexRecoveryHeader]
  · simp only [recoverySeedHeader,complexRecoveryHeader,hk,ite_false,Nat.add_zero]

theorem recoverySeedCopyCost_affine (H : ReplicaHaloProblem s) (W N : ℕ) :
    recoverySeedCopyCost H W N = recoverySeedCopyCost H W 0+4*N := by
  have hterm (k : Fin 392) : 4*recoverySeedHeader H W N k+4 =
      (4*recoverySeedHeader H W 0 k+4)+(if k = 390 then 4*N else 0) := by
    rw [recoverySeedHeader_affine]
    split_ifs <;> ring
  unfold recoverySeedCopyCost
  simp_rw [hterm]
  rw [List.sum_map_add]
  have hs : (recoverySeedHeaderPorts.map (fun k => if k = 390 then 4*N else 0)).sum = 4*N := by
    simp [recoverySeedHeaderPorts,complexRecoveryHeaderPorts,derivedRecoveryHeaderPorts]
  rw [hs]
  omega

end IntegerMultBounds.MathlibTM2.Cost
