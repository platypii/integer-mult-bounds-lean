module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseReplicaCouplingCaller

/-! Coupling's two row queues lie outside recovery's caller bank. Its factor
extension is disjoint from the complete coupling bank, by injectivity. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

theorem replicaRecoveryCallerCoupling_right {A : ℕ} (S : Stacks 389 A) (i : Fin 168) :
    S.R (replicaRecoveryCallerCoupling.bank i) =
      (embStk replicaRecoveryCallerNativeReg S).R (Fin.castLE (by decide) i) := by
  rw [replicaRecoveryCallerCoupling_bank]
  rfl

theorem replicaRecoveryCallerCoupling_runtime_view {A : ℕ} (S : Stacks 389 A) :
    embStk packedRecoveryRuntimeReg (embStk replicaRecoveryCallerNativeReg S) =
      embStk replicaRecoveryCallerCoupling.bank S := by
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
  · exact congrArg S.L (replicaRecoveryCallerCoupling_bank i).symm
  · exact (replicaRecoveryCallerCoupling_right S i).symm

theorem replicaRecoveryCallerCoupling_native_view {A : ℕ} (S : Stacks 389 A) :
    embStk weightCacheCoreReg (embStk replicaRecoveryCallerInterior.solver S) =
      embStk (Fin.castLE (by decide : 117 ≤ 248)) (embStk replicaRecoveryCallerNativeReg S) := by
  rw [← replicaRecoveryCallerCoupling.native_view]
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
  · exact congrArg S.L (replicaRecoveryCallerCoupling_bank (Fin.castLE (by decide) i))
  · exact replicaRecoveryCallerCoupling_right S (Fin.castLE (by decide) i)

theorem replicaRecoveryCallerReg_outputs_disjoint (i : Fin 259) :
    replicaRecoveryCallerReg i ≠ 247 ∧ replicaRecoveryCallerReg i ≠ 248 := by
  unfold replicaRecoveryCallerReg
  generalize recoveryBankSplit (recoveryPortOrder i) = k
  cases k with
  | inl k =>
    have h := ReplicaCouplingPlacement.standard_outputs_disjoint k
    constructor
    · intro he; exact h.1 (Fin.castLE_injective (by decide : 300 ≤ 389) he)
    · intro he; exact h.2 (Fin.castLE_injective (by decide : 300 ≤ 389) he)
  | inr k =>
    cases k with
    | inl k =>
      constructor <;> intro he <;> have hv := congrArg (fun i : Fin 389 => i.val) he
      all_goals change 300+k.val = _ at hv; norm_num at hv; omega
    | inr k => fin_cases k <;> decide

theorem replicaRecoveryCallerCoupling_outside_bank (k : Fin 259) (hk : 168 ≤ k.val)
    (i : Fin 168) : replicaRecoveryCallerCoupling.bank i ≠ replicaRecoveryCallerReg k := by
  rw [replicaRecoveryCallerCoupling_bank]
  intro he
  have hv := congrArg (fun k : Fin 259 => k.val) (replicaRecoveryCallerReg_injective he)
  have hi := i.isLt
  change i.val = k.val at hv
  omega

theorem replicaRecoveryCallerCoupling_extension_frame {A : ℕ} {S F : Stacks 389 A}
    (hframe : ∀ k, (∀ i, replicaRecoveryCallerCoupling.bank i ≠ k) →
      k ∉ [247,248,replicaRecoveryCallerInterior.gather 125] → F.R k = S.R k)
    (k : Fin 259) (hk : 168 ≤ k.val) (harchive : k ≠ 257) :
    F.R (replicaRecoveryCallerReg k) = S.R (replicaRecoveryCallerReg k) := by
  apply hframe _ (replicaRecoveryCallerCoupling_outside_bank k hk)
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨(replicaRecoveryCallerReg_outputs_disjoint k).1,
    (replicaRecoveryCallerReg_outputs_disjoint k).2,?_⟩
  intro he
  apply harchive
  apply replicaRecoveryCallerReg_injective
  exact he.trans replicaRecoveryCallerReg_residual.symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
