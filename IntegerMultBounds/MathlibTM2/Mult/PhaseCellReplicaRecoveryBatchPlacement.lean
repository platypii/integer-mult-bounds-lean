module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryCallerSetup

/-! Extend the established caller by three roles: computed RHS archive 389,
preparation counter 390 and assembled output 391. The old worker map is kept. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def replicaRecoveryPreparationCallerReg (i : Fin 258) : Fin 392 :=
  if h : i.val < 256 then Fin.castLE (by decide : 389 ≤ 392)
    (replicaRecoveryCallerReg ⟨i.val,by omega⟩)
  else ⟨389+(i.val-256),by have hi := i.isLt; omega⟩

theorem replicaRecoveryPreparationCallerReg_injective : Function.Injective replicaRecoveryPreparationCallerReg := by
  intro i j hij
  by_cases hi : i.val < 256 <;> by_cases hj : j.val < 256
  · simp only [replicaRecoveryPreparationCallerReg,dif_pos hi,dif_pos hj] at hij
    have hh := replicaRecoveryCallerReg_injective
      (Fin.castLE_injective (by decide : 389 ≤ 392) hij)
    exact Fin.ext (congrArg (fun k : Fin 259 => k.val) hh)
  · simp only [replicaRecoveryPreparationCallerReg,dif_pos hi,dif_neg hj] at hij
    have hv := congrArg (fun k : Fin 392 => k.val) hij
    have hb := (replicaRecoveryCallerReg ⟨i.val,by omega⟩).isLt
    change (replicaRecoveryCallerReg ⟨i.val,by omega⟩).val = 389+(j.val-256) at hv
    omega
  · simp only [replicaRecoveryPreparationCallerReg,dif_neg hi,dif_pos hj] at hij
    have hv := congrArg (fun k : Fin 392 => k.val) hij
    have hb := (replicaRecoveryCallerReg ⟨j.val,by omega⟩).isLt
    change 389+(i.val-256) = (replicaRecoveryCallerReg ⟨j.val,by omega⟩).val at hv
    omega
  · simp only [replicaRecoveryPreparationCallerReg,dif_neg hi,dif_neg hj] at hij
    apply Fin.ext
    have hv := congrArg (fun k : Fin 392 => k.val) hij
    change 389+(i.val-256) = 389+(j.val-256) at hv
    omega

theorem replicaRecoveryPreparationCallerReg_worker (i : Fin 255) :
    replicaRecoveryPreparationCallerReg (Fin.castLE (by decide : 255 ≤ 258) i) =
      Fin.castLE (by decide : 389 ≤ 392) (replicaRecoveryCallerWorkerReg i) := by
  have hi : (Fin.castLE (by decide : 255 ≤ 258) i).val < 256 := by have hh := i.isLt; dsimp; omega
  simp only [replicaRecoveryPreparationCallerReg,dif_pos hi]
  rfl

@[simp] theorem replicaRecoveryPreparationCallerReg_rhs : replicaRecoveryPreparationCallerReg 256 = 389 := by decide +kernel
@[simp] theorem replicaRecoveryPreparationCallerReg_count : replicaRecoveryPreparationCallerReg 257 = 390 := by decide +kernel
@[simp] theorem replicaRecoveryPreparationCallerReg_mask : replicaRecoveryPreparationCallerReg 254 = 386 := by decide +kernel
@[simp] theorem replicaRecoveryPreparationCallerReg_boundary : replicaRecoveryPreparationCallerReg 125 = 257 := by decide +kernel

theorem replicaRecoveryPreparationCallerReg_output_disjoint (i : Fin 258) :
    replicaRecoveryPreparationCallerReg i ≠ 391 := by
  intro he
  have hv := congrArg (fun k : Fin 392 => k.val) he
  by_cases hi : i.val < 256
  · simp only [replicaRecoveryPreparationCallerReg,dif_pos hi] at hv
    have hb := (replicaRecoveryCallerReg ⟨i.val,by omega⟩).isLt
    change (replicaRecoveryCallerReg ⟨i.val,by omega⟩).val = 391 at hv
    omega
  · simp only [replicaRecoveryPreparationCallerReg,dif_neg hi] at hv
    have hb := i.isLt
    change 389+(i.val-256) = 391 at hv
    omega

theorem replicaRecoveryPreparationCallerReg_gather_disjoint (i : Fin 258) (j : Fin 126) :
    replicaRecoveryPreparationCallerReg i ≠ Fin.castLE (by decide : 126 ≤ 392) j := by
  by_cases hi : i.val < 255
  · have heq : i = Fin.castLE (by decide : 255 ≤ 258) (⟨i.val,hi⟩ : Fin 255) := Fin.ext rfl
    rw [heq,replicaRecoveryPreparationCallerReg_worker]
    intro he
    apply replicaRecoveryCallerReg_worker_gather_disjoint ⟨i.val,hi⟩ j
    apply Fin.ext
    exact congrArg (fun k : Fin 392 => k.val) he
  by_cases h255 : i.val = 255
  · have heq : i = 255 := Fin.ext h255
    subst i
    intro he
    have hv := congrArg (fun k : Fin 392 => k.val) he
    have hj := j.isLt
    change 387 = j.val at hv
    omega
  · intro he
    have h256 : ¬i.val < 256 := by omega
    have hv := congrArg (fun k : Fin 392 => k.val) he
    simp only [replicaRecoveryPreparationCallerReg,dif_neg h256] at hv
    change 389+(i.val-256) = j.val at hv
    have hj := j.isLt
    omega

def replicaRecoveryBatchInterior : ReplicaInteriorPlacement 392 :=
  replicaRecoveryCallerInterior.reindex (Fin.castLE (by decide : 389 ≤ 392)) (Fin.castLE_injective _)

@[simp] theorem replicaRecoveryBatchInterior_gather (i : Fin 126) :
    replicaRecoveryBatchInterior.gather i = Fin.castLE (by decide : 126 ≤ 392) i := rfl

theorem replicaRecoveryPreparationCallerReg_native (i : Fin 117) :
    replicaRecoveryPreparationCallerReg (Fin.castLE (by decide : 117 ≤ 258) i) =
      replicaRecoveryBatchInterior.solver (Fin.castLE (by decide : 117 ≤ 121) i) := by
  have hi : (Fin.castLE (by decide : 117 ≤ 258) i).val < 256 := by have hh := i.isLt; dsimp; omega
  simp only [replicaRecoveryPreparationCallerReg,dif_pos hi]
  change Fin.castLE (by decide : 389 ≤ 392)
    (replicaRecoveryCallerReg (Fin.castLE (by decide : 168 ≤ 259) (Fin.castLE (by decide : 117 ≤ 168) i))) = _
  rw [replicaRecoveryCallerReg_native]
  change Fin.castLE (by decide : 300 ≤ 392)
    (ReplicaCouplingPlacement.standard.bank (Fin.castLE (by decide : 117 ≤ 168) i)) = _
  unfold ReplicaCouplingPlacement.bank
  rw [dif_pos (show (Fin.castLE (by decide : 117 ≤ 168) i).val < 117 from i.isLt)]
  rfl

theorem replicaRecoveryCallerReg_gap (i : Fin 259) :
    (replicaRecoveryCallerReg i).val < 243 ∨ 249 ≤ (replicaRecoveryCallerReg i).val := by
  change (recoveryBankSum (recoveryBankSplit (recoveryPortOrder i))).val < 243 ∨
    249 ≤ (recoveryBankSum (recoveryBankSplit (recoveryPortOrder i))).val
  cases hs : recoveryBankSplit (recoveryPortOrder i) with
  | inl k =>
    change (ReplicaCouplingPlacement.standard.bank k).val < 243 ∨
      249 ≤ (ReplicaCouplingPlacement.standard.bank k).val
    unfold ReplicaCouplingPlacement.bank
    split
    · left
      change 126+k.val < 243
      omega
    · right
      change 249+(k.val-117) ≥ 249
      omega
  | inr k =>
    cases k with
    | inl k => right; change 249 ≤ 300+k.val; omega
    | inr k => fin_cases k <;> left <;> decide

theorem replicaRecoveryPreparationCallerReg_gap (i : Fin 258) :
    (replicaRecoveryPreparationCallerReg i).val < 243 ∨ 249 ≤ (replicaRecoveryPreparationCallerReg i).val := by
  by_cases hi : i.val < 256
  · simpa only [replicaRecoveryPreparationCallerReg,dif_pos hi,Fin.val_castLE] using
      replicaRecoveryCallerReg_gap ⟨i.val,by omega⟩
  · right
    change 249 ≤ (replicaRecoveryPreparationCallerReg i).val
    simp only [replicaRecoveryPreparationCallerReg,dif_neg hi]
    omega

theorem replicaRecoveryPreparationCallerReg_reserved (i : Fin 258) (j : Fin 121) (hj : 117 ≤ j.val) :
    replicaRecoveryPreparationCallerReg i ≠ replicaRecoveryBatchInterior.solver j := by
  intro he
  have hv := congrArg (fun k : Fin 392 => k.val) he
  change (replicaRecoveryPreparationCallerReg i).val = 126+j.val at hv
  have hg := replicaRecoveryPreparationCallerReg_gap i
  have hb := j.isLt
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
