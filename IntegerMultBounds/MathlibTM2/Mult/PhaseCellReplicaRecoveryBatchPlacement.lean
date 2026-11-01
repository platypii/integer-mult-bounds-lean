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

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
