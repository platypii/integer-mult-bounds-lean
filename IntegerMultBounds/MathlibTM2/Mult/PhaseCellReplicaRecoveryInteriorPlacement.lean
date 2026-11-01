module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchPlacement

/-! The second pass needs only the original interior banks, its output and the
computed RHS archive. All boundary, factor and assembly storage is spectator. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def replicaRecoverySmallInterior : ReplicaInteriorPlacement 249 :=
  ReplicaInteriorPlacement.standard.reindex (Fin.castLE (by decide : 247 ≤ 249)) (Fin.castLE_injective _)

def replicaRecoveryInteriorCallerReg (i : Fin 249) : Fin 392 :=
  if h : i.val < 248 then ⟨i.val,by omega⟩ else 389

theorem replicaRecoveryInteriorCallerReg_injective : Function.Injective replicaRecoveryInteriorCallerReg := by
  intro i j hij
  by_cases hi : i.val < 248 <;> by_cases hj : j.val < 248
  · have hv := congrArg (fun k : Fin 392 => k.val) hij
    simp only [replicaRecoveryInteriorCallerReg,dif_pos hi,dif_pos hj] at hv
    exact Fin.ext hv
  · have hv := congrArg (fun k : Fin 392 => k.val) hij
    simp only [replicaRecoveryInteriorCallerReg,dif_pos hi,dif_neg hj] at hv
    change i.val = 389 at hv
    omega
  · have hv := congrArg (fun k : Fin 392 => k.val) hij
    simp only [replicaRecoveryInteriorCallerReg,dif_neg hi,dif_pos hj] at hv
    change 389 = j.val at hv
    omega
  · apply Fin.ext
    have hib := i.isLt
    have hjb := j.isLt
    omega

theorem replicaRecoveryInteriorCallerReg_gather (i : Fin 126) :
    replicaRecoveryInteriorCallerReg (replicaRecoverySmallInterior.gather i) = replicaRecoveryBatchInterior.gather i := by
  have hi : (replicaRecoverySmallInterior.gather i).val < 248 := by change i.val < 248; have hh := i.isLt; omega
  simp only [replicaRecoveryInteriorCallerReg,dif_pos hi]
  rfl

theorem replicaRecoveryInteriorCallerReg_solver (i : Fin 121) :
    replicaRecoveryInteriorCallerReg (replicaRecoverySmallInterior.solver i) = replicaRecoveryBatchInterior.solver i := by
  have hi : (replicaRecoverySmallInterior.solver i).val < 248 := by change 126+i.val < 248; have hh := i.isLt; omega
  simp only [replicaRecoveryInteriorCallerReg,dif_pos hi]
  rfl

@[simp] theorem replicaRecoveryInteriorCallerReg_source : replicaRecoveryInteriorCallerReg 248 = 389 := by decide +kernel
@[simp] theorem replicaRecoveryInteriorCallerReg_output : replicaRecoveryInteriorCallerReg 247 = 247 := by decide +kernel

theorem replicaRecoveryInteriorCallerReg_spectator (i : Fin 249) (k : Fin 392)
    (hk : 248 ≤ k.val) (h389 : k ≠ 389) : replicaRecoveryInteriorCallerReg i ≠ k := by
  intro he
  by_cases hi : i.val < 248
  · have hv := congrArg (fun k : Fin 392 => k.val) he
    simp only [replicaRecoveryInteriorCallerReg,dif_pos hi] at hv
    change i.val = k.val at hv
    omega
  · have hh : replicaRecoveryInteriorCallerReg i = 389 := by simp [replicaRecoveryInteriorCallerReg,hi]
    exact h389 (he.symm.trans hh)

theorem replicaRecoveryInteriorCaller_gather_view {A : ℕ} (S : Stacks 392 A) :
    embStk replicaRecoverySmallInterior.gather (embStk replicaRecoveryInteriorCallerReg S) =
      embStk replicaRecoveryBatchInterior.gather S := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i; exact congrArg S.L (replicaRecoveryInteriorCallerReg_gather i)
  · funext i; exact congrArg S.R (replicaRecoveryInteriorCallerReg_gather i)

theorem replicaRecoveryInteriorCaller_solver_view {A : ℕ} (S : Stacks 392 A) :
    embStk replicaRecoverySmallInterior.solver (embStk replicaRecoveryInteriorCallerReg S) =
      embStk replicaRecoveryBatchInterior.solver S := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i; exact congrArg S.L (replicaRecoveryInteriorCallerReg_solver i)
  · funext i; exact congrArg S.R (replicaRecoveryInteriorCallerReg_solver i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
