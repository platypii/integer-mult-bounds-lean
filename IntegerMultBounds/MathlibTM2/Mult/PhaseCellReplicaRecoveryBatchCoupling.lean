module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaCouplingRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingRecoveryFrame

/-! The first pass's coupling bank and the cached recovery worker are the same
physical bank. Factor extension ports are outside the entire interior/coupling
footprint, so the first pass can retain the generated factor pages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A : ℕ}

def replicaRecoveryBatchCoupling : ReplicaCouplingPlacement replicaRecoveryBatchInterior :=
  replicaRecoveryCallerCoupling.reindex (Fin.castLE (by decide : 389 ≤ 392)) (Fin.castLE_injective _)

theorem replicaRecoveryBatchCoupling_bank (i : Fin 168) :
    replicaRecoveryBatchCoupling.bank i = replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide) i) := by
  have hb := ReplicaCouplingPlacement.reindex_bank replicaRecoveryCallerCoupling
    (Fin.castLE (by decide : 389 ≤ 392)) (Fin.castLE_injective _) i
  change replicaRecoveryBatchCoupling.bank i = Fin.castLE (by decide : 389 ≤ 392) (replicaRecoveryCallerCoupling.bank i) at hb
  rw [hb,replicaRecoveryCallerCoupling_bank]
  exact (replicaRecoveryPreparationCallerReg_worker (Fin.castLE (by decide : 168 ≤ 255) i)).symm

theorem replicaRecoveryBatchCoupling_runtime_view (S : Stacks 392 A) :
    embStk packedRecoveryRuntimeReg (embStk replicaRecoveryPreparationNativeReg S) =
      embStk replicaRecoveryBatchCoupling.bank S := by
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
  · exact congrArg S.L (replicaRecoveryBatchCoupling_bank i).symm
  · exact congrArg S.R (replicaRecoveryBatchCoupling_bank i).symm

theorem replicaRecoveryBatchCoupling_native_view (S : Stacks 392 A) :
    embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver S) =
      embStk (Fin.castLE (by decide : 117 ≤ 248)) (embStk replicaRecoveryPreparationNativeReg S) := by
  rw [← replicaRecoveryBatchCoupling.native_view]
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
  · exact congrArg S.L (replicaRecoveryBatchCoupling_bank (Fin.castLE (by decide : 117 ≤ 168) i))
  · exact congrArg S.R (replicaRecoveryBatchCoupling_bank (Fin.castLE (by decide : 117 ≤ 168) i))

/-- High recovery worker ports are outside both the numerical core and its cache. -/
theorem replicaRecoveryBatchInterior_solver_worker_disjoint (k : Fin 257) (hk : 117 ≤ k.val)
    (j : Fin 121) : replicaRecoveryBatchInterior.solver j ≠ replicaRecoveryPreparationCallerWorkerReg k := by
  have hinj : Function.Injective replicaRecoveryPreparationCallerWorkerReg :=
    replicaRecoveryPreparationCallerReg_injective.comp (Fin.castLE_injective _)
  intro he
  by_cases hj : j.val < 117
  · have hnative := replicaRecoveryPreparationCallerReg_native (⟨j.val,hj⟩ : Fin 117)
    have heq : replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 117 ≤ 257) ⟨j.val,hj⟩) =
        replicaRecoveryBatchInterior.solver j := hnative
    have hv := congrArg (fun i : Fin 257 => i.val) (hinj (heq.trans he))
    change j.val = k.val at hv
    omega
  · exact replicaRecoveryPreparationCallerReg_reserved _ j (by omega) he.symm

/-- Structural spectators for the first interior pass and its residual coupling. -/
theorem replicaRecoveryBatchCoupling_factor_extension_frame {S F : Stacks 392 A}
    (hframe : ∀ k, (∀ i, replicaRecoveryBatchCoupling.bank i ≠ k) →
      (∀ i, replicaRecoveryBatchInterior.gather i ≠ k) →
      (∀ i, replicaRecoveryBatchInterior.solver i ≠ k) →
      (247 : Fin 392) ≠ k → (248 : Fin 392) ≠ k → F.R k = S.R k)
    (k : Fin 257) (hk : 168 ≤ k.val) :
    F.R (replicaRecoveryPreparationCallerWorkerReg k) = S.R (replicaRecoveryPreparationCallerWorkerReg k) := by
  have hinj : Function.Injective replicaRecoveryPreparationCallerWorkerReg :=
    replicaRecoveryPreparationCallerReg_injective.comp (Fin.castLE_injective _)
  apply hframe
  · intro i he
    rw [replicaRecoveryBatchCoupling_bank] at he
    have hv := congrArg (fun j : Fin 257 => j.val) (hinj he)
    have hi := i.isLt
    change i.val = k.val at hv
    omega
  · intro j he
    exact (replicaRecoveryPreparationCallerReg_gather_disjoint _ j) he.symm
  · exact fun j => replicaRecoveryBatchInterior_solver_worker_disjoint k (by omega) j
  · intro he
    have hv := congrArg Fin.val he
    have hg := replicaRecoveryPreparationCallerReg_gap (Fin.castLE (by decide : 257 ≤ 258) k)
    change 247 = (replicaRecoveryPreparationCallerReg (Fin.castLE (by decide : 257 ≤ 258) k)).val at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    have hg := replicaRecoveryPreparationCallerReg_gap (Fin.castLE (by decide : 257 ≤ 258) k)
    change 248 = (replicaRecoveryPreparationCallerReg (Fin.castLE (by decide : 257 ≤ 258) k)).val at hv
    omega

/-- Left spectators cover all high worker ports, including private recovery buffers. -/
theorem replicaRecoveryBatchCoupling_worker_left_frame {S F : Stacks 392 A}
    (hframe : ∀ k, (∀ i, replicaRecoveryBatchInterior.gather i ≠ k) →
      (∀ i, replicaRecoveryBatchInterior.solver i ≠ k) → (247 : Fin 392) ≠ k → F.L k = S.L k)
    (k : Fin 257) (hk : 117 ≤ k.val) :
    F.L (replicaRecoveryPreparationCallerWorkerReg k) = S.L (replicaRecoveryPreparationCallerWorkerReg k) := by
  apply hframe
  · intro j he
    exact replicaRecoveryPreparationCallerReg_gather_disjoint _ j he.symm
  · exact fun j => replicaRecoveryBatchInterior_solver_worker_disjoint k hk j
  · intro he
    have hv := congrArg Fin.val he
    have hg := replicaRecoveryPreparationCallerReg_gap (Fin.castLE (by decide : 257 ≤ 258) k)
    change 247 = (replicaRecoveryPreparationCallerReg (Fin.castLE (by decide : 257 ≤ 258) k)).val at hv
    omega

/-- Restored native left stacks and structural spectators preserve the complete
factor workspace through the first interior pass and residual coupling. -/
theorem replicaRecoveryBatchCoupling_factor_left_frame {S F : Stacks 392 A}
    (hnative : (embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver F)).L =
      (embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver S)).L)
    (hframe : ∀ k, (∀ i, replicaRecoveryBatchInterior.gather i ≠ k) →
      (∀ i, replicaRecoveryBatchInterior.solver i ≠ k) → (247 : Fin 392) ≠ k → F.L k = S.L k) :
    (embStk replicaRecoveryBoundaryFactoryReg F).L = (embStk replicaRecoveryBoundaryFactoryReg S).L := by
  rw [replicaRecoveryBatchCoupling_native_view F,replicaRecoveryBatchCoupling_native_view S] at hnative
  funext k
  by_cases hk : k.val < 117
  · exact congrFun hnative ⟨k.val,hk⟩
  · exact replicaRecoveryBatchCoupling_worker_left_frame hframe
      (Fin.castLE (by decide : 242 ≤ 257) k) (by change 117 ≤ k.val; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
