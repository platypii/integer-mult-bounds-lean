module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedRecoveryPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseMasterInput

/-! State-independent bills for generated raw recovery, including source setup
and retirement of the exported master bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {U : Type}

noncomputable def recoverySeedCopyCost (H : ReplicaHaloProblem s) (W N : ℕ) : ℕ :=
  (recoverySeedHeaderPorts.map (fun i => 4*recoverySeedHeader H W N i+4)).sum+1

theorem recoverySeedCopyCost_eq (H : ReplicaHaloProblem s) (W N : ℕ)
    (source work : Fin 392 → Fin T) (S : Stacks T A)
    (hvalues : ∀ i ∈ recoverySeedHeaderPorts, (S.R (source i)).length = recoverySeedHeader H W N i) :
    copyUnaryHeadersCost (fun k => (S.R k).length) (recoverySeedHeaderCopies source work) =
      recoverySeedCopyCost H W N := by
  simp only [copyUnaryHeadersCost,recoverySeedHeaderCopies,List.map_map,Function.comp_def,recoverySeedCopyCost]
  congr 2
  apply List.map_congr_left
  intro i hi
  rw [hvalues i hi]

noncomputable def recoveryDescriptorProductionCost (work : Fin 392 → Fin T) (r : RawRecoveryJob s) (N : ℕ) : ℕ :=
  prepareComplexRecoveryInputCost r.problem.span r.W N+
    13*(descriptorBankTape (placedDescriptorFields work (r.words (A := A)))).length+3

noncomputable def recoveryLifecycleTime (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (r : RawRecoveryJob s) (N : ℕ) : ℕ :=
  recoverySeedCopyCost r.problem r.W N+completeComplexRecoveryHeadersCost r.problem N+
    recoveryDescriptorProductionCost (A := A) work r N+rawRecoveryScheduleTimeBudget b work [r]+
    (9*(descriptorBankTape (placedDescriptorFields work (r.words (A := A)))).length+5)

noncomputable def recoveryLifecycleStock (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (r : RawRecoveryJob s) (N Cprog : ℕ) : ℕ :=
  2*recoverySeedCopyCost r.problem r.W N+18*completeComplexRecoveryHeadersCost r.problem N+
    2*recoveryDescriptorProductionCost (A := A) work r N+(Cprog+1)*rawRecoveryScheduleWorkspaceBudget b work [r]+
    (9*(descriptorBankTape (placedDescriptorFields work (r.words (A := A)))).length+5)

noncomputable def retireRecoveryMastersCost (H : ReplicaHaloProblem s) : ℕ :=
  2*(List.ofFn (recoveryMasterValues H)).sum+21

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
