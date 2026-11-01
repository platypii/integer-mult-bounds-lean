module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedRecoveryPlan

/-! Placement of generated crop controls in cleared recovery workspace.
Only register wiring and separation facts are stored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

structure RecoveryCropPlacement {T : ℕ} (plan : ComputedRecoveryPlan T) where
  reg : Fin 19 → Fin T
  injective : Function.Injective reg
  masters : reg 0 = plan.master.masters 2 ∧ reg 1 = plan.master.masters 8 ∧ reg 2 = plan.master.masters 9
  replicas : reg 5 = plan.replicas
  source : reg 11 = plan.result
  scratch : ∀ k ∈ ([(6 : Fin 19),7,8,9,10,13,14,15,16,17,18]), reg k ∈ List.ofFn plan.work
  external : ∀ k ∈ ([(3 : Fin 19),4,12]), reg k ∉ List.ofFn plan.work ∧
    (∀ i, plan.master.masters i ≠ reg k) ∧ reg k ≠ plan.result

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
