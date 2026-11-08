module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageBoundaryRealUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryPlacement
public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks

/-! Inverse folding reads only the old numerical core and four new scratch
left stacks. No condition on unrelated private left stacks is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A : ℕ}

theorem sharedPageBoundaryUnfoldReg_left (S : Stacks 240 A)
    (hcore : ∀ i : Fin 224, S.L (Fin.castLE (by decide) i) = [])
    (hnew : ∀ i : Fin 6, S.L ⟨234+i.val,by have := i.isLt; omega⟩ = []) :
    ∀ i : Fin 224, S.L (sharedPageBoundaryUnfoldReg i) = [] := by
  intro i
  unfold sharedPageBoundaryUnfoldReg
  split_ifs
  · exact hnew 0
  · exact hnew 1
  · exact hnew 2
  · exact hnew 3
  · exact hcore i

theorem extendedCyclicBoundaryUnfold_left (S : Stacks 834 A)
    (hcore : ∀ i : Fin 224,
      (embStk (Fin.castLE (by decide : 224 ≤ 234)) (embStk CyclicReplicaPlacement.factorReg S)).L i = []) :
    ∀ i : Fin 224, (extendStacks (by decide : 834 ≤ 840) S).L
      (CyclicRecoveryPlacement.bank (sharedPageBoundaryUnfoldReg i)) = [] := by
  apply sharedPageBoundaryUnfoldReg_left (embStk CyclicRecoveryPlacement.bank (extendStacks (by decide) S))
  · intro i
    have hview := CyclicRecoveryPlacement.bank_core_view (extendStacks (by decide : 834 ≤ 840) S)
    simp only [CyclicRecoveryPlacement.extend,embStk_extendStacks] at hview
    exact (congrArg (fun F : Stacks 224 A => F.L i) hview).trans (hcore i)
  · intro i
    change (extendStacks (by decide : 834 ≤ 840) S).L
      (CyclicRecoveryPlacement.bank ⟨234+i.val,by have := i.isLt; omega⟩) = []
    exact (extendStacks_fresh (by decide : 834 ≤ 840) S _ (by
      change 834 ≤ 600+(234+i.val)
      omega)).1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
