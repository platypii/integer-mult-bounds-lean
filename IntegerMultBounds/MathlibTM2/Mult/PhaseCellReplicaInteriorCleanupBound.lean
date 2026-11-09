module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseReplicaInteriorBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingNativeStock
public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks

/-! The second-interior eraser is the existing native coupling eraser under
placement. Reuse generated-bank cleanup bounds instead of enumerating tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack

theorem releaseReplicaInteriorBankCost_eq_native {T A : ℕ}
    (plan : ReplicaInteriorPlacement T) (S : Stacks T A) :
    releaseReplicaInteriorBankCost plan S = releaseReplicaCouplingNativeCost
      (extendStacks (by decide : 117 ≤ 248) (embStk weightCacheCoreReg (embStk plan.solver S))) := by
  have hread (i : Fin 117) :
      (extendStacks (by decide : 117 ≤ 248) (embStk weightCacheCoreReg (embStk plan.solver S))).R
        (Fin.castLE (by decide) i) = S.R (plan.solver (weightCacheCoreReg i)) := by
    exact congrArg (fun X : Stacks 117 A => X.R i)
      (embStk_extendStacks (by decide : 117 ≤ 248) (embStk weightCacheCoreReg (embStk plan.solver S)))
  unfold releaseReplicaInteriorBankCost releaseReplicaCouplingNativeCost
    replicaInteriorReleasePorts replicaCouplingNativePorts
  simp only [List.map_map,List.length_map,Function.comp_def,hread]

/-- Recovery may change payload tapes 93 and 110. Only the disposable native
ports must retain their frame for the cleanup charge to transfer. -/
theorem releaseReplicaInteriorBankCost_eq_of_disposable_frame {T T' A : ℕ}
    (plan : ReplicaInteriorPlacement T) (plan' : ReplicaInteriorPlacement T')
    (S : Stacks T A) (F : Stacks T' A)
    (hframe : ∀ i ∈ replicaCouplingNativeIndices,
      F.R (plan'.solver (weightCacheCoreReg i)) = S.R (plan.solver (weightCacheCoreReg i))) :
    releaseReplicaInteriorBankCost plan' F = releaseReplicaInteriorBankCost plan S := by
  have hm : replicaCouplingNativeIndices.map (fun i => (F.R (plan'.solver (weightCacheCoreReg i))).length) =
      replicaCouplingNativeIndices.map (fun i => (S.R (plan.solver (weightCacheCoreReg i))).length) := by
    apply List.map_congr_left
    intro i hi
    exact congrArg List.length (hframe i hi)
  unfold releaseReplicaInteriorBankCost replicaInteriorReleasePorts
  simp only [List.map_map,List.length_map,Function.comp_def]
  rw [hm]

theorem releaseReplicaInteriorBankCost_le_of_generated {T A : ℕ}
    (plan : ReplicaInteriorPlacement T) (S : Stacks T A)
    (P q w s t u band a b : ℕ) (borrowed output : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (hgenerated : ∀ i : Fin 117, S.R (plan.solver (weightCacheCoreReg i)) =
      counterR q w (replicaCouplingUnaryBank A P q w s t u band a b borrowed output inp out).R i) :
    releaseReplicaInteriorBankCost plan S ≤ replicaCouplingNativeCleanupBound P q w s t u band a b := by
  rw [releaseReplicaInteriorBankCost_eq_native]
  apply releaseReplicaCouplingNativeCost_le_of_generated _ P q w s t u band a b borrowed output inp out
  intro i
  have hread := congrArg (fun X : Stacks 117 A => X.R i)
    (embStk_extendStacks (by decide : 117 ≤ 248) (embStk weightCacheCoreReg (embStk plan.solver S)))
  exact hread.trans (hgenerated i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
