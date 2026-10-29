module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellInputBank

/-! Route only the factory's raw table away from the halo publication buffer.
Register 220 is unused by the flat numerical placement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

def packedBoundaryTableRouting : Fin 242 → Fin 242 := Equiv.swap 132 220

theorem packedBoundaryTableRouting_injective : Function.Injective packedBoundaryTableRouting :=
  (Equiv.swap 132 220).injective

theorem packedBoundaryFactorReg_ne_table (i : Fin 226) : packedBoundaryFactorReg i ≠ 220 := by
  intro he
  have hv := congrArg (fun j : Fin 242 => j.val) he
  unfold packedBoundaryFactorReg at hv
  split_ifs at hv <;> (try simp only at hv)
  all_goals omega

theorem packedBoundaryTableRouting_fixed (i : Fin 242) (h132 : i ≠ 132) (h220 : i ≠ 220) :
    packedBoundaryTableRouting i = i := by
  simp [packedBoundaryTableRouting,Equiv.swap_apply_def,h132,h220]

theorem packedBoundaryTableRouting_factor (r : RsbR) :
    packedBoundaryTableRouting (packedBoundaryFactorReg (preparedBoundaryCoreReg (boundaryFactorReg r))) =
      packedBoundaryFactorReg (preparedBoundaryCoreReg (boundaryFactorReg r)) := by
  apply packedBoundaryTableRouting_fixed
  · by_cases hr : r = .vk
    · subst r; decide
    · have hh := packedBoundaryFactorReg_high r hr
      intro he
      rw [he] at hh
      contradiction
  · exact packedBoundaryFactorReg_ne_table _

theorem packedBoundaryTableRouting_state {A : ℕ} (S : Stacks 242 A) :
    boundaryFactorState (embStk preparedBoundaryCoreReg
      (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S))) =
      boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)) := by
  funext r
  exact congrArg S.R (packedBoundaryTableRouting_factor r)

theorem packedBoundaryTableRouting_native {A : ℕ} (S : Stacks 242 A) :
    embStk ScalarPlacement.packedCellCoreReg
      (embStk packedHaloRuntimeReg (embStk packedBoundaryTableRouting S)) =
      embStk ScalarPlacement.packedCellCoreReg (embStk packedHaloRuntimeReg S) := by
  have hfixed (i : Fin 117) :
      packedBoundaryTableRouting (packedHaloRuntimeReg (ScalarPlacement.packedCellCoreReg i)) =
        packedHaloRuntimeReg (ScalarPlacement.packedCellCoreReg i) := by
    apply packedBoundaryTableRouting_fixed <;> intro he
    all_goals
      have hv := congrArg (fun j : Fin 242 => j.val) he
      have hi := i.isLt
      change i.val = _ at hv
      omega
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i; exact congrArg S.L (hfixed i)
  · funext i; exact congrArg S.R (hfixed i)

/-- The only left stack changed by routing a legacy factor view is its table port. -/
theorem packedBoundaryTableRouting_left {A : ℕ} (S : Stacks 242 A)
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg
      (embStk packedBoundaryTableRouting S)).L (preparedBoundaryCoreReg i) = [])
    (h132 : S.L 132 = []) :
    ∀ i : Fin 224, (embStk packedBoundaryFactorReg S).L (preparedBoundaryCoreReg i) = [] := by
  intro i
  by_cases hi : i = 132
  · subst i; exact h132
  have hne : packedBoundaryFactorReg (preparedBoundaryCoreReg i) ≠ 132 :=
    packedBoundaryFactorReg_injective.ne (show preparedBoundaryCoreReg i ≠ (132 : Fin 226) from by
      intro he
      apply hi
      apply Fin.ext
      exact congrArg (fun j : Fin 226 => j.val) he)
  have hf := packedBoundaryTableRouting_fixed _ hne (packedBoundaryFactorReg_ne_table _)
  simpa only [embStk,Function.comp_apply,hf] using hleft i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
