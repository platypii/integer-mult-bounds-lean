module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryPhaseBank

/-! Prepared factors already supply their arithmetic left workspace. Only the
displaced mask and new private registers need separate left-bank freshness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

theorem PackedBoundarySolveWorkspace.left_low {A q : ℕ} {S : Stacks 242 A}
    (h : PackedBoundarySolveWorkspace q S) (i : Fin 140) : S.L ⟨i.val,by omega⟩ = [] := by
  have hh := h.left ⟨i.val,by omega⟩
  change S.L (packedBoundaryFactorReg (preparedBoundaryCoreReg ⟨i.val,by omega⟩)) = [] at hh
  have hi := i.isLt
  have hp : packedBoundaryFactorReg (preparedBoundaryCoreReg ⟨i.val,by omega⟩) = (⟨i.val,by omega⟩ : Fin 242) := by
    simp [preparedBoundaryCoreReg,packedBoundaryFactorReg,Fin.ext_iff,
      show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,show i.val ≠ 206 by omega,
      show i.val < 154 by omega]
  rw [hp] at hh
  exact hh

namespace ScalarPlacement
theorem replicaBoundaryPhase_left_of_bank {A q w W N : ℕ} (S : Stacks 255 A)
    (hbank : PackedPreparedBank q w W N (embStk (Fin.castLE (by decide : 242 ≤ 255)) S))
    (hmask : S.L 167 = []) (hprivate : ∀ k : Fin 255, 248 ≤ k.val → S.L k = []) :
    ∀ i : Fin 242, S.L (Fin.castLE (by decide) i) = S.L (replicaBoundaryPhaseReg i) := by
  intro i
  by_cases hi : i ∈ ([117,118,120,123,124,116,167] : List (Fin 242))
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hbank.workspace.left_low 117).trans (hprivate 248 (by decide)).symm
    · exact (hbank.workspace.left_low 118).trans (hprivate 249 (by decide)).symm
    · exact (hbank.workspace.left_low 120).trans (hprivate 250 (by decide)).symm
    · exact (hbank.workspace.left_low 123).trans (hprivate 251 (by decide)).symm
    · exact (hbank.workspace.left_low 124).trans (hprivate 252 (by decide)).symm
    · exact (hbank.workspace.left_low 116).trans (hprivate 253 (by decide)).symm
    · exact hmask.trans (hprivate 254 (by decide)).symm
  · rw [replicaBoundaryPhaseReg_fixed i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      tauto)]

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
