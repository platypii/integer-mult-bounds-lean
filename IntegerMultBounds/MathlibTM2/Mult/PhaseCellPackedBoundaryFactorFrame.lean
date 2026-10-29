module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPreparedResidualSolve

/-! Any low-bank halo producer preserves the retained numerical factor state,
except for the RHS it installs on 143. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

/-- All factor roles except the input RHS lie above the packed halo bank. -/
theorem packedBoundaryFactorReg_high (r : RsbR) (hr : r ≠ .vk) :
    168 ≤ (packedBoundaryFactorReg (preparedBoundaryCoreReg (boundaryFactorReg r))).val := by
  cases r <;> first | decide | (exact False.elim (hr rfl)) | (rename_i c; cases c <;> decide)

theorem packedBoundaryFactorState_of_high_frame {A : ℕ} (S F : Stacks 242 A)
    (hframe : ∀ k : Fin 242, 168 ≤ k.val → F.R k = S.R k) :
    boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F)) =
      Function.update
        (boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)))
        .vk (F.R 143) := by
  funext r
  by_cases hr : r = .vk
  · subst r; simp [boundaryFactorState,embStk,preparedBoundaryCoreReg,
      packedBoundaryFactorReg,boundaryFactorReg]
  · rw [Function.update_of_ne hr]
    exact hframe _ (packedBoundaryFactorReg_high r hr)

/-- A halo execution need only preserve the high bank to retain solve readiness. -/
theorem packedBoundarySolveReady_of_high_frame {A q w W N : ℕ} (S F : Stacks 242 A)
    (hframe : ∀ k : Fin 242, 168 ≤ k.val → F.R k = S.R k)
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S))) q w W N) :
    BoundarySolveReady (boundaryFactorState
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F))) q w W N := by
  rw [packedBoundaryFactorState_of_high_frame S F hframe]
  exact hready.update_vk _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
