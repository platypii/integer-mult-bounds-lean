module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryMasks
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock

/-! Closed native mask setup, shared by original and recovery passes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

@[irreducible] def replicaBoundaryMaskPush {Q A : ℕ} {U : Type} : ℕ :=
  mnProgPush (metadataBoundaryMask (P := Empty) (Q := Q) (A := A) (U := U))

theorem placedReplicaBoundaryMask_native {T Q A : ℕ} {P U : Type}
    (bank : Fin 168 → Fin T) (dst : Fin T) :
    mnNativePushBound (replicaBoundaryMaskPush (Q := Q) (A := A) (U := U))
      (placedReplicaBoundaryMask (P := P) (Q := Q) (A := A) (U := U) bank dst) := by
  unfold replicaBoundaryMaskPush
  exact embProg_native (replicaBoundaryMaskPort bank dst) Empty.elim _ (WordCmd.empty_native _)

theorem cyclicReplicaBoundaryMasks_native {T Q A : ℕ} {P U : Type}
    (leftBank rightBank : Fin 168 → Fin T) (leftDst rightDst : Fin T) :
    mnNativePushBound (replicaBoundaryMaskPush (Q := Q) (A := A) (U := U))
      (cyclicReplicaBoundaryMasks (P := P) (Q := Q) (A := A) (U := U) leftBank rightBank leftDst rightDst) :=
  ⟨placedReplicaBoundaryMask_native _ _,placedReplicaBoundaryMask_native _ _⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
