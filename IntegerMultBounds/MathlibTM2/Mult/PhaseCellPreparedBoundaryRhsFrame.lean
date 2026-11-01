module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace

/-! Replacing the current RHS and the owned solution/archive stack preserves
all shared factor data and numerical workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

/-- The row queue and published solution share the owned stack on port 238. -/
def preparedBoundaryRhsState {A : ℕ} (S : Stacks 242 A)
    (remaining rhs : List (Fin (A+4))) : Stacks 242 A :=
  {S with R := Function.update (Function.update S.R 238 remaining) 143 rhs}

theorem PackedPreparedBank.replace_rhs {A q w W N : ℕ} {S : Stacks 242 A}
    (h : PackedPreparedBank q w W N S) (remaining rhs : List (Fin (A+4))) :
    PackedPreparedBank q w W N (preparedBoundaryRhsState S remaining rhs) := by
  apply h.of_runtime_frame (F := preparedBoundaryRhsState S remaining rhs) rfl
  · intro k hk
    have h143 : k ≠ 143 := by intro he; subst k; omega
    have h238 : k ≠ 238 := by intro he; subst k; omega
    simp [preparedBoundaryRhsState,h143,h238]
  · simp [preparedBoundaryRhsState]
  · intro k hk h238
    have h143 : k ≠ 143 := by intro he; subst k; omega
    simp [preparedBoundaryRhsState,h143,h238]

theorem PackedBoundaryFactorPages.replace_rhs {A : ℕ} {S : Stacks 242 A}
    {bo hf df : List (Fin (A+4))} (h : PackedBoundaryFactorPages bo hf df S)
    (remaining rhs : List (Fin (A+4))) :
    PackedBoundaryFactorPages bo hf df (preparedBoundaryRhsState S remaining rhs) := by
  apply h.of_solution_frame
  intro k hk h238
  have h143 : k ≠ 143 := by intro he; subst k; omega
  simp [preparedBoundaryRhsState,h143,h238]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
