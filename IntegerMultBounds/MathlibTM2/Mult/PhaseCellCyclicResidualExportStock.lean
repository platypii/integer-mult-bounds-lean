module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportCyclicResidualRows
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock

/-! The closed residual exporter performs linear stream work. Its fixed native
push allowance does not depend on geometry or replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

@[irreducible] def cyclicResidualExportPush {Q A : ℕ} {U : Type} : ℕ :=
  mnProgPush (exportCyclicResidualRows (P := Empty) (Q := Q) (A := A) (U := U))

theorem exportCyclicResidualRows_exec_within_of_exec {Q A : ℕ} {U : Type}
    {body : Empty → Pr Empty 234 Q A U} {v vf : HS 234 Q A U} {S F : Stacks 234 A}
    {steps replicas n N w : ℕ}
    (he : Exec body exportCyclicResidualRows (mk v S) steps (mk vf F))
    (htime : steps ≤ exportCyclicResidualRowsCost replicas n N w) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      cyclicResidualExportPush (Q := Q) (A := A) (U := U)*
        exportCyclicResidualRowsCost replicas n N w) depth
      exportCyclicResidualRows (mk v S) steps (mk vf F) := by
  have hnative : mnNativePushBound (cyclicResidualExportPush (Q := Q) (A := A) (U := U))
      (exportCyclicResidualRows (P := Empty) (Q := Q) (A := A) (U := U)) := by
    unfold cyclicResidualExportPush
    exact WordCmd.empty_native _
  apply mn_native_exec_within he _ hnative depth _
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ htime) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
