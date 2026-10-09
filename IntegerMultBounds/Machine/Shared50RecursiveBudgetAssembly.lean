import IntegerMultBounds.Machine.Shared50RecursiveBudget

/-! Absorb the fully charged physical node trace into the recursive budget.
Arithmetic is checked symbolically before specializing the fixed coefficients. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveBudgetAssembly
noncomputable section
open Networks
open Shared50TapeGlobal (roleCount)
open Shared50RecursiveBudget (budget node)
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50RecursiveCallLayout.parked
  RecursiveRowsNode.rowConstant RecursiveRowsNodeRoleBank.constant Shared50Parameters.s

/-- All fixed joins and return costs are paid from positive logical volume. -/
theorem assembly {E X T V R S C H k : ℕ} (hV : 0 < V) (hR : R ≤ V)
    (hH : H ≤ 127*V) :
    (E+X)*V+T*R+S*C+H+k+8 ≤ (E+X+T+135+k)*V+S*C := by
  have hT := Nat.mul_le_mul_left T hR
  have hk := Nat.mul_le_mul_left (k+8) hV
  nlinarith

theorem coefficients (k : ℕ) : node k =
    (74+RecursiveRowsNode.rowConstant roleCount+RecursiveRowsNodeRoleBank.constant roleCount)+
      (128+RecursiveRowsNode.rowConstant roleCount)+
      (Shared50PieceSchedule.pieces.map (Shared50RecursivePieceExecution.overhead k)).sum+135+k := rfl

/-- The exact bound of the actual guard-to-return node trace meets the same
natural budget used by the recursive child induction. -/
theorem node_bound (k depth V R H : ℕ) (hV : 0 < V) (hR : R ≤ V)
    (hH : H ≤ 127*V) :
    ((74+RecursiveRowsNode.rowConstant roleCount+RecursiveRowsNodeRoleBank.constant roleCount)+
      (128+RecursiveRowsNode.rowConstant roleCount))*V+
      (Shared50PieceSchedule.pieces.map (Shared50RecursivePieceExecution.overhead k)).sum*R+
      Shared50Parameters.s*budget k depth (V/roleCount)+H+k+8 ≤ budget k (depth+1) V := by
  rw [Shared50RecursiveBudget.budget.eq_2,coefficients]
  exact assembly (E := 74+RecursiveRowsNode.rowConstant roleCount+RecursiveRowsNodeRoleBank.constant roleCount)
    (X := 128+RecursiveRowsNode.rowConstant roleCount)
    (T := (Shared50PieceSchedule.pieces.map (Shared50RecursivePieceExecution.overhead k)).sum)
    (S := Shared50Parameters.s) (C := budget k depth (V/roleCount)) (k := k) hV hR hH

end
end IntegerMultBounds.Machine.Shared50RecursiveBudgetAssembly
