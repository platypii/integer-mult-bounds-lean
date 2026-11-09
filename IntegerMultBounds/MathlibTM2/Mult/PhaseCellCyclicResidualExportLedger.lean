module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportCyclicResidualRows
import Mathlib.Tactic.Ring

/-! Residual export pays scalar setup once and linear packed traffic per RHS. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem exportCyclicResidualRowsCost_le (replicas n N w : ℕ) :
    exportCyclicResidualRowsCost replicas n N w ≤
      100*(n+N+1)*(w+1)+137*replicas*(n+N+1)*(w+1) := by
  have h := cyclicReplicaBoundaryBatchCost_le replicas n N w
  unfold exportCyclicResidualRowsCost initializedCyclicReplicaBoundaryBatchCost
    boundaryFoldCountersCost
  nlinarith only [h]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
