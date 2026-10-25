module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedData

/-! The generated single-cell page is the existing execution model's exact
output-weight table followed by its reciprocal input-weight row. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

theorem executedOutputTable_single (s t p u L : ℕ) (lo : ZMod s) :
    executedOutputTable s t p u 1 L (fun _ => lo) =
      (List.range L).reverse.map (weightData s t p u lo) := by
  apply List.ext_getElem
  · simp [executedOutputTable]
  · intro i hi hi'
    have hiL : i < L := by simpa [executedOutputTable] using hi
    simp [executedOutputTable, reversedRowTable, List.getElem_reverse,
      Nat.mod_eq_of_lt hiL]

theorem weightPage_eq_execution_tables (A w q s t p u L : ℕ) [NeZero s] (lo : ZMod s) :
    weightPage A w q (2 ^ 15 * p) s t u lo.val L =
      cstream A w (outputWeightWords q (executedOutputTable s t p u 1 L (fun _ => lo))) ++
        cstream A w (reciprocalWeightWords q (cellWeightRows s t p u L (fun _ => lo) 0)) := by
  rw [executedOutputTable_single]
  simp only [weightPage, outputWeightWords, reciprocalWeightWords, cellWeightRows,
    List.map_map, Function.comp_def, ambientWeightSample_eq_weightData]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
