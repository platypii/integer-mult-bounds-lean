module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightPage

/-! Identify the two generated weight banks separately when inserting the raw
RHS between them. Both retain the original ambient phase coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

theorem outputWeightRows_eq_execution_table (A w q s t p u B L : ℕ) [NeZero s]
    (lo : ℕ → ZMod s) :
    (List.range B).flatMap (fun i => outputWeightRow A w q (2^15*p) s t u L (lo i).val) =
      cstream A w (outputWeightWords q (executedOutputTable s t p u B L lo)) := by
  rw [executedOutputTable, reversedRowTable_eq_flatMap]
  simp only [outputWeightRow, outputWeightWords, List.map_flatMap, cstream,
    List.flatMap_map, List.flatMap_assoc, List.map_map, Function.comp_def,
    ambientWeightSample_eq_weightData]

theorem inputWeightRows_eq_execution_table (A w q s t p u B L : ℕ) [NeZero s]
    (lo : ℕ → ZMod s) :
    (List.range B).flatMap (fun i => inputWeightRow A w q (2^15*p) s t u L (lo i).val) =
      cstream A w (reciprocalWeightWords q ((List.range B).flatMap (cellWeightRows s t p u L lo))) := by
  simp only [inputWeightRow, reciprocalWeightWords, cellWeightRows, List.map_flatMap,
    cstream, List.flatMap_map, List.flatMap_assoc, List.map_map, Function.comp_def,
    ambientWeightSample_eq_weightData]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
