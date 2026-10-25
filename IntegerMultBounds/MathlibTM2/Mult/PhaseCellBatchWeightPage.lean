module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightBatchStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightPageModel
import Mathlib.Data.List.OfFn

/-! The grouped weight page has forward cell order, reversed output coordinates
within each cell, and forward input coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

def batchWeightPage (A w q P s t u B L : ℕ) (lo : ℕ → ℕ) : List (Fin (A + 4)) :=
  (List.range B).flatMap (fun n => outputWeightRow A w q P s t u L (lo n)) ++
    (List.range B).flatMap (fun n => inputWeightRow A w q P s t u L (lo n))

@[simp] theorem batchWeightPage_length (A w q P s t u B L : ℕ) (lo : ℕ → ℕ) :
    (batchWeightPage A w q P s t u B L lo).length = 2 * (B * (L * w)) := by
  simp [batchWeightPage, List.length_flatMap]
  ring

theorem reversedRowTable_eq_flatMap {K : Type*} (B L : ℕ) (f : ℕ → ℕ → K) :
    reversedRowTable B L f = (List.range B).flatMap (fun n => (List.range L).reverse.map (f n)) := by
  rw [reversedRowTable, List.ofFn_mul]
  have hrow (n : Fin B) :
      List.ofFn (fun i : Fin L => f ((n.val * L + i.val) / L) (L - 1 - (n.val * L + i.val) % L)) =
        (List.range L).reverse.map (f n.val) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hiL : i < L := by simpa using hi
      have hL : 0 < L := by omega
      have hdiv : (n.val * L + i) / L = n.val := by
        rw [Nat.add_comm, Nat.mul_comm n.val L, Nat.add_mul_div_left _ _ hL,
          Nat.div_eq_of_lt hiL, Nat.zero_add]
      simp [List.getElem_reverse, hdiv, Nat.add_mod, Nat.mod_eq_of_lt hiL]
  simp_rw [hrow]
  have hh : List.ofFn (fun n : Fin B => (List.range L).reverse.map (f n.val)) =
      (List.range B).map (fun n => (List.range L).reverse.map (f n)) := by
    simpa using (List.ofFn_getElem_eq_map (List.range B) (fun n => (List.range L).reverse.map (f n)))
  rw [hh]
  rfl

theorem batchWeightPage_eq_execution_tables (A w q s t p u B L : ℕ) [NeZero s]
    (lo : ℕ → ZMod s) :
    batchWeightPage A w q (2^15*p) s t u B L (fun n => (lo n).val) =
      cstream A w (outputWeightWords q (executedOutputTable s t p u B L lo)) ++
        cstream A w (reciprocalWeightWords q ((List.range B).flatMap (cellWeightRows s t p u L lo))) := by
  rw [executedOutputTable, reversedRowTable_eq_flatMap]
  simp only [batchWeightPage, outputWeightRow, inputWeightRow, outputWeightWords,
    reciprocalWeightWords, cellWeightRows, List.map_flatMap, cstream, List.flatMap_map,
    List.flatMap_assoc, List.map_map, Function.comp_def, ambientWeightSample_eq_weightData]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
