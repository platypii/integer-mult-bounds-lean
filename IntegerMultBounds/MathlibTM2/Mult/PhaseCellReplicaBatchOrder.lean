module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightPage

/-! Replica-major order for combined interior inputs and retained weight pages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

private theorem range_mul_flatMap {α : Type} (N B : ℕ) (f : ℕ → List α) :
    (List.range (N*B)).flatMap f =
      (List.range N).flatMap (fun r => (List.range B).flatMap (fun j => f (r*B+j))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul,List.range_add,List.flatMap_append,ih,List.range_succ,
      List.flatMap_append,List.flatMap_singleton,List.flatMap_map]

theorem replicaCell_index {B : ℕ} (hB : 0 < B) (r j : ℕ) (hj : j < B) :
    (r*B+j)%B = j ∧ (r*B+j)/B = r := by
  constructor
  · simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,Nat.zero_add,
      Nat.mod_eq_of_lt hj]
  · rw [Nat.mul_comm r B,Nat.add_comm,Nat.add_mul_div_left _ _ hB,Nat.div_eq_of_lt hj,Nat.zero_add]

/-- One combined numerical input has exactly the ordinary replica-major stream. -/
theorem replicaInteriorRows_eq {s : ℕ} (N B L : ℕ) (hB : 0 < B)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt) :
    (List.range (N*B)).flatMap
      (cellSourceRows L (fun n => lo (n%B)) (fun n => C (n/B))) =
    (List.range N).flatMap (fun r => (List.range B).flatMap
      (cellSourceRows L lo (fun _ => C r))) := by
  rw [range_mul_flatMap]
  apply List.flatMap_congr
  intro r _
  apply List.flatMap_congr
  intro j hj
  have hi := replicaCell_index hB r j (List.mem_range.mp hj)
  simp only [cellSourceRows,hi.1,hi.2]

private theorem range_const_flatMap {α : Type} (N : ℕ) (xs : List α) :
    (List.range N).flatMap (fun _ => xs) = (List.replicate N xs).flatten := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,ih,
      List.replicate_succ',List.flatten_append,List.flatten_singleton]

private theorem replicaRows_eq {α : Type} (N B : ℕ) (hB : 0 < B) (f : ℕ → List α) :
    (List.range (N*B)).flatMap (fun n => f (n%B)) =
      (List.replicate N ((List.range B).flatMap f)).flatten := by
  rw [range_mul_flatMap]
  calc
    _ = (List.range N).flatMap (fun _ => (List.range B).flatMap f) := by
      apply List.flatMap_congr
      intro r _
      apply List.flatMap_congr
      intro j hj
      rw [(replicaCell_index hB r j (List.mem_range.mp hj)).1]
    _ = _ := range_const_flatMap N _

/-- A replica-major origin tape repeats the one-key origin page. -/
theorem range_mod_flatMap_eq_replicate {α : Type} (N B : ℕ) (f : ℕ → List α) :
    (List.range (N*B)).flatMap (fun n => f (n%B)) =
      (List.replicate N ((List.range B).flatMap f)).flatten := by
  cases B with
  | zero => simp
  | succ B => exact replicaRows_eq N (B+1) (by omega) f

/-- Repeat the two numerical banks separately, preserving the cached ABI. -/
theorem batchWeightPage_replicas (A w q P s t u N B L : ℕ) (hB : 0 < B) (lo : ℕ → ℕ) :
    batchWeightPage A w q P s t u (N*B) L (fun n => lo (n%B)) =
      (List.replicate N ((List.range B).flatMap (fun j => outputWeightRow A w q P s t u L (lo j)))).flatten++
      (List.replicate N ((List.range B).flatMap (fun j => inputWeightRow A w q P s t u L (lo j)))).flatten := by
  unfold batchWeightPage
  exact congrArg₂ List.append
    (replicaRows_eq N B hB (fun j => outputWeightRow A w q P s t u L (lo j)))
    (replicaRows_eq N B hB (fun j => inputWeightRow A w q P s t u L (lo j)))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
