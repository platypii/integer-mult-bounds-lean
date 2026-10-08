import IntegerMultBounds.Machine.ScalingPieceBridge

/-! Contiguous quotient pieces partition the complete payload in source order.
This is the final semantic bridge for inverse scaling by scatter/concatenate. -/
namespace IntegerMultBounds.Machine.ScalingPartitionData

variable {α : Type*}

/-- Every initial family of pieces concatenates to the exact boundary prefix. -/
theorem prefix_blocks {Q c : ℕ} (hc : 0 < c) (payload : ℕ → α) (n : ℕ) :
    ((List.range n).map (fun j => ScalingMergeData.blocks Q c j payload)).flatten =
      (List.range (ScalingControl.boundary Q c n)).map payload := by
  induction n with
  | zero => simp [ScalingControl.boundary_zero hc]
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.flatten_append]
    simp only [List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]
    rw [ih]
    unfold ScalingMergeData.blocks
    rw [← List.map_append,List.range_eq_range']
    have hm : ScalingControl.boundary Q c n ≤ ScalingControl.boundary Q c (n+1) := by
      have h := ScalingSplit.offset_mono (Q := Q) (B := 1) hc (Nat.le_succ n)
      simpa only [ScalingSplit.offset,Nat.mul_one] using h
    have h := List.range'_append (s := 0) (m := ScalingControl.boundary Q c n)
      (n := ScalingControl.boundary Q c (n+1)-ScalingControl.boundary Q c n) (step := 1)
    simp only [one_mul,zero_add,Nat.add_sub_of_le hm] at h
    rw [h,List.range_eq_range']

/-- All fixed-coefficient pieces recover the complete unpermuted list. -/
theorem blocks_flatten {Q c : ℕ} (hc : 0 < c) (payload : ℕ → α) :
    ((List.range c).map (fun j => ScalingMergeData.blocks Q c j payload)).flatten =
      (List.range Q).map payload := by
  simpa only [ScalingControl.boundary_last hc] using prefix_blocks hc payload c

/-- Fin-indexed physical buffer order agrees with the natural-index partition. -/
theorem blocks_ofFn {Q c : ℕ} (hc : 0 < c) (payload : ℕ → α) :
    (List.ofFn (fun j : Fin c => ScalingMergeData.blocks Q c j.val payload)).flatten =
      (List.range Q).map payload := by
  have he : List.ofFn (fun j : Fin c => ScalingMergeData.blocks Q c j.val payload) =
      (List.range c).map (fun j => ScalingMergeData.blocks Q c j payload) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [he,blocks_flatten hc]

/-- After inverse scatter, concatenation returns exactly multiplication by c
on input block indices, with each complete payload block unchanged. -/
theorem inverse_blocks {Q c : ℕ} (hc : 0 < c) (input : ℕ → List α) :
    (((List.range c).map (fun j =>
      ScalingMergeData.blocks Q c j (fun y => input (ScalingPieces.output Q c y)))).flatten).flatten =
      ((List.range Q).map (fun y => input (ScalingPieces.output Q c y))).flatten := by
  rw [blocks_flatten hc]

end IntegerMultBounds.Machine.ScalingPartitionData
