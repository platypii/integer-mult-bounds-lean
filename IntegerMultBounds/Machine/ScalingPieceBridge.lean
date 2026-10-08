import IntegerMultBounds.Machine.ScalingSplit
import IntegerMultBounds.Machine.ScalingMergeData
import IntegerMultBounds.Machine.BlockRotationData

/-! Representation bridge between literal flat-tape splitting and the FIFO
block-stream merge. This equality preserves each block's complete payload. -/
namespace IntegerMultBounds.Machine.ScalingPieceBridge

private theorem interval_volume {Q B start len : ℕ} (payload : ℕ → List (Fin 4))
    (hw : ∀ i < Q, (payload i).length = B) (hb : start+len ≤ Q) :
    ((List.range' start len).map payload).flatten.length = len*B := by
  rw [BlockRotationData.uniform_volume B _]
  · simp
  · intro block hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    have hi := List.mem_range'.mp hi
    exact hw i (by omega)

/-- Cutting between block boundaries produces precisely the corresponding
contiguous block stream, including empty pieces and zero-width blocks. -/
theorem interval_eq {Q B lo hi : ℕ} (payload : ℕ → List (Fin 4))
    (hw : ∀ i < Q, (payload i).length = B) (hlh : lo ≤ hi) (hhQ : hi ≤ Q) :
    (((List.range Q).map payload).flatten.drop (lo*B)).take (hi*B-lo*B) =
      ((List.range' lo (hi-lo)).map payload).flatten := by
  have hparts : List.range Q = List.range' 0 lo ++
      (List.range' lo (hi-lo) ++ List.range' hi (Q-hi)) := by
    have hfirst := List.range'_append (s := 0) (m := lo) (n := hi-lo) (step := 1)
    have hsecond := List.range'_append (s := 0) (m := hi) (n := Q-hi) (step := 1)
    simp only [one_mul,zero_add,Nat.add_sub_of_le hlh] at hfirst
    simp only [one_mul,zero_add,Nat.add_sub_of_le hhQ] at hsecond
    rw [← List.append_assoc,hfirst,hsecond,List.range_eq_range']
  have hp := interval_volume payload hw (show 0+lo ≤ Q by omega)
  have hm := interval_volume payload hw (show lo+(hi-lo) ≤ Q by omega)
  rw [hparts,List.map_append,List.map_append,List.flatten_append,List.flatten_append]
  rw [← hp,List.drop_left]
  have he : hi*B-lo*B = (hi-lo)*B := (Nat.sub_mul hi lo B).symm
  rw [hp,he,← hm,List.take_left]

/-- The exact flat words written by ScalingSplit are the exact input streams
read by ScalingMerge, without reversal or reinterpretation of payload cells. -/
theorem piece_eq_blocks {Q c B : ℕ} (hc : 0 < c) (j : Fin c)
    (payload : ℕ → List (Fin 4)) (hw : ∀ i < Q, (payload i).length = B) :
    ScalingSplit.piece Q c B ((List.range Q).map payload).flatten j =
      (ScalingMergeData.blocks Q c j.val payload).flatten := by
  unfold ScalingSplit.piece ScalingSplit.offset ScalingMergeData.blocks
  apply interval_eq payload hw
  · have hm := ScalingSplit.offset_mono (Q := Q) (B := 1) hc (Nat.le_succ j.val)
    simpa only [ScalingSplit.offset,Nat.mul_one] using hm
  · exact ScalingControl.boundary_le Q c (j.val+1)

end IntegerMultBounds.Machine.ScalingPieceBridge
