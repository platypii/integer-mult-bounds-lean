module

public import IntegerMultBounds.NLogN.PhaseCellCoreWindows

/-! Generated owned cores pay for one ambient line in total. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

private theorem coreLength_range_sum (s width n : ℕ) :
    ((List.range n).map (coreLength s width)).sum = min s (n*width) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append,ih]
    simp only [List.map_singleton,List.sum_singleton,coreLength,coreStart,Nat.succ_mul]
    omega

/-- Clipping the final core preserves exact total volume. -/
theorem coreLength_sum (s width : ℕ) (hw : 0 < width) :
    ((coreIndices s width).map (coreLength s width)).sum = s := by
  rw [coreIndices,coreLength_range_sum]
  apply min_eq_left
  have hdiv := Nat.div_add_mod (s+width-1) width
  have hmod := Nat.mod_lt (s+width-1) hw
  rw [Nat.mul_comm width] at hdiv
  omega

/-- Replica and word-width factors do not introduce a core-count multiplier. -/
theorem coreOutputVolume_sum (s width replicas W : ℕ) (hw : 0 < width) :
    ((coreIndices s width).map (fun k => replicas*coreLength s width k*W)).sum = replicas*s*W := by
  have hscale : ∀ ks : List ℕ,
      (ks.map (fun k => replicas*coreLength s width k*W)).sum =
        replicas*(ks.map (coreLength s width)).sum*W := by
    intro ks
    induction ks with
    | nil => simp
    | cons k ks ih => simp only [List.map_cons,List.sum_cons,ih]; ring
  rw [hscale,coreLength_sum s width hw]

end IntegerMultBounds.NLogN.PhaseCellMatrix
