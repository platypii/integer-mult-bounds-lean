module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership

/-! Floor-owned core crops concatenate in original source order, with no sort
or large coordinate permutation. The list proof is structural in the cuts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership

theorem adjacent_slices_flatMap {E : Type} (xs : List E) (boundary : ℕ → ℕ)
    (hzero : boundary 0 = 0) (hmono : Monotone boundary) (Q : ℕ) :
    (List.range Q).flatMap (fun k => (xs.drop (boundary k)).take (boundary (k+1)-boundary k)) =
      xs.take (boundary Q) := by
  induction Q with
  | zero => simp [hzero]
  | succ Q ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,ih,List.take_drop]
    have hm := hmono (show Q ≤ Q+1 by omega)
    rw [Nat.add_sub_of_le hm]
    have ht : (xs.take (boundary (Q+1))).take (boundary Q) = xs.take (boundary Q) := by
      rw [List.take_take,Nat.min_eq_left hm]
    rw [←ht,List.take_append_drop]

theorem targetCorePacked_concat {s t L Q : ℕ} (F : ZMod s → GaussianInt)
    (ht : 0 < t) (hQ : Q*L = t) :
    (List.range Q).flatMap (fun k => packedInterval (cut s t L k) (rows s t L k) F) = chirpLine s F := by
  change (List.range Q).flatMap (fun k => ((chirpLine s F).drop (cut s t L k)).take
    (cut s t L (k+1)-cut s t L k)) = _
  rw [adjacent_slices_flatMap _ _ (cut_zero s t L) (cut_mono s t L),cut_last s t L Q ht hQ]
  simpa only [length_chirpLine] using (show (chirpLine s F).take (chirpLine s F).length = chirpLine s F from List.take_length)

/-- The generic recovery crop's offset/row ABI returns exactly J_k, without
an equal-source-core-width premise. -/
theorem targetCorePacked_crop {s t L k radius : ℕ} (F : ZMod s → GaussianInt)
    (ha : radius ≤ cut s t L k) :
    ((packedInterval (cut s t L k-radius) (rows s t L k+2*radius) F).drop radius).take
      (rows s t L k) = packedInterval (cut s t L k) (rows s t L k) F := by
  rw [packedInterval_crop F (show radius+rows s t L k ≤ rows s t L k+2*radius by omega),
    Nat.sub_add_cancel ha]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
