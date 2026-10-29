module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPackedCellInputs

/-! Packed local gathering has the existing closed cell-batch row and origin
packet representation. Ambient origins are retained for coefficient generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedCellOrigin {s : ℕ} (origin : ℕ) (offsets : List ℕ) (i : ℕ) : ZMod s :=
  (origin+(offsets[i]?.getD 0) : ℕ)

theorem range_getD_map (xs : List ℕ) :
    (List.range xs.length).map (fun i => xs[i]?.getD 0) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hb : i < xs.length := by simpa only [List.length_map,List.length_range] using hi
  simp [List.getElem?_eq_getElem hb]

theorem range_getD_flatMap {α : Type*} (xs : List ℕ) (f : ℕ → List α) :
    (List.range xs.length).flatMap (fun i => f (xs[i]?.getD 0)) = xs.flatMap f := by
  rw [← List.flatMap_map,range_getD_map]

/-- The actual gathered rows can enter the unchanged closed arithmetic batch. -/
theorem packedCellRows_eq_sourceRows {s origin N L : ℕ}
    (C : ZMod s → GaussianInt) (offsets : List ℕ) (hhalo : origin+N ≤ s)
    (hfit : ∀ j ∈ offsets, j+L ≤ N) :
    offsets.flatMap (fun j => packedInterval (origin+j) L C) =
      (List.range offsets.length).flatMap
        (cellSourceRows L (packedCellOrigin origin offsets) (fun _ => C)) := by
  rw [← range_getD_flatMap offsets (fun j => packedInterval (origin+j) L C)]
  apply List.flatMap_congr
  intro i hi
  have hb : i < offsets.length := List.mem_range.mp hi
  have hm : offsets[i]?.getD 0 ∈ offsets := by
    simpa only [List.getElem?_eq_getElem hb,Option.getD_some] using List.getElem_mem hb
  have hf := hfit _ hm
  simpa only [cellSourceRows,packedCellOrigin] using
    packedInterval_eq_cellSourceRows C (show origin+offsets[i]?.getD 0+L ≤ s by omega)

theorem packedCellOrigin_val {s origin N L : ℕ} (offsets : List ℕ)
    (hhalo : origin+N ≤ s) (hL : 0 < L) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (i : ℕ) (hi : i < offsets.length) :
    (packedCellOrigin (s := s) origin offsets i).val = origin+offsets[i]?.getD 0 := by
  have hm : offsets[i]?.getD 0 ∈ offsets := by
    simpa only [List.getElem?_eq_getElem hi,Option.getD_some] using List.getElem_mem hi
  have hf := hfit _ hm
  exact ZMod.val_cast_of_lt (by omega)

/-- A packed cell coordinate addresses its original local word index. -/
theorem packedCellOrigin_local_index {s a N L : ℕ} [NeZero s] (offsets : List ℕ)
    (hhalo : a+N ≤ s) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (n : Fin offsets.length) (i : Fin L) :
    (packedCellOrigin (s := s) a offsets n+(i.val : ZMod s)).val-a =
      offsets[n.val]+i.val := by
  have hf := hfit _ (List.getElem_mem n.isLt)
  have he : packedCellOrigin (s := s) a offsets n+(i.val : ZMod s) =
      ((a+(offsets[n.val]+i.val) : ℕ) : ZMod s) := by
    simp only [packedCellOrigin,List.getElem?_eq_getElem n.isLt,Option.getD_some,Nat.cast_add,add_assoc]
  rw [he,ZMod.val_cast_of_lt (by omega)]
  omega

theorem packedCellOrigin_packets {A s origin N L : ℕ} (V : ℕ) (offsets : List ℕ)
    (hhalo : origin+N ≤ s) (hL : 0 < L) (hfit : ∀ j ∈ offsets, j+L ≤ N) :
    (List.range offsets.length).flatMap (fun i =>
      binSyms (A := A) V (packedCellOrigin (s := s) origin offsets i).val) =
      (offsets.map (origin+·)).flatMap (binSyms V) := by
  have he : (List.range offsets.length).flatMap (fun i =>
      binSyms (A := A) V (packedCellOrigin (s := s) origin offsets i).val) =
      (List.range offsets.length).flatMap (fun i => binSyms V (origin+offsets[i]?.getD 0)) := by
    apply List.flatMap_congr
    intro i hi
    rw [packedCellOrigin_val offsets hhalo hL hfit i (List.mem_range.mp hi)]
  rw [he,range_getD_flatMap offsets (fun j => binSyms (A := A) V (origin+j))]
  simp only [List.flatMap_map]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
