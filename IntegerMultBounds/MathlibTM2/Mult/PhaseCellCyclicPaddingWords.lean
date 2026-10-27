module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath
public import IntegerMultBounds.NLogN.PhaseCellSpatialCouplingOffsets

/-! Three finite intervals realize the ambient cyclic padding, including a full-width band. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

theorem cyclicPaddedLine_split {s : ℕ} [NeZero s] (F : ZMod s → GaussianInt)
    (band : ℕ) (hb : band ≤ s) :
    cyclicPaddedLine F band = (chirpLine s F).drop (s-band)++chirpLine s F++(chirpLine s F).take band := by
  rw [List.append_assoc]
  have hs : (chirpLine s F).length = s := by simp
  have hd : ((chirpLine s F).drop (s-band)).length = band := by simp; omega
  have ht : ((chirpLine s F).take band).length = band := by simp [Nat.min_eq_left hb]
  apply List.ext_getElem
  · simp [cyclicPaddedLine,hd,ht]; omega
  · intro n hn hn'
    have hnall : n < s+2*band := by simpa [cyclicPaddedLine] using hn
    by_cases hnb : n < band
    · simp only [List.getElem_append,hd,ht,hs,hnb,ite_true]
      simp only [cyclicPaddedLine,chirpLine,List.getElem_map,List.getElem_range,List.getElem_drop]
      congr 1
      rw [Nat.cast_add,Nat.cast_sub hb]
      simp
      ring
    · have hbn : band ≤ n := by omega
      by_cases hns : n-band < s
      · simp only [List.getElem_append,hd,ht,hs,hnb,ite_false,hns,ite_true]
        simp only [cyclicPaddedLine,chirpLine,List.getElem_map,List.getElem_range]
        rw [Nat.cast_sub hbn]
        simp
      · have hsn : s ≤ n-band := by omega
        simp only [List.getElem_append,hd,ht,hs,hnb,ite_false,hns]
        simp only [cyclicPaddedLine,chirpLine,List.getElem_map,List.getElem_range,List.getElem_take]
        congr 1
        rw [Nat.cast_sub hsn,Nat.cast_sub hbn]
        simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
