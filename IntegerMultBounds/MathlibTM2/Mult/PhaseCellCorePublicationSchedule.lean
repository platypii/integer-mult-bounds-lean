module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationWindows
public import Mathlib.Data.List.Sort

/-! Generated publication has two simple control patterns: consecutive full
cores, followed by at most one clipped core. No origin-table scan is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN.PhaseCellMatrix

theorem corePublication_full_indices (s width : ℕ) (hw : 0 < width) :
    corePublicationIndices s width width = List.range (s/width) := by
  apply (List.pairwise_lt_range.filter _).eq_of_mem_iff List.pairwise_lt_range
  intro k
  change k ∈ corePublicationIndices s width width ↔ k ∈ List.range (s/width)
  rw [mem_corePublicationIndices,List.mem_range]
  constructor
  · intro ⟨hk,hlen⟩
    have hs := coreStart_lt_of_mem hk
    have hfull : width ≤ s-k*width := by
      have hh : coreLength s width k ≤ s-coreStart width k := Nat.min_le_right width (s-coreStart width k)
      rw [hlen] at hh
      exact hh
    have hm : (k+1)*width ≤ s := by rw [Nat.add_mul,Nat.one_mul]; dsimp [coreStart] at hs; omega
    have hd := (Nat.le_div_iff_mul_le hw).mpr hm
    omega
  · intro hk
    have hq : s/width ≤ (s+width-1)/width := Nat.div_le_div_right (by omega)
    have hmem : k ∈ coreIndices s width := List.mem_range.mpr (hk.trans_le hq)
    have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hk)
    have hd := Nat.div_mul_le_self s width
    simp only [Nat.succ_mul] at hm
    refine ⟨hmem,?_⟩
    exact Nat.min_eq_left (by dsimp [coreStart]; omega)

theorem corePublication_remainder_mem (s width k : ℕ) (hw : 0 < width) :
    k ∈ corePublicationIndices s width (s%width) ↔ 0 < s%width ∧ k = s/width := by
  rw [mem_corePublicationIndices]
  have hr := Nat.mod_lt s hw
  have hd := Nat.div_add_mod s width
  rw [Nat.mul_comm width] at hd
  constructor
  · intro ⟨hk,hlen⟩
    have hs := coreStart_lt_of_mem hk
    have hlo : k ≤ s/width := (Nat.le_div_iff_mul_le hw).mpr hs.le
    have hnotfull : ¬width ≤ s-k*width := by
      intro hh
      have he : coreLength s width k = width := min_eq_left hh
      omega
    have hhi : s/width < k+1 := (Nat.div_lt_iff_lt_mul hw).mpr (by
      rw [Nat.add_mul,Nat.one_mul]
      dsimp [coreStart] at hs
      omega)
    have he : k = s/width := by omega
    refine ⟨?_,he⟩
    rw [he] at hs
    dsimp [coreStart] at hs
    omega
  · rintro ⟨hrpos,rfl⟩
    have hq : s/width < (s+width-1)/width := (Nat.lt_div_iff_mul_lt hw).mpr (by
      omega)
    refine ⟨List.mem_range.mpr hq,?_⟩
    dsimp only [coreLength,coreStart]
    have he : s-s/width*width = s%width := by omega
    rw [he,Nat.min_eq_right hr.le]

theorem corePublication_remainder_indices (s width : ℕ) (hw : 0 < width) :
    corePublicationIndices s width (s%width) = if 0 < s%width then [s/width] else [] := by
  split_ifs with hr
  · apply (List.pairwise_lt_range.filter _).eq_of_mem_iff (by simp)
    intro k
    change k ∈ corePublicationIndices s width (s%width) ↔ k ∈ [s/width]
    simp [corePublication_remainder_mem s width k hw,hr]
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro k hk
    exact hr ((corePublication_remainder_mem s width k hw).mp hk).1

private theorem windowGaps_consecutive (L k N : ℕ) :
    windowGaps L (k*L) ((List.range' k N).map (·*L)) = List.replicate N 0 := by
  induction N generalizing k with
  | zero => simp [windowGaps]
  | succ N ih =>
    simp only [List.range'_succ,List.map_cons,windowGaps,Nat.sub_self,List.replicate_succ]
    have he : k*L+L = (k+1)*L := by simp [Nat.add_mul]
    rw [he,ih]

theorem corePublication_full_gaps (s width w : ℕ) (hw : 0 < width) :
    (corePublicationWindows s width width hw).gaps w = List.replicate (s/width) 0 := by
  simpa only [PublicationWindows.gaps,PublicationWindows.symbolOrigins,corePublicationWindows,
    corePublication_full_indices s width hw,List.map_map,Function.comp_def,coreStart,Nat.mul_assoc,
    ←List.range_eq_range',Nat.zero_mul] using windowGaps_consecutive (width*w) 0 (s/width)

theorem corePublication_remainder_gaps (s width w : ℕ) (hw : 0 < width) :
    (corePublicationWindows s width (s%width) hw).gaps w =
      if 0 < s%width then [s/width*width*w] else [] := by
  simp only [PublicationWindows.gaps,PublicationWindows.symbolOrigins,corePublicationWindows,
    corePublication_remainder_indices s width hw]
  split_ifs <;> simp [windowGaps,coreStart]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
