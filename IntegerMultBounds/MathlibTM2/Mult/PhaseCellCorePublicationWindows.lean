module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWindows
public import IntegerMultBounds.NLogN.PhaseCellCoreGather

/-! Group owned cores by their published length, independently of halo length
or numerical setup keys. There are at most two publication sweeps. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN.PhaseCellMatrix

def corePublicationIndices (s width L : ℕ) : List ℕ :=
  (coreIndices s width).filter (fun k => decide (coreLength s width k = L))

theorem mem_corePublicationIndices (s width L k : ℕ) :
    k ∈ corePublicationIndices s width L ↔ k ∈ coreIndices s width ∧ coreLength s width k = L := by
  simp [corePublicationIndices]

theorem coreIndices_length_le (s width : ℕ) (hw : 0 < width) :
    (coreIndices s width).length ≤ s := by
  simp only [coreIndices,List.length_range]
  have hs : s ≤ s*width := by simpa using Nat.mul_le_mul_left s hw
  have hlt : s+width-1 < (s+1)*width := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have := (Nat.div_lt_iff_lt_mul hw).mpr hlt
  omega

def corePublicationWindows (s width L : ℕ) (hw : 0 < width) : PublicationWindows s L where
  origins := (corePublicationIndices s width L).map (coreStart width)
  disjoint := by
    apply List.pairwise_map.mpr
    have h : (corePublicationIndices s width L).Pairwise (· < ·) :=
      List.pairwise_lt_range.filter _
    apply h.imp_of_mem
    intro i j hi _ hij
    have hL := ((mem_corePublicationIndices s width L i).mp hi).2
    have hlen : L ≤ width := by rw [← hL]; exact Nat.min_le_left _ _
    have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hij)
    simp only [Nat.succ_mul] at hm
    dsimp only [coreStart]
    omega
  fits := by
    intro p hp
    obtain ⟨k,hk,he⟩ := List.mem_map.mp hp
    subst p
    have hk' := (mem_corePublicationIndices s width L k).mp hk
    have hs := coreStart_lt_of_mem hk'.1
    have hlen : L ≤ s-coreStart width k := by rw [← hk'.2]; exact Nat.min_le_right _ _
    omega
  count_le := by
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans (coreIndices_length_le s width hw)

def corePublicationLengths (s width : ℕ) : List ℕ := [width,s%width].dedup

theorem corePublicationLengths_length (s width : ℕ) :
    (corePublicationLengths s width).length ≤ 2 :=
  List.Sublist.length_le (List.dedup_sublist [width,s%width])

theorem corePublicationLengths_cover (s width k : ℕ) (hw : 0 < width)
    (hk : k ∈ coreIndices s width) :
    ∃ L ∈ corePublicationLengths s width, k ∈ corePublicationIndices s width L := by
  refine ⟨coreLength s width k,?_,(mem_corePublicationIndices ..).mpr ⟨hk,rfl⟩⟩
  rcases coreLength_cases s width k hw hk with h | h <;> simp [corePublicationLengths,h]

theorem corePublicationWindows_cost_le (s width L w : ℕ) (hw : 0 < width) (hw1 : 1 ≤ w) :
    (corePublicationWindows s width L hw).cost w ≤ 35*s*w+6 :=
  PublicationWindows.cost_le _ w hw1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
