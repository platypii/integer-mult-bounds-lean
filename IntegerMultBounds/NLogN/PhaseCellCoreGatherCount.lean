module

public import IntegerMultBounds.NLogN.PhaseCellCoreGather
public import IntegerMultBounds.NLogN.PhaseCellCoreLocalityGeometry
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-! All interior full-width cores fit when the guard is no wider than a core.
At most two full cores are lost from the quotient count. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

theorem fullCoreGather_count_lower (s width radius : ℕ) (hw : 0 < width) (hr : radius ≤ width) :
    s/width-2 ≤ (coreGatherIndices s width radius (width+2*radius)).length := by
  have hsubset : Finset.Ico 1 (s/width-1) ⊆ (coreGatherIndices s width radius (width+2*radius)).toFinset := by
    intro k hk
    obtain ⟨hk1,hkq⟩ := Finset.mem_Ico.mp hk
    have hq : k+2 ≤ s/width := by omega
    have hmul := Nat.mul_le_mul_right width hq
    have hdiv := Nat.div_mul_le_self s width
    have hstart : radius ≤ coreStart width k := by
      have hm := Nat.mul_le_mul_right width hk1
      dsimp only [coreStart]
      omega
    have hfull : coreLength s width k = width := by
      unfold coreLength coreStart
      apply min_eq_left
      have hfit : k*width+width ≤ s := by nlinarith only [hmul,hdiv]
      omega
    have hcount : s/width ≤ (s+width-1)/width := Nat.div_le_div_right (by omega)
    have hindex : k ∈ coreIndices s width := by
      simp only [coreIndices,List.mem_range]
      omega
    apply List.mem_toFinset.mpr
    simp only [coreGatherIndices,List.mem_filter,decide_eq_true_eq]
    refine ⟨hindex,hstart,?_,by rw [hfull]⟩
    rw [hfull]
    dsimp only [coreStart]
    nlinarith only [hmul,hdiv,hr]
  have hcard := Finset.card_le_card hsubset
  have hnd : (coreGatherIndices s width radius (width+2*radius)).Nodup := by
    unfold coreGatherIndices coreIndices
    exact List.nodup_range.filter _
  rw [Nat.card_Ico,List.toFinset_card_of_nodup hnd] at hcard
  omega

/-- A quotient count above the half-axis scale gives a comparable key exponent.
The quotient condition will follow from the selected upper bound on core width. -/
theorem fullCoreGather_clog_bounds (s width radius ell : ℕ) (hw : 0 < width)
    (hr : radius ≤ width) (hs : s ≤ 2^ell)
    (hquot : 2^((ell+1)/2)+2 ≤ s/width) :
    Nat.clog 2 (coreGatherIndices s width radius (width+2*radius)).length ≤ ell ∧
    ell ≤ 2*Nat.clog 2 (coreGatherIndices s width radius (width+2*radius)).length := by
  have hcount := fullCoreGather_count_lower s width radius hw hr
  have hlower : 2^((ell+1)/2) ≤ (coreGatherIndices s width radius (width+2*radius)).length := by omega
  have hlog := Nat.clog_mono_right 2 hlower
  rw [Nat.clog_pow 2 _ (by decide)] at hlog
  have hupper := (coreGatherIndices_length_le s width radius (width+2*radius) hw).trans hs
  exact ⟨(Nat.clog_le_iff_le_pow (by decide)).mpr hupper,by omega⟩

/-- A clipped-length group contains only the final quotient core. -/
theorem clippedCoreGather_index (s width radius k : ℕ) (hw : 0 < width)
    (hk : k ∈ coreGatherIndices s width radius (s%width+2*radius)) : k = s/width := by
  have hspec := (coreGatherIndices_spec s width radius _ k hk).2.2
  have hindex : k ∈ coreIndices s width := (List.mem_filter.mp hk).1
  have hstart := coreIndex_start_lt s width k hw hindex
  have hmod := Nat.mod_lt s hw
  have hdiv := Nat.div_add_mod s width
  have hlen : coreLength s width k = s%width := by omega
  unfold coreLength coreStart at hlen
  dsimp only [coreStart] at hstart
  have htail : s-k*width = s%width := by omega
  rw [Nat.mul_comm width (s/width)] at hdiv
  have he : k*width = (s/width)*width := by omega
  exact mul_right_cancel₀ (by omega : width ≠ 0) he

theorem clippedCoreGather_length_le_one (s width radius : ℕ) (hw : 0 < width) :
    (coreGatherIndices s width radius (s%width+2*radius)).length ≤ 1 := by
  have hnd : (coreGatherIndices s width radius (s%width+2*radius)).Nodup := by
    unfold coreGatherIndices coreIndices
    exact List.nodup_range.filter _
  rw [←List.toFinset_card_of_nodup hnd]
  have hsubset : (coreGatherIndices s width radius (s%width+2*radius)).toFinset ⊆ {s/width} := by
    intro k hk
    exact Finset.mem_singleton.mpr (clippedCoreGather_index s width radius k hw (List.mem_toFinset.mp hk))
  simpa using Finset.card_le_card hsubset

end IntegerMultBounds.NLogN.PhaseCellMatrix
