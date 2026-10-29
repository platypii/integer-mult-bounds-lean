module

public import IntegerMultBounds.NLogN.PhaseCellCoreWindows

/-! # Bounds on exceptional full-line halos

With guard radius at most the core width, every core except the first and
last two has a fitting interval halo. Thus the periodic-seam fallback has
constant multiplicity, independently of the line length and number of cores.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open Finset

/-- A core with a full following core has room for its right guard. -/
theorem coreHalo_fits_of_room (s width k radius : ℕ)
    (hr : radius ≤ width) (hk : 0 < k) (hroom : (k+2)*width ≤ s) :
    radius ≤ coreStart width k ∧ coreStart width k+coreLength s width k+radius ≤ s := by
  have hleft : width ≤ k*width := by simpa using Nat.mul_le_mul_right width hk
  have hlen : coreLength s width k ≤ width := min_le_left _ _
  dsimp only [coreStart]
  constructor
  · omega
  · have he : (k+2)*width = k*width+2*width := by ring
    omega

/-- Every nonexceptional generated core has a fitting interval halo. -/
theorem coreHalo_fits (s width k radius : ℕ) (hr : radius ≤ width)
    (hk : 0 < k) (hinterior : k+2 < (s+width-1)/width) :
    radius ≤ coreStart width k ∧ coreStart width k+coreLength s width k+radius ≤ s := by
  apply coreHalo_fits_of_room s width k radius hr hk
  have hmul := Nat.mul_le_mul_right width hinterior
  simp only [Nat.succ_eq_add_one] at hmul
  have hdiv := Nat.div_mul_le_self (s+width-1) width
  have he : (k+2+1)*width = (k+2)*width+width := by ring
  omega

/-- Only three indices can request a full-line fallback. -/
theorem coreHalo_fallback_indices (s width k radius : ℕ)
    (hr : radius ≤ width) (hk : k ∈ coreIndices s width)
    (hnot : ¬ (radius ≤ coreStart width k ∧
      coreStart width k+coreLength s width k+radius ≤ s)) :
    k ∈ ({0, (s+width-1)/width-2, (s+width-1)/width-1} : Finset ℕ) := by
  have hlt : k < (s+width-1)/width := List.mem_range.mp hk
  by_cases hzero : k = 0
  · simp [hzero]
  · have hlast : (s+width-1)/width ≤ k+2 := by
      by_contra h
      exact hnot (coreHalo_fits s width k radius hr (by omega) (by omega))
    have he : k = (s+width-1)/width-2 ∨ k = (s+width-1)/width-1 := by omega
    rcases he with rfl | rfl <;> simp

/-- The exception bound counts generated indices, so duplicate work cannot be
hidden by merely identifying equal full-line halo sets. -/
theorem coreHalo_fallback_count (s width radius : ℕ) (hr : radius ≤ width) :
    (((coreIndices s width).toFinset).filter (fun k =>
      ¬ (radius ≤ coreStart width k ∧
        coreStart width k+coreLength s width k+radius ≤ s))).card ≤ 3 := by
  have hsub : (((coreIndices s width).toFinset).filter (fun k =>
      ¬ (radius ≤ coreStart width k ∧
        coreStart width k+coreLength s width k+radius ≤ s))) ⊆
      ({0, (s+width-1)/width-2, (s+width-1)/width-1} : Finset ℕ) := by
    intro k hk
    obtain ⟨hk,hn⟩ := mem_filter.mp hk
    exact coreHalo_fallback_indices s width k radius hr (List.mem_toFinset.mp hk) hn
  exact (card_le_card hsub).trans (by
    have h₁ := card_insert_le 0 ({(s+width-1)/width-2, (s+width-1)/width-1} : Finset ℕ)
    have h₂ := card_insert_le ((s+width-1)/width-2) ({(s+width-1)/width-1} : Finset ℕ)
    simp only [card_singleton] at h₂
    omega)

open scoped BigOperators
open PhaseCellDiscreteGeometry

/-- A fitting halo pays its core width and two guards; a fallback pays one line. -/
theorem coreHalo_card_le {s : ℕ} [NeZero s] (width k band n : ℕ) :
    (coreHalo s width k band n).card ≤ width+2*(n*band)+
      if n*band ≤ coreStart width k ∧
        coreStart width k+coreLength s width k+n*band ≤ s then 0 else s := by
  unfold coreHalo
  split
  · rename_i hfit
    have hc := haloVertices_card_le s (coreStart width k-n*band)
      (coreStart width k+coreLength s width k+n*band)
    have hl : coreLength s width k ≤ width := min_le_left _ _
    omega
  · rename_i hfit
    simp

/-- Total halo volume charges at most three complete lines in addition to the
uniform core-and-guard budget. -/
theorem coreHalo_volume_le {s : ℕ} [NeZero s] (width band n : ℕ)
    (hr : n*band ≤ width) :
    (∑ k ∈ (coreIndices s width).toFinset, (coreHalo s width k band n).card) ≤
      (coreIndices s width).length*(width+2*(n*band))+3*s := by
  let K := (coreIndices s width).toFinset
  let bad := K.filter (fun k => ¬ (n*band ≤ coreStart width k ∧
    coreStart width k+coreLength s width k+n*band ≤ s))
  have hc : bad.card ≤ 3 := coreHalo_fallback_count s width (n*band) hr
  have hcount : K.card = (coreIndices s width).length :=
    List.toFinset_card_of_nodup (List.nodup_range)
  calc
    _ ≤ ∑ k ∈ K, (width+2*(n*band) +
        if n*band ≤ coreStart width k ∧
          coreStart width k+coreLength s width k+n*band ≤ s then 0 else s) :=
      sum_le_sum (fun k _ => coreHalo_card_le width k band n)
    _ = K.card*(width+2*(n*band))+bad.card*s := by
      rw [sum_add_distrib]
      congr 1
      · simp
      · calc
          _ = ∑ k ∈ bad, s := by
            rw [show bad = K.filter (fun k => ¬ (n*band ≤ coreStart width k ∧
              coreStart width k+coreLength s width k+n*band ≤ s)) from rfl, sum_filter]
            apply sum_congr rfl
            intro k _
            by_cases h : n*band ≤ coreStart width k ∧
              coreStart width k+coreLength s width k+n*band ≤ s <;> simp [h]
          _ = _ := by simp
    _ ≤ _ := by rw [hcount]; exact Nat.add_le_add_left (Nat.mul_le_mul_right s hc) _

/-- For cores no longer than the ambient line and guards no longer than a core,
the entire generated halo schedule has linear volume. -/
theorem coreHalo_volume_le_nine {s : ℕ} [NeZero s] (width band n : ℕ)
    (hw : width ≤ s) (hr : n*band ≤ width) :
    (∑ k ∈ (coreIndices s width).toFinset, (coreHalo s width k band n).card) ≤ 9*s := by
  apply (coreHalo_volume_le width band n hr).trans
  have hcount : (coreIndices s width).length*width ≤ s+width := by
    simp only [coreIndices,List.length_range]
    exact (Nat.div_mul_le_self (s+width-1) width).trans (Nat.sub_le _ _)
  have hguard : width+2*(n*band) ≤ 3*width := by omega
  have hmul := Nat.mul_le_mul_left (coreIndices s width).length hguard
  have he : (coreIndices s width).length*(3*width) =
      3*((coreIndices s width).length*width) := by ring
  rw [he] at hmul
  omega

end IntegerMultBounds.NLogN.PhaseCellMatrix
