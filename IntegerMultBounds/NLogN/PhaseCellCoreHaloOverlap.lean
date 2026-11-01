module

public import IntegerMultBounds.NLogN.PhaseCellCoreWindowCost
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Pointwise halo overlap bounds apply to every sparse subset of an axis. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix
open Finset PhaseCellDiscreteGeometry
open scoped BigOperators

private theorem card_triple_le (a b c : ℕ) : ({a,b,c} : Finset ℕ).card ≤ 3 := by
  have h₁ := card_insert_le a ({b,c} : Finset ℕ)
  have h₂ := card_insert_le b ({c} : Finset ℕ)
  simp only [card_singleton] at h₂
  omega

/-- A fitting halo can meet only its point's quotient owner or a neighbour. -/
theorem coreHalo_fitting_index_near {s : ℕ} [NeZero s] (width k band n : ℕ)
    (hw : 0 < width) (hr : n*band ≤ width) (i : ZMod s)
    (hfit : n*band ≤ coreStart width k ∧ coreStart width k+coreLength s width k+n*band ≤ s)
    (hi : i ∈ coreHalo s width k band n) :
    k ∈ ({i.val/width-1,i.val/width,i.val/width+1} : Finset ℕ) := by
  have hv : coreStart width k-n*band ≤ i.val ∧
      i.val < coreStart width k+coreLength s width k+n*band := by
    simpa only [coreHalo,hfit,and_self,ite_true,mem_haloVertices] using hi
  have hlen : coreLength s width k ≤ width := min_le_left _ _
  have hupper : i.val/width < k+2 := (Nat.div_lt_iff_lt_mul hw).mpr (by
    have he : (k+2)*width = k*width+2*width := by ring
    dsimp only [coreStart] at hv
    omega)
  have hlower : k ≤ i.val/width+1 := by
    by_cases hk : k = 0
    · subst k
      exact Nat.zero_le _
    · have hmul : (k-1)*width ≤ i.val := by
        rw [Nat.sub_mul]
        dsimp only [coreStart] at hv hfit
        omega
      have hd := (Nat.le_div_iff_mul_le hw).mpr hmul
      omega
  have he : k = i.val/width-1 ∨ k = i.val/width ∨ k = i.val/width+1 := by omega
  rcases he with h | h | h <;> simp [h]

/-- Three fitting neighbours and at most three full-line fallbacks. -/
theorem coreHalo_overlap_le_six {s : ℕ} [NeZero s] (width band n : ℕ)
    (hw : 0 < width) (hr : n*band ≤ width) (i : ZMod s) :
    (((coreIndices s width).toFinset).filter (fun k => i ∈ coreHalo s width k band n)).card ≤ 6 := by
  let near : Finset ℕ := {i.val/width-1,i.val/width,i.val/width+1}
  let bad : Finset ℕ := {0,(s+width-1)/width-2,(s+width-1)/width-1}
  have hsub : (((coreIndices s width).toFinset).filter (fun k => i ∈ coreHalo s width k band n)) ⊆ near ∪ bad := by
    intro k hk
    obtain ⟨hk,hi⟩ := mem_filter.mp hk
    by_cases hfit : n*band ≤ coreStart width k ∧ coreStart width k+coreLength s width k+n*band ≤ s
    · exact mem_union.mpr (Or.inl (coreHalo_fitting_index_near width k band n hw hr i hfit hi))
    · exact mem_union.mpr (Or.inr (coreHalo_fallback_indices s width k (n*band) hr (List.mem_toFinset.mp hk) hfit))
  have hnear : near.card ≤ 3 := card_triple_le _ _ _
  have hbad : bad.card ≤ 3 := card_triple_le _ _ _
  exact (card_le_card hsub).trans ((card_union_le near bad).trans (by omega))

/-- Sparse work is counted only where it occurs, including seam fallbacks. -/
theorem coreHalo_inter_volume_le_six {s : ℕ} [NeZero s] (width band n : ℕ)
    (hw : 0 < width) (hr : n*band ≤ width) (E : Finset (ZMod s)) :
    (∑ k ∈ (coreIndices s width).toFinset, (coreHalo s width k band n ∩ E).card) ≤ 6*E.card := by
  let K := (coreIndices s width).toFinset
  have hd := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := K) (t := E) (fun k i => i ∈ coreHalo s width k band n)
  calc
    _ = ∑ i ∈ E, (K.filter (fun k => i ∈ coreHalo s width k band n)).card := by
      simpa only [bipartiteAbove,bipartiteBelow,filter_mem_eq_inter,inter_comm] using hd
    _ ≤ ∑ _i ∈ E, 6 := sum_le_sum (fun i _ => coreHalo_overlap_le_six width band n hw hr i)
    _ = _ := by simp [Nat.mul_comm]

end IntegerMultBounds.NLogN.PhaseCellMatrix
