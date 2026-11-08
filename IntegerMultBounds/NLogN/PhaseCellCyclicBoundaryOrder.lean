module

public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry
public import IntegerMultBounds.NLogN.PhaseCellBoundaryFold

/-! Separated physical boundary pieces concatenate in their original coordinate order. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix
variable {s : ℕ} [NeZero s]

theorem bOrder_union_of_separated (B C : Finset (ZMod s))
    (hsep : ∀ i ∈ B, ∀ j ∈ C, i.val < j.val) :
    bOrder s (B ∪ C) = bOrder s B ++ bOrder s C := by
  have hmem (D : Finset (ZMod s)) (i : ZMod s) : i ∈ bOrder s D ↔ i ∈ D := by
    rw [← List.mem_toFinset,bOrder_toFinset]
  have hsorted : (bOrder s B ++ bOrder s C).Pairwise (fun i j => i.val < j.val) := by
    apply List.pairwise_append.mpr
    exact ⟨bOrder_val_sorted s B,bOrder_val_sorted s C,
      fun i hi j hj => hsep i ((hmem B i).mp hi) j ((hmem C j).mp hj)⟩
  have hnd : (bOrder s B ++ bOrder s C).Nodup :=
    hsorted.imp (fun h => ne_of_apply_ne ZMod.val (ne_of_lt h))
  have hperm : (bOrder s B ++ bOrder s C).Perm (bOrder s (B ∪ C)) := by
    apply (List.perm_ext_iff_of_nodup hnd (bOrder_nodup s (B ∪ C))).mpr
    intro i
    simp only [List.mem_append,hmem,Finset.mem_union]
  symm
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => False.elim (Nat.lt_asymm h₁ h₂))
    hsorted (bOrder_val_sorted s (B ∪ C)) hperm

end IntegerMultBounds.NLogN.PhaseCellMatrix

namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open PhaseCellMatrix
variable {s : ℕ} [NeZero s]

theorem cyclicPrincipalBoundary_order (t band a n : ℕ) (ha : a < s) (hn : n ≤ s) :
    bOrder s (cyclicPrincipalBoundary s t band a n) =
      bOrder s (haloBoundary s t band 0 (n-min n (s-a))) ++
        bOrder s (haloBoundary s t band a (a+min n (s-a))) := by
  rw [cyclicPrincipalBoundary_eq t band a n ha hn,Finset.union_comm]
  apply bOrder_union_of_separated
  intro i hi j hj
  have hiV := (Finset.mem_sdiff.mp hi).1
  have hjV := (Finset.mem_sdiff.mp hj).1
  obtain ⟨_,hiEnd⟩ := (mem_haloVertices _ _ i).mp hiV
  obtain ⟨hjStart,_⟩ := (mem_haloVertices _ _ j).mp hjV
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
