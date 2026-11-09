module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreRecoveryLocalVolume
public import IntegerMultBounds.NLogN.PhaseCellCoreGather
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry
import Mathlib.Tactic.Linarith

/-! Sum the actual joint boundary batch volume over a computed fitting class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix
open scoped BigOperators

theorem computedFittingCyclicPreparedVolume_sum_le {s t : ℕ} [NeZero s]
    (hst : s < t) (width band depth L : ℕ) (hw : 0 < width) (hwidth : width ≤ s)
    (hguard : depth*band ≤ width) (hband : 1 ≤ band) (hprepare : band^2 ≤ width) :
    ((coreGatherIndices s width (depth*band) L).map (fun k =>
      ((cyclicPrincipalBoundary s t band (coreStart width k-depth*band) L).card+1)*
        (24*band+1))).sum ≤ 800*(s+(t-s)*band^2) := by
  let indices := coreGatherIndices s width (depth*band) L
  let V := fun k => ((haloBoundary s t band (coreHaloEndpoints s width k band depth).1
    (coreHaloEndpoints s width k band depth).2).card+1)*(12*band+1)
  have hn : indices.Nodup := (coreIndices_nodup s width).filter _
  have hsub : indices.toFinset ⊆ (coreIndices s width).toFinset := by
    intro k hk
    exact List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hk)).1
  have hb : ∀ k ∈ indices,
      cyclicPrincipalBoundary s t band (coreStart width k-depth*band) L =
        haloBoundary s t band (coreHaloEndpoints s width k band depth).1
          (coreHaloEndpoints s width k band depth).2 := by
    intro k hk
    obtain ⟨hl,hr,hL⟩ := coreGatherIndices_spec s width (depth*band) L k hk
    have hstart := coreIndex_start_lt s width k hw (List.mem_filter.mp hk).1
    have ha : coreStart width k-depth*band < s := by omega
    have hfit : L ≤ s-(coreStart width k-depth*band) := by omega
    have hlen : L ≤ s := by omega
    rw [cyclicPrincipalBoundary_eq t band _ L ha hlen,min_eq_left hfit,Nat.sub_self]
    have hz : haloBoundary s t band 0 0 = ∅ := by simp [haloBoundary,haloVertices]
    rw [hz,Finset.union_empty]
    have he : coreHaloEndpoints s width k band depth =
        (coreStart width k-depth*band,coreStart width k+coreLength s width k+depth*band) := by
      simp only [coreHaloEndpoints,hl,hr,and_self,ite_true]
    rw [he]
    congr 1
    dsimp only
    omega
  rw [←List.sum_toFinset _ hn]
  have hsum : (∑ k ∈ indices.toFinset,
      ((cyclicPrincipalBoundary s t band (coreStart width k-depth*band) L).card+1)*(24*band+1)) ≤
      2*(∑ k ∈ (coreIndices s width).toFinset, V k) := by
    calc
      _ ≤ ∑ k ∈ indices.toFinset, 2*V k := by
        apply Finset.sum_le_sum
        intro k hk
        rw [hb k (List.mem_toFinset.mp hk)]
        dsimp only [V]
        nlinarith
      _ = 2*(∑ k ∈ indices.toFinset, V k) := by rw [Finset.mul_sum]
      _ ≤ _ := Nat.mul_le_mul_left 2 (Finset.sum_le_sum_of_subset hsub)
  have hv := coreHalo_boundaryWork_sum_le hst width band depth hw hguard hband
  have hcount := (Nat.mul_le_mul_left (coreIndices s width).length hprepare).trans
    (coreSlots_le_two s width hwidth)
  dsimp only [V] at hsum
  change (∑ k ∈ indices.toFinset, _) ≤ _
  nlinarith

end IntegerMultBounds.MathlibTM2.Cost
