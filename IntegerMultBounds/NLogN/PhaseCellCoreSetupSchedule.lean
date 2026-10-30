module

public import IntegerMultBounds.NLogN.PhaseCellCoreSetupGroups
public import Mathlib.Data.List.Nodup

/-! A deterministic endpoint-key schedule, with each owned core visited once. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

def coreSetupKeyList (s width band n : ℕ) : List (ℕ × ℕ) :=
  ((coreIndices s width).map (fun k => coreHaloEndpoints s width k band n)).dedup

@[simp] theorem mem_coreSetupKeyList (s width band n : ℕ) (key : ℕ × ℕ) :
    key ∈ coreSetupKeyList s width band n ↔ key ∈ coreSetupKeys s width band n := by
  simp [coreSetupKeyList,coreSetupKeys]

theorem coreSetupKeyList_nodup (s width band n : ℕ) :
    (coreSetupKeyList s width band n).Nodup := List.nodup_dedup _

def coreSetupOrder (s width band n : ℕ) : List ℕ :=
  (coreSetupKeyList s width band n).flatMap (coreSetupGroup s width band n)

@[simp] theorem mem_coreSetupOrder (s width band n k : ℕ) :
    k ∈ coreSetupOrder s width band n ↔ k ∈ coreIndices s width := by
  constructor
  · intro hk
    obtain ⟨key,_,hk⟩ := List.mem_flatMap.mp hk
    exact ((mem_coreSetupGroup _ _ _ _ _ _).mp hk).1
  · intro hk
    obtain ⟨key,hkey,hgroup⟩ := coreSetupGroup_cover s width band n k hk
    exact List.mem_flatMap.mpr ⟨key,(mem_coreSetupKeyList ..).mpr hkey,hgroup⟩

theorem coreSetupOrder_nodup (s width band n : ℕ) :
    (coreSetupOrder s width band n).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun key _ => coreSetupGroup_nodup s width band n key,?_⟩
  apply (coreSetupKeyList_nodup s width band n).imp
  intro x y hne
  apply List.disjoint_left.mpr
  intro k hx hy
  exact hne (coreSetupGroup_unique s width band n k x y hx hy)

/-- Arithmetic regrouping changes only order, preserving every core exactly once. -/
theorem coreSetupOrder_perm (s width band n : ℕ) :
    (coreSetupOrder s width band n).Perm (coreIndices s width) := by
  apply (List.perm_ext_iff_of_nodup (coreSetupOrder_nodup ..) (coreIndices_nodup ..)).mpr
  exact fun k => mem_coreSetupOrder s width band n k

end IntegerMultBounds.NLogN.PhaseCellMatrix
