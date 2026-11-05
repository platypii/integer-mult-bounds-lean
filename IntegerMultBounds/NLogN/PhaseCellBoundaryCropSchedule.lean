module

public import IntegerMultBounds.NLogN.PhaseCellCoreGatherSupplier
public import IntegerMultBounds.NLogN.PhaseCellCoreWindowCost

/-! Three fixed boundary slots cover every full-period fallback. Executing them
in reverse order makes the prepending archive appear in increasing core order.
A slot may also cover a fitting core; its certified full-line value is valid. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Slot identities are fixed; only the two final indices depend on geometry. -/
def boundaryCropIndex (s width : ℕ) (i : Fin 3) : ℕ :=
  if i = 0 then 0 else (s+width-1)/width-(3-i.val)

def boundaryCropSchedule (s width : ℕ) : List ℕ :=
  [(s+width-1)/width-1, (s+width-1)/width-2, 0]

theorem boundaryCropSchedule_eq_reverse_slots (s width : ℕ) :
    boundaryCropSchedule s width = (List.ofFn (boundaryCropIndex s width)).reverse := by
  simp [boundaryCropSchedule,boundaryCropIndex,List.ofFn_succ]

theorem boundaryCropIndex_injective (s width : ℕ) (hw : 0 < width)
    (hroom : 3*width < s) : Function.Injective (boundaryCropIndex s width) := by
  have hq : 3 ≤ (s+width-1)/width :=
    (Nat.le_div_iff_mul_le hw).mpr (by omega)
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  dsimp only [boundaryCropIndex] at he
  split_ifs at he <;> simp_all only [Fin.ext_iff, Fin.val_zero] <;> omega

theorem mem_boundaryCropSchedule (s width k : ℕ) :
    k ∈ boundaryCropSchedule s width ↔
      k = 0 ∨ k = (s+width-1)/width-2 ∨ k = (s+width-1)/width-1 := by
  simp only [boundaryCropSchedule,List.mem_cons,List.not_mem_nil,or_false]
  tauto

theorem boundaryCropSchedule_spec (s width : ℕ) (hw : 0 < width)
    (hroom : 3*width < s) :
    (boundaryCropSchedule s width).length = 3 ∧
    (boundaryCropSchedule s width).Nodup ∧
    ∀ k ∈ boundaryCropSchedule s width,
      k ∈ coreIndices s width ∧ coreStart width k < s ∧ 0 < coreLength s width k := by
  have hq : 3 ≤ (s+width-1)/width :=
    (Nat.le_div_iff_mul_le hw).mpr (by omega)
  refine ⟨rfl,?_,?_⟩
  · simp only [boundaryCropSchedule,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      or_false,List.nodup_nil,and_true,not_or]
    exact ⟨⟨by omega,by omega⟩,by omega,by simp⟩
  · intro k hk
    have hk' : k < (s+width-1)/width := by
      rw [mem_boundaryCropSchedule] at hk
      rcases hk with rfl | rfl | rfl <;> omega
    have hmem : k ∈ coreIndices s width := List.mem_range.mpr hk'
    have hs := coreStart_lt_of_mem hmem
    exact ⟨hmem,hs,by dsimp only [coreLength]; omega⟩

/-- Every owned core is supplied by the fitting sweep or by a boundary slot. -/
theorem fullGather_or_boundaryCropSchedule (s width band n k : ℕ)
    (hw : 0 < width) (hr : 0 < n*band) (hrw : n*band ≤ width)
    (hroom : 3*width < s) (hk : k ∈ coreIndices s width) :
    k ∈ coreGatherIndices s width (n*band) (width+2*(n*band)) ∨
      k ∈ boundaryCropSchedule s width := by
  rcases fullGather_or_fullSetupGroup s width band n k hw hr hk with hfit | hfull
  · exact Or.inl hfit
  · right
    have hn := (coreEndpoints_full_iff_not_fitting s width band n k hw hr hrw hroom hk).mp
      ((mem_coreSetupGroup s width band n k (0,s)).mp hfull).2
    have hb := coreHalo_fallback_indices s width k (n*band) hrw hk hn
    simpa only [Finset.mem_insert,Finset.mem_singleton,mem_boundaryCropSchedule] using hb

end IntegerMultBounds.NLogN.PhaseCellMatrix
