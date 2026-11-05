module

public import IntegerMultBounds.NLogN.PhaseCellCoreGatherEligibility
public import IntegerMultBounds.NLogN.PhaseCellCoreSupplierSchedule

/-! The singleton live movement group is exactly the existing proper supplier
schedule. All remaining cores use the one full-period endpoint key. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

/-- A fitting guarded core is proper when three core widths are strictly shorter
than the line. This excludes the degenerate fitting interval equal to (0,s). -/
theorem fittingCoreEndpoints_ne_full (s width band n k : ℕ) (hw : 0 < width)
    (hr : 0 < n*band) (hrw : n*band ≤ width) (hroom : 3*width < s)
    (hk : k ∈ coreIndices s width)
    (hfit : n*band ≤ coreStart width k ∧ coreStart width k+coreLength s width k+n*band ≤ s) :
    coreHaloEndpoints s width k band n ≠ (0,s) := by
  have hlen := fittingCoreLength_eq_width s width (n*band) k hw hr hk hfit
  intro he
  simp only [coreHaloEndpoints,if_pos hfit] at he
  have hl := congrArg Prod.fst he
  have hright := congrArg Prod.snd he
  simp only [hlen] at hright
  omega

theorem coreEndpoints_full_iff_not_fitting (s width band n k : ℕ) (hw : 0 < width)
    (hr : 0 < n*band) (hrw : n*band ≤ width) (hroom : 3*width < s)
    (hk : k ∈ coreIndices s width) :
    coreHaloEndpoints s width k band n = (0,s) ↔
      ¬ (n*band ≤ coreStart width k ∧ coreStart width k+coreLength s width k+n*band ≤ s) := by
  constructor
  · intro he hfit
    exact fittingCoreEndpoints_ne_full s width band n k hw hr hrw hroom hk hfit he
  · intro hnot
    simp [coreHaloEndpoints,hnot]

/-- Movement groups do not identify arithmetic setup keys. This equality says
only which proper cores the full-width movement sweep supplies. -/
theorem coreBulkIndices_eq_fullGather (s width band n : ℕ) (hw : 0 < width)
    (hr : 0 < n*band) (hrw : n*band ≤ width) (hroom : 3*width < s) :
    coreBulkIndices s width band n = coreGatherIndices s width (n*band) (width+2*(n*band)) := by
  unfold coreBulkIndices coreGatherIndices
  apply List.filter_congr
  intro k hk
  by_cases hne : coreHaloEndpoints s width k band n ≠ (0,s)
  · have hfit := coreHaloEndpoints_fits_of_ne_full s width k band n hne
    have hlen := fittingCoreLength_eq_width s width (n*band) k hw hr hk hfit
    have hright : coreStart width k+width+n*band ≤ s := by simpa only [hlen] using hfit.2
    simp [hne,hfit.1,hlen,hright]
  · have hnot : ¬ (n*band ≤ coreStart width k ∧ coreStart width k+coreLength s width k+n*band ≤ s) := by
      intro hfit
      exact hne (fittingCoreEndpoints_ne_full s width band n k hw hr hrw hroom hk hfit)
    by_cases hl : n*band ≤ coreStart width k
    · have hrnot : ¬coreStart width k+coreLength s width k+n*band ≤ s := fun hh => hnot ⟨hl,hh⟩
      simp [hne,hl,hrnot]
    · simp [hne,hl]

/-- A positive left guard sends the first owned core to the full-period task.
Thus the fallback task is nonempty as well as unique by its endpoint key. -/
theorem firstCore_mem_fullSetupGroup (s width band n : ℕ) (hw : 0 < width)
    (hs : 0 < s) (hr : 0 < n*band) :
    0 ∈ coreSetupGroup s width band n (0,s) := by
  apply (mem_coreSetupGroup s width band n 0 (0,s)).mpr
  constructor
  · have hq : 1 ≤ (s+width-1)/width := (Nat.le_div_iff_mul_le hw).mpr (by omega)
    simp only [coreIndices,List.mem_range]
    omega
  · have hleft : ¬n*band ≤ 0 := by omega
    simp [coreHaloEndpoints,coreStart,hleft]

/-- The proper movement sweep and the one full-period setup task cover every
owned core. No clipped fitting task or empty-class probe is required here. -/
theorem fullGather_or_fullSetupGroup (s width band n k : ℕ) (hw : 0 < width)
    (hr : 0 < n*band) (hk : k ∈ coreIndices s width) :
    k ∈ coreGatherIndices s width (n*band) (width+2*(n*band)) ∨
      k ∈ coreSetupGroup s width band n (0,s) := by
  by_cases he : coreHaloEndpoints s width k band n = (0,s)
  · exact Or.inr ((mem_coreSetupGroup s width band n k (0,s)).mpr ⟨hk,he⟩)
  · left
    have hfit := coreHaloEndpoints_fits_of_ne_full s width k band n he
    have hlen := fittingCoreLength_eq_width s width (n*band) k hw hr hk hfit
    simp only [coreGatherIndices,List.mem_filter,decide_eq_true_eq]
    exact ⟨hk,hfit.1,hfit.2,by rw [hlen]⟩

theorem fullGather_disjoint_fullSetupGroup (s width band n : ℕ) (hw : 0 < width)
    (hr : 0 < n*band) (hrw : n*band ≤ width) (hroom : 3*width < s) :
    List.Disjoint (coreGatherIndices s width (n*band) (width+2*(n*band)))
      (coreSetupGroup s width band n (0,s)) := by
  apply List.disjoint_left.mpr
  intro k hk hfull
  have hindex := (List.mem_filter.mp hk).1
  have hfit := coreGatherIndices_spec s width (n*band) _ k hk
  exact fittingCoreEndpoints_ne_full s width band n k hw hr hrw hroom hindex ⟨hfit.1,hfit.2.1⟩
    ((mem_coreSetupGroup s width band n k (0,s)).mp hfull).2

end IntegerMultBounds.NLogN.PhaseCellMatrix
