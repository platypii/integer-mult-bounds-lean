module

public import IntegerMultBounds.NLogN.PhaseCellCoreGatherCount

/-! Positive guards exclude the clipped final core from every fitting sweep.
With room for three full cores, the only live movement length is the full one. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

/-- The clipped core ends at s, leaving no room for a positive right guard. -/
theorem clippedCoreGather_eq_nil (s width radius : ℕ) (hw : 0 < width) (hr : 0 < radius) :
    coreGatherIndices s width radius (s%width+2*radius) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro k hk
  have hq := clippedCoreGather_index s width radius k hw hk
  obtain ⟨_,hfit,hlen⟩ := coreGatherIndices_spec s width radius _ k hk
  rw [hq] at hfit hlen
  have hdiv := Nat.div_add_mod s width
  rw [Nat.mul_comm width] at hdiv
  dsimp only [coreStart] at hfit
  omega

theorem fullCoreGather_nonempty (s width radius : ℕ) (hw : 0 < width)
    (hr : radius ≤ width) (hroom : 3*width ≤ s) :
    0 < (coreGatherIndices s width radius (width+2*radius)).length := by
  have hquot : 3 ≤ s/width := (Nat.le_div_iff_mul_le hw).mpr hroom
  have hcount := fullCoreGather_count_lower s width radius hw hr
  omega

/-- This is a mathematical schedule selector. The selected implementation uses
its proved singleton directly rather than evaluating a list scan at runtime. -/
def liveCoreGatherLengths (s width radius : ℕ) : List ℕ :=
  (coreGatherLengths s width radius).filter (fun L => decide (0 < (coreGatherIndices s width radius L).length))

theorem liveCoreGatherLengths_eq_singleton (s width radius : ℕ) (hw : 0 < width)
    (hr : 0 < radius) (hrw : radius ≤ width) (hroom : 3*width ≤ s) :
    liveCoreGatherLengths s width radius = [width+2*radius] := by
  have hfull := fullCoreGather_nonempty s width radius hw hrw hroom
  have hclip := clippedCoreGather_eq_nil s width radius hw hr
  have hne : width+2*radius ≠ s%width+2*radius := by
    have := Nat.mod_lt s hw
    omega
  have hnd : [width+2*radius,s%width+2*radius].Nodup := by
    refine List.nodup_cons.mpr ⟨?_,by simp⟩
    simpa only [List.mem_singleton] using hne
  simp only [liveCoreGatherLengths,coreGatherLengths,List.dedup_eq_self.mpr hnd]
  simp [hfull,hclip]

theorem coreGather_nonempty_iff_full (s width radius L : ℕ) (hw : 0 < width)
    (hr : 0 < radius) (hrw : radius ≤ width) (hroom : 3*width ≤ s)
    (hL : L ∈ coreGatherLengths s width radius) :
    0 < (coreGatherIndices s width radius L).length ↔ L = width+2*radius := by
  constructor
  · intro hpos
    have hm : L ∈ liveCoreGatherLengths s width radius := List.mem_filter.mpr ⟨hL,by simpa using hpos⟩
    rw [liveCoreGatherLengths_eq_singleton s width radius hw hr hrw hroom] at hm
    exact List.mem_singleton.mp hm
  · rintro rfl
    exact fullCoreGather_nonempty s width radius hw hrw hroom

/-- Fitting owned cores all have the full width; the clipped tail belongs to
fallback publication, never to a second proper-interval gather. -/
theorem fittingCoreLength_eq_width (s width radius k : ℕ) (hw : 0 < width) (hr : 0 < radius)
    (hk : k ∈ coreIndices s width)
    (hfit : radius ≤ coreStart width k ∧ coreStart width k+coreLength s width k+radius ≤ s) :
    coreLength s width k = width := by
  rcases coreLength_cases s width k hw hk with he | he
  · exact he
  · have hm : k ∈ coreGatherIndices s width radius (s%width+2*radius) := by
      simp only [coreGatherIndices,List.mem_filter,decide_eq_true_eq]
      exact ⟨hk,hfit.1,hfit.2,by rw [he]⟩
    rw [clippedCoreGather_eq_nil s width radius hw hr] at hm
    simp at hm

end IntegerMultBounds.NLogN.PhaseCellMatrix
