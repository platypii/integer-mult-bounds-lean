module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAmortizedCoreGeometry
public import IntegerMultBounds.NLogN.PhaseCellCoreGatherSupplier

/-! At selected sizes the proper movement schedule is one nonempty full-width
class, and the existing unique full-period task serves at most three seam cores.
No dynamic emptiness scan is needed to select these two kinds of work. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix

theorem selectedAmortizedGatherSchedule (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
    ∀ (u target : ℕ), target ≤ ct*Sizes.p n →
      let width := amortizedCoreWidth ct (Sizes.p n)
      let band := PhaseCellBand.width (Sizes.p n) u
      let depth := localityDepth (Sizes.p n) target
      let radius := depth*band
      0 < (coreGatherIndices (Sizes.s n i) width radius (width+2*radius)).length ∧
      coreGatherIndices (Sizes.s n i) width radius (Sizes.s n i%width+2*radius) = [] ∧
      liveCoreGatherLengths (Sizes.s n i) width radius = [width+2*radius] ∧
      coreBulkIndices (Sizes.s n i) width band depth = coreGatherIndices (Sizes.s n i) width radius (width+2*radius) ∧
      0 ∈ coreSetupGroup (Sizes.s n i) width band depth (0,Sizes.s n i) ∧
      (coreSetupGroup (Sizes.s n i) width band depth (0,Sizes.s n i)).length ≤ 3 ∧
      List.Disjoint (coreGatherIndices (Sizes.s n i) width radius (width+2*radius))
        (coreSetupGroup (Sizes.s n i) width band depth (0,Sizes.s n i)) ∧
      ∀ k ∈ coreIndices (Sizes.s n i) width,
        k ∈ coreGatherIndices (Sizes.s n i) width radius (width+2*radius) ∨
          k ∈ coreSetupGroup (Sizes.s n i) width band depth (0,Sizes.s n i) := by
  filter_upwards [selectedAmortizedCoreGeometry ct,selectedAmortizedCoreHalo ct] with n hgeometry hhalo
  intro h i _ u target htarget
  dsimp only
  let width := amortizedCoreWidth ct (Sizes.p n)
  let band := PhaseCellBand.width (Sizes.p n) u
  let depth := localityDepth (Sizes.p n) target
  let radius := depth*band
  obtain ⟨hw,_,hrw,hroom,_⟩ := hgeometry h i u target htarget
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hr : 0 < radius := localityCoreWidth_pos hp u target
  have hb : 0 < band := PhaseCellBand.width_pos _ _
  have hroom' : 3*width < Sizes.s n i := by omega
  have hs : 0 < Sizes.s n i := by omega
  have hcount : (coreSetupGroup (Sizes.s n i) width band depth (0,Sizes.s n i)).length ≤ 3 := by
    have hset : (coreSetupGroup (Sizes.s n i) width band depth (0,Sizes.s n i)).toFinset =
        ((coreIndices (Sizes.s n i) width).toFinset).filter (fun k =>
          ¬ (radius ≤ coreStart width k ∧ coreStart width k+coreLength (Sizes.s n i) width k+radius ≤ Sizes.s n i)) := by
      ext k
      simp only [List.mem_toFinset,mem_coreSetupGroup,Finset.mem_filter]
      constructor
      · rintro ⟨hk,he⟩
        exact ⟨hk,(coreEndpoints_full_iff_not_fitting _ _ _ _ _ hw hr hrw hroom' hk).mp he⟩
      · rintro ⟨hk,he⟩
        exact ⟨hk,(coreEndpoints_full_iff_not_fitting _ _ _ _ _ hw hr hrw hroom' hk).mpr he⟩
    rw [←List.toFinset_card_of_nodup (coreSetupGroup_nodup (Sizes.s n i) width band depth (0,Sizes.s n i)),hset]
    exact (hhalo h i u target htarget).2.1
  exact ⟨fullCoreGather_nonempty _ _ _ hw hrw hroom'.le,
    clippedCoreGather_eq_nil _ _ _ hw hr,
    liveCoreGatherLengths_eq_singleton _ _ _ hw hr hrw hroom'.le,
    coreBulkIndices_eq_fullGather _ _ _ _ hw hr hrw hroom',
    firstCore_mem_fullSetupGroup _ _ _ _ hw hs hr,hcount,
    fullGather_disjoint_fullSetupGroup _ _ _ _ hw hr hrw hroom',
    fun k hk => fullGather_or_fullSetupGroup _ _ _ _ k hw hr hk⟩

end IntegerMultBounds.MathlibTM2.Cost
