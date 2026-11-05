module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatherSchedule
public import IntegerMultBounds.NLogN.PhaseCellBoundaryCropSchedule

/-! The selected geometry admits the same three physical crop slots on every
axis. Their mathematical indices vary, but their count and execution order do not. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix

theorem selectedAmortizedBoundaryCropSchedule (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
    ∀ (u target : ℕ), target ≤ ct*Sizes.p n →
      let width := amortizedCoreWidth ct (Sizes.p n)
      let radius := localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u
      Function.Injective (boundaryCropIndex (Sizes.s n i) width) ∧
      (boundaryCropSchedule (Sizes.s n i) width).length = 3 ∧
      (boundaryCropSchedule (Sizes.s n i) width).Nodup ∧
      (∀ k ∈ boundaryCropSchedule (Sizes.s n i) width,
        k ∈ coreIndices (Sizes.s n i) width ∧ coreStart width k < Sizes.s n i ∧
          0 < coreLength (Sizes.s n i) width k) ∧
      ∀ k ∈ coreIndices (Sizes.s n i) width,
        k ∈ coreGatherIndices (Sizes.s n i) width radius (width+2*radius) ∨
          k ∈ boundaryCropSchedule (Sizes.s n i) width := by
  filter_upwards [selectedAmortizedCoreGeometry ct] with n hgeometry
  intro h i _ u target htarget
  dsimp only
  obtain ⟨hw,_,hrw,hroom,_⟩ := hgeometry h i u target htarget
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hr := localityCoreWidth_pos hp u target
  have hb := PhaseCellBand.width_pos (Sizes.p n) u
  have hroom' : 3*amortizedCoreWidth ct (Sizes.p n) < Sizes.s n i := by omega
  obtain ⟨hlen,hnd,hvalid⟩ := boundaryCropSchedule_spec _ _ hw hroom'
  exact ⟨boundaryCropIndex_injective _ _ hw hroom',hlen,hnd,hvalid,
    fun k hk => fullGather_or_boundaryCropSchedule _ _ _ _ k hw hr hrw hroom' hk⟩

end IntegerMultBounds.MathlibTM2.Cost
