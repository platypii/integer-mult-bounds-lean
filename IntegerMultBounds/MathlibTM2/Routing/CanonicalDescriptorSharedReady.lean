module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorInstallReady
public import IntegerMultBounds.MathlibTM2.Routing.DescriptorSharedInstall

/-! Canonical geometry supplies the six shared descriptor widths and raw
operands; no further numerical inputs are needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T A : ℕ}

def canonicalDescriptorSharedCore : Fin 46 → Fin 108 := Fin.castLE (by decide)
theorem canonicalDescriptorSharedCore_injective : Function.Injective canonicalDescriptorSharedCore := by
  decide +kernel

theorem canonicalDescriptorShared_width_le (p : Par) (i : Fin 6) :
    descriptorSharedWidth (canonicalStageWidths p) i ≤ (canonicalStageWidths p).coordinateBits := by
  have hw : canonicalScalarWidth (canonicalStageWidths p).coordinateBits ≤
      (canonicalStageWidths p).coordinateBits := by
    apply Nat.clog_le_of_le_pow
    exact Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hg := (canonicalStageWidths_bounds p 0).group_width
  fin_cases i <;> simp [descriptorSharedWidth, canonicalStageWidths_selector,
    LiveDescriptorWidths.coordinateBits] at * <;> assumption

theorem canonicalDescriptorShared_value_fit (L n : ℕ) (hn : n < 2 ^ L)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n)) (i : Fin 6) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    descriptorSharedValue p (canonicalStageWidths p) i <
      2 ^ descriptorSharedInputWidth L (canonicalStageWidths p).coordinateBits i := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  have hw := canonicalDescriptorInstall_width_fit L n hn hlarge r
  have hg : canonicalRouterGap n < 2 ^ L := by
    change 64 * canonicalRouterGap n ≤ n at hlarge
    omega
  have hpos : 1 ≤ W := by
    change 1 ≤ (liveDescriptorArithmeticWidths p 0 repairLiveMode).indexBits + 1 +
      (liveDescriptorArithmeticWidths p 0 repairLiveMode).strideBits
    omega
  have hone : 1 < 2 ^ W := (by decide : 1 < 2 ^ 1).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hpos)
  fin_cases i <;> simp [descriptorSharedValue, descriptorSharedInputWidth,
    canonicalStageWidths_selector, routerProfileParameters] <;> first
      | exact hw | exact hg | exact hone | exact Nat.ne_of_gt hpos

theorem canonicalProfileSetup_shared (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 28 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n)) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let w := canonicalStageWidths p
    let B := canonicalProfileSetupBank R rg L n r.val
    B (rg 2) = binSyms L p.G ∧ B (rg 21) = binSyms L w.groupBits ∧
      B (rg 25) = binSyms L w.indexBits ∧ B (rg 26) = binSyms L w.selectorBits ∧
      B (rg 27) = binSyms L w.widthBits := by
  dsimp only
  obtain ⟨hi,hg,hs,hsel,hw⟩ := canonicalStageWidths_router n hlarge r
  rw [hi,hg,hsel,hw]
  simp [canonicalProfileSetupBank, canonicalDescriptorWidthsBank, canonicalResidueGeometryBank,
    canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank,
    canonicalProfileWidthSlot, canonicalProfileGeometrySlot, canonicalResidueCommonSlot,
    routerReservoirCommonSlot, routerProfileParameters, canonicalRouterStride, hrg.eq_iff]

theorem canonicalDescriptorScalarBank_shared_keep (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 46 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (i : Fin 46) (hi : i ∈ ([2,21,25,26,27] : List (Fin 46))) :
    canonicalDescriptorScalarBank R rg L n r (rg i) =
      canonicalProfileSetupBank R (rg ∘ canonicalDescriptorGeometrySlot) L n r (rg i) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp [canonicalDescriptorScalarBank,descriptorScalarResizedBank,descriptorScalarBank,
      binaryResizeBatchBank,descriptorScalarResizeSlot,descriptorScalarInputIndex,
      descriptorScalarCoreSlot,canonicalDescriptorScalarInputBank,
      canonicalDescriptorScalarSlot,hrg.eq_iff]

theorem canonicalDescriptorShared_inputs (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n)) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let w := canonicalStageWidths p
    let B := canonicalDescriptorScalarBank R (rg ∘ canonicalDescriptorSharedCore) L n r.val
    (∀ i, B (rg (descriptorSharedWidthSlot i)) = binSyms L (descriptorSharedWidth w i)) ∧
    (∀ i : Fin 6, i ≠ 3 → i ≠ 5 → B (rg (descriptorSharedValueSlot i)) =
      binSyms (descriptorSharedInputWidth L w.coordinateBits i) (descriptorSharedValue p w i)) ∧
    B (rg 32) = binSyms w.coordinateBits 0 := by
  dsimp only
  let core := rg ∘ canonicalDescriptorSharedCore
  have hc : Function.Injective core := hrg.comp canonicalDescriptorSharedCore_injective
  obtain ⟨hG,hgroup,hindex,hselector,hwidth⟩ := canonicalProfileSetup_shared R
    (core ∘ canonicalDescriptorGeometrySlot) (hc.comp canonicalDescriptorGeometrySlot_injective) L n hlarge r
  have keep (i : Fin 46) (hi : i ∈ ([2,21,25,26,27] : List (Fin 46))) :=
    canonicalDescriptorScalarBank_shared_keep R core hc L n r.val i hi
  have h2 := (keep 2 (by simp)).trans hG
  have h21 := (keep 21 (by simp)).trans hgroup
  have h25 := (keep 25 (by simp)).trans hindex
  have h26 := (keep 26 (by simp)).trans hselector
  have h27 := (keep 27 (by simp)).trans hwidth
  have hz := canonicalDescriptorInstall_palette R
    (rg ∘ (Fin.castLE (by decide) : Fin 101 → Fin 108))
    (hrg.comp (by decide +kernel)) L n r.val 4
  change canonicalDescriptorScalarBank R core L n r.val (rg 32) =
    binSyms (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val)).coordinateBits 0 at hz
  refine ⟨?_,?_,hz⟩
  · intro i
    fin_cases i <;> first | exact h27 | exact h21 | exact h25 | exact h26
  · intro i h3 h5
    fin_cases i <;> first | exact h26 | exact h2 | exact hz | contradiction

theorem canonicalDescriptorShared_blank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hblank : ∀ i : Fin 108, 39 ≤ i.val → R (rg i) = [])
    (i : Fin 108) (hi : 39 ≤ i.val) (h44 : i ≠ 44) :
    canonicalDescriptorScalarBank R (rg ∘ canonicalDescriptorSharedCore) L n r (rg i) = [] := by
  rw [canonicalDescriptorScalarBank_keep]
  · exact hblank i hi
  · have hn44 : i.val ≠ 44 := fun h => h44 (Fin.ext h)
    simp [canonicalDescriptorScalarTargets, hrg.eq_iff, canonicalDescriptorSharedCore, Fin.ext_iff]
    omega

end IntegerMultBounds.MathlibTM2.Routing
