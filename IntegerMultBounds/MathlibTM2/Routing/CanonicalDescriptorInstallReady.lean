module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorScalarClean
public import IntegerMultBounds.MathlibTM2.Routing.DescriptorScalarInstall

/-! The generated canonical palette directly occupies the installation sources;
installation scratch and destinations remain blank after scalar generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T A : ℕ}

def canonicalDescriptorInstallCore : Fin 46 → Fin 101 := Fin.castLE (by decide)

theorem canonicalDescriptorInstallCore_injective :
    Function.Injective canonicalDescriptorInstallCore := by decide +kernel

theorem canonicalDescriptorInstall_width_le (p : Par) (f : Fin 5) :
    repairDescriptorScalarWidth (canonicalStageWidths p) f ≤
      (canonicalStageWidths p).coordinateBits := by
  fin_cases f <;> simp [repairDescriptorScalarWidth, canonicalStageWidths_selector,
    LiveDescriptorWidths.coordinateBits]

theorem canonicalDescriptorInstall_width_fit (L n : ℕ) (hn : n < 2 ^ L)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n)) :
    (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val)).coordinateBits < 2 ^ L := by
  obtain ⟨_,_,_,hs,_⟩ := canonicalStageWidths_router n hlarge r
  have hcoord : (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val)).coordinateBits ≤ canonicalRouterGap n := by
    rw [← canonicalStageWidths_selector, hs]
    exact canonicalDescriptorCoordinateWidth_le_gap n
  have hg : canonicalRouterGap n ≤ n := by
    change 64 * canonicalRouterGap n ≤ n at hlarge
    omega
  exact (hcoord.trans hg).trans_lt hn

theorem canonicalDescriptorInstall_palette (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 101 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ) (j : Fin 11) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
    canonicalDescriptorScalarBank R (rg ∘ canonicalDescriptorInstallCore) L n r
      (rg ⟨28 + j.val, by have := j.isLt; omega⟩) =
        binSyms (canonicalStageWidths p).coordinateBits (repairDescriptorScalarPalette p j) := by
  dsimp only
  have he := descriptorScalarResizedBank_palette
    (canonicalDescriptorScalarInputBank R (rg ∘ canonicalDescriptorInstallCore) L n r)
    ((rg ∘ canonicalDescriptorInstallCore) ∘ canonicalDescriptorScalarSlot)
    ((hrg.comp canonicalDescriptorInstallCore_injective).comp canonicalDescriptorScalarSlot_injective)
    (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r)).coordinateBits
    (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r) j
  change canonicalDescriptorScalarBank R (rg ∘ canonicalDescriptorInstallCore) L n r _ = _ at he
  convert he using 1
  congr 1
  fin_cases j <;> rfl

theorem canonicalDescriptorInstall_blank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 101 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hblank : ∀ i : Fin 101, 39 ≤ i.val → R (rg i) = [])
    (i : Fin 101) (hi : 39 ≤ i.val) (h44 : i ≠ 44) :
    canonicalDescriptorScalarBank R (rg ∘ canonicalDescriptorInstallCore) L n r (rg i) = [] := by
  rw [canonicalDescriptorScalarBank_keep]
  · exact hblank i hi
  · have hn44 : i.val ≠ 44 := fun h => h44 (Fin.ext h)
    simp [canonicalDescriptorScalarTargets, hrg.eq_iff,
      canonicalDescriptorInstallCore, Fin.ext_iff]
    omega

theorem canonicalDescriptorInstall_widths (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 101 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n))
    (hresidue : R (rg 18) = binSyms L r.val) (q : Fin 11 × Fin 5) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    canonicalDescriptorScalarBank R (rg ∘ canonicalDescriptorInstallCore) L n r.val
      (rg (descriptorScalarInstallSlot q 0)) =
        binSyms L (repairDescriptorScalarWidth (canonicalStageWidths p) q.2) := by
  dsimp only
  let core := rg ∘ canonicalDescriptorInstallCore
  have hc : Function.Injective core := hrg.comp canonicalDescriptorInstallCore_injective
  have keep (i : Fin 46) (hi : i = 21 ∨ i = 26) :
      canonicalDescriptorScalarBank R core L n r.val (core i) =
        canonicalProfileSetupBank R (core ∘ canonicalDescriptorGeometrySlot) L n r.val (core i) := by
    rcases hi with rfl | rfl <;>
      simp [canonicalDescriptorScalarBank, descriptorScalarResizedBank, descriptorScalarBank,
        binaryResizeBatchBank, descriptorScalarResizeSlot, descriptorScalarInputIndex,
        descriptorScalarCoreSlot, canonicalDescriptorScalarInputBank,
        canonicalDescriptorScalarSlot, hc.eq_iff]
  obtain ⟨_,_,_,hs,hw⟩ := canonicalProfileSetup_parameters R
    (core ∘ canonicalDescriptorGeometrySlot) (hc.comp canonicalDescriptorGeometrySlot_injective)
    L n hlarge r hresidue
  have h21 := (keep 21 (Or.inl rfl)).trans hs
  have h26 := (keep 26 (Or.inr rfl)).trans hw
  obtain ⟨j,f⟩ := q
  fin_cases f <;>
    simp only [descriptorScalarInstallSlot, Matrix.cons_val_zero, repairDescriptorScalarWidth]
  · exact h21
  · exact h26
  · exact h26
  · exact h26
  · rw [canonicalStageWidths_selector]
    exact h26

end IntegerMultBounds.MathlibTM2.Routing
