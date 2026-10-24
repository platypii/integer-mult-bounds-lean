module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorScalarLayout

/-! Existing canonical setup already computes all three source words needed
for the remaining auxiliary banks. No further numeric input is necessary. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T A : ℕ}

theorem canonicalAuxiliarySources (R : Fin T → List (Fin (A+4)))
    (rg : Fin 46 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n))
    (hresidue : R (rg 18) = binSyms L r.val) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let bank := canonicalDescriptorScalarInputBank R rg L n r.val
    bank (rg 11) = binSyms L p.n ∧
      bank (rg 25) = binSyms L (canonicalStageWidths p).indexBits ∧
      bank (rg 44) = binSyms L p.wy := by
  dsimp only
  have params := canonicalProfileSetup_parameters R (rg ∘ canonicalDescriptorGeometrySlot)
    (hrg.comp canonicalDescriptorGeometrySlot_injective) L n hlarge r hresidue
  have count : canonicalDescriptorScalarInputBank R rg L n r.val (rg 11) =
      binSyms L (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val).n := by
    simpa [canonicalDescriptorScalarInputBank,canonicalDescriptorGeometrySlot,Function.comp_def,
      hrg.eq_iff] using params.2.2.1
  have widths := canonicalDescriptorWidthsBank_router
    (canonicalResidueGeometryBank R (rg ∘ canonicalDescriptorGeometrySlot ∘ canonicalProfileGeometrySlot) L n r.val)
    (rg ∘ canonicalDescriptorGeometrySlot ∘ canonicalProfileWidthSlot)
    ((hrg.comp canonicalDescriptorGeometrySlot_injective).comp canonicalProfileWidthSlot_injective) L n hlarge r
  have index : canonicalDescriptorScalarInputBank R rg L n r.val (rg 25) =
      binSyms L (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n)
        (canonicalRouterGap n) r.val)).indexBits := by
    simpa [canonicalDescriptorScalarInputBank,canonicalProfileSetupBank,canonicalDescriptorGeometrySlot,
      canonicalProfileWidthSlot,Function.comp_def,hrg.eq_iff] using widths.2.2.1
  have target := (canonicalDescriptorScalarInputBank_ready R rg hrg L n hlarge r hresidue).1 3
  refine ⟨count,index,?_⟩
  simpa [canonicalDescriptorScalarSlot,descriptorScalarInputIndex,repairDescriptorScalarPalette,
    Function.comp_def] using target

end IntegerMultBounds.MathlibTM2.Routing
