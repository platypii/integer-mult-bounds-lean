module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalProfileScope
public import IntegerMultBounds.MathlibTM2.Routing.MatchingFixedProfile

/-! Canonical setup operates entirely inside the fixed producer's core. Its
workspace table and all compiler scratch retain the declared bank layout. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {N A : ℕ}

theorem canonicalProfileSetupBank_production
    (coreWords : Fin N → List (Fin (A + 4))) (rg : Fin 28 → Fin N)
    (count table stride residue : List (Fin (A + 4))) (L n r : ℕ) :
    canonicalProfileSetupBank (matchingProductionBank coreWords count table stride residue)
      (matchingCoreEmbed N ∘ rg) L n r =
      matchingProductionBank (canonicalProfileSetupBank coreWords rg L n r) count table stride residue := by
  simp only [canonicalProfileSetupBank, canonicalDescriptorWidthsBank,
    canonicalResidueGeometryBank, canonicalGeometryBank, routerReservoirGeometryBank,
    routerGeometryBank, matchingProductionBank_updateCore, Function.comp_apply]

end IntegerMultBounds.MathlibTM2.Routing
