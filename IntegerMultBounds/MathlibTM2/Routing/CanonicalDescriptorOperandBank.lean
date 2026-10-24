module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorGenerate

/-! Read the complete canonical descriptor bank from generated scalar fields.
Every empty role shares one restored blank source for frame serialization. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T A : ℕ}

def descriptorOperandSource : LiveDescriptorRole 11 → Fin 108
  | .stride j => canonicalDescriptorFieldCore (descriptorScalarDestination (j,0))
  | .base j => canonicalDescriptorFieldCore (descriptorScalarDestination (j,1))
  | .last j => canonicalDescriptorFieldCore (descriptorScalarDestination (j,2))
  | .rows j => canonicalDescriptorFieldCore (descriptorScalarDestination (j,3))
  | .sourceWidth j => canonicalDescriptorFieldCore (descriptorScalarDestination (j,4))
  | .selectorBits => descriptorSharedDestination 0
  | .group => descriptorSharedDestination 1
  | .profile (.coordinate (.arithmetic .index)) => descriptorSharedDestination 2
  | .profile (.coordinate .one) => descriptorSharedDestination 3
  | .coordinate .cursor => descriptorSharedDestination 4
  | .coordinate .one => descriptorSharedDestination 5
  | _ => 39

theorem descriptorOperandSource_field (j : Fin 11) (f : Fin 5) :
    descriptorOperandSource (descriptorScalarRole j f) =
      canonicalDescriptorFieldCore (descriptorScalarDestination (j,f)) := by
  fin_cases f <;> rfl

theorem descriptorOperandSource_shared (i : Fin 6) :
    descriptorOperandSource (descriptorSharedRole i) = descriptorSharedDestination i := by
  fin_cases i <;> rfl

theorem descriptorOperandSource_other (r : LiveDescriptorRole 11)
    (hscalar : ∀ j f, r ≠ descriptorScalarRole j f)
    (hshared : ∀ i, r ≠ descriptorSharedRole i) : descriptorOperandSource r = 39 := by
  cases r with
  | stride j => exact (hscalar j 0 rfl).elim
  | base j => exact (hscalar j 1 rfl).elim
  | last j => exact (hscalar j 2 rfl).elim
  | rows j => exact (hscalar j 3 rfl).elim
  | sourceWidth j => exact (hscalar j 4 rfl).elim
  | selectorBits => exact (hshared 0 rfl).elim
  | group => exact (hshared 1 rfl).elim
  | profile r =>
    cases r with
    | coordinate r =>
      cases r with
      | arithmetic r => cases r <;> first | exact (hshared 2 rfl).elim | rfl
      | one => exact (hshared 3 rfl).elim
      | _ => rfl
    | _ => rfl
  | coordinate r =>
    cases r with
    | cursor => exact (hshared 4 rfl).elim
    | one => exact (hshared 5 rfl).elim
    | _ => rfl
  | _ => rfl

theorem canonicalDescriptorGeneratedBank_operands (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hblank : ∀ i : Fin 108, 39 ≤ i.val → R (rg i) = [])
    (hG : 0 < canonicalRouterGap n) (hK : 0 < canonicalRouterStride n)
    (active : Fin (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r).n → Bool)
    (source : Fin (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r).n →
      SlotSource (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r) 0) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
    (fun role => canonicalDescriptorGeneratedBank R rg L n r (rg (descriptorOperandSource role))) =
      canonicalDescriptorOperands p 0 hG hK active source (canonicalStageWidths p) := by
  dsimp only
  apply canonicalDescriptorOperands_eq
  · intro j f
    rw [descriptorOperandSource_field]
    exact canonicalDescriptorGeneratedBank_field R rg hrg L n r (j,f)
  · intro i
    rw [descriptorOperandSource_shared]
    exact canonicalDescriptorGeneratedBank_shared R rg hrg L n r i
  · intro role hs hh
    rw [descriptorOperandSource_other role hs hh]
    exact canonicalDescriptorGeneratedBank_scratch R rg hrg L n r hblank 39
      (by decide) (by decide) (by decide)

end IntegerMultBounds.MathlibTM2.Routing
