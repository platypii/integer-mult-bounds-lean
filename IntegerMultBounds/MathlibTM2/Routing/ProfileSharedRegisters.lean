module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileClosedGenerate
public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileGenerate

/-! Embed the affine profile engine in the grouped engine's register roles.
Both descriptor paths can therefore share one profile workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

def affineGroupedRole : AffineProfileReg → GroupedProfileReg
  | .src => .src
  | .archive => .archive
  | .activity => .activity
  | .wire => .coordinate .wire
  | .loadTmp => .loadTmp
  | .index => .coordinate (.arithmetic .index)
  | .stride => .coordinate (.arithmetic .stride)
  | .product => .coordinate (.arithmetic .product)
  | .offset => .coordinate (.arithmetic .base)
  | .pos => .coordinate (.arithmetic .dst)
  | .muls => .coordinate (.arithmetic .muls)
  | .mult => .coordinate (.arithmetic .mult)
  | .last => .coordinate .last
  | .one => .coordinate .one
  | .selector => .coordinate .selector
  | .gap => .coordinate .gap
  | .dst => .coordinate .dst
  | .tx => .coordinate (.arithmetic .tx)
  | .ty => .coordinate (.arithmetic .ty)
  | .tz => .coordinate (.arithmetic .tz)

theorem affineGroupedRole_injective : Function.Injective affineGroupedRole := by
  intro r s he
  cases r <;> cases s <;> simp_all [affineGroupedRole]

def sharedAffineProfile {T : ℕ} (rg : GroupedProfileReg → Fin T) : AffineProfileReg → Fin T :=
  rg ∘ affineGroupedRole

theorem sharedAffineProfile_injective {T : ℕ} (rg : GroupedProfileReg → Fin T)
    (hrg : Function.Injective rg) : Function.Injective (sharedAffineProfile rg) :=
  hrg.comp affineGroupedRole_injective

theorem sharedAffineProfile_output {T : ℕ} (rg : GroupedProfileReg → Fin T) :
    sharedAffineProfile rg .dst = rg (.coordinate .dst) := rfl

end IntegerMultBounds.MathlibTM2.Routing
