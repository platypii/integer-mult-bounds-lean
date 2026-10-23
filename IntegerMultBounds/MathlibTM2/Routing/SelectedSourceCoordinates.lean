module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorMode

/-! Raw source choices consist of a region tag and local coordinates. The key
and X profiles share physical-source arithmetic; only key activity differs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

namespace SlotSource
variable {p : Par} {X : ℕ}

def tag : SlotSource p X → Fin 4
  | .low _ => 0
  | .digit _ _ => 1
  | .high _ => 2
  | .spectator _ => 3

def index : SlotSource p X → ℕ
  | .digit c _ => c.val
  | _ => 0

def offset : SlotSource p X → ℕ
  | .low r | .high r | .spectator r => r.val
  | .digit _ r => r.val

def regionBase (p : Par) : Fin 4 → ℕ :=
  ![0, p.ρ, p.ρ + p.n * p.K, p.wy + 2 * p.wc]

theorem sourceWire_coordinates (x : SlotSource p X) :
    (sourceWire p X x).val = x.index * p.K + regionBase p x.tag + x.offset := by
  cases x <;> simp [sourceWire, index, offset, tag, regionBase, Nat.add_comm]

end SlotSource

noncomputable section

theorem repairXSourceProfile_coordinates (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) :
    affineSourceProfile (repairAffineSources p X hG hK active s (some (.X, 0))) =
      List.ofFn (fun c : Fin p.n => (true,
        (s c).index * p.K + SlotSource.regionBase p (s c).tag + (s c).offset)) := by
  simp [repairAffineSources, repairRotationSources, affineSourceProfile, Option.elim, SlotSource.sourceWire_coordinates]

theorem repairKeySourceProfile_coordinates (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) :
    affineSourceProfile (repairAffineSources p X hG hK active s none) =
      List.ofFn (fun c : Fin p.n => (active c, if active c then
        (s c).index * p.K + SlotSource.regionBase p (s c).tag + (s c).offset else 0)) := by
  unfold affineSourceProfile
  apply congrArg List.ofFn
  funext c
  cases hb : active c <;>
    simp [repairAffineSources, selectiveKeySources, hb, Option.elim, SlotSource.sourceWire_coordinates]

end
end IntegerMultBounds.MathlibTM2.Routing
