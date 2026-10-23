module

public import IntegerMultBounds.MathlibTM2.Routing.SelectedSourceEncoding
public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceGenerate

/-! Encode typed source choices and activity for the key-profile interpreter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

namespace SlotSource
variable {p : Par} {X : ℕ}

def gatedChoice (x : SlotSource p X) (enabled : Bool) : GatedSelectedSourceChoice :=
  ⟨x.index, x.offset, sourceTagLo x.tag, sourceTagHi x.tag, enabled⟩

theorem gatedChoice_tag (x : SlotSource p X) (enabled : Bool) :
    (x.gatedChoice enabled).tag = x.tag := sourceTagIndex_bits x.tag

theorem gatedChoice_position (x : SlotSource p X) (enabled : Bool) :
    (x.gatedChoice enabled).position p.K (regionBase p) = (sourceWire p X x).val := by
  unfold GatedSelectedSourceChoice.position
  rw [gatedChoice_tag, sourceWire_coordinates]
  rfl

theorem gatedChoice_index_fit (x : SlotSource p X) (enabled : Bool) (Li : ℕ)
    (hn : p.n ≤ 2 ^ Li) : (x.gatedChoice enabled).index < 2 ^ Li :=
  x.choice_index_fit Li hn

end SlotSource

noncomputable section
variable {A : ℕ}

theorem repairKeySourceProfile_encoded (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (Li Lk : ℕ) :
    gatedSelectedSourceProfileWord (A := A) Li Lk p.K (SlotSource.regionBase p)
      (List.ofFn (fun c => (s c).gatedChoice (active c))) =
      (LiveDescriptorMode.ofKey none).profileFrames p X hG hK active s (Li + Lk) := by
  rw [gatedSelectedSourceProfileWord_profile]
  change _ = affineProfileFrames _ (affineSourceProfile _)
  rw [repairKeySourceProfile_coordinates, List.map_ofFn]
  apply congrArg (affineProfileFrames (Li + Lk))
  apply congrArg List.ofFn
  funext c
  change (active c, if active c then ((s c).gatedChoice (active c)).position p.K (SlotSource.regionBase p) else 0) = _
  rw [SlotSource.gatedChoice_position, SlotSource.sourceWire_coordinates]

end
end IntegerMultBounds.MathlibTM2.Routing
