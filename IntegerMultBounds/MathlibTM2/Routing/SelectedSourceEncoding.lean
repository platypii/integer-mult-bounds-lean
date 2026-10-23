module

public import IntegerMultBounds.MathlibTM2.Routing.SelectedSourceCoordinates
public import IntegerMultBounds.MathlibTM2.Routing.SelectedSourceGenerate

/-! Encode typed source choices as raw tags and local coordinates. The address
computed by the fixed interpreter is exactly the source's physical wire. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def sourceTagLo (tag : Fin 4) : Bool := decide (tag.val % 2 = 1)
def sourceTagHi (tag : Fin 4) : Bool := decide (2 ≤ tag.val)

theorem sourceTagIndex_bits (tag : Fin 4) : sourceTagIndex (sourceTagLo tag) (sourceTagHi tag) = tag := by
  fin_cases tag <;> decide

namespace SlotSource
variable {p : Par} {X : ℕ}

def choice (x : SlotSource p X) : SelectedSourceChoice :=
  ⟨x.index, x.offset, sourceTagLo x.tag, sourceTagHi x.tag⟩

theorem choice_tag (x : SlotSource p X) : x.choice.tag = x.tag := sourceTagIndex_bits x.tag

theorem choice_position (x : SlotSource p X) :
    x.choice.position p.K (regionBase p) = (sourceWire p X x).val := by
  unfold SelectedSourceChoice.position
  rw [choice_tag, sourceWire_coordinates]
  rfl

theorem choice_index_fit (x : SlotSource p X) (Li : ℕ) (hn : p.n ≤ 2 ^ Li) :
    x.choice.index < 2 ^ Li := by
  cases x with
  | low r => simp [choice, index]
  | digit c r => exact c.isLt.trans_le hn
  | high r => simp [choice, index]
  | spectator r => simp [choice, index]

end SlotSource

noncomputable section
variable {A : ℕ}

theorem repairXSourceProfile_encoded (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (Li Lk : ℕ) :
    selectedSourceProfileWord (A := A) Li Lk p.K (SlotSource.regionBase p)
      (List.ofFn (fun c => (s c).choice)) =
      (LiveDescriptorMode.ofKey (some (.X, 0))).profileFrames p X hG hK active s (Li + Lk) := by
  rw [selectedSourceProfileWord_profile]
  change _ = affineProfileFrames _ (affineSourceProfile _)
  rw [repairXSourceProfile_coordinates]
  rw [List.map_ofFn]
  apply congrArg (affineProfileFrames (Li + Lk))
  apply congrArg List.ofFn
  funext c
  simp [Function.comp_apply, SlotSource.choice_position, SlotSource.sourceWire_coordinates]

end
end IntegerMultBounds.MathlibTM2.Routing
