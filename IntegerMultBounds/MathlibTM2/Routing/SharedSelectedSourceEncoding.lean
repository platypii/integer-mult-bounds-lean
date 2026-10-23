module

public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceEncoding
public import IntegerMultBounds.MathlibTM2.Routing.SharedSelectedSourceGenerate

/-! The shared activity-bearing raw choices compute the actual X profile;
activity affects key generation only. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {A : ℕ}

theorem repairSharedXSourceProfile_encoded (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (Li Lk : ℕ) :
    sharedSelectedSourceProfileWord (A := A) Li Lk p.K (SlotSource.regionBase p)
      (List.ofFn (fun c => (s c).gatedChoice (active c))) =
      (LiveDescriptorMode.ofKey (some (.X, 0))).profileFrames p X hG hK active s (Li + Lk) := by
  rw [sharedSelectedSourceProfileWord_profile]
  change _ = affineProfileFrames _ (affineSourceProfile _)
  rw [repairXSourceProfile_coordinates, List.map_ofFn]
  apply congrArg (affineProfileFrames (Li + Lk))
  apply congrArg List.ofFn
  funext c
  simp [Function.comp_apply, SlotSource.gatedChoice_position, SlotSource.sourceWire_coordinates]

end
end IntegerMultBounds.MathlibTM2.Routing
