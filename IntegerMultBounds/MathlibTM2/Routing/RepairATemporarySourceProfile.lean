module

public import IntegerMultBounds.MathlibTM2.Routing.RepairYSourceProfile

/-! The second A profile enumerates the temporary wires in their natural order.
Its grouped destination positions do not change this affine source sequence. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section
variable {A : ℕ}

theorem repairATemporarySourceProfile (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) :
    affineSourceProfile (repairRotationSources p X hG hK active s .A 1) =
      List.ofFn (fun c : Fin (p.n * p.G) => (true, c.val)) := by
  simp [repairRotationSources, repairRotationSlots, aSources, affineSourceProfile, tempWire, Option.elim]

theorem repairATemporarySourceProfile_frames (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (L : ℕ) :
    (LiveDescriptorMode.ofKey (some (.A, 1))).profileFrames (A := A) p X hG hK active s L =
      affineProfileFrames L (List.ofFn (fun c : Fin (p.n * p.G) => (true, c.val))) :=
  congrArg (affineProfileFrames L) (repairATemporarySourceProfile p X hG hK active s)

end
end IntegerMultBounds.MathlibTM2.Routing
