module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceStep
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorMode

/-! The first Y source profile is a live affine counter stream. Its selectors
need no supplied source table or activity decisions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ}

theorem repairYSourceProfile (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) :
    affineSourceProfile (repairAffineSources p X hG hK active s (some (.Y, 0))) =
      List.ofFn (fun c : Fin p.n => (true, c.val * p.K + p.ρ)) := by
  simp [repairAffineSources, repairRotationSources, affineSourceProfile, targetWire, posS, Option.elim,
    Nat.add_comm]

theorem repairYSourceProfile_frames (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (L : ℕ) :
    (LiveDescriptorMode.ofKey (some (.Y, 0))).profileFrames (A := A) p X hG hK active s L =
      affineProfileFrames L (List.ofFn (fun c : Fin p.n => (true, c.val * p.K + p.ρ))) := by
  exact congrArg (affineProfileFrames L) (repairYSourceProfile p X hG hK active s)

end
end IntegerMultBounds.MathlibTM2.Routing
