module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorMode

/-! The first Z source profile is the activity-gated affine control stream.
Its selectors are generated from the control stride and base. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ}

theorem repairZSourceProfile (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) :
    affineSourceProfile (repairAffineSources p X hG hK active s (some (.Z, 0))) =
      List.ofFn (fun c : Fin p.n => (active c, if active c then c.val * p.G + p.wc else 0)) := by
  unfold affineSourceProfile
  apply congrArg List.ofFn
  funext c
  cases hb : active c <;>
    simp [repairAffineSources, repairRotationSources, controlWire, posC, hb, Option.elim, Nat.add_comm]

theorem repairZSourceProfile_frames (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (Li Lk : ℕ) :
    (LiveDescriptorMode.ofKey (some (.Z, 0))).profileFrames (A := A) p X hG hK active s (Li + Lk) =
      optionalAffineSourceWord Li Lk 0 p.G p.wc (List.ofFn active) := by
  rw [optionalAffineSourceWord_profile]
  change affineProfileFrames _ _ = affineProfileFrames _ _
  rw [repairZSourceProfile]
  simp only [Nat.zero_add]

end
end IntegerMultBounds.MathlibTM2.Routing
