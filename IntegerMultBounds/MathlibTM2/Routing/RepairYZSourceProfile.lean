module

public import IntegerMultBounds.MathlibTM2.Routing.RepairZSourceProfile
public import IntegerMultBounds.MathlibTM2.Routing.RepairYSourceProfile

/-! Both YZ profiles use the existing affine source generators: target wires
are unconditional, while control wires follow the raw activity stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section
variable {A : ℕ}

theorem repairYZTargetSourceProfile (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) :
    affineSourceProfile (repairAffineSources p X hG hK active s (some (.YZ, 0))) =
      List.ofFn (fun c : Fin p.n => (true, c.val * p.K + p.ρ)) := by
  simp [repairAffineSources, repairRotationSources, yzSources, affineSourceProfile,
    targetWire, posS, Option.elim, Nat.add_comm]

theorem repairYZControlSourceProfile (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) :
    affineSourceProfile (repairAffineSources p X hG hK active s (some (.YZ, 1))) =
      List.ofFn (fun c : Fin p.n => (active c, if active c then c.val * p.G + (p.wy + p.wc) else 0)) := by
  unfold affineSourceProfile
  apply congrArg List.ofFn
  funext c
  cases hb : active c <;>
    simp [repairAffineSources, repairRotationSources, yzSources, controlWire, posC, hb,
      Option.elim, Nat.add_comm]

theorem repairYZTargetSourceProfile_frames (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (L : ℕ) :
    (LiveDescriptorMode.ofKey (some (.YZ, 0))).profileFrames (A := A) p X hG hK active s L =
      affineProfileFrames L (List.ofFn (fun c : Fin p.n => (true, c.val * p.K + p.ρ))) :=
  congrArg (affineProfileFrames L) (repairYZTargetSourceProfile p X hG hK active s)

theorem repairYZControlSourceProfile_frames (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (Li Lk : ℕ) :
    (LiveDescriptorMode.ofKey (some (.YZ, 1))).profileFrames (A := A) p X hG hK active s (Li + Lk) =
      optionalAffineSourceWord Li Lk 0 p.G (p.wy + p.wc) (List.ofFn active) := by
  rw [optionalAffineSourceWord_profile]
  change affineProfileFrames _ _ = affineProfileFrames _ _
  rw [repairYZControlSourceProfile]
  simp only [Nat.zero_add]

end
end IntegerMultBounds.MathlibTM2.Routing
