module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorMode
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorSeparation

/-! One concrete auxiliary-bank specification supplies live profiles and scalar
operands for all jobs. Intermediate coordinate, compact and dense streams start
empty. Generation of the supplied scalar/profile inputs remains separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N J A : ℕ}

def liveDescriptorData (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths) : LiveDescriptorRole J → List (Fin (A + 4))
  | .input j => (mode j).profileFrames p X hG hK active s w.selectorBits
  | .stride j => binSyms w.strideBits ((mode j).stride p)
  | .base j => binSyms w.coordinateBits ((mode j).base p)
  | .last j => binSyms w.coordinateBits (repairCompactRows p (mode j).key - 1)
  | .rows j => binSyms w.coordinateBits (repairCompactRows p (mode j).key)
  | .sourceWidth j => binSyms w.selectorBits (repairCompactSourceWidth p X (mode j).key + 1)
  | .selectorBits => binSyms w.widthBits w.selectorBits
  | .group => binSyms w.groupBits p.G
  | .profile (.coordinate (.arithmetic .index)) => binSyms w.indexBits 0
  | .profile (.coordinate .one) => binSyms w.selectorBits 1
  | .coordinate .cursor => binSyms w.coordinateBits 0
  | .coordinate .one => binSyms w.coordinateBits 1
  | _ => []

def liveDescriptorBank (core : Fin N → List (Fin (A + 4)))
    (data : LiveDescriptorRole J → List (Fin (A + 4))) : Fin (liveDescriptorT N J) → List (Fin (A + 4)) :=
  Fin.addCases core (fun i => data ((Fintype.equivFin (LiveDescriptorRole J)).symm i))

theorem liveDescriptorBank_core (core : Fin N → List (Fin (A + 4)))
    (data : LiveDescriptorRole J → List (Fin (A + 4))) (i : Fin N) :
    liveDescriptorBank core data (liveDescriptorCore i) = core i := by
  change Fin.addCases (motive := fun _ => List (Fin (A + 4))) core
    (fun x : Fin (Fintype.card (LiveDescriptorRole J)) => data ((Fintype.equivFin (LiveDescriptorRole J)).symm x))
    (Fin.castAdd _ i) = core i
  simp

theorem liveDescriptorBank_aux (core : Fin N → List (Fin (A + 4)))
    (data : LiveDescriptorRole J → List (Fin (A + 4))) (r : LiveDescriptorRole J) :
    liveDescriptorBank core data (liveDescriptorAux r) = data r := by
  change Fin.addCases (motive := fun _ => List (Fin (A + 4))) core
    (fun x : Fin (Fintype.card (LiveDescriptorRole J)) => data ((Fintype.equivFin (LiveDescriptorRole J)).symm x))
    (Fin.natAdd N ((Fintype.equivFin (LiveDescriptorRole J)) r)) = data r
  simp

structure LiveDescriptorBounds (p : Par) (X : ℕ) (w : LiveDescriptorWidths) (mode : LiveDescriptorMode) : Prop where
  group_fits : p.G < 2 ^ w.groupBits
  stride_fits : mode.stride p < 2 ^ w.strideBits
  coordinate_fits : repairCompactRows p mode.key < 2 ^ w.coordinateBits
  group_width : w.groupBits ≤ w.coordinateBits
  slots_fit : mode.slots p ≤ 2 ^ w.indexBits
  source_fits : repairCompactSourceWidth p X mode.key + 1 < 2 ^ w.selectorBits
  selector_fits : w.selectorBits < 2 ^ w.widthBits

structure LiveDescriptorReady (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths)
    (R : Fin (liveDescriptorT N J) → List (Fin (A + 4))) : Prop where
  bounds : ∀ j, LiveDescriptorBounds p X w (mode j)
  bank : ∀ r, R (liveDescriptorAux r) = liveDescriptorData p X hG hK active s mode w r

theorem LiveDescriptorReady.update_core
    {p : Par} {X : ℕ} {hG : 0 < p.G} {hK : 0 < p.K}
    {active : Fin p.n → Bool} {s : Fin p.n → SlotSource p X}
    {mode : Fin J → LiveDescriptorMode} {w : LiveDescriptorWidths}
    {R : Fin (liveDescriptorT N J) → List (Fin (A + 4))}
    (h : LiveDescriptorReady p X hG hK active s mode w R)
    (i : Fin N) (word : List (Fin (A + 4))) :
    LiveDescriptorReady p X hG hK active s mode w (Function.update R (liveDescriptorCore i) word) := by
  refine ⟨h.bounds, ?_⟩
  intro r
  rw [liveDescriptorAux_update_core]
  exact h.bank r

theorem liveDescriptorBank_ready (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths)
    (core : Fin N → List (Fin (A + 4))) (hfit : ∀ j, LiveDescriptorBounds p X w (mode j)) :
    LiveDescriptorReady p X hG hK active s mode w
      (liveDescriptorBank core (liveDescriptorData p X hG hK active s mode w)) :=
  ⟨hfit, fun r => liveDescriptorBank_aux core _ r⟩

end
end IntegerMultBounds.MathlibTM2.Routing
