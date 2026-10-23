module

public import IntegerMultBounds.MathlibTM2.Routing.InactiveProfileRepair
public import IntegerMultBounds.MathlibTM2.Routing.EmbeddedRepairHeaderData

/-! Header generation around the inactive-profile bank preserves both live
inputs and the seven-tape profile-generation workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev repairInactiveProfileT := liveInactiveProfileT repairT 11
abbrev inactiveProfileHeaderT := sharedHeaderT repairInactiveProfileT

def inactiveProfileRaw (i : Fin repairT) : Fin repairInactiveProfileT :=
  liveInactiveProfileCore (liveDescriptorCore i)

theorem inactiveProfileRaw_injective : Function.Injective inactiveProfileRaw :=
  liveInactiveProfileCore_injective.comp liveDescriptorCore_injective

def inactiveProfileHeaderRaw (i : Fin repairT) : Fin inactiveProfileHeaderT :=
  embeddedRepairHeaderRaw inactiveProfileRaw i

def inactiveProfileHeaderBank (c : Fin 2) : RepairHeaderReg → Fin inactiveProfileHeaderT :=
  embeddedRepairHeaderBank inactiveProfileRaw c

@[simp] theorem inactiveProfileHeaderBank_header (c : Fin 2) (k : Fin 5) :
    inactiveProfileHeaderBank c (.exchange (.base (.header k))) = inactiveProfileHeaderRaw (repairRoutingConfig (.header c k)) := rfl

@[simp] theorem inactiveProfileHeaderRaw_eq (i : Fin repairT) :
    embeddedRepairHeaderRaw inactiveProfileRaw i = inactiveProfileHeaderRaw i := rfl

variable {A : ℕ} (p : Par) (X rb R B : ℕ)

theorem inactiveProfileHeaderPair_liveAux
    (bank : Fin inactiveProfileHeaderT → List (Fin (A + 4))) (r : LiveDescriptorRole 11) :
    repairHeaderPairBank p X rb R B inactiveProfileHeaderBank bank
      (sharedHeaderCore (liveInactiveProfileCore (liveDescriptorAux r))) =
      bank (sharedHeaderCore (liveInactiveProfileCore (liveDescriptorAux r))) := by
  apply embeddedRepairHeaderPair_keep
  intro c k
  exact liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux _ r).symm

theorem inactiveProfileHeaderPair_outerAux
    (bank : Fin inactiveProfileHeaderT → List (Fin (A + 4))) (i : Fin 7) :
    repairHeaderPairBank p X rb R B inactiveProfileHeaderBank bank (sharedHeaderCore (liveInactiveProfileAux i)) =
      bank (sharedHeaderCore (liveInactiveProfileAux i)) := by
  apply embeddedRepairHeaderPair_keep
  intro c k
  exact liveInactiveProfileAux_core _ _

theorem inactiveProfileHeaderPair_raw_keep
    (bank : Fin inactiveProfileHeaderT → List (Fin (A + 4))) (i : Fin repairT)
    (hi : ∀ c k, i ≠ repairRoutingConfig (.header c k)) :
    repairHeaderPairBank p X rb R B inactiveProfileHeaderBank bank (inactiveProfileHeaderRaw i) =
      bank (inactiveProfileHeaderRaw i) :=
  embeddedRepairHeaderPair_raw_keep inactiveProfileRaw inactiveProfileRaw_injective p X rb R B bank i hi

end
end IntegerMultBounds.MathlibTM2.Routing
