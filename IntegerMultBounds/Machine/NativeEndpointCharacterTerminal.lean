import IntegerMultBounds.Machine.NativeEndpointCharacterReadout

/-! The actual fixed terminal-vector sign correction specializes the physical
aggregate character to the exceptional complex network source and sink. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterTerminal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open NativeEndpointCharacterReadout (weights coordinates)
open Networks
variable {s : Shape}

def vector (v : ActivePrefixStageParameters.Stage s) (hslots : v.slots=25^3)
    (b : Wires.Address 25) : BinaryWalsh.Address v.slots :=
  ComplexEndpoints.terminalVector b ∘ finCongr hslots

def terminalWeights (v : ActivePrefixStageParameters.Stage s) (hslots : v.slots=25^3)
    (b : Wires.Address 25) := weights v (vector v hslots b)

theorem length (v : ActivePrefixStageParameters.Stage s) (hslots : v.slots=25^3)
    (b : Wires.Address 25) : (terminalWeights v hslots b).length=v.slots := by
  simp [terminalWeights,weights]

private theorem chi_cast {m n : ℕ} (h : m=n) (u : BinaryWalsh.Address n) (x : BinaryWalsh.Address m) :
    BinaryWalsh.chi (u ∘ finCongr h) x=BinaryWalsh.chi u (x ∘ finCongr h.symm) := by
  subst n
  rfl

theorem character (d : Inputs s) (hslots : d.stage.slots=25^3)
    (b : Wires.Address 25) (k : Fin (d.rows*s.recordWidth)) :
    BinaryPhase.phase ((AllAxisPhaseFlagsCaller.phase d.stage d.stage.slots
      (terminalWeights d.stage hslots b)
      (BinaryAddressTableData.row s.bits (k.val/s.payload))).val : ZMod 4)=
      ∏ j : Fin d.stage.f,BinaryWalsh.chi (ComplexEndpoints.terminalVector b)
        (CompactComplexPhasePhysical.originalCoordinates d hslots k j) := by
  unfold terminalWeights
  rw [NativeEndpointCharacterReadout.character]
  apply Finset.prod_congr rfl
  intro j _
  exact chi_cast hslots (ComplexEndpoints.terminalVector b) (coordinates d.stage k j)

theorem tensor_action (d : Inputs s) (hslots : d.stage.slots=25^3)
    (b : Wires.Address 25) (k : Fin (d.rows*s.recordWidth))
    (f : BinaryColumns.Arrays (25^3) d.stage.f) :
    BinaryPhase.phase ((AllAxisPhaseFlagsCaller.phase d.stage d.stage.slots
      (terminalWeights d.stage hslots b)
      (BinaryAddressTableData.row s.bits (k.val/s.payload))).val : ZMod 4)*
      f (CompactComplexPhasePhysical.originalCoordinates d hslots k)=
    ComplexEndpoints.signColumns d.stage.f (ComplexEndpoints.terminalVector b) f
      (CompactComplexPhasePhysical.originalCoordinates d hslots k) := by
  rw [character,ComplexEndpoints.signColumns_apply]

end
end IntegerMultBounds.Machine.NativeEndpointCharacterTerminal
