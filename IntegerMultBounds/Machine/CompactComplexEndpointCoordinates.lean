import IntegerMultBounds.Machine.NativeEndpointCharacterAddress
import IntegerMultBounds.Machine.NativeEndpointCharacterTerminal
import IntegerMultBounds.Machine.CompactComplexNonleafChildAddress
import IntegerMultBounds.Machine.NativePolynomialStageShape

/-! The endpoint character's serialized bit coordinates are the original
recursive node coordinates. All row and polynomial positions are retained;
the native codec changes only the trailing payload size. -/
namespace IntegerMultBounds.Machine.CompactComplexEndpointCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open Networks
open CompactComplexRecursiveGeometry (arity Visit node)
open ActivePrefixStageRuntimeOrdinal (highCoordinates originalPosition)
variable {s : Shape}

theorem rank_bit {D : ℕ} (x : BinaryWalsh.Address D) (t : ℕ) (ht : t<D) :
    BinaryRowColumns.scalar (Nat.testBit (FlatCoordinateLayout.rank x).val t)=
      x (ButterflyAxisWalsh.coordinate D t ht) := by
  have h := FlatCoordinateLayout.coordinate_value x (ButterflyAxisWalsh.coordinate D t ht)
  rw [ButterflyAxisWalsh.suffix_fields] at h
  have hb : Nat.testBit (FlatCoordinateLayout.rank x).val t=
      BinaryRowColumns.bit (x (ButterflyAxisWalsh.coordinate D t ht)) := by
    rw [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.one_and_eq_mod_two,h]
    generalize x (ButterflyAxisWalsh.coordinate D t ht)=z
    fin_cases z <;> decide
  rw [hb,BinaryRowColumns.scalar_bit]

def rowCoordinates {rows : ℕ} (sh : Shape) (i : Fin (rows*sh.recordWidth)) :
    BinaryWalsh.Address sh.bits :=
  FlatCoordinateLayout.coordinates ⟨i.val/sh.payload%2^sh.bits, Nat.mod_lt _ (by positivity)⟩

theorem high_coordinate (v : ActivePrefixStageParameters.Stage s) {rows : ℕ}
    (i : Fin (rows*s.recordWidth)) (column : Fin v.f) (slot : Fin v.slots) :
    BinaryRowColumns.scalar (highCoordinates v i column slot)=
      rowCoordinates s i (ButterflyAxisWalsh.coordinate s.bits
        (s.H+s.B+originalPosition v slot column)
        (by have h := NativeEndpointCharacterAddress.position_lt v slot column
            unfold Shape.bits; omega)) := by
  have hp := NativeEndpointCharacterAddress.position_lt v slot column
  have hf : s.H+s.B+originalPosition v slot column<s.bits := by unfold Shape.bits; omega
  have hb : highCoordinates v i column slot=
      Nat.testBit (FlatCoordinateLayout.rank (rowCoordinates s i)).val
        (s.H+s.B+originalPosition v slot column) := by
    simp only [rowCoordinates,FlatCoordinateLayout.rank_coordinates,Fin.val_mk,
      highCoordinates,ActivePrefixStageRuntimeOrdinal.activeOrdinal,Nat.testBit_mod_two_pow,
      hf,hp,decide_true,Bool.true_and,Nat.testBit_div_two_pow]
    congr 1
    omega
  rw [hb]
  exact rank_bit _ _ hf

theorem node_position {left k : ℕ} (rho : Fin s.chunk)
    (visit : Visit s.active left (k+1)) (ha : s.active≤s.axes)
    (pair : BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (column : Fin (arity^k)) :
    s.H+s.B+originalPosition (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) slot column=
      CompactSpectatorVisitGeometry.selected s rho.val left
        (CompactComplexNonleafChildAddress.axisIndex slot column).val := by
  simp only [originalPosition,ActivePrefixStageRuntimeOrdinal.originalAxis,
    CompactBinaryBasisSchedule.stage,node,CompactComplexNonleafChildAddress.axisIndex,
    Fin.val_cast,RecursiveInterchangeRows.pack_val,CompactSpectatorVisitGeometry.selected]
  have hs : s.active-(left+slot.val*arity^k+column.val)-1=
      s.active-1-(left+(slot.val*arity^k+column.val)) := by omega
  rw [hs]
  omega

/-- The actual native codec scanner sees exactly the enclosing recursive
node's original tensor address, including all untouched binary spectators. -/
theorem native_node_address {left k : ℕ} (rho : Fin s.chunk)
    (visit : Visit s.active left (k+1)) (ha : s.active≤s.axes)
    (pair : BinaryRowProgram.Op (Fin arity)) (rows ell p : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows)
    (i : Fin (rows*(NativePolynomialStageShape.shape s ell p).recordWidth)) :
    CompactComplexPhasePhysical.originalCoordinates
      (NativePolynomialStageShape.inputs (CompactBinaryBasisSchedule.stage (node rho visit ha) pair)
        rows ell p hG hGK hr) rfl i=
      CompactComplexNonleafChildAddress.address rho visit
        (rowCoordinates (NativePolynomialStageShape.shape s ell p) i) := by
  funext column slot
  change BinaryRowColumns.scalar (highCoordinates
    (NativePolynomialStageShape.stage (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) ell p)
    i column slot)=_
  refine (high_coordinate
    (NativePolynomialStageShape.stage (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) ell p)
    i column slot).trans ?_
  apply congrArg (rowCoordinates (NativePolynomialStageShape.shape s ell p) i)
  apply congrArg Fin.rev
  apply Fin.ext
  change s.H+s.B+originalPosition (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) slot column=
    CompactSpectatorVisitGeometry.selected s rho.val left
      (CompactComplexNonleafChildAddress.axisIndex slot column).val
  exact node_position rho visit ha pair slot column

/-- The actual aggregate character phase acts on the genuine original node
address, rather than on a separately supplied compatible coordinate map. -/
theorem terminal_node_action {left k : ℕ} (rho : Fin s.chunk)
    (visit : Visit s.active left (k+1)) (ha : s.active≤s.axes)
    (pair : BinaryRowProgram.Op (Fin arity)) (rows ell p : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows)
    (b : Wires.Address 25)
    (i : Fin (rows*(NativePolynomialStageShape.shape s ell p).recordWidth))
    (f : BinaryColumns.Arrays (25^3) (arity^k)) :
    let d := NativePolynomialStageShape.inputs
      (CompactBinaryBasisSchedule.stage (node rho visit ha) pair) rows ell p hG hGK hr
    let x := CompactComplexNonleafChildAddress.address rho visit
      (rowCoordinates (NativePolynomialStageShape.shape s ell p) i)
    BinaryPhase.phase ((AllAxisPhaseFlagsCaller.phase d.stage d.stage.slots
      (NativeEndpointCharacterTerminal.terminalWeights d.stage rfl b)
      (BinaryAddressTableData.row (NativePolynomialStageShape.shape s ell p).bits
        (i.val/(NativePolynomialStageShape.shape s ell p).payload))).val : ZMod 4)*f x=
      ComplexEndpoints.signColumns (arity^k) (ComplexEndpoints.terminalVector b) f x := by
  dsimp only
  have h := NativeEndpointCharacterTerminal.tensor_action
    (NativePolynomialStageShape.inputs (CompactBinaryBasisSchedule.stage (node rho visit ha) pair)
      rows ell p hG hGK hr) rfl b i f
  rw [native_node_address rho visit ha pair rows ell p hG hGK hr i] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexEndpointCoordinates
