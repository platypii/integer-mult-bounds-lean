import IntegerMultBounds.Networks.BinaryRowProgram
import IntegerMultBounds.Machine.ActivePrefixStageParameters

/-! Original consecutive node geometry and actual binary bases determine every
literal compact stage. A basis decomposition is proved, not a caller premise.
This module asserts address-coordinate semantics, not physical list execution. -/
namespace IntegerMultBounds.Machine.CompactBinaryBasisSchedule

open Module
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open Networks.BinaryRowProgram

/-- A recursive node's actual consecutive equal-width slots and surrounding
active axes. The selected column is shared by its binary basis schedule. -/
structure Node (s : Shape) where
  slots : ℕ
  f : ℕ
  left : ℕ
  right : ℕ
  rho : ℕ
  activeAxes : left + slots*f + right = s.active
  positiveWidth : 0 < f
  widthFits : f ≤ s.axes
  selectedFits : rho < s.chunk

variable {s : Shape}

def stage (node : Node s) (op : Op (Fin node.slots)) : Stage s where
  slots := node.slots
  f := node.f
  left := node.left
  right := node.right
  rho := node.rho
  source := op.source
  target := op.target
  distinct := op.distinct.symm
  activeAxes := node.activeAxes
  positiveWidth := node.positiveWidth
  widthFits := node.widthFits
  selectedFits := node.selectedFits

noncomputable def schedule {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (node : Node s) (old new : Basis (Fin node.slots) (ZMod 2) E) : List (Stage s) :=
  (basisWord old new).map (stage node)

/-- The number of row additions depends only on the two fixed bases, never
on runtime slot width, selected column, or reserved-field sizes. -/
theorem schedule_length {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (node : Node s) (old new : Basis (Fin node.slots) (ZMod 2) E) :
    (schedule node old new).length = (basisWord old new).length := by
  simp [schedule]

/-- Every scheduled stage retains literal source/target order and the same
node width and selected column; no direction flag is supplied by the caller. -/
theorem schedule_members {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (node : Node s) (old new : Basis (Fin node.slots) (ZMod 2) E)
    (v : Stage s) (hv : v ∈ schedule node old new) :
    ∃ op ∈ basisWord old new, v = stage node op := by
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hv
  exact ⟨op, hop, rfl⟩

/-- The chosen fixed stage pairs perform the required basis change in each
of the node's f selected coordinates independently. -/
theorem selected_coordinate_run {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (node : Node s) (old new : Basis (Fin node.slots) (ZMod 2) E)
    (x : Fin node.f → E) (column : Fin node.f) :
    Networks.BinaryRowProgram.run (basisWord old new) (old.equivFun (x column)) = new.equivFun (x column) :=
  basisWord_run old new (x column)

end IntegerMultBounds.Machine.CompactBinaryBasisSchedule
