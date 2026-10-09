import IntegerMultBounds.Networks.ComplexPhaseRowSchedule
import IntegerMultBounds.Machine.CompactBinaryBasisSchedule

/-! Actual fixed complex25 phase words determine literal compact stages on
an original node with the established 15625 consecutive slots. Geometry is
still supplied by that node; no physical tape execution is asserted here. -/
namespace IntegerMultBounds.Machine.CompactComplexPhaseSchedule
noncomputable section
open Networks.BinaryRowProgram
open Networks.ComplexPhaseRowSchedule
open CompactBinaryBasisSchedule
open CompactGadgetReservationShape (Shape)

variable {ι κ : Type*}
def mapOp (e : ι ≃ κ) (op : Op ι) : Op κ where
  target := e op.target
  source := e op.source
  distinct := e.injective.ne op.distinct

variable [DecidableEq ι] [DecidableEq κ]
theorem execute_map (e : ι ≃ κ) (op : Op ι) (x : ι → ZMod 2) :
    (mapOp e op).execute (x ∘ e.symm) = op.execute x ∘ e.symm := by
  simpa [mapOp, Op.execute] using
    (Function.update_comp_eq_of_injective x e.symm.injective (e op.target)
      (x op.target + x op.source)).symm

theorem run_map (e : ι ≃ κ) (ops : List (Op ι)) (x : ι → ZMod 2) :
    Networks.BinaryRowProgram.run (ops.map (mapOp e)) (x ∘ e.symm) =
      Networks.BinaryRowProgram.run ops x ∘ e.symm := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    change Networks.BinaryRowProgram.run (ops.map (mapOp e))
      ((mapOp e op).execute (x ∘ e.symm)) = _
    rw [execute_map, ih]
    rfl

variable {s : Shape}
def nodeWord (node : Node s) (hslots : node.slots = 25 ^ 3) (edge : Edge) :
    List (Op (Fin node.slots)) :=
  (Networks.ComplexPhaseRowSchedule.word edge).map (mapOp (finCongr hslots.symm))

def stages (node : Node s) (hslots : node.slots = 25 ^ 3) (edge : Edge) :
    List (ActivePrefixStageParameters.Stage s) := (nodeWord node hslots edge).map (stage node)

theorem stages_length (node : Node s) (hslots : node.slots = 25 ^ 3) (edge : Edge) :
    (stages node hslots edge).length = (Networks.ComplexPhaseRowSchedule.word edge).length := by
  simp [stages, nodeWord]

/-- The original node's literal pair list has exactly the actual fixed edge's
coordinate action after the proved slot-count identification. -/
theorem nodeWord_run (node : Node s) (hslots : node.slots = 25 ^ 3) (edge : Edge)
    (x : Fin (25 ^ 3) → ZMod 2) :
    Networks.BinaryRowProgram.run (nodeWord node hslots edge) (x ∘ finCongr hslots) =
      Networks.BinaryRowProgram.run (Networks.ComplexPhaseRowSchedule.word edge) x ∘ finCongr hslots :=
  run_map (finCongr hslots.symm) _ x

end
end IntegerMultBounds.Machine.CompactComplexPhaseSchedule
