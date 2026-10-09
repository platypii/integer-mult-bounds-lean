import IntegerMultBounds.Machine.ActivePrefixStageRuntimeOrdinal
import IntegerMultBounds.Machine.ActivePrefixStagePairSchedule

/-! Literal physical row-addition lists act on original serialized addresses
exactly as the Boolean binary basis word, despite changing target splits. -/
namespace IntegerMultBounds.Machine.ActivePrefixStagePairCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixStageRuntimeOrdinal (rawCoordinates)
open ActivePrefixStagePairData (changePair)
open ActivePrefixDirtyControlGlobalSwap (index)
open ActiveRepairLayoutRecordsData (Array)
open Networks.BinaryRowProgram (Op)
variable {s : Shape}

def addressEquiv (d : Inputs s) :=
  CompactActiveTargetLayout.indexEquiv s ((geometry d).n*(geometry d).b) ((geometry d).n*(geometry d).q)
    (geometry d).before (geometry d).after d.rows (geometry d).compactFits (geometry d).activeSize

theorem index_decode (d : Inputs s) (k : Fin (d.rows*s.recordWidth)) :
    index s (geometry d) ((addressEquiv d).symm k)=k :=
  (addressEquiv d).apply_symm_apply k

def destination (d : Inputs s) (op : Op (Fin d.stage.slots)) (k : Fin (d.rows*s.recordWidth)) :=
  index s (geometry (changePair d op))
    (ActivePrefixStageRuntimeSelected.destination (changePair d op) ((addressEquiv (changePair d op)).symm k))

theorem execute (d : Inputs s) (op : Op (Fin d.stage.slots)) (k : Fin (d.rows*s.recordWidth)) :
    rawCoordinates d.stage (destination d op k)=Networks.BinaryRowColumns.execute op (rawCoordinates d.stage k) := by
  let input := changePair d op
  let i := (addressEquiv input).symm k
  have h := ActivePrefixStageRuntimeCoordinates.execute input i
  rw [←ActivePrefixStageRuntimeOrdinal.coordinates_at_index,
    ←ActivePrefixStageRuntimeOrdinal.coordinates_at_index] at h
  have hi : index s (geometry input) i=k := index_decode input k
  rw [hi] at h
  have ho : ActivePrefixStageRuntimeCoordinates.op input=op := rfl
  rw [ho] at h
  exact h

theorem entry (d : Inputs s) (op : Op (Fin d.stage.slots)) (x : Array s d.rows)
    (k : Fin (d.rows*s.recordWidth)) : ActivePrefixStagePairRun.action d op x (destination d op k)=x k := by
  have h := ActivePrefixStageRuntimeSelected.entry (changePair d op) x ((addressEquiv (changePair d op)).symm k)
  rw [index_decode] at h
  exact h

def run (d : Inputs s) : List (Op (Fin d.stage.slots)) → Fin (d.rows*s.recordWidth) → Fin (d.rows*s.recordWidth)
  | [],k => k
  | op::ops,k => run d ops (destination d op k)

theorem run_coordinates (d : Inputs s) (ops : List (Op (Fin d.stage.slots))) (k : Fin (d.rows*s.recordWidth)) :
    rawCoordinates d.stage (run d ops k)=Networks.BinaryRowColumns.run ops (rawCoordinates d.stage k) := by
  induction ops generalizing k with
  | nil => rfl
  | cons op ops ih =>
    change rawCoordinates d.stage (run d ops (destination d op k))=_
    rw [ih,execute]
    rfl

/-- The chronological physical machine moves each original array cell to
exactly the address obtained by the literal Boolean row-addition word. -/
theorem run_entry (d : Inputs s) (ops : List (Op (Fin d.stage.slots))) (x : Array s d.rows)
    (k : Fin (d.rows*s.recordWidth)) : ActivePrefixStagePairSchedule.result d ops x (run d ops k)=x k := by
  induction ops generalizing x k with
  | nil => rfl
  | cons op ops ih =>
    exact (ih (ActivePrefixStagePairRun.action d op x) (destination d op k)).trans (entry d op x k)

theorem run_f2_coordinates (d : Inputs s) (ops : List (Op (Fin d.stage.slots))) (k : Fin (d.rows*s.recordWidth))
    (axis : Fin d.stage.f) :
    Networks.BinaryRowColumns.coordinates (rawCoordinates d.stage (run d ops k)) axis=
      Networks.BinaryRowProgram.run ops (Networks.BinaryRowColumns.coordinates (rawCoordinates d.stage k) axis) := by
  rw [run_coordinates,Networks.BinaryRowColumns.run_coordinates]

theorem high_execute (d : Inputs s) (op : Op (Fin d.stage.slots)) (k : Fin (d.rows*s.recordWidth)) :
    ActivePrefixStageRuntimeOrdinal.highCoordinates d.stage (destination d op k)=
      Networks.BinaryRowColumns.execute op (ActivePrefixStageRuntimeOrdinal.highCoordinates d.stage k) := by
  funext axis slot
  have h := congrFun (congrFun (execute d op k) (ActivePrefixStageRuntimeOrdinal.reverseAxis axis)) slot
  simpa only [ActivePrefixStageRuntimeOrdinal.high_coordinates,Networks.BinaryRowColumns.execute,
    Function.update_apply] using h

theorem high_run_coordinates (d : Inputs s) (ops : List (Op (Fin d.stage.slots))) (k : Fin (d.rows*s.recordWidth)) :
    ActivePrefixStageRuntimeOrdinal.highCoordinates d.stage (run d ops k)=
      Networks.BinaryRowColumns.run ops (ActivePrefixStageRuntimeOrdinal.highCoordinates d.stage k) := by
  induction ops generalizing k with
  | nil => rfl
  | cons op ops ih =>
    change ActivePrefixStageRuntimeOrdinal.highCoordinates d.stage (run d ops (destination d op k))=_
    rw [ih,high_execute]
    rfl

/-- The original high-to-low axis coordinates undergo the requested basis
change at every physical address. No row-action premise is assumed. -/
theorem basis_coordinates {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (d : Inputs s) (old new : Module.Basis (Fin d.stage.slots) (ZMod 2) E)
    (k : Fin (d.rows*s.recordWidth)) (axis : Fin d.stage.f) :
    Networks.BinaryRowColumns.coordinates
      (ActivePrefixStageRuntimeOrdinal.highCoordinates d.stage (run d (Networks.BinaryRowProgram.basisWord old new) k)) axis=
      new.equivFun (old.equivFun.symm (Networks.BinaryRowColumns.coordinates
        (ActivePrefixStageRuntimeOrdinal.highCoordinates d.stage k) axis)) := by
  rw [high_run_coordinates,Networks.BinaryRowColumns.run_coordinates]
  simpa only [LinearEquiv.apply_symm_apply] using Networks.BinaryRowProgram.basisWord_run old new
    (old.equivFun.symm (Networks.BinaryRowColumns.coordinates
      (ActivePrefixStageRuntimeOrdinal.highCoordinates d.stage k) axis))

end
end IntegerMultBounds.Machine.ActivePrefixStagePairCoordinates
