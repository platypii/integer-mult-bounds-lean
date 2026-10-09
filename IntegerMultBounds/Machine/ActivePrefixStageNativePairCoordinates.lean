import IntegerMultBounds.Machine.ActivePrefixStageNativePairSchedule
import IntegerMultBounds.Machine.ActivePrefixStagePairCoordinates

/-! Canonical native rows use the original serialized address ordinals. Each
physical native instruction therefore has exactly the original Boolean basis
word's address semantics, including all spectators and payload record starts. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativePairCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixStageNativeRows (ordinal recordOf rowDestination Rows)
open ActivePrefixStageTripleWords (count recordEquiv cellAt)
open ActiveRepairLayoutRecordsShape
open ActivePrefixDirtyControlGlobalSwap (index)
open ActivePrefixStagePairData (changePair)
open Networks.BinaryRowProgram (Op)
variable {s : Shape}

def start (d : Inputs s) (r : Fin (count d)) : Fin (d.rows*s.recordWidth) :=
  ⟨r.val*s.payload,by
    have hp : 0<s.payload := by have := d.hrecord; omega
    have hv := record_count s d.rows
    change count d*s.payload=d.rows*s.recordWidth at hv
    have h := Nat.mul_lt_mul_of_pos_right r.isLt hp
    rwa [hv] at h⟩

theorem index_ordinal (d : Inputs s) (i : Address d) :
    (index s (geometry d) i).val=(ordinal d i).val*s.payload+i.payload.val := by
  exact cell_index s ((geometry d).n*(geometry d).b) ((geometry d).n*(geometry d).q)
    (geometry d).before (geometry d).after d.rows (geometry d).compactFits (geometry d).activeSize
    (recordOf d i) i.payload

theorem start_cell (d : Inputs s) (r : Fin (count d)) :
    index s (geometry d) (cellAt d ((recordEquiv d).symm r) ⟨0,by have := d.hrecord; omega⟩)=start d r := by
  apply Fin.ext
  have h := cell_index s ((geometry d).n*(geometry d).b) ((geometry d).n*(geometry d).q)
    (geometry d).before (geometry d).after d.rows (geometry d).compactFits (geometry d).activeSize
    ((recordEquiv d).symm r) ⟨0,by have := d.hrecord; omega⟩
  change _=(recordEquiv d ((recordEquiv d).symm r)).val*s.payload+0 at h
  simpa only [index,cellAt,start,Equiv.apply_symm_apply,Nat.add_zero] using h

theorem decode_start (d : Inputs s) (r : Fin (count d)) :
    (ActivePrefixStagePairCoordinates.addressEquiv d).symm (start d r)=
      cellAt d ((recordEquiv d).symm r) ⟨0,by have := d.hrecord; omega⟩ := by
  apply (ActivePrefixStagePairCoordinates.addressEquiv d).injective
  rw [Equiv.apply_symm_apply]
  exact (start_cell d r).symm

theorem destination_start (d : Inputs s) (op : Op (Fin d.stage.slots)) (r : Fin (count d)) :
    ActivePrefixStagePairCoordinates.destination d op (start d r)=
      start d (rowDestination (changePair d op) r) := by
  unfold ActivePrefixStagePairCoordinates.destination
  change index s (geometry (changePair d op))
    (ActivePrefixStageRuntimeSelected.destination (changePair d op)
      ((ActivePrefixStagePairCoordinates.addressEquiv (changePair d op)).symm
        (start (changePair d op) r)))=start (changePair d op) (rowDestination (changePair d op) r)
  rw [decode_start (changePair d op) r]
  apply Fin.ext
  rw [index_ordinal]
  have hp := congrArg (fun a => a.payload) (ActivePrefixStageTripleTransport.destination_payload (changePair d op)
    (cellAt (changePair d op) ((recordEquiv (changePair d op)).symm r) ⟨0,by have := d.hrecord; omega⟩)
    ⟨0,by have := d.hrecord; omega⟩)
  change (ActivePrefixStageRuntimeSelected.destination (changePair d op)
    (cellAt (changePair d op) ((recordEquiv (changePair d op)).symm r) ⟨0,by have := d.hrecord; omega⟩)).payload=⟨0,by have := d.hrecord; omega⟩ at hp
  rw [hp]
  rfl

def run (d : Inputs s) : List (Op (Fin d.stage.slots)) → Fin (count d) → Fin (count d)
  | [],r => r
  | op::ops,r => run d ops (rowDestination (changePair d op) r)

theorem run_start (d : Inputs s) (ops : List (Op (Fin d.stage.slots))) (r : Fin (count d)) :
    ActivePrefixStagePairCoordinates.run d ops (start d r)=start d (run d ops r) := by
  induction ops generalizing r with
  | nil => rfl
  | cons op ops ih =>
    change ActivePrefixStagePairCoordinates.run d ops
      (ActivePrefixStagePairCoordinates.destination d op (start d r))=_
    rw [destination_start]
    exact ih (rowDestination (changePair d op) r)

theorem run_coordinates (d : Inputs s) (ops : List (Op (Fin d.stage.slots))) (r : Fin (count d)) :
    ActivePrefixStageRuntimeOrdinal.rawCoordinates d.stage (start d (run d ops r))=
      Networks.BinaryRowColumns.run ops (ActivePrefixStageRuntimeOrdinal.rawCoordinates d.stage (start d r)) := by
  rw [←run_start]
  exact ActivePrefixStagePairCoordinates.run_coordinates d ops (start d r)

theorem start_injective (d : Inputs s) : Function.Injective (start d) := by
  intro r t h
  have hp : 0<s.payload := by have := d.hrecord; omega
  have he := congrArg Fin.val h
  change r.val*s.payload=t.val*s.payload at he
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right hp he)

theorem raw_destination_involutive (d : Inputs s) (op : Op (Fin d.stage.slots)) :
    Function.Involutive (ActivePrefixStagePairCoordinates.destination d op) := by
  intro k
  let input := changePair d op
  let e := ActivePrefixStagePairCoordinates.addressEquiv input
  change e (ActivePrefixStageRuntimeSelected.destination input
    (e.symm (e (ActivePrefixStageRuntimeSelected.destination input (e.symm k)))))=k
  rw [Equiv.symm_apply_apply,ActivePrefixStageTripleEndpoint.destination_involutive,
    Equiv.apply_symm_apply]

theorem row_destination_involutive (d : Inputs s) (op : Op (Fin d.stage.slots)) :
    Function.Involutive (rowDestination (changePair d op)) := by
  intro r
  apply start_injective d
  have h1 := destination_start d op r
  have h2 := destination_start d op (rowDestination (changePair d op) r)
  have h := raw_destination_involutive d op (start d r)
  rw [h1,h2] at h
  exact h

theorem action_entry (d : Inputs s) (op : Op (Fin d.stage.slots)) {B : ℕ}
    (xs : Rows d B) (r : Fin (count d)) (j : Fin B) :
    ActivePrefixStageNativePairRun.action d op xs (rowDestination (changePair d op) r) j=xs r j := by
  change xs (rowDestination (changePair d op) (rowDestination (changePair d op) r)) j=xs r j
  rw [row_destination_involutive d op r]

/-- The actual native word's chronological output moves every original row to
exactly its original-address basis destination, retaining all payload symbols. -/
theorem run_entry (d : Inputs s) (ops : List (Op (Fin d.stage.slots))) {B : ℕ}
    (xs : Rows d B) (r : Fin (count d)) (j : Fin B) :
    ActivePrefixStageNativePairSchedule.result d ops xs (run d ops r) j=xs r j := by
  induction ops generalizing xs r with
  | nil => rfl
  | cons op ops ih =>
    exact (ih (ActivePrefixStageNativePairRun.action d op xs)
      (rowDestination (changePair d op) r)).trans (action_entry d op xs r j)

end
end IntegerMultBounds.Machine.ActivePrefixStageNativePairCoordinates
