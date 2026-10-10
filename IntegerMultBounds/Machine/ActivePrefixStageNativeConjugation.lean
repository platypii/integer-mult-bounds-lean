import IntegerMultBounds.Machine.ActivePrefixStageNativePairInverse

/-! Exact original-row semantics of a native basis word, one row-local action,
and the reversed word. This is coordinate algebra for the physical native
word; execution of the row-local action is a separate obligation. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativeConjugation
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageTripleWords (count)
open ActivePrefixStageNativeRows (Rows)
open ActivePrefixStageNativePairSchedule (result)
open ActivePrefixStagePairData (changePair)
open Networks.BinaryRowProgram (Op)
variable {s : Shape}

theorem run_append (d : Inputs s) (u v : List (Op (Fin d.stage.slots))) (r : Fin (count d)) :
    ActivePrefixStageNativePairCoordinates.run d (u++v) r=
      ActivePrefixStageNativePairCoordinates.run d v (ActivePrefixStageNativePairCoordinates.run d u r) := by
  induction u generalizing r with
  | nil => rfl
  | cons op ops ih => exact ih (ActivePrefixStageNativeRows.rowDestination (changePair d op) r)

theorem reverse_restores_row (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (r : Fin (count d)) :
    ActivePrefixStageNativePairCoordinates.run d ops.reverse
      (ActivePrefixStageNativePairCoordinates.run d ops r)=r := by
  induction ops generalizing r with
  | nil => rfl
  | cons op ops ih =>
    rw [List.reverse_cons,run_append]
    change ActivePrefixStageNativeRows.rowDestination (changePair d op)
      (ActivePrefixStageNativePairCoordinates.run d ops.reverse
        (ActivePrefixStageNativePairCoordinates.run d ops
          (ActivePrefixStageNativeRows.rowDestination (changePair d op) r)))=r
    exact (congrArg (fun x : Fin (count d) => ActivePrefixStageNativeRows.rowDestination (changePair d op) x)
      (ih (ActivePrefixStageNativeRows.rowDestination (changePair d op) r))).trans
      (ActivePrefixStageNativePairCoordinates.row_destination_involutive d op r)

/-- Every original row receives the local action indexed by the physical row
reached after the forward word, then returns to its exact original position. -/
theorem conjugated_entry {B : ℕ} (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (F : Fin (count d) → (Fin B → Fin 6) → Fin B → Fin 6)
    (xs : Rows d B) (r : Fin (count d)) (j : Fin B) :
    result d ops.reverse (fun i => F i (result d ops xs i)) r j=
      F (ActivePrefixStageNativePairCoordinates.run d ops r) (xs r) j := by
  have h := ActivePrefixStageNativePairCoordinates.run_entry d ops.reverse
    (fun i => F i (result d ops xs i)) (ActivePrefixStageNativePairCoordinates.run d ops r) j
  rw [reverse_restores_row] at h
  have hr : result d ops xs (ActivePrefixStageNativePairCoordinates.run d ops r)=xs r := by
    funext k
    exact ActivePrefixStageNativePairCoordinates.run_entry d ops xs r k
  rw [hr] at h
  exact h

end
end IntegerMultBounds.Machine.ActivePrefixStageNativeConjugation
