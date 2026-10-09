import IntegerMultBounds.Machine.ActivePrefixStageDispatchEndpoint
import IntegerMultBounds.Machine.ActivePrefixStageFullSelected
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullInverseData

/-! The runtime-selected full stage acts on every original address and is its
own inverse. Branch geometry is derived from the original source/target slots. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageDispatchSelected
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageFullData (Inputs descriptors)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixStageDispatchData (result)
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape}

def destination (d : Inputs s) (i : Address d) :=
  if h : d.stage.source.val<d.stage.target.val then ActivePrefixStageFullSelected.earlyDestination d h i
  else ActivePrefixStageFullSelected.lateDestination d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h) i

theorem entry (d : Inputs s) (x : Array s d.rows) (i : Address d) :
    result d x (ActivePrefixDirtyControlGlobalSwap.index s (geometry d) (destination d i))=
      x (ActivePrefixDirtyControlGlobalSwap.index s (geometry d) i) := by
  by_cases h : d.stage.source.val<d.stage.target.val
  · simp only [result,destination,dite_eq_left h]
    exact ActivePrefixStageFullSelected.early_entry d h x i
  · simp only [result,destination,dite_eq_right h]
    exact ActivePrefixStageFullSelected.late_entry d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h) x i

theorem involutive (d : Inputs s) (x : Array s d.rows) : result d (result d x)=x := by
  by_cases h : d.stage.source.val<d.stage.target.val
  · simp only [result,dite_eq_left h]
    exact ActiveRepairLayoutRecordsFullInverseData.early (descriptors .early d) x
      (early_fits d.stage h) (early_high_positive d.stage h) (positive_H d.stage d.hG) (early_disjoint d.stage)
  · simp only [result,dite_eq_right h]
    have ho := ActivePrefixStageOrderCompare.late_of_not_early d.stage h
    exact ActiveRepairLayoutRecordsFullInverseData.late (descriptors .late d) x
      (late_fits d.stage ho) (positive_before d.stage) (positive_H d.stage d.hG)

end
end IntegerMultBounds.Machine.ActivePrefixStageDispatchSelected
