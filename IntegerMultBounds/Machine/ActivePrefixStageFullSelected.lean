import IntegerMultBounds.Machine.ActivePrefixStageFullBudget
import IntegerMultBounds.Machine.ActivePrefixStageFullEndpoint

/-! Actual original-input array endpoints have the complete selected low and
highest address action, preserving every original source-slot bit. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageFullSelected
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageFullData
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape}

abbrev geometry (d : Inputs s) := parameters d.stage d.hG d.hGK
abbrev Address (d : Inputs s) := ActivePrefixLayoutShapes.Address s (geometry d) d.rows

def earlyDestination (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) :=
  ActiveTargetHighestLayoutFullSelected.earlyDestination s (geometry d) (earlyOffset d.stage) d.rows
    (early_fits d.stage horder) (early_high_positive d.stage horder)
def lateDestination (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) :=
  ActiveTargetHighestLayoutFullSelected.lateDestination s (geometry d) (lateOffset d.stage) d.rows
    (late_fits d.stage horder) (positive_before d.stage)

theorem early_entry (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val)
    (x : Array s d.rows) (i : Address d) :
    earlyResult d horder x (ActivePrefixDirtyControlGlobalSwap.index s (geometry d) (earlyDestination d horder i))=
      x (ActivePrefixDirtyControlGlobalSwap.index s (geometry d) i) :=
  ActiveRepairLayoutRecordsFullEarlySelected.entry (descriptors .early d)
    (early_fits d.stage horder) (early_high_positive d.stage horder) (positive_H d.stage d.hG) x i

theorem late_entry (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val)
    (x : Array s d.rows) (i : Address d) :
    lateResult d horder x (ActivePrefixDirtyControlGlobalSwap.index s (geometry d) (lateDestination d horder i))=
      x (ActivePrefixDirtyControlGlobalSwap.index s (geometry d) i) :=
  ActiveRepairLayoutRecordsFullLateSelected.entry (descriptors .late d)
    (late_fits d.stage horder) (positive_before d.stage) (positive_H d.stage d.hG) x i

theorem early_source (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) (i : Address d) :
    Gather.field (BinaryAddressTableData.row (before d.stage) (earlyDestination d horder i).activeBefore.val)
      (earlyOffset d.stage) (d.stage.f*s.chunk)=
        Gather.field (BinaryAddressTableData.row (before d.stage) i.activeBefore.val)
          (earlyOffset d.stage) (d.stage.f*s.chunk) :=
  ActiveRepairLayoutRecordsFullEarlySelected.source (descriptors .early d)
    (early_fits d.stage horder) (early_high_positive d.stage horder) (early_disjoint d.stage) i

theorem late_source (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) (i : Address d) :
    (lateDestination d horder i).activeAfter=i.activeAfter :=
  ActiveTargetHighestLayoutFullSelected.late_source s (geometry d) (lateOffset d.stage) d.rows
    (late_fits d.stage horder) (positive_before d.stage) i

end
end IntegerMultBounds.Machine.ActivePrefixStageFullSelected
