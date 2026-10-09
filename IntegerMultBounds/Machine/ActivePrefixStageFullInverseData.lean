import IntegerMultBounds.Machine.ActivePrefixStageFullData
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullInverseData

namespace IntegerMultBounds.Machine.ActivePrefixStageFullInverseData
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageFullData
variable {s : Shape}

theorem early (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val) :
    Function.Involutive (earlyResult d horder) := fun x =>
  ActiveRepairLayoutRecordsFullInverseData.early (descriptors .early d) x
    (early_fits d.stage horder) (early_high_positive d.stage horder) (positive_H d.stage d.hG)
    (early_disjoint d.stage)

theorem late (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val) :
    Function.Involutive (lateResult d horder) := fun x =>
  ActiveRepairLayoutRecordsFullInverseData.late (descriptors .late d) x
    (late_fits d.stage horder) (positive_before d.stage) (positive_H d.stage d.hG)

end IntegerMultBounds.Machine.ActivePrefixStageFullInverseData
