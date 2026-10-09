import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyBudget
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutFullSelected

/-! The actual complete early low/high machine has the full-selected address
destination. Its literal forward array equation covers every original address;
source retention carries the real interval-disjointness hypothesis. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlySelected
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsData (Array)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

theorem destination_eq (d : Inputs s p offset rows)
    (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset) (x : Address s p rows) :
    ActiveRepairLayoutRecordsFullEarlyData.destination d hfit hsource x=
      ActiveTargetHighestLayoutFullSelected.earlyDestination s p offset rows hfit hsource x := rfl

theorem entry (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H) (array : Array s rows) (x : Address s p rows) :
    ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH array
      (ActivePrefixDirtyControlGlobalSwap.index s p
        (ActiveTargetHighestLayoutFullSelected.earlyDestination s p offset rows hfit hsource x))=
      array (ActivePrefixDirtyControlGlobalSwap.index s p x) :=
  ActiveRepairLayoutRecordsFullEarlyData.entry d hfit hsource hH array x

theorem source (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<sourceHigh s p offset) (hoff : 0<offset) (x : Address s p rows) :
    Gather.field (BinaryAddressTableData.row p.before
      (ActiveRepairLayoutRecordsFullEarlyData.destination d hfit hsource x).activeBefore.val) offset (p.f*p.q)=
      Gather.field (BinaryAddressTableData.row p.before x.activeBefore.val) offset (p.f*p.q) :=
  ActiveTargetHighestLayoutFullSelected.early_source s p offset rows hfit hsource hoff x

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlySelected
