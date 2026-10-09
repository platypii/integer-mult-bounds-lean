import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateBudget
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutFullSelected

/-! The actual complete later low/high machine has the full-selected address
destination. Its literal forward array equation covers every original address;
the complete later source is retained. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateSelected
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsData (Array)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

theorem destination_eq (d : Inputs s p offset rows)
    (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before) (x : Address s p rows) :
    ActiveRepairLayoutRecordsFullLateData.destination d hfit hbefore x=
      ActiveTargetHighestLayoutFullSelected.lateDestination s p offset rows hfit hbefore x := rfl

theorem entry (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (array : Array s rows) (x : Address s p rows) :
    ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH array
      (ActivePrefixDirtyControlGlobalSwap.index s p
        (ActiveTargetHighestLayoutFullSelected.lateDestination s p offset rows hfit hbefore x))=
      array (ActivePrefixDirtyControlGlobalSwap.index s p x) :=
  ActiveRepairLayoutRecordsFullLateData.entry d hfit hbefore hH array x

theorem source (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (x : Address s p rows) :
    (ActiveRepairLayoutRecordsFullLateData.destination d hfit hbefore x).activeAfter=x.activeAfter :=
  ActiveTargetHighestLayoutFullSelected.late_source s p offset rows hfit hbefore x

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateSelected
