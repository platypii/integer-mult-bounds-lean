import IntegerMultBounds.Machine.ActiveTargetHighestLayoutWords

/-! Highest-bit actions retain complete source intervals. For an earlier
source, its original interval must lie strictly above target-high bit zero;
this explicit disjointness condition cannot be inferred from sourceHigh>0. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutSourceFrames
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters Address)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open ActiveTargetHighestLayoutWords
open BinaryAddressTableData (row)
open Compact.ActiveTargetSubsegmentWords (highest)


theorem highest_field (z : Bool) (xs : List Bool) (offset width : ℕ) (hoff : 0<offset) :
    Gather.field (highest z xs) offset width=Gather.field xs offset width := by
  cases offset with
  | zero => omega
  | succ offset =>
    cases xs with
    | nil => rfl
    | cons x xs => simp [Gather.field,highest,Nat.succ_add]

variable (s : Shape) (p : Parameters s) (offset rows : ℕ)

theorem early_source (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (hoff : 0<offset) (x : Address s p rows) :
    Gather.field
      (row p.before (ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource x).activeBefore.val)
      offset (p.f*p.q)=Gather.field (row p.before x.activeBefore.val) offset (p.f*p.q) := by
  rw [early_word]
  exact highest_field _ _ _ _ hoff

theorem late_source (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
    (x : Address s p rows) :
    Gather.field
      (row p.after (ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore x).activeAfter.val)
      offset (p.f*p.q)=Gather.field (row p.after x.activeAfter.val) offset (p.f*p.q) := rfl

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutSourceFrames
