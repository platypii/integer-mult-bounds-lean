import IntegerMultBounds.Machine.ActiveTargetHighestLayoutCompose
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutSourceFrames
import IntegerMultBounds.Machine.ActiveRepairLayoutIdealCoordinates

/-! Both complete repaired low-plus-high address destinations implement the
full selected XOR mask, with no remaining conditional low-row specification.
All compact fields and spectators survive; complete earlier-source retention
uses the explicit disjointness of its interval from target-high bit zero. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutFullSelected
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters Address)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open ActiveTargetHighestLayoutWords
open ActiveTargetHighestLayoutCompose (targetWord)
open ActiveRepairLayoutPermutation (earlyIdeal lateIdeal)
open ActiveRepairLayoutPermutationFiber (controlWord)
open BinaryAddressTableData (row)

variable (s : Shape) (p : Parameters s) (offset rows : ℕ)
theorem positive : 1≤p.q := by have := p.hbq; omega
local notation "EI" => earlyIdeal s p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.before (positive s p)
local notation "LI" => lateIdeal s p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.after (positive s p)
local notation "EZ" => controlWord p.before p.after p.q p.rho p.n offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.before
local notation "LZ" => controlWord p.before p.after p.q p.rho p.n offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.after

def earlyDestination (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset) (x : Address s p rows) :=
  ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource (EI x)
def lateDestination (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before) (x : Address s p rows) :=
  ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore (LI x)

theorem early_fields (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset) (x : Address s p rows) :
    earlyDestination s p offset rows hfit hsource x=
      { x with
        target := (EI x).target
        activeBefore := (ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource x).activeBefore } := by
  unfold earlyDestination
  rw [ActiveRepairLayoutIdealCoordinates.early_fields]
  rfl

theorem late_fields (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before) (x : Address s p rows) :
    lateDestination s p offset rows hfit hbefore x=
      { x with
        target := (LI x).target
        activeBefore := (ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore x).activeBefore } := by
  unfold lateDestination
  rw [ActiveRepairLayoutIdealCoordinates.late_fields]
  rfl

theorem early_target_word (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (x : Address s p rows) (lo : List Bool) :
    targetWord s p rows lo (earlyDestination s p offset rows hfit hsource x)=
      List.zipWith xor (targetWord s p rows lo x)
        (List.replicate lo.length false++Compact.PowerTwo.toggleMask p.q (EZ (x.activeBefore,x.activeAfter))++
          (earlyControl s p offset rows x::List.replicate (p.before-1) false)) := by
  apply ActiveTargetHighestLayoutCompose.early_after_low_word s p offset rows hfit hsource x (EI x) lo
    (EZ (x.activeBefore,x.activeAfter)) (ActiveRepairLayoutPermutationFiber.control_length _ _ _ _ _ _ _ _ _)
  · rw [ActiveRepairLayoutIdealCoordinates.early_fields]
    rfl
  · exact ActiveRepairLayoutIdealCoordinates.early_target_row s p.q p.b p.n p.before p.after rows
      p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.before (positive s p) x

theorem late_target_word (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
    (x : Address s p rows) (lo : List Bool) :
    targetWord s p rows lo (lateDestination s p offset rows hfit hbefore x)=
      List.zipWith xor (targetWord s p rows lo x)
        (List.replicate lo.length false++Compact.PowerTwo.toggleMask p.q (LZ (x.activeBefore,x.activeAfter))++
          (lateControl s p offset rows x::List.replicate (p.before-1) false)) := by
  apply ActiveTargetHighestLayoutCompose.late_after_low_word s p offset rows hfit hbefore x (LI x) lo
    (LZ (x.activeBefore,x.activeAfter)) (ActiveRepairLayoutPermutationFiber.control_length _ _ _ _ _ _ _ _ _)
  · rw [ActiveRepairLayoutIdealCoordinates.late_fields]
    rfl
  · rw [ActiveRepairLayoutIdealCoordinates.late_fields]
    rfl
  · exact ActiveRepairLayoutIdealCoordinates.late_target_row s p.q p.b p.n p.before p.after rows
      p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.after (positive s p) x

theorem early_source (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (hoff : 0<offset) (x : Address s p rows) :
    Gather.field (row p.before (earlyDestination s p offset rows hfit hsource x).activeBefore.val) offset (p.f*p.q)=
      Gather.field (row p.before x.activeBefore.val) offset (p.f*p.q) := by
  rw [early_fields]
  exact ActiveTargetHighestLayoutSourceFrames.early_source s p offset rows hfit hsource hoff x

theorem late_source (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before) (x : Address s p rows) :
    (lateDestination s p offset rows hfit hbefore x).activeAfter=x.activeAfter := by
  rw [late_fields]

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutFullSelected
