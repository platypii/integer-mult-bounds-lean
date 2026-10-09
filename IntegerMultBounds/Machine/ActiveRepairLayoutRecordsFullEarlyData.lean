import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadEarlyClean
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalGlobal

/-! Original-input common caller for the complete early low/high action.
The highest stage shares the genuine raw array and all fourteen original
layout words; no highest geometry or derived descriptor is an input. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsData (Array)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def focus : Fin 15 → Fin 243 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,228]
theorem focus_injective : Function.Injective focus := by decide

theorem sources (d : Inputs s p offset rows) (x : Array s rows) :
    SharedBank.payload (ActiveRepairLayoutRecordsPayloadEarlyData.input d x) focus=
      ActiveTargetHighestLayoutOriginalPlaced.sources d.hs x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem input_set (d : Inputs s p offset rows) (x y : Array s rows) :
    SharedPlacementAlphabet.setTape (ActiveRepairLayoutRecordsPayloadEarlyData.input d x)
      (focus 14) (ActiveTargetRotation.word y) 0=ActiveRepairLayoutRecordsPayloadEarlyData.input d y :=
  ActiveRepairLayoutRecordsPayloadEarlyData.input_set d x y

def result (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H) (x : Array s rows) :=
  ActiveTargetHighestLayoutGlobal.earlyAction s p offset rows hfit hsource hH d.hr (by have := d.hrecord; omega)
    (ActiveRepairLayoutRecordsPayloadEarlyClean.ideal d x)

def destination (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<sourceHigh s p offset) (x : Address s p rows) :=
  ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource
    (ActiveRepairLayoutPermutation.earlyIdeal s p.q p.b p.n p.before p.after rows p.rho offset
      (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive (ActiveRepairLayoutRecordsHeadersData.repair d)) x)

theorem entry (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H) (array : Array s rows) (x : Address s p rows) :
    result d hfit hsource hH array
      (ActivePrefixDirtyControlGlobalSwap.index s p (destination d hfit hsource x))=
      array (ActivePrefixDirtyControlGlobalSwap.index s p x) := by
  unfold result destination
  rw [ActiveTargetHighestLayoutGlobal.early_entry]
  exact ActiveRepairLayoutRecordsMove.move_entry s (p.n*p.b) (p.n*p.q) p.before p.after rows
    p.compactFits p.activeSize _ array x

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyData
