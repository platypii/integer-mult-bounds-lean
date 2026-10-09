import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullInvolution
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyPlaced
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLatePlaced

/-! Actual complete low/high array transformations square to the identity,
on every original address including all spectator and payload coordinates. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullInverseData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsData (Array)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open ActiveTargetHighestLayoutFullSelected (earlyDestination lateDestination)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

theorem early (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (hH : 1≤s.H) (hoff : 0<offset) :
    ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH
      (ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH x)=x := by
  funext i
  obtain ⟨a,rfl⟩ := (CompactActiveTargetLayout.index_bijective s (p.n*p.b) (p.n*p.q)
    p.before p.after rows p.compactFits p.activeSize).2 i
  have h := ActiveRepairLayoutRecordsFullEarlySelected.entry d hfit hsource hH
    (ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH x)
    (earlyDestination s p offset rows hfit hsource a)
  rw [ActiveRepairLayoutRecordsFullInvolution.early_involutive s p offset rows hfit hsource hoff a] at h
  exact h.trans (ActiveRepairLayoutRecordsFullEarlySelected.entry d hfit hsource hH x a)

theorem late (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before) (hH : 1≤s.H) :
    ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH
      (ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH x)=x := by
  funext i
  obtain ⟨a,rfl⟩ := (CompactActiveTargetLayout.index_bijective s (p.n*p.b) (p.n*p.q)
    p.before p.after rows p.compactFits p.activeSize).2 i
  have h := ActiveRepairLayoutRecordsFullLateSelected.entry d hfit hbefore hH
    (ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH x)
    (lateDestination s p offset rows hfit hbefore a)
  rw [ActiveRepairLayoutRecordsFullInvolution.late_involutive s p offset rows hfit hbefore a] at h
  exact h.trans (ActiveRepairLayoutRecordsFullLateSelected.entry d hfit hbefore hH x a)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullInverseData
