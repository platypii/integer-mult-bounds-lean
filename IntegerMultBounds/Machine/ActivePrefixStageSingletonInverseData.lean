import IntegerMultBounds.Machine.ActivePrefixStageSingletonSelected
import IntegerMultBounds.Machine.ActivePrefixStageSingletonDispatch

/-! Highest-only singleton actions and their physical direction selection
square to the identity on the complete original array. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageSingletonInverseData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Address)
open ActivePrefixStageSingletonData
open ActivePrefixStageSingletonSelected
open ActiveTargetHighestBits
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape}

theorem early_destination (d : Inputs s) (h : d.stage.source.val<d.stage.target.val)
    (x : Address s (params d) d.rows) : earlyDestination d h (earlyDestination d h x)=x := by
  let p := params d
  let off := ActivePrefixStageGeometry.earlyOffset d.stage
  let hf : off+p.f*p.q≤p.before := ActivePrefixStageGeometry.early_fits d.stage h
  let hs : 0<ActiveTargetHighestPairLayoutGeometry.sourceHigh s p off := ActivePrefixStageGeometry.early_high_positive d.stage h
  change ActiveTargetHighestLayoutEarlyCoordinates.destination s p off d.rows hf hs
    (ActiveTargetHighestLayoutEarlyCoordinates.destination s p off d.rows hf hs x)=x
  change {x with activeBefore := (join p.before _ _
    ((ActiveTargetHighestLayoutEarlyCoordinates.sourceParts s p off d.rows hf
      (ActiveTargetHighestLayoutEarlyCoordinates.destination s p off d.rows hf hs x)).1,
     toggle _ 0 hs
      (ActiveTargetHighestLayoutEarlyCoordinates.sourceParts s p off d.rows hf
        (ActiveTargetHighestLayoutEarlyCoordinates.destination s p off d.rows hf hs x)).1.2
      (ActiveTargetHighestLayoutEarlyCoordinates.sourceParts s p off d.rows hf
        (ActiveTargetHighestLayoutEarlyCoordinates.destination s p off d.rows hf hs x)).2))}=x
  rw [ActiveTargetHighestLayoutEarlyCoordinates.source_destination]
  simp only [toggle_twice]
  let hlt := ActiveTargetHighestPairLayoutGeometry.source_high_lt s p off p.before hf
  change {x with activeBefore := (join p.before (ActiveTargetHighestPairLayoutGeometry.sourceHigh s p off) hlt
    (split p.before (ActiveTargetHighestPairLayoutGeometry.sourceHigh s p off) hlt x.activeBefore))}=x
  rw [join_split]

theorem late_destination (d : Inputs s) (h : d.stage.target.val<d.stage.source.val)
    (x : Address s (params d) d.rows) : lateDestination d h (lateDestination d h x)=x := by
  simp only [lateDestination,ActiveTargetHighestLayoutLateCoordinates.destination,
    ActiveTargetHighestLayoutLateCoordinates.sourceParts,toggle_twice]

theorem early (d : Inputs s) (h : d.stage.source.val<d.stage.target.val) :
    Function.Involutive (earlyResult d h) := by
  intro x
  funext i
  obtain ⟨a,rfl⟩ := (CompactActiveTargetLayout.index_bijective s ((params d).n*(params d).b)
    ((params d).n*(params d).q) (params d).before (params d).after d.rows
    (params d).compactFits (params d).activeSize).2 i
  have hh := early_entry d h (earlyResult d h x) (earlyDestination d h a)
  rw [early_destination] at hh
  exact hh.trans (early_entry d h x a)

theorem late (d : Inputs s) (h : d.stage.target.val<d.stage.source.val) :
    Function.Involutive (lateResult d h) := by
  intro x
  funext i
  obtain ⟨a,rfl⟩ := (CompactActiveTargetLayout.index_bijective s ((params d).n*(params d).b)
    ((params d).n*(params d).q) (params d).before (params d).after d.rows
    (params d).compactFits (params d).activeSize).2 i
  have hh := late_entry d h (lateResult d h x) (lateDestination d h a)
  rw [late_destination] at hh
  exact hh.trans (late_entry d h x a)

theorem dispatch (d : Inputs s) : Function.Involutive (ActivePrefixStageSingletonDispatch.result d) := by
  intro x
  by_cases h : d.stage.source.val<d.stage.target.val
  · simp only [ActivePrefixStageSingletonDispatch.result,dite_eq_left h]
    exact early d h x
  · simp only [ActivePrefixStageSingletonDispatch.result,dite_eq_right h]
    exact late d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h) x

end
end IntegerMultBounds.Machine.ActivePrefixStageSingletonInverseData
