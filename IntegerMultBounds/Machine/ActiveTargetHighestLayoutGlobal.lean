import IntegerMultBounds.Machine.ActiveTargetHighestLayoutEarlyCoordinates

/-! Full-array semantics of both physically executed highest-bit actions at
every unchanged active-layout address, including all source and spectator
coordinates. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutGlobal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters Address)
open ActiveTargetHighestPairData
open ActiveTargetHighestPairLayoutGeometry
open ActivePrefixDirtyControlConjugationData (FullArray)
open ActivePrefixDirtyControlGlobalSwap (index)

variable (s : Shape) (p : Parameters s) (offset rows : ℕ)

def earlyAction (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) (array : FullArray s rows) : FullArray s rows :=
  view (early_volume s p offset rows hfit hsource hH hr hp)
    (result (early s p offset rows hfit hsource hH hr hp)
      (view (early_volume s p offset rows hfit hsource hH hr hp).symm array))

def lateAction (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
    (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) (array : FullArray s rows) : FullArray s rows :=
  view (late_volume s p offset rows hfit hbefore hH hr hp)
    (later (late s p offset rows hfit hbefore hH hr hp)
      (view (late_volume s p offset rows hfit hbefore hH hr hp).symm array))

theorem early_entry (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) (array : FullArray s rows) (x : Address s p rows) :
    earlyAction s p offset rows hfit hsource hH hr hp array
      (index s p (ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource x))=
      array (index s p x) := by
  rw [←ActiveTargetHighestLayoutEarlyCoordinates.original_index s p offset rows hfit hsource hH hr hp
    (ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource x),
    ←ActiveTargetHighestLayoutEarlyCoordinates.original_index s p offset rows hfit hsource hH hr hp x]
  simp only [earlyAction,view,Fin.cast_cast,Fin.cast_eq_self]
  rw [ActiveTargetHighestLayoutEarlyCoordinates.index_destination]
  exact ActiveTargetHighestPairSemantics.earlier_entry _ _ _ _ _ _ _

theorem late_entry (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
    (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) (array : FullArray s rows) (x : Address s p rows) :
    lateAction s p offset rows hfit hbefore hH hr hp array
      (index s p (ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore x))=
      array (index s p x) := by
  rw [←ActiveTargetHighestLayoutLateCoordinates.original_index s p offset rows hfit hbefore hH hr hp
    (ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore x),
    ←ActiveTargetHighestLayoutLateCoordinates.original_index s p offset rows hfit hbefore hH hr hp x]
  simp only [lateAction,view,Fin.cast_cast,Fin.cast_eq_self]
  rw [ActiveTargetHighestLayoutLateCoordinates.index_destination]
  exact ActiveTargetHighestPairSemantics.later_entry _ _ _ _ _ _ _

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutGlobal
