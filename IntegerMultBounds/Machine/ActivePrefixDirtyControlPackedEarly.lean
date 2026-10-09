import IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalCoordinates
import IntegerMultBounds.Machine.BinaryPackedLateData

/-! The actual dirty-U-controlled early block is precisely the early step of
the packed late algorithm, with every original spectator retained. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlPackedEarly
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open ActivePrefixDirtyControlGlobalSequence
open ActivePrefixDirtyControlGlobalCoordinates
open ActivePrefixDirtyControlGlobalTarget (selectedDestination correctionDestination)
variable (s : Shape) (p : Parameters s) {rows : ℕ}

def state (x : Address s p rows) : BinaryPackedLateData.State p.q p.b p.n Unit :=
  (x.target,x.t,x.u,())

theorem destination_as_run (x : Address s p rows) :
    earlyDestination s p rows x=
      let y := BinaryPackedLateData.early p.q p.b p.n p.hb p.hbq (state s p x)
      {x with target:=y.1,t:=y.2.1} := by
  simp only [earlyDestination,negative_destination,pure_destination,
    selectedDestination,correctionDestination]
  rfl

theorem packed_state (x : Address s p rows) :
    state s p (earlyDestination s p rows x)=
      BinaryPackedLateData.early p.q p.b p.n p.hb p.hbq (state s p x) := by
  rw [destination_as_run]
  rfl

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlPackedEarly
