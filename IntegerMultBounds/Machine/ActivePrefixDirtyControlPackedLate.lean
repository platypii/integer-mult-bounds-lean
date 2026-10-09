import IntegerMultBounds.Machine.ActivePrefixDirtyControlPackedEarly
import IntegerMultBounds.Machine.ActivePrefixDirtyControlSourcePacked

/-! The actual prepared later coordinate action is the packed late word
algorithm on every address, preserving the original source and spectators. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlPackedLate
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixLayoutBack
open ActivePrefixDirtyControlGlobalSequence
open ActivePrefixDirtyControlPackedEarly (state)
variable (s : Shape) (p : Parameters s) (offset : ℕ) (hfit : offset+p.f*p.q≤p.after) {rows : ℕ}

theorem destination_as_run (x : Address s p rows) :
    destination s p rows offset hfit x=
      let y := BinaryPackedLateData.run p.q p.b p.n p.hb p.hbq
        (afterControls s p x offset) (SelectedSourceBitsData.selected_length _ _ _ _) (state s p x)
      {x with target:=y.1,t:=y.2.1,u:=y.2.2.1} := by
  simp only [destination,ActivePrefixDirtyControlSourcePacked.unload_destination,
    ActivePrefixDirtyControlSourcePacked.source_destination,ActivePrefixDirtyControlPackedEarly.destination_as_run]
  rfl

theorem packed_state (x : Address s p rows) :
    state s p (destination s p rows offset hfit x)=
      BinaryPackedLateData.run p.q p.b p.n p.hb p.hbq
        (afterControls s p x offset) (SelectedSourceBitsData.selected_length _ _ _ _) (state s p x) := by
  rw [destination_as_run]
  rfl

theorem packed_value (x : Address s p rows) :
    (((destination s p rows offset hfit x).target.val : ℤ),
      ((destination s p rows offset hfit x).t.val : ℤ),((destination s p rows offset hfit x).u.val : ℤ))=
      Compact.packedLate ((2 : ℤ)^p.q) ((2 : ℤ)^p.b)
        ((afterControls s p x offset).map Compact.PowerTwo.ctrl) x.target.val x.t.val x.u.val := by
  have hh := BinaryPackedLateData.agrees p.q p.b p.n p.hb p.hbq
    (afterControls s p x offset) (SelectedSourceBitsData.selected_length _ _ _ _) (state s p x)
  rw [←packed_state s p offset hfit x] at hh
  exact hh

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlPackedLate
