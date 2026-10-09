import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsData

/-! Record-level ideal output serializes to the original-width physical bit
array. This is semantic serialization; no formatting machine is assumed. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsMove
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairLayoutRecordsShape ActiveRepairLayoutRecordsData
open Compact
variable (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
variable (ha : before+m+after=s.active*s.chunk)
local notation "E" => indexEquiv (addressShape s) w m before after rows hw ha
local notation "F" => indexEquiv s w m before after rows hw ha

def move (P : Equiv.Perm (Address s w m before after rows)) (array : Array s rows) : Array s rows :=
  fun i => array (F (P.symm ((F).symm i)))

theorem move_entry (P : Equiv.Perm (Address s w m before after rows)) (array : Array s rows)
    (x : Address s w m before after rows) :
    move s w m before after rows hw ha P array (F (P x))=array (F x) := by
  simp only [move,Equiv.symm_apply_apply]

theorem data_move (P : Equiv.Perm (Address s w m before after rows))
    (Q : Equiv.Perm (RecordAddress s w m before after rows)) (array : Array s rows)
    (hc : ∀ x r, P (cell s w m before after rows x r)=cell s w m before after rows (Q x) r) :
    data s w m before after rows hw ha (move s w m before after rows hw ha P array)=
      data s w m before after rows hw ha array ∘ Q.symm :=
  data_after s w m before after rows hw ha array _ hc (move_entry s w m before after rows hw ha P array)

theorem serialize_stream (bad : RecordAddress s w m before after rows → Prop) [DecidablePred bad]
    (d : RecordAddress s w m before after rows → List Bool) :
    serialize (stream E bad d)=serialize (plain E d) := by
  simp only [serialize,stream,plain,List.map_map,Function.comp_def]

theorem serialize_move (P : Equiv.Perm (Address s w m before after rows))
    (Q : Equiv.Perm (RecordAddress s w m before after rows)) (array : Array s rows)
    (bad : RecordAddress s w m before after rows → Prop) [DecidablePred bad]
    (hc : ∀ x r, P (cell s w m before after rows x r)=cell s w m before after rows (Q x) r) :
    serialize (stream E bad (data s w m before after rows hw ha array ∘ Q.symm))=
      List.ofFn (move s w m before after rows hw ha P array) := by
  rw [←data_move s w m before after rows hw ha P Q array hc,serialize_stream]
  exact records_serialize s w m before after rows hw ha _

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsMove
