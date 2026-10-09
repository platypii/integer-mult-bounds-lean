import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPermutation
import IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineCommon
import IntegerMultBounds.Machine.ActiveRepairRankHeadersEndpoint

/-! The payload-one rank indexes one entire original-width bit record. The
flattened records are exactly the physical unchanged row-major bit array. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsData
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairLayoutRecordsShape
open IntegerMultBounds.Compact

variable (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
variable (ha : before+m+after=s.active*s.chunk)
abbrev Array := Fin (rows*s.recordWidth) → Bool
local notation "E" => indexEquiv (addressShape s) w m before after rows hw ha

def data (array : Array s rows) (x : RecordAddress s w m before after rows) : List Bool :=
  List.ofFn fun r : Fin s.payload => array (index s w m before after rows hw ha (cell s w m before after rows x r))
def records (array : Array s rows) := plain E (data s w m before after rows hw ha array)
def serialize (rs : List Partition.Record) : List Bool := (rs.map Partition.Record.payload).flatten

@[simp] theorem data_length (array : Array s rows) (x : RecordAddress s w m before after rows) :
    (data s w m before after rows hw ha array x).length=s.payload := by simp only [data,List.length_ofFn]
@[simp] theorem records_length (array : Array s rows) :
    (records s w m before after rows hw ha array).length=rows*(addressShape s).recordWidth := plain_length _ _

theorem records_serialize (array : Array s rows) :
    serialize (records s w m before after rows hw ha array)=List.ofFn array := by
  unfold serialize records plain
  rw [List.map_map,←List.ofFn_eq_map]
  have hcount := record_count s rows
  conv_rhs => rw [List.ofFn_congr hcount.symm array,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext r
  apply congrArg array
  apply Fin.ext
  rw [cell_index]
  exact congrArg (fun j : Fin (rows*(addressShape s).recordWidth) => j.val*s.payload+r.val)
    ((E).apply_symm_apply i)

theorem geometry_address (offset width rowBits : ℕ) :
    ActiveRepairRankHeadersEndpoint.geometry (addressShape s) w m before after offset width rowBits=
    ActiveRepairRankHeadersEndpoint.geometry s w m before after offset width rowBits := rfl

/-- A concrete physical operation that moves whole records supplies the repair
input records of the induced address-only permutation. -/
theorem data_after {P : Equiv.Perm (Address s w m before after rows)}
    {Q : Equiv.Perm (RecordAddress s w m before after rows)} (array result : Array s rows)
    (hcell : ∀ x r, P (cell s w m before after rows x r)=cell s w m before after rows (Q x) r)
    (hentry : ∀ x, result (index s w m before after rows hw ha (P x))=array (index s w m before after rows hw ha x)) :
    data s w m before after rows hw ha result=data s w m before after rows hw ha array ∘ Q.symm := by
  funext x
  apply congrArg List.ofFn
  funext r
  have hh := hentry (cell s w m before after rows (Q.symm x) r)
  rw [hcell,Q.apply_symm_apply] at hh
  exact hh

theorem records_after {P : Equiv.Perm (Address s w m before after rows)}
    {Q : Equiv.Perm (RecordAddress s w m before after rows)} (array result : Array s rows)
    (hcell : ∀ x r, P (cell s w m before after rows x r)=cell s w m before after rows (Q x) r)
    (hentry : ∀ x, result (index s w m before after rows hw ha (P x))=array (index s w m before after rows hw ha x)) :
    records s w m before after rows hw ha result=repairRecords E Q (data s w m before after rows hw ha array) := by
  unfold records repairRecords
  rw [data_after s w m before after rows hw ha array result hcell hentry]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsData
