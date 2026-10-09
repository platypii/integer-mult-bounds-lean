import IntegerMultBounds.Machine.ActivePrefixLayoutFields

/-! Exact bit locations in the literal target and back-rotation prefixes of
the unchanged active-target layout. Payload and dirty spectators are arbitrary. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutGeometry
open CompactGadgetReservationShape CompactActiveTargetLayout CompactActiveTargetGeometry
open RecursiveInterchangeRows (pack pack_val)
open ActivePrefixLayoutFields
open BinaryAddressTableData (row)

def targetWidth (s : Shape) (before : ℕ) := 2*s.H+s.F+before
def backWidth (s : Shape) (m before after : ℕ) := targetWidth s before+m+after
def tStart (s : Shape) (w before : ℕ) := (s.H-w)+s.F+before

variable (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
variable (x : Address s w m before after rows)

include hw in
theorem target_count : targetPrefix s w before rows=rows*2^(targetWidth s before) :=
  target_prefix_bits s w before rows hw

include hw in
theorem back_count : backPrefix s w m before after rows=rows*2^(backWidth s m before after) := by
  unfold backPrefix
  rw [target_count s w before rows hw,Nat.mul_assoc,←pow_add,Nat.mul_assoc,←pow_add]
  simp only [backWidth,Nat.add_assoc]

include hw in
theorem target_t_fits : tStart s w before+w≤targetWidth s before := by
  unfold tStart targetWidth
  omega

include hw in
theorem target_t :
    Gather.field (prefixWord (targetWidth s before) (targetPrefixIndex s w m before after rows x).val)
      (tStart s w before) w=row w x.t.val := by
  apply field_eq_row _ _ _ _ _ (target_t_fits s w before hw) x.t.isLt
  have he := congrArg Fin.val (t_prefix_index s w m before after rows x)
  change (targetPrefixIndex s w m before after rows x).val=
    (pack (pack (pack (pack x.row x.u) x.uTail) x.t) (tRestIndex s w m before after rows x)).val at he
  rw [he]
  have hp : 2^(tStart s w before)=tCopies s w before :=
    (ActiveRepairRankFieldsGeometry.t_copies_pow s w before).symm
  rw [hp,packed_high,packed_low]

theorem target_before :
    Gather.field (prefixWord (targetWidth s before) (targetPrefixIndex s w m before after rows x).val)
      0 before=row before x.activeBefore.val := by
  apply field_eq_row _ _ _ _ _ (by unfold targetWidth; omega) x.activeBefore.isLt
  simp only [pow_zero,Nat.div_one]
  exact packed_low _ x.activeBefore

theorem target_source (offset width : ℕ) (hfit : offset+width≤before) :
    Gather.field (prefixWord (targetWidth s before) (targetPrefixIndex s w m before after rows x).val)
      offset width=Gather.field (row before x.activeBefore.val) offset width := by
  rw [←target_before s w m before after rows x]
  simpa only [Nat.zero_add] using (field_field _ 0 before offset width hfit).symm

theorem back_target :
    Gather.field (prefixWord (backWidth s m before after) (backPrefixIndex s w m before after rows x).val)
      after m=row m x.target.val := by
  apply field_eq_row _ _ _ _ _ (by unfold backWidth; omega) x.target.isLt
  change (pack (pack (targetPrefixIndex s w m before after rows x) x.target) x.activeAfter).val/2^after%2^m=_
  rw [packed_high,packed_low]

theorem back_before :
    Gather.field (prefixWord (backWidth s m before after) (backPrefixIndex s w m before after rows x).val)
      (m+after) before=row before x.activeBefore.val := by
  apply field_eq_row _ _ _ _ _ (by unfold backWidth targetWidth; omega) x.activeBefore.isLt
  rw [pow_add,Nat.mul_comm (2^m),←Nat.div_div_eq_div_mul]
  change (pack (pack (targetPrefixIndex s w m before after rows x) x.target) x.activeAfter).val/2^after/2^m%2^before=_
  rw [packed_high,packed_high]
  exact packed_low _ x.activeBefore

theorem back_after :
    Gather.field (prefixWord (backWidth s m before after) (backPrefixIndex s w m before after rows x).val)
      0 after=row after x.activeAfter.val := by
  apply field_eq_row _ _ _ _ _ (by unfold backWidth; omega) x.activeAfter.isLt
  simp only [pow_zero,Nat.div_one]
  exact packed_low _ x.activeAfter

theorem back_source_before (offset width : ℕ) (hfit : offset+width≤before) :
    Gather.field (prefixWord (backWidth s m before after) (backPrefixIndex s w m before after rows x).val)
      (m+after+offset) width=Gather.field (row before x.activeBefore.val) offset width := by
  rw [←back_before s w m before after rows x]
  exact (field_field _ (m+after) before offset width hfit).symm

theorem back_source_after (offset width : ℕ) (hfit : offset+width≤after) :
    Gather.field (prefixWord (backWidth s m before after) (backPrefixIndex s w m before after rows x).val)
      offset width=Gather.field (row after x.activeAfter.val) offset width := by
  rw [←back_after s w m before after rows x]
  simpa only [Nat.zero_add] using (field_field _ 0 after offset width hfit).symm

end IntegerMultBounds.Machine.ActivePrefixLayoutGeometry
