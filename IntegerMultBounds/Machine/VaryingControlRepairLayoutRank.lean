import IntegerMultBounds.Machine.CompactActiveTargetGeometry
import IntegerMultBounds.Machine.CountedRankSplitData
import IntegerMultBounds.Machine.BinaryAddressTableData

/-! Extracting genuine original-array coordinates from the current full rank.
These identities use the unchanged serialized active-target layout; they do
not reorder the array or assume a semantic source word supplied to the key.
Physical division and copying are separate machine obligations. -/
namespace IntegerMultBounds.Machine.VaryingControlRepairLayoutRank
open CompactGadgetReservationShape CompactActiveTargetLayout CompactActiveTargetGeometry
open RecursiveInterchangeRows (pack pack_val)

private theorem packed_high {P B : ℕ} (p : Fin P) (j : Fin B) :
    (pack p j).val/B=p.val := by
  have hB : 0<B := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  rw [pack_val,Nat.add_comm,Nat.add_mul_div_right _ _ hB,Nat.div_eq_of_lt j.isLt,zero_add]

private theorem packed_low {P B : ℕ} (p : Fin P) (j : Fin B) :
    (pack p j).val%B=j.val := by
  rw [pack_val,Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt j.isLt]

variable (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
variable (hactive : before+m+after=s.active*s.chunk)
variable (x : Address s w m before after rows)

theorem target_prefix_from_rank :
    (index s w m before after rows hw hactive x).val/(2^m*targetSuffix s after)=
      (targetPrefixIndex s w m before after rows x).val := by
  have h := congrArg Fin.val (target_index s w m before after rows hw hactive x)
  change (targetIndex s w m before after rows x).val=(index s w m before after rows hw hactive x).val at h
  rw [←h]
  exact packed_high (targetPrefixIndex s w m before after rows x)
    (pack x.target (targetSuffixIndex s w m before after rows x))

theorem target_from_rank :
    (index s w m before after rows hw hactive x).val/targetSuffix s after%2^m=x.target.val := by
  have h := congrArg Fin.val (target_index s w m before after rows hw hactive x)
  change (targetIndex s w m before after rows x).val=(index s w m before after rows hw hactive x).val at h
  rw [←h]
  have he : (targetIndex s w m before after rows x).val=
      (pack (pack (targetPrefixIndex s w m before after rows x) x.target)
        (targetSuffixIndex s w m before after rows x)).val := by
    unfold targetIndex
    rw [FiberLayoutData.index_val,pack_val,pack_val]
    ring
  rw [he,packed_high,packed_low]

theorem before_from_rank :
    (index s w m before after rows hw hactive x).val/(2^m*targetSuffix s after)%2^before=x.activeBefore.val := by
  rw [target_prefix_from_rank]
  exact packed_low
    (pack (pack (pack (pack (pack x.row x.u) x.uTail) x.t) x.tTail) x.frontSlack) x.activeBefore

theorem t_from_rank :
    ((index s w m before after rows hw hactive x).val/(2^m*targetSuffix s after)/tCopies s w before)%2^w=x.t.val := by
  rw [target_prefix_from_rank]
  have h := congrArg Fin.val (t_prefix_index s w m before after rows x)
  change (targetPrefixIndex s w m before after rows x).val=
    (pack (pack (pack (pack x.row x.u) x.uTail) x.t) (tRestIndex s w m before after rows x)).val at h
  rw [h,packed_high,packed_low]

theorem u_from_rank :
    ((index s w m before after rows hw hactive x).val/(2^m*targetSuffix s after)/uCopies s w before)%2^w=x.u.val := by
  rw [target_prefix_from_rank]
  have h := congrArg Fin.val (u_prefix_index s w m before after rows x)
  change (targetPrefixIndex s w m before after rows x).val=
    (pack (pack x.row x.u) (uRestIndex s w m before after rows x)).val at h
  rw [h,packed_high,packed_low]

theorem after_from_rank :
    ((index s w m before after rows hw hactive x).val%targetSuffix s after)/
      (2^(s.H+s.B)*s.payload)=x.activeAfter.val := by
  have h := congrArg Fin.val (target_index s w m before after rows hw hactive x)
  change (targetIndex s w m before after rows x).val=(index s w m before after rows hw hactive x).val at h
  rw [←h]
  have he : (targetIndex s w m before after rows x).val=
      (pack (pack (targetPrefixIndex s w m before after rows x) x.target)
        (targetSuffixIndex s w m before after rows x)).val := by
    unfold targetIndex
    rw [FiberLayoutData.index_val,pack_val,pack_val]
    ring
  rw [he,packed_low]
  have hs : (targetSuffixIndex s w m before after rows x).val=
      (pack x.activeAfter (pack x.back x.payload)).val := by
    simp only [targetSuffixIndex,pack_val]
    ring
  rw [hs,packed_high]

/-- A source slot at a stated offset in the existing active prefix is read
from this current rank, with no fixed control word added to the address. -/
def beforeSource (j offset width : ℕ) :=
  Gather.field (BinaryAddressTableData.row before (j/(2^m*targetSuffix s after)%2^before)) offset width

theorem before_source_word (offset width : ℕ) (cs : List Bool)
    (hc : Counter.value cs=(index s w m before after rows hw hactive x).val) :
    beforeSource s m before after (Counter.value cs) offset width=
      Gather.field (BinaryAddressTableData.row before x.activeBefore.val) offset width := by
  unfold beforeSource
  rw [hc,before_from_rank]

/-- The full varying source slot occupies these explicit original prefix
bits. The placement condition belongs to the caller, not to a new reservation. -/
theorem before_source_value (offset width : ℕ) (cs : List Bool)
    (hc : Counter.value cs=(index s w m before after rows hw hactive x).val) :
    Counter.value (beforeSource s m before after (Counter.value cs) offset width)=
      x.activeBefore.val/2^offset%2^width := by
  rw [before_source_word s w m before after rows hw hactive x offset width cs hc]
  rw [CountedRankSplitData.value_middle,BinaryAddressTableData.row_rank before x.activeBefore.val x.activeBefore.isLt]

def afterSource (j offset width : ℕ) :=
  Gather.field (BinaryAddressTableData.row after ((j%targetSuffix s after)/(2^(s.H+s.B)*s.payload))) offset width

theorem after_source_word (offset width : ℕ) (cs : List Bool)
    (hc : Counter.value cs=(index s w m before after rows hw hactive x).val) :
    afterSource s after (Counter.value cs) offset width=
      Gather.field (BinaryAddressTableData.row after x.activeAfter.val) offset width := by
  unfold afterSource
  rw [hc,after_from_rank]

theorem after_source_value (offset width : ℕ) (cs : List Bool)
    (hc : Counter.value cs=(index s w m before after rows hw hactive x).val) :
    Counter.value (afterSource s after (Counter.value cs) offset width)=
      x.activeAfter.val/2^offset%2^width := by
  rw [after_source_word s w m before after rows hw hactive x offset width cs hc]
  rw [CountedRankSplitData.value_middle,BinaryAddressTableData.row_rank after x.activeAfter.val x.activeAfter.isLt]

end IntegerMultBounds.Machine.VaryingControlRepairLayoutRank
