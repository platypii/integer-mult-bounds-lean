import IntegerMultBounds.Machine.ActivePrefixDirtyControlLayoutFields
import IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionData
import IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativeData
import IntegerMultBounds.Machine.ActivePrefixDirtyControlPureSemantics

/-! Every generated early-load row is evaluated at the current compact U
word and current target/T coordinates of the unchanged physical layout. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlLayoutRows
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes hiding targetShape
open ActivePrefixLayoutFields ActivePrefixDirtyControlLayoutFields
open BinaryAddressTableData (row)
open BinaryAddressOffsetRepeatData (copies)
open ActivePrefixDirtyControlSemantics (tempRow sourceRow)

variable (s : Shape) (p : Parameters s) {rows : ℕ}
def controls (x : Address s p rows) := CountedPackedParityRun.parities p.b (row (p.n*p.b) x.u.val) p.n

theorem target_temp (x : Address s p rows) :
    tempRow (targetShape s p) (targetRank s p x%2^(targetShape s p).W)=row (p.n*p.b) x.t.val :=
  ActivePrefixLayoutGeometry.target_t s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits x

theorem target_controls (x : Address s p rows) :
    ActivePrefixDirtyControlSemantics.controls (targetShape s p)
      (targetRank s p x%2^(targetShape s p).W)=controls s p x := by
  unfold ActivePrefixDirtyControlSemantics.controls sourceRow
  change CountedPackedParityRun.parities p.b
    (Gather.field (prefixWord (ActivePrefixLayoutGeometry.targetWidth s p.before) (targetRank s p x))
      (uStart s (p.n*p.b) p.before) (p.n*p.b)) p.n=_
  rw [target_u s p x]
  rfl

theorem back_temp (x : Address s p rows) :
    tempRow (compactShape s p) (backRank s p x%2^(compactShape s p).W)=row (p.n*p.q) x.target.val :=
  ActivePrefixLayoutGeometry.back_target s (p.n*p.b) (p.n*p.q) p.before p.after rows x

theorem back_controls (x : Address s p rows) :
    ActivePrefixDirtyControlSemantics.controls (compactShape s p)
      (backRank s p x%2^(compactShape s p).W)=controls s p x := by
  unfold ActivePrefixDirtyControlSemantics.controls sourceRow
  change CountedPackedParityRun.parities p.b
    (Gather.field (prefixWord (ActivePrefixLayoutGeometry.backWidth s (p.n*p.q) p.before p.after) (backRank s p x))
      (p.n*p.q+p.after+uStart s (p.n*p.b) p.before) (p.n*p.b)) p.n=_
  rw [back_u s p x]
  rfl

theorem selected_row (x : Address s p rows) :
    Gather.field (copies (ActivePrefixDirtyControlData.offsetWord (targetShape s p)) rows)
      (targetRank s p x*(p.n*p.q)) (p.n*p.q)=
      Gather.gather (fun z c => z && c) (PackedArith.maskShift p.q p.b p.hb p.hbq)
        (row (p.n*p.b) x.t.val) (controls s p x) p.n := by
  let l := targetShape s p
  rw [repeated_field _ (2^l.W) (p.n*p.q) rows (targetRank s p x) (by positivity)
    (ActivePrefixDirtyControlData.offset_length l) (target_rank_lt s p x)]
  have h := ActivePrefixDirtyControlSemantics.selected_row l (targetRank s p x%2^l.W) (Nat.mod_lt _ (by positivity))
  rw [target_temp s p x,target_controls s p x] at h
  exact h

theorem correction_row (x : Address s p rows) :
    Gather.field (copies (ActivePrefixDirtyControlCorrectionData.word (targetShape s p)) rows)
      (targetRank s p x*(p.n*p.q)) (p.n*p.q)=
      BinaryCorrectionOffsetRow.diff (Compact.PowerTwo.toggleMask p.q (controls s p x))
        (Gather.gather (fun z c => z && c) (PackedArith.maskShift p.q p.b p.hb p.hbq)
          (row (p.n*p.b) x.t.val) (controls s p x) p.n) := by
  let l := targetShape s p
  rw [repeated_field _ (2^l.W) (p.n*p.q) rows (targetRank s p x) (by positivity)
    (ActivePrefixDirtyControlCorrectionData.word_length l) (target_rank_lt s p x)]
  have h := ActivePrefixDirtyControlCorrectionData.current_prefix_row l (targetRank s p x%2^l.W)
    (Nat.mod_lt _ (by positivity))
  rw [target_temp s p x,target_controls s p x] at h
  exact h

theorem pure_row (x : Address s p rows) :
    Gather.field (copies (ActivePrefixDirtyControlPureBank.offsetWord (compactShape s p)) rows)
      (backRank s p x*(p.n*p.b)) (p.n*p.b)=
      Gather.gather (fun z _ => z) (PackedArith.parity p.q p.b p.hb p.hbq)
        (row (p.n*p.q) x.target.val) (controls s p x) p.n := by
  let l := compactShape s p
  rw [repeated_field _ (2^l.W) (p.n*p.b) rows (backRank s p x) (by positivity)
    (ActivePrefixDirtyControlPureBank.offset_length l) (back_rank_lt s p x)]
  have h := ActivePrefixDirtyControlPureSemantics.offset_row l (backRank s p x%2^l.W)
    (Nat.mod_lt _ (by positivity))
  rw [back_temp s p x,back_controls s p x] at h
  exact h

theorem negative_row (x : Address s p rows) :
    Gather.field (copies (ActivePrefixDirtyControlNegativeData.negative (compactShape s p)) rows)
      (backRank s p x*(p.n*p.b)) (p.n*p.b)=TwosComplement.negWord
      (Gather.gather xor (PackedArith.parity p.q p.b p.hb p.hbq)
        (row (p.n*p.q) x.target.val) (controls s p x) p.n) := by
  let l := compactShape s p
  rw [repeated_field _ (2^l.W) (p.n*p.b) rows (backRank s p x) (by positivity)
    (ActivePrefixDirtyControlNegativeData.negative_length l) (back_rank_lt s p x)]
  have h := ActivePrefixDirtyControlNegativeData.negative_field l (backRank s p x%2^l.W)
    (Nat.mod_lt _ (by positivity))
  rw [back_temp s p x,back_controls s p x] at h
  exact h

end IntegerMultBounds.Machine.ActivePrefixDirtyControlLayoutRows
