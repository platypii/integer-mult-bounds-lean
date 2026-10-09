import IntegerMultBounds.Machine.ActivePrefixCorrectionLoadData
import IntegerMultBounds.Machine.ActivePrefixLayoutFields

/-! Every original row receives this address's freshly computed modular
control-minus-selected correction. Repetition preserves prefix order exactly,
including the empty target-width case. -/
namespace IntegerMultBounds.Machine.ActivePrefixCorrectionLoadValue
open ActivePrefixCorrectionLoadData
open ActivePrefixSelectedOffsetBank (Shape)
open BinaryAddressOffsetRepeatData (copies)

theorem copies_field (xs : List Bool) (N w rows r i : ℕ) (hlen : xs.length=N*w)
    (hr : r<rows) (hi : i<N) :
    Gather.field (copies xs rows) ((r*N+i)*w) w=Gather.field xs (i*w) w := by
  have hN : 0<N := by omega
  have hm := Nat.mul_le_mul_right N (show r+1≤rows by omega)
  have h := ActivePrefixLayoutFields.repeated_field xs N w rows (r*N+i) hN hlen (by nlinarith only [hm,hi])
  simpa only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hi] using h

theorem field_row (s : Shape) (rows r i : ℕ) (hr : r<rows) (hi : i<2^s.W) :
    Gather.field (offsets s rows) ((r*2^s.W+i)*width s) (width s)=
      BinaryCorrectionOffsetRow.diff
        (Gather.field (ActivePrefixCorrectionOffsetData.control s) (i*width s) (width s))
        (Gather.field (ActivePrefixCorrectionOffsetData.selected s) (i*width s) (width s)) := by
  rw [offsets,copies_field (offsetWord s) (2^s.W) (width s) rows r i
    (ActivePrefixCorrectionOffsetData.word_length s) hr hi]
  exact ActivePrefixCorrectionOffsetData.field_eq s i hi

theorem correction_value (s : Shape) (rows r i : ℕ) (hr : r<rows) (hi : i<2^s.W) :
    (PackedOffsetPayloadValue.offset (offsets s rows) (width s) (r*2^s.W+i) : ℤ)=
      ((Counter.value (Gather.field (ActivePrefixCorrectionOffsetData.control s) (i*width s) (width s)) : ℤ)-
        Counter.value (Gather.field (ActivePrefixCorrectionOffsetData.selected s) (i*width s) (width s))) %
          (2 : ℤ)^width s := by
  unfold PackedOffsetPayloadValue.offset
  rw [offsets,copies_field (offsetWord s) (2^s.W) (width s) rows r i
    (ActivePrefixCorrectionOffsetData.word_length s) hr hi]
  exact ActivePrefixCorrectionOffsetData.field_value s i hi

theorem current_prefix_row (s : Shape) (rows r i : ℕ) (hr : r<rows) (hi : i<2^s.W) :
    Gather.field (offsets s rows) ((r*2^s.W+i)*width s) (width s)=
      BinaryCorrectionOffsetRow.diff
        (Compact.PowerTwo.toggleMask s.q
          (ActivePrefixSelectedOffsetData.controls s.W s.startX s.q s.rho s.n s.f i))
        (Gather.gather (fun x z => x && z) (PackedArith.maskShift s.q s.b s.hb s.hbq)
          (ActivePrefixSelectedOffsetData.temp s.W s.startT s.b s.n i)
          (ActivePrefixSelectedOffsetData.controls s.W s.startX s.q s.rho s.n s.f i) s.n) := by
  rw [offsets,copies_field (offsetWord s) (2^s.W) (width s) rows r i
    (ActivePrefixCorrectionOffsetData.word_length s) hr hi]
  exact ActivePrefixCorrectionOffsetData.current_prefix_row s i hi

end IntegerMultBounds.Machine.ActivePrefixCorrectionLoadValue
