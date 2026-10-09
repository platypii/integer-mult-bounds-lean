import IntegerMultBounds.Machine.ActivePrefixDirtyControlPurePlaced
import IntegerMultBounds.Machine.ActivePrefixDirtyControlSemantics

/-! Literal pure target parity at every prefix, independent of the compact-U
control values scanned by the physical gather. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlPureSemantics
open ActivePrefixDirtyControlData hiding offsetWord
open ActivePrefixDirtyControlPureBank (offsetWord)
open ActivePrefixDirtyControlSemantics (tempRow controls)

theorem offset_row (s : Shape .parity) (i : ℕ) (hi : i<2^s.W) :
    Gather.field (offsetWord s) (i*(s.n*s.b)) (s.n*s.b)=
      Gather.gather (fun x _ => x) (PackedArith.parity s.q s.b s.hb s.hbq)
        (tempRow s i) (controls s i) s.n := by
  change Gather.field (Gather.gather (fun x _ => x) (PackedArith.parity s.q s.b s.hb s.hbq)
    (BinaryPrefixFieldTableData.word s.W s.startT (s.n*s.q) s.tempFits) (controlWord s)
    (controlWord s).length) _ _=_
  rw [ActivePrefixDirtyControlSemantics.extracted_controls,
    BinaryPrefixFieldTableData.word_rows s.W s.startT (s.n*s.q) s.tempFits]
  exact GatherStreamData.field_eq (fun x _ => x) (PackedArith.parity s.q s.b s.hb s.hbq) s.hb s.n (2^s.W) i
    (tempRow s) (controls s) (by intros; exact Gather.field_length _ _ _) (by intros; simp) hi

theorem offset_bits (s : Shape .parity) (i : ℕ) (hi : i<2^s.W) :
    Gather.field (offsetWord s) (i*(s.n*s.b)) (s.n*s.b)=
      ((List.range s.n).map (fun j => Nat.testBit i (s.startT+j*s.q)::List.replicate (s.b-1) false)).flatten := by
  rw [offset_row s i hi,Compact.PowerTwo.gather_flatten]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  have hjn : j<s.n := List.mem_range.mp hj
  have hjq : j*s.q<s.n*s.q := Nat.mul_lt_mul_of_pos_right hjn (by have := s.hbq; omega)
  have hd (X Z : List Bool) :
      Gather.digitWord (fun x _ => x) (PackedArith.parity s.q s.b s.hb s.hbq) X Z j=
        X.getD (j*s.q) false::List.replicate (s.b-1) false := by
    simp [Gather.digitWord,PackedArith.parity,Gather.field]
  rw [hd]
  change (Gather.field (BinaryAddressTableData.row s.W i) s.startT (s.n*s.q)).getD (j*s.q) false::_=_
  rw [ActivePrefixSelectedOffsetData.field_bit _ _ _ _ hjq,
    ←Compact.PowerTwo.testBit_value,BinaryAddressTableData.row_rank s.W i hi]

end IntegerMultBounds.Machine.ActivePrefixDirtyControlPureSemantics
