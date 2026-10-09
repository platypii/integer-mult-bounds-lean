import IntegerMultBounds.Machine.ActivePrefixParityOffsetBank
import IntegerMultBounds.Machine.BinaryParityXorOffsetNegate
import IntegerMultBounds.Machine.BinaryParityXorOffsetValue

/-! Independent modular negation of each current original-prefix parity row,
including zero-width rows when n is zero. -/
namespace IntegerMultBounds.Machine.ActivePrefixParityNegativeData
open ActivePrefixParityOffsetBank

def rows (s : Shape) := ActivePrefixParityOffsetData.rows s.W s.startT s.startX s.q s.b s.rho s.n s.f s.hb s.hbq
def negative (s : Shape) := BinaryParityXorOffsetLoop.result (rows s)

@[simp] theorem rows_length (s : Shape) : (rows s).length=2^s.W := by simp [rows]
theorem rows_uniform (s : Shape) : BlockRotationData.Uniform (s.n*s.b) (rows s) :=
  ActivePrefixParityOffsetData.rows_uniform _ _ _ _ _ _ _ _ _ _
theorem rows_flatten (s : Shape) : (rows s).flatten=offsetWord s :=
  ActivePrefixParityOffsetData.rows_flatten _ _ _ _ _ _ _ _ s.tempFits s.sourceFits s.hb s.hbq s.hnf s.hr
@[simp] theorem negative_length (s : Shape) : (negative s).length=2^s.W*(s.n*s.b) := by
  rw [negative,BinaryParityXorOffsetLoop.result_length _ _ (rows_uniform s),rows_length]

theorem row_current (s : Shape) (i : ℕ) (hi : i<2^s.W) :
    (rows s)[i]'(by simpa using hi)=
      Gather.gather xor (PackedArith.parity s.q s.b s.hb s.hbq)
        (Gather.field (BinaryAddressTableData.row s.W i) s.startT (s.n*s.q))
        (ActivePrefixSelectedOffsetData.controls s.W s.startX s.q s.rho s.n s.f i) s.n := by
  simp only [rows,ActivePrefixParityOffsetData.rows,List.getElem_map,List.getElem_range]

theorem negative_field (s : Shape) (i : ℕ) (hi : i<2^s.W) :
    Gather.field (negative s) (i*(s.n*s.b)) (s.n*s.b)=TwosComplement.negWord
      (Gather.gather xor (PackedArith.parity s.q s.b s.hb s.hbq)
        (Gather.field (BinaryAddressTableData.row s.W i) s.startT (s.n*s.q))
        (ActivePrefixSelectedOffsetData.controls s.W s.startX s.q s.rho s.n s.f i) s.n) := by
  let blocks := (rows s).map TwosComplement.negWord
  have hu : BlockRotationData.Uniform (s.n*s.b) blocks := by
    intro xs hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    rw [TwosComplement.negWord_length]
    exact rows_uniform s ys hy
  apply List.ext_getElem
  · simp [Gather.gather_length,PackedArith.parity,TwosComplement.negWord_length]
  · intro j hj hj'
    have hjW : j<s.n*s.b := by simpa only [Gather.field_length] using hj
    have hh := BlockRotationData.flatten_index (s.n*s.b) blocks hu i j (by simpa [blocks] using hi) hjW
    simp only [blocks,List.getElem_map,row_current s i hi] at hh
    simp only [Gather.field,List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD]
    change (blocks.flatten[i*(s.n*s.b)+j]?).getD false=_
    rw [hh,List.getElem?_eq_getElem hj']
    rfl

 theorem negative_value (s : Shape) (i : ℕ) (hi : i<2^s.W) :
    (Counter.value (Gather.field (negative s) (i*(s.n*s.b)) (s.n*s.b)) : ℤ)=
      (-(Counter.value (Gather.gather xor (PackedArith.parity s.q s.b s.hb s.hbq)
        (Gather.field (BinaryAddressTableData.row s.W i) s.startT (s.n*s.q))
        (ActivePrefixSelectedOffsetData.controls s.W s.startX s.q s.rho s.n s.f i) s.n) : ℤ))%2^(s.n*s.b) := by
  rw [negative_field s i hi,BinaryParityXorOffsetValue.negWord_value]
  simp [Gather.gather_length,PackedArith.parity]

 theorem negative_zero (s : Shape) (hn : s.n=0) : negative s=[] := by
  apply List.length_eq_zero_iff.mp
  rw [negative_length,hn]
  simp

end IntegerMultBounds.Machine.ActivePrefixParityNegativeData
