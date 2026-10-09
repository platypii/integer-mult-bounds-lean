import IntegerMultBounds.Machine.ActivePrefixDirtyControlSemantics
import IntegerMultBounds.Machine.BinaryParityXorOffsetNegate
import IntegerMultBounds.Machine.BinaryParityXorOffsetValue

/-! Independent modular negation of each current original-prefix parity row,
including zero-width rows when n is zero. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativeData
open ActivePrefixDirtyControlData
open ActivePrefixDirtyControlSemantics (controls tempRow)

def rows (s : Shape .parity) := (List.range (2^s.W)).map (fun i =>
  Gather.gather xor (PackedArith.parity s.q s.b s.hb s.hbq) (tempRow s i) (controls s i) s.n)
def negative (s : Shape .parity) := BinaryParityXorOffsetLoop.result (rows s)

@[simp] theorem rows_length (s : Shape .parity) : (rows s).length=2^s.W := by simp [rows]
theorem rows_uniform (s : Shape .parity) : BlockRotationData.Uniform (s.n*s.b) (rows s) :=
by
  intro xs hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  simp [Gather.gather_length,PackedArith.parity]
theorem rows_flatten (s : Shape .parity) : (rows s).flatten=offsetWord s :=
by
  have h : rows s=(List.range (2^s.W)).map (fun i => Gather.field (offsetWord s) (i*(s.n*s.b)) (s.n*s.b)) := by
    apply List.map_congr_left
    intro i hi
    exact (ActivePrefixDirtyControlSemantics.parity_row s i (List.mem_range.mp hi)).symm
  rw [h]
  exact GatherStreamData.stream_fields _ _ _ (offset_length s)
@[simp] theorem negative_length (s : Shape .parity) : (negative s).length=2^s.W*(s.n*s.b) := by
  rw [negative,BinaryParityXorOffsetLoop.result_length _ _ (rows_uniform s),rows_length]

theorem row_current (s : Shape .parity) (i : ℕ) (hi : i<2^s.W) :
    (rows s)[i]'(by simpa using hi)=
      Gather.gather xor (PackedArith.parity s.q s.b s.hb s.hbq)
        (tempRow s i)
        (controls s i) s.n := by
  simp only [rows,List.getElem_map,List.getElem_range]

theorem negative_field (s : Shape .parity) (i : ℕ) (hi : i<2^s.W) :
    Gather.field (negative s) (i*(s.n*s.b)) (s.n*s.b)=TwosComplement.negWord
      (Gather.gather xor (PackedArith.parity s.q s.b s.hb s.hbq)
        (tempRow s i)
        (controls s i) s.n) := by
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

 theorem negative_value (s : Shape .parity) (i : ℕ) (hi : i<2^s.W) :
    (Counter.value (Gather.field (negative s) (i*(s.n*s.b)) (s.n*s.b)) : ℤ)=
      (-(Counter.value (Gather.gather xor (PackedArith.parity s.q s.b s.hb s.hbq)
        (tempRow s i)
        (controls s i) s.n) : ℤ))%2^(s.n*s.b) := by
  rw [negative_field s i hi,BinaryParityXorOffsetValue.negWord_value]
  simp [Gather.gather_length,PackedArith.parity]

 theorem negative_zero (s : Shape .parity) (hn : s.n=0) : negative s=[] := by
  apply List.length_eq_zero_iff.mp
  rw [negative_length,hn]
  simp

end IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativeData
