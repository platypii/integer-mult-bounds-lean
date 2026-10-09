import IntegerMultBounds.Machine.BinaryParityXorOffsetValue
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatValue

/-! Literal independently negated parity-XOR offsets in regular address order. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatData
open BinaryAddressOffsetRepeatData (copies expanded)

def offsets (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  (BinaryParityXorOffsetData.rows q b n Z hb hbq).map TwosComplement.negWord
def destination (q b n L K : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  copies (expanded (offsets q b n Z hb hbq) L) K

theorem offsets_flatten (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    (offsets q b n Z hb hbq).flatten=BinaryParityXorOffsetData.word q b n Z hb hbq := rfl

theorem offsets_uniform (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    BlockRotationData.Uniform (n*b) (offsets q b n Z hb hbq) := by
  intro xs hx
  obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
  rw [TwosComplement.negWord_length]
  exact BinaryParityXorOffsetData.rows_uniform q b n Z hb hbq ys hy

end IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatData
