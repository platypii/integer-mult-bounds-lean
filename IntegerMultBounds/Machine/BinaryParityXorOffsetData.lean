import IntegerMultBounds.Machine.BinarySelectedOffsetData
import IntegerMultBounds.Machine.BinaryParityXorOffsetNegate
import IntegerMultBounds.Compact.PackedArithValue

/-! Fourth-line offsets: gather parity XOR original controls from each regular
q-bit source address, then negate each n*b-bit row independently. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetData

def source (q n : ℕ) := BinarySelectedOffsetData.source q n
def controls (q n : ℕ) (Z : List Bool) := BinarySelectedOffsetData.controls q n Z
def positiveWord (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  Gather.gather (fun x z => xor x z) (PackedArith.parity q b hb hbq) (source q n) (controls q n Z) (n*2^(n*q))
def rowWord (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  Gather.gather (fun x z => xor x z) (PackedArith.parity q b hb hbq) (BinaryAddressTableData.row (n*q) i) Z n
@[simp] theorem rowWord_length (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    (rowWord q b n i Z hb hbq).length=n*b := Gather.gather_length _ _ _ _ _
def rows (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  (List.range (2^(n*q))).map (fun i => rowWord q b n i Z hb hbq)
def word (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryParityXorOffsetLoop.result (rows q b n Z hb hbq)

theorem rows_uniform (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    BlockRotationData.Uniform (n*b) (rows q b n Z hb hbq) := by
  intro xs hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact rowWord_length _ _ _ _ _ _ _

theorem source_length (q n : ℕ) : (source q n).length=(n*2^(n*q))*q := BinarySelectedOffsetData.source_length q n
theorem controls_length (q n : ℕ) (Z : List Bool) (hZ : Z.length=n) :
    (controls q n Z).length=n*2^(n*q) := BinarySelectedOffsetData.controls_length q n Z hZ
theorem positiveWord_length (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    (positiveWord q b n Z hb hbq).length=(n*2^(n*q))*b := Gather.gather_length _ _ _ _ _
theorem word_length (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    (word q b n Z hb hbq).length=2^(n*q)*(n*b) := by
  rw [word,BinaryParityXorOffsetLoop.result_length (n*b) _ (rows_uniform q b n Z hb hbq)]
  simp [rows]

end IntegerMultBounds.Machine.BinaryParityXorOffsetData
