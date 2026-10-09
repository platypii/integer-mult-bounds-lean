import IntegerMultBounds.Machine.BinarySelectedOffsetPrepare
import IntegerMultBounds.Machine.PackedArith

/-! Literal selected mask-shift offsets for all regular temporary addresses.
Each copy of the original control word aligns with one complete source row. -/
namespace IntegerMultBounds.Machine.BinarySelectedOffsetData
open BinaryAddressOffsetRepeatData (copies)

def source (b n : ℕ) := BinaryAddressOffsetData.source b n
def controls (b n : ℕ) (Z : List Bool) := copies Z (2^(n*b))
def word (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (Z : List Bool) :=
  Gather.gather (fun x z => x && z) (PackedArith.maskShift q b hb hbq)
    (source b n) (controls b n Z) (n*2^(n*b))
@[simp] theorem source_length (b n : ℕ) : (source b n).length=(n*2^(n*b))*b :=
  BinaryAddressOffsetData.source_length b n
@[simp] theorem controls_length (b n : ℕ) (Z : List Bool) (hZ : Z.length=n) :
    (controls b n Z).length=n*2^(n*b) := by
  simp [controls,hZ,Nat.mul_comm]
@[simp] theorem word_length (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (Z : List Bool) :
    (word q b n hb hbq Z).length=(n*2^(n*b))*q :=
  Gather.gather_length _ _ _ _ _
end IntegerMultBounds.Machine.BinarySelectedOffsetData
