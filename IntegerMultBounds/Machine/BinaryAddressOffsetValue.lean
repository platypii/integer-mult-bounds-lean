import IntegerMultBounds.Machine.BinaryAddressOffset
import IntegerMultBounds.Compact.PackedArithValue

/-! Each generated n*b-bit offset is exactly the packed parities of the
radix-2^q digits of its regular source address. This identifies the actual
physical output field with the second line of packedEarly, without an oracle. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetValue
open BinaryAddressOffsetData BinaryAddressTableData

theorem gather_bit (q b n k r : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (X Z : List Bool)
    (hk : k<n) (hr : r<b) :
    (Gather.gather (fun x _ => x) (PackedArith.parity q b hb hbq) X Z n).getD (k*b+r) false =
      (digit b (X.getD (k*q) false)).getD r false := by
  have hh := BlockRotationData.flatten_index b
    ((List.range n).map (Gather.digitWord (fun x _ => x) (PackedArith.parity q b hb hbq) X Z))
    (by intro xs hx; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx; exact Gather.digitWord_length _ _ _ _ _)
    k r (by simpa using hk) hr
  rw [Compact.PowerTwo.gather_flatten,List.getD_eq_getElem?_getD,hh]
  simp only [List.getElem_map,List.getElem_range]
  congr 2

def rowWord (q b n i : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  Gather.gather (fun x _ => x) (PackedArith.parity q b hb hbq) (row (n*q) i) (List.replicate n false) n

@[simp] theorem rowWord_length (q b n i : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    (rowWord q b n i hb hbq).length=n*b := Gather.gather_length _ _ _ _ _

theorem field_eq (q b n i : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (hi : i<2^(n*q)) :
    Gather.field (word q b n hb hbq) (i*(n*b)) (n*b)=rowWord q b n i hb hbq := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjn : j<n*b := by simpa only [Gather.field_length] using hj
    have hk : j/b<n := (Nat.div_lt_iff_lt_mul (by omega)).mpr hjn
    have hr : j%b<b := Nat.mod_lt _ (by omega)
    have hbig : i*n+j/b<n*2^(n*q) := by nlinarith
    have hsplit : (j/b)*b+j%b=j := by simpa only [Nat.mul_comm] using Nat.div_add_mod j b
    have hindex : i*(n*b)+j=(i*n+j/b)*b+j%b := by nlinarith
    have hl := gather_bit q b (n*2^(n*q)) (i*n+j/b) (j%b) hb hbq (source q n) (dummy q n) hbig hr
    have hr' := gather_bit q b n (j/b) (j%b) hb hbq (row (n*q) i) (List.replicate n false) hk hr
    rw [source_entry q n i (j/b) hi hk (by omega)] at hl
    rw [hsplit] at hr'
    rw [←hindex] at hl
    change (word q b n hb hbq).getD (i*(n*b)+j) false = _ at hl
    change (rowWord q b n i hb hbq).getD j false = _ at hr'
    simp only [Gather.field,List.getElem_map,List.getElem_range]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some] at hr'
    exact hl.trans hr'.symm

/-- Exact integer offset required by the second early-source modular line. -/
theorem field_value (q b n i : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (hi : i<2^(n*q)) :
    (Counter.value (Gather.field (word q b n hb hbq) (i*(n*b)) (n*b)) : ℤ) =
      Compact.Radix.pack ((2 : ℤ)^b) ((Compact.Radix.digits ((2 : ℤ)^q) n i).map (· % 2)) := by
  rw [field_eq q b n i hb hbq hi]
  have hh := Compact.PowerTwo.parity_value q b hb hbq (List.replicate n false)
    (row (n*q) i) (by simp)
  simpa only [List.length_replicate,rowWord,row_rank (n*q) i hi] using hh

/-- Every padded physical offset is in the target field's modular range. -/
theorem field_bounded (q b n i : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    Counter.value (Gather.field (word q b n hb hbq) (i*(n*b)) (n*b)) < 2^(n*b) := by
  simpa only [Gather.field_length] using Counter.value_lt (Gather.field (word q b n hb hbq) (i*(n*b)) (n*b))

end IntegerMultBounds.Machine.BinaryAddressOffsetValue
