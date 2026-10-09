import IntegerMultBounds.Machine.BinaryPackedEarlyLayout
import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixAction

/-! Literal array coordinates shared by all four packed early translations.
The two rectangle decompositions change only types: dirty back bits and every
unused front/middle/payload bit have the same serialized ordinal throughout. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyGeometry
open CompactGadgetReservationShape
open BinaryPackedEarlyLayout
open RecursiveInterchangeRows (pack pack_val)

 def middle (s : Shape) := 2^(s.F+s.active*s.chunk)
 def targetTail (s : Shape) (q n : ℕ) := 2^(s.H-n*q)
 def tempTail (s : Shape) (b n : ℕ) := 2^(s.H-n*b)
 def suffix (s : Shape) (w : ℕ) := 2^(s.H-w+s.B)*s.payload
 def tempGap (s : Shape) (q b n : ℕ) := targetTail s q n*2^(n*b)*(tempTail s b n*middle s)
 def controlGap (s : Shape) (b n : ℕ) := tempTail s b n*middle s
 def controlPrefix (s : Shape) (q n rows : ℕ) := rows*2^(n*q)*targetTail s q n

 theorem back_size (s : Shape) (w : ℕ) (hw : w≤s.H) :
    2^(s.H+s.B)=2^w*2^(s.H-w+s.B) := by
  rw [←pow_add]
  congr 1
  omega

 def splitBack (s : Shape) (w : ℕ) (hw : w≤s.H) (v : Fin (2^(s.H+s.B))) :
    Fin (2^w) × Fin (2^(s.H-w+s.B)) :=
  finProdFinEquiv.symm (Fin.cast (back_size s w hw) v)

 theorem splitBack_value (s : Shape) (w : ℕ) (hw : w≤s.H) (v : Fin (2^(s.H+s.B))) :
    (splitBack s w hw v).1.val*2^(s.H-w+s.B)+(splitBack s w hw v).2.val=v.val := by
  have h := finProdFinEquiv.apply_symm_apply (Fin.cast (back_size s w hw) v)
  have hv := congrArg Fin.val h
  change (pack (splitBack s w hw v).1 (splitBack s w hw v).2).val=v.val at hv
  rw [pack_val] at hv
  exact hv

 theorem temp_volume (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H) :
    RadixRangePadding.volume rows (2^(n*q)) (tempGap s q b n) (suffix s (n*q))=rows*s.recordWidth := by
  have hqpow : 2^(n*q)*targetTail s q n=2^s.H := by rw [targetTail,←pow_add,Nat.add_sub_of_le hq]
  have hbpow : 2^(n*b)*tempTail s b n=2^s.H := by rw [tempTail,←pow_add,Nat.add_sub_of_le hb]
  calc
    _ = rows*(2^(n*q)*targetTail s q n)*(2^(n*b)*tempTail s b n)*middle s*
        (2^(n*q)*2^(s.H-n*q+s.B))*s.payload := by
      unfold RadixRangePadding.volume tempGap suffix; ring
    _ = rows*2^s.H*2^s.H*middle s*2^(s.H+s.B)*s.payload := by rw [hqpow,hbpow,←back_size s (n*q) hq]
    _ = _ := by unfold middle Shape.recordWidth Shape.bits; rw [two_mul]; simp only [pow_add]; ring

 theorem control_volume (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H) :
    RadixRangePadding.volume (controlPrefix s q n rows) (2^(n*b)) (controlGap s b n) (suffix s (n*b))=rows*s.recordWidth := by
  have hqpow : 2^(n*q)*targetTail s q n=2^s.H := by rw [targetTail,←pow_add,Nat.add_sub_of_le hq]
  have hbpow : 2^(n*b)*tempTail s b n=2^s.H := by rw [tempTail,←pow_add,Nat.add_sub_of_le hb]
  calc
    _ = rows*(2^(n*q)*targetTail s q n)*(2^(n*b)*tempTail s b n)*middle s*
        (2^(n*b)*2^(s.H-n*b+s.B))*s.payload := by
      unfold RadixRangePadding.volume controlPrefix controlGap suffix; ring
    _ = rows*2^s.H*2^s.H*middle s*2^(s.H+s.B)*s.payload := by rw [hqpow,hbpow,←back_size s (n*b) hb]
    _ = _ := by unfold middle Shape.recordWidth Shape.bits; rw [two_mul]; simp only [pow_add]; ring

 def tempIndex (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (x : Address s q b n rows) :=
  RadixRangePadding.index x.2.2.row x.1
    (pack (pack x.2.2.targetTail x.2.1) (pack x.2.2.tempTail x.2.2.middle))
    (splitBack s (n*q) hq x.2.2.back).1 (pack (splitBack s (n*q) hq x.2.2.back).2 x.2.2.payload)
 def controlIndex (s : Shape) (q b n rows : ℕ) (hb : n*b≤s.H) (x : Address s q b n rows) :=
  RadixRangePadding.index (pack (pack x.2.2.row x.1) x.2.2.targetTail) x.2.1
    (pack x.2.2.tempTail x.2.2.middle)
    (splitBack s (n*b) hb x.2.2.back).1 (pack (splitBack s (n*b) hb x.2.2.back).2 x.2.2.payload)

 theorem temp_index (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H) (x : Address s q b n rows) :
    Fin.cast (temp_volume s q b n rows hq hb) (tempIndex s q b n rows hq x)=index s q b n rows hq hb x := by
  apply Fin.ext
  change (tempIndex s q b n rows hq x).val=(index s q b n rows hq hb x).val
  rw [index_val]
  simp only [tempIndex,RadixRangePadding.index,pack_val]
  have h := splitBack_value s (n*q) hq x.2.2.back
  rw [←h,back_size s (n*q) hq]
  ring

 theorem control_index (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H) (x : Address s q b n rows) :
    Fin.cast (control_volume s q b n rows hq hb) (controlIndex s q b n rows hb x)=index s q b n rows hq hb x := by
  apply Fin.ext
  change (controlIndex s q b n rows hb x).val=(index s q b n rows hq hb x).val
  rw [index_val]
  simp only [controlIndex,RadixRangePadding.index,pack_val]
  have h := splitBack_value s (n*b) hb x.2.2.back
  rw [←h,back_size s (n*b) hb]
  ring

 theorem temp_gap_carved (s : Shape) (q b n : ℕ) (hb : n*b≤s.H) :
    tempGap s q b n=CompactGadgetReservationHeadersCarvedData.gap s (n*q) .temp := by
  have he : (s.H-n*q)+n*b+((s.H-n*b)+(s.F+s.active*s.chunk))=
      (s.H-n*q)+s.H+s.F+s.active*s.chunk := by omega
  unfold tempGap targetTail tempTail middle CompactGadgetReservationHeadersCarvedData.gap
    CompactGadgetReservationHeadersCarvedData.gapBits
  rw [←pow_add,←pow_add,←pow_add,he]

 theorem control_gap_carved (s : Shape) (b n : ℕ) :
    controlGap s b n=CompactGadgetReservationHeadersCarvedData.gap s (n*b) .control := by
  unfold controlGap tempTail middle CompactGadgetReservationHeadersCarvedData.gap
    CompactGadgetReservationHeadersCarvedData.gapBits
  rw [←pow_add]
  change 2^((s.H-n*b)+(s.F+s.active*s.chunk))=2^((s.H-n*b)+s.F+s.active*s.chunk)
  congr 1
  omega

 theorem suffix_carved (s : Shape) (w : ℕ) :
    suffix s w=CompactGadgetReservationHeadersCarvedData.suffix s w := rfl

 theorem control_prefix_carved (s : Shape) (q n rows : ℕ) (hq : n*q≤s.H) :
    controlPrefix s q n rows=s.prefixRange rows .control := by
  unfold controlPrefix targetTail Shape.prefixRange Shape.prefixBits
  rw [Nat.mul_assoc,←pow_add,Nat.add_sub_of_le hq]

end IntegerMultBounds.Machine.BinaryPackedEarlyGeometry
