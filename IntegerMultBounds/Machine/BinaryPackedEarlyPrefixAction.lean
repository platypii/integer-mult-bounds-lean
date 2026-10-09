import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixBudget
import IntegerMultBounds.Machine.BinaryPackedOffsetData
import IntegerMultBounds.Machine.BinaryPackedEarlyData

/-! The source is in the existing prefix of the translated front. Offsets are
repeated across unused source-tail bits, dirty back and the entire gap, in their
actual physical rotation-row order. No source permutation is used. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyPrefixAction
open RadixRangePadding (volume index)
open RecursiveInterchangeRows (pack pack_val)
open BinaryAddressOffsetRepeatData (copies expanded)

 def repeatLength (A w G : ℕ) := A*2^w*G

 theorem repeated_field (K N A w G : ℕ) (table : List (List Bool))
    (hu : BlockRotationData.Uniform w table) (hlen : table.length=N)
    (k : Fin K) (y : Fin N) (tail : Fin A) (back : Fin (2^w)) (g : Fin G) :
    Gather.field (copies (expanded table (repeatLength A w G)) K)
      ((BinaryPackedOffsetData.rowIndex (pack (pack k y) tail) back g).val*w) w=
      table[y.val]'(by rw [hlen]; exact y.isLt) := by
  let l := pack (pack tail back) g
  have h := BinaryAddressOffsetRepeatValue.repeated_field table w (repeatLength A w G) K
    k.val y.val l.val hu k.isLt (by rw [hlen]; exact y.isLt) l.isLt
  simp only [hlen] at h
  have he : (BinaryPackedOffsetData.rowIndex (pack (pack k y) tail) back g).val=
      (k.val*N+y.val)*repeatLength A w G+l.val := by
    simp only [BinaryPackedOffsetData.rowIndex,pack_val,repeatLength,l]
    ring
  rw [he]
  exact h

 theorem parity_offset (q b n K A G : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (k : Fin K) (y : Fin (2^(n*q))) (tail : Fin A) (back : Fin (2^(n*b))) (g : Fin G) :
    PackedOffsetPayloadValue.offset
      (BinaryAddressOffsetRepeatData.destination q b n (repeatLength A (n*b) G) K hb hbq)
      (n*b) (BinaryPackedOffsetData.rowIndex (pack (pack k y) tail) back g).val=
      BinaryPackedEarlyData.parity q b n hb hbq y := by
  unfold PackedOffsetPayloadValue.offset BinaryAddressOffsetRepeatData.destination
  rw [repeated_field K (2^(n*q)) A (n*b) G _
    (BinaryAddressOffsetRepeatValue.offsets_uniform q b n hb hbq)
    (by simp [BinaryAddressOffsetRepeatData.offsets]) k y tail back g]
  simp only [BinaryAddressOffsetRepeatData.offsets,List.getElem_map,List.getElem_range,BinaryPackedEarlyData.parity]

 theorem negative_offset (q b n K A G : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (k : Fin K) (y : Fin (2^(n*q))) (tail : Fin A) (back : Fin (2^(n*b))) (g : Fin G) :
    PackedOffsetPayloadValue.offset
      (BinaryParityXorOffsetRepeatData.destination q b n (repeatLength A (n*b) G) K Z hb hbq)
      (n*b) (BinaryPackedOffsetData.rowIndex (pack (pack k y) tail) back g).val=
      BinaryPackedEarlyData.negative q b n Z hb hbq y := by
  unfold PackedOffsetPayloadValue.offset BinaryParityXorOffsetRepeatData.destination
  rw [repeated_field K (2^(n*q)) A (n*b) G _
    (BinaryParityXorOffsetRepeatData.offsets_uniform q b n Z hb hbq)
    (by simp [BinaryParityXorOffsetRepeatData.offsets,BinaryParityXorOffsetData.rows]) k y tail back g]
  simp only [BinaryParityXorOffsetRepeatData.offsets,BinaryParityXorOffsetData.rows,
    List.getElem_map,List.getElem_range,BinaryPackedEarlyData.negative]

 theorem parity_length (q b n K A G : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    (BinaryAddressOffsetRepeatData.destination q b n (repeatLength A (n*b) G) K hb hbq).length=
      BinaryPackedOffsetData.rows (K*2^(n*q)*A) (n*b) G*(n*b) := by
  rw [BinaryAddressOffsetRepeatData.destination,BinaryAddressOffsetRepeatData.copies_length,
    BinaryAddressOffsetRepeatData.expanded_length _ (n*b) _ (BinaryAddressOffsetRepeatValue.offsets_uniform q b n hb hbq)]
  simp only [BinaryAddressOffsetRepeatData.offsets,List.length_map,List.length_range,
    BinaryPackedOffsetData.rows,repeatLength]
  ring

 theorem negative_length (q b n K A G : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    (BinaryParityXorOffsetRepeatData.destination q b n (repeatLength A (n*b) G) K Z hb hbq).length=
      BinaryPackedOffsetData.rows (K*2^(n*q)*A) (n*b) G*(n*b) := by
  rw [BinaryParityXorOffsetRepeatData.destination,BinaryAddressOffsetRepeatData.copies_length,
    BinaryAddressOffsetRepeatData.expanded_length _ (n*b) _ (BinaryParityXorOffsetRepeatData.offsets_uniform q b n Z hb hbq)]
  simp only [BinaryParityXorOffsetRepeatData.offsets,BinaryParityXorOffsetData.rows,List.length_map,List.length_range,
    BinaryPackedOffsetData.rows,repeatLength]
  ring

 theorem parity_entry (q b n K A G B : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (x : Fin (volume (K*2^(n*q)*A) (2^(n*b)) G B) → Bool)
    (k : Fin K) (y : Fin (2^(n*q))) (tail : Fin A) (front back : Fin (2^(n*b))) (g : Fin G) (j : Fin B) :
    BinaryPackedOffsetData.result
      (BinaryAddressOffsetRepeatData.destination q b n (repeatLength A (n*b) G) K hb hbq)
      (K*2^(n*q)*A) (n*b) G B x
      (index (pack (pack k y) tail) (BinaryPackedEarlyData.add front (BinaryPackedEarlyData.parity q b n hb hbq y)) g back j)=
      x (index (pack (pack k y) tail) front g back j) := by
  have h := BinaryPackedOffsetData.result_entry _ _ _ _ _ (parity_length q b n K A G hb hbq) x
    (pack (pack k y) tail) front back g j
  simpa only [parity_offset q b n K A G hb hbq k y tail back g,BinaryPackedEarlyData.add] using h

 theorem negative_entry (q b n K A G B : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (x : Fin (volume (K*2^(n*q)*A) (2^(n*b)) G B) → Bool)
    (k : Fin K) (y : Fin (2^(n*q))) (tail : Fin A) (front back : Fin (2^(n*b))) (g : Fin G) (j : Fin B) :
    BinaryPackedOffsetData.result
      (BinaryParityXorOffsetRepeatData.destination q b n (repeatLength A (n*b) G) K Z hb hbq)
      (K*2^(n*q)*A) (n*b) G B x
      (index (pack (pack k y) tail) (BinaryPackedEarlyData.add front (BinaryPackedEarlyData.negative q b n Z hb hbq y)) g back j)=
      x (index (pack (pack k y) tail) front g back j) := by
  have h := BinaryPackedOffsetData.result_entry _ _ _ _ _ (negative_length q b n K A G Z hb hbq) x
    (pack (pack k y) tail) front back g j
  simpa only [negative_offset q b n K A G Z hb hbq k y tail back g,BinaryPackedEarlyData.add] using h

end IntegerMultBounds.Machine.BinaryPackedEarlyPrefixAction
