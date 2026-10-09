import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCoordinates
import IntegerMultBounds.Machine.BinarySelectedOffsetRepeatCoordinates
import IntegerMultBounds.Machine.BinaryPackedOffsetData

/-! The physically constructed repeated words drive the actual packed-field
permutation in the required source-address order. Every dirty back coordinate
and every suffix bit is retained; spectators do not change the chosen offset.
This identifies action semantics, not producer/action bank sequencing. -/
namespace IntegerMultBounds.Machine.BinaryRepeatedOffsetAction
noncomputable section
open RadixRangePadding (volume index)
open RecursiveInterchangeRows (pack pack_val)

theorem parity_offset (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (p : Fin P) (back : Fin (2^(n*b))) (h : Fin H) (y : Fin (2^(n*q))) (l : Fin L) :
    PackedOffsetPayloadValue.offset
      (BinaryAddressOffsetRepeatData.destination q b n L ((P*H)*2^(n*b)) hb hbq)
      (n*b) (BinaryPackedOffsetData.rowIndex p back (pack (pack h y) l)).val =
      Counter.value (BinaryAddressOffsetValue.rowWord q b n y.val hb hbq) := by
  unfold PackedOffsetPayloadValue.offset
  have hi : (BinaryPackedOffsetData.rowIndex p back (pack (pack h y) l)).val =
      BinaryAddressOffsetRepeatCoordinates.row q b n H L p.val back.val h.val y.val l.val := by
    simp only [BinaryPackedOffsetData.rowIndex,pack_val,
      BinaryAddressOffsetRepeatCoordinates.row]
    ring
  rw [hi,BinaryAddressOffsetRepeatCoordinates.field_eq q b n P H L
    p.val back.val h.val y.val l.val hb hbq p.isLt back.isLt h.isLt y.isLt l.isLt]

theorem parity_offset_value (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (p : Fin P) (back : Fin (2^(n*b))) (h : Fin H) (y : Fin (2^(n*q))) (l : Fin L) :
    (PackedOffsetPayloadValue.offset
      (BinaryAddressOffsetRepeatData.destination q b n L ((P*H)*2^(n*b)) hb hbq)
      (n*b) (BinaryPackedOffsetData.rowIndex p back (pack (pack h y) l)).val : ℤ) =
      Compact.Radix.pack ((2 : ℤ)^b)
        ((Compact.Radix.digits ((2 : ℤ)^q) n y.val).map (·%2)) := by
  rw [parity_offset q b n P H L hb hbq p back h y l,
    ←BinaryAddressOffsetValue.field_eq q b n y.val hb hbq y.isLt]
  exact BinaryAddressOffsetValue.field_value q b n y.val hb hbq y.isLt

theorem parity_entry (q b n P H L B : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (x : Fin (volume P (2^(n*b)) (H*2^(n*q)*L) B) → Bool)
    (p : Fin P) (front back : Fin (2^(n*b)))
    (h : Fin H) (y : Fin (2^(n*q))) (l : Fin L) (j : Fin B) :
    BinaryPackedOffsetData.result
      (BinaryAddressOffsetRepeatData.destination q b n L ((P*H)*2^(n*b)) hb hbq)
      P (n*b) (H*2^(n*q)*L) B x
      (index p ⟨(front.val+Counter.value
        (BinaryAddressOffsetValue.rowWord q b n y.val hb hbq))%2^(n*b),
        Nat.mod_lt _ (by positivity)⟩ (pack (pack h y) l) back j) =
      x (index p front (pack (pack h y) l) back j) := by
  have hlen := BinaryAddressOffsetRepeatCoordinates.word_length q b n P H L hb hbq
  have ha := BinaryPackedOffsetData.result_entry _ P (n*b) (H*2^(n*q)*L) B
    hlen x p front back (pack (pack h y) l) j
  simpa only [parity_offset q b n P H L hb hbq p back h y l] using ha

theorem selected_offset (q b n P H L : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (p : Fin P) (back : Fin (2^(n*q))) (h : Fin H) (y : Fin (2^(n*b))) (l : Fin L) :
    PackedOffsetPayloadValue.offset
      (BinarySelectedOffsetRepeatData.destination q b n L ((P*H)*2^(n*q)) Z hb hbq)
      (n*q) (BinaryPackedOffsetData.rowIndex p back (pack (pack h y) l)).val =
      Counter.value (BinarySelectedOffsetValue.rowWord q b n y.val Z hb hbq) := by
  unfold PackedOffsetPayloadValue.offset
  have hi : (BinaryPackedOffsetData.rowIndex p back (pack (pack h y) l)).val =
      BinarySelectedOffsetRepeatCoordinates.row q b n H L p.val back.val h.val y.val l.val := by
    simp only [BinaryPackedOffsetData.rowIndex,pack_val,
      BinarySelectedOffsetRepeatCoordinates.row]
    ring
  rw [hi,BinarySelectedOffsetRepeatCoordinates.field_eq q b n P H L
    p.val back.val h.val y.val l.val Z hb hbq p.isLt back.isLt h.isLt y.isLt l.isLt]

theorem selected_offset_value (q b n P H L : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) (p : Fin P) (back : Fin (2^(n*q)))
    (h : Fin H) (y : Fin (2^(n*b))) (l : Fin L) :
    (PackedOffsetPayloadValue.offset
      (BinarySelectedOffsetRepeatData.destination q b n L ((P*H)*2^(n*q)) Z hb hbq)
      (n*q) (BinaryPackedOffsetData.rowIndex p back (pack (pack h y) l)).val : ℤ) =
      Compact.Radix.pack ((2 : ℤ)^q)
        (List.zipWith (fun z w => 2*z*w) (Z.map Compact.PowerTwo.ctrl)
          (Compact.Radix.digits ((2 : ℤ)^b) n y.val)) := by
  rw [selected_offset q b n P H L Z hb hbq p back h y l,
    ←BinarySelectedOffsetValue.field_eq q b n y.val Z hb hbq hZ y.isLt]
  exact BinarySelectedOffsetValue.field_value q b n y.val Z hb hbq hZ y.isLt

theorem selected_entry (q b n P H L B : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (x : Fin (volume P (2^(n*q)) (H*2^(n*b)*L) B) → Bool)
    (p : Fin P) (front back : Fin (2^(n*q)))
    (h : Fin H) (y : Fin (2^(n*b))) (l : Fin L) (j : Fin B) :
    BinaryPackedOffsetData.result
      (BinarySelectedOffsetRepeatData.destination q b n L ((P*H)*2^(n*q)) Z hb hbq)
      P (n*q) (H*2^(n*b)*L) B x
      (index p ⟨(front.val+Counter.value
        (BinarySelectedOffsetValue.rowWord q b n y.val Z hb hbq))%2^(n*q),
        Nat.mod_lt _ (by positivity)⟩ (pack (pack h y) l) back j) =
      x (index p front (pack (pack h y) l) back j) := by
  have hlen := BinarySelectedOffsetRepeatCoordinates.word_length q b n P H L Z hb hbq
  have ha := BinaryPackedOffsetData.result_entry _ P (n*q) (H*2^(n*b)*L) B
    hlen x p front back (pack (pack h y) l) j
  simpa only [selected_offset q b n P H L Z hb hbq p back h y l] using ha

end
end IntegerMultBounds.Machine.BinaryRepeatedOffsetAction
