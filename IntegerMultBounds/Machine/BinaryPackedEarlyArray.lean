import IntegerMultBounds.Machine.BinaryPackedEarlyGeometry

/-! The four actual produced-table permutations act on the same complete
serialized reservation. These are the array functions computed by the real
swap/rotation/swap machines, with no supplied action oracle. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyArray
noncomputable section
open CompactGadgetReservationShape
open BinaryPackedEarlyLayout
open BinaryPackedEarlyGeometry
open RecursiveInterchangeRows (pack)

 def asTemp (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H)
    (x : Fin (rows*s.recordWidth) → Bool) :=
  fun i => x (Fin.cast (temp_volume s q b n rows hq hb) i)
 def fromTemp (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H)
    (x : Fin (RadixRangePadding.volume rows (2^(n*q)) (tempGap s q b n) (suffix s (n*q))) → Bool) :=
  fun i => x (Fin.cast (temp_volume s q b n rows hq hb).symm i)
 def asControl (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H)
    (x : Fin (rows*s.recordWidth) → Bool) :=
  fun i => x (Fin.cast (control_volume s q b n rows hq hb) i)
 def fromControl (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H)
    (x : Fin (RadixRangePadding.volume (controlPrefix s q n rows) (2^(n*b)) (controlGap s b n) (suffix s (n*b))) → Bool) :=
  fun i => x (Fin.cast (control_volume s q b n rows hq hb).symm i)

 theorem cast_temp_index (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H) (a : Address s q b n rows) :
    Fin.cast (temp_volume s q b n rows hq hw).symm (index s q b n rows hq hw a)=tempIndex s q b n rows hq a := by
  apply Fin.ext
  have h := congrArg Fin.val (temp_index s q b n rows hq hw a).symm
  exact h
 theorem cast_control_index (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H) (a : Address s q b n rows) :
    Fin.cast (control_volume s q b n rows hq hw).symm (index s q b n rows hq hw a)=controlIndex s q b n rows hw a := by
  apply Fin.ext
  have h := congrArg Fin.val (control_index s q b n rows hq hw a).symm
  exact h

 def selectedWord (s : Shape) (q b n rows : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  BinarySelectedOffsetRepeatData.destination q b n (controlGap s b n)
    ((rows*targetTail s q n)*2^(n*q)) Z hb hbq
 def parityWord (s : Shape) (q b n rows : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryAddressOffsetRepeatData.destination q b n
    (BinaryPackedEarlyPrefixAction.repeatLength (targetTail s q n) (n*b) (controlGap s b n)) rows hb hbq
 def correctionWord (s : Shape) (q b n rows : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryCorrectionOffsetRepeatData.destination q b n (controlGap s b n)
    ((rows*targetTail s q n)*2^(n*q)) Z hb hbq
 def negativeWord (s : Shape) (q b n rows : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryParityXorOffsetRepeatData.destination q b n
    (BinaryPackedEarlyPrefixAction.repeatLength (targetTail s q n) (n*b) (controlGap s b n)) rows Z hb hbq

 def first (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : Fin (rows*s.recordWidth) → Bool) :=
  fromTemp s q b n rows hq hw (BinaryPackedOffsetData.result (selectedWord s q b n rows Z hb hbq)
    rows (n*q) (tempGap s q b n) (suffix s (n*q)) (asTemp s q b n rows hq hw x))
 def second (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (hb : 1≤b) (hbq : b+1≤q) (x : Fin (rows*s.recordWidth) → Bool) :=
  fromControl s q b n rows hq hw (BinaryPackedOffsetData.result (parityWord s q b n rows hb hbq)
    (controlPrefix s q n rows) (n*b) (controlGap s b n) (suffix s (n*b)) (asControl s q b n rows hq hw x))
 def third (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : Fin (rows*s.recordWidth) → Bool) :=
  fromTemp s q b n rows hq hw (BinaryPackedOffsetData.result (correctionWord s q b n rows Z hb hbq)
    rows (n*q) (tempGap s q b n) (suffix s (n*q)) (asTemp s q b n rows hq hw x))
 def fourth (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : Fin (rows*s.recordWidth) → Bool) :=
  fromControl s q b n rows hq hw (BinaryPackedOffsetData.result (negativeWord s q b n rows Z hb hbq)
    (controlPrefix s q n rows) (n*b) (controlGap s b n) (suffix s (n*b)) (asControl s q b n rows hq hw x))

 theorem first_entry (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : Fin (rows*s.recordWidth) → Bool) (a : Address s q b n rows) :
    first s q b n rows hq hw Z hb hbq x
      (index s q b n rows hq hw (BinaryPackedEarlyData.first q b n Z hb hbq a))=
      x (index s q b n rows hq hw a) := by
  have h := BinaryRepeatedOffsetAction.selected_entry q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*q)) Z hb hbq
    (asTemp s q b n rows hq hw x) a.2.2.row a.1 (splitBack s (n*q) hq a.2.2.back).1
    a.2.2.targetTail a.2.1 (pack a.2.2.tempTail a.2.2.middle) (pack (splitBack s (n*q) hq a.2.2.back).2 a.2.2.payload)
  change BinaryPackedOffsetData.result _ _ _ _ _ _ (tempIndex s q b n rows hq (BinaryPackedEarlyData.first q b n Z hb hbq a))=
    asTemp s q b n rows hq hw x (tempIndex s q b n rows hq a) at h
  simp only [first,fromTemp,cast_temp_index]
  exact h.trans (congrArg x (temp_index s q b n rows hq hw a))

 theorem second_entry (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (hb : 1≤b) (hbq : b+1≤q) (x : Fin (rows*s.recordWidth) → Bool) (a : Address s q b n rows) :
    second s q b n rows hq hw hb hbq x
      (index s q b n rows hq hw (BinaryPackedEarlyData.second q b n hb hbq a))=
      x (index s q b n rows hq hw a) := by
  have h := BinaryPackedEarlyPrefixAction.parity_entry q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*b)) hb hbq
    (asControl s q b n rows hq hw x) a.2.2.row a.1 a.2.2.targetTail a.2.1 (splitBack s (n*b) hw a.2.2.back).1
    (pack a.2.2.tempTail a.2.2.middle) (pack (splitBack s (n*b) hw a.2.2.back).2 a.2.2.payload)
  change BinaryPackedOffsetData.result _ _ _ _ _ _ (controlIndex s q b n rows hw (BinaryPackedEarlyData.second q b n hb hbq a))=
    asControl s q b n rows hq hw x (controlIndex s q b n rows hw a) at h
  simp only [second,fromControl,cast_control_index]
  exact h.trans (congrArg x (control_index s q b n rows hq hw a))

 theorem third_entry (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : Fin (rows*s.recordWidth) → Bool) (a : Address s q b n rows) :
    third s q b n rows hq hw Z hb hbq x
      (index s q b n rows hq hw (BinaryPackedEarlyData.third q b n Z hb hbq a))=
      x (index s q b n rows hq hw a) := by
  have h := BinaryRepeatedOffsetAction.correction_entry q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*q)) Z hb hbq hZ
    (asTemp s q b n rows hq hw x) a.2.2.row a.1 (splitBack s (n*q) hq a.2.2.back).1
    a.2.2.targetTail a.2.1 (pack a.2.2.tempTail a.2.2.middle) (pack (splitBack s (n*q) hq a.2.2.back).2 a.2.2.payload)
  change BinaryPackedOffsetData.result _ _ _ _ _ _ (tempIndex s q b n rows hq (BinaryPackedEarlyData.third q b n Z hb hbq a))=
    asTemp s q b n rows hq hw x (tempIndex s q b n rows hq a) at h
  simp only [third,fromTemp,cast_temp_index]
  exact h.trans (congrArg x (temp_index s q b n rows hq hw a))

 theorem fourth_entry (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : Fin (rows*s.recordWidth) → Bool) (a : Address s q b n rows) :
    fourth s q b n rows hq hw Z hb hbq x
      (index s q b n rows hq hw (BinaryPackedEarlyData.fourth q b n Z hb hbq a))=
      x (index s q b n rows hq hw a) := by
  have h := BinaryPackedEarlyPrefixAction.negative_entry q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*b)) Z hb hbq
    (asControl s q b n rows hq hw x) a.2.2.row a.1 a.2.2.targetTail a.2.1 (splitBack s (n*b) hw a.2.2.back).1
    (pack a.2.2.tempTail a.2.2.middle) (pack (splitBack s (n*b) hw a.2.2.back).2 a.2.2.payload)
  change BinaryPackedOffsetData.result _ _ _ _ _ _ (controlIndex s q b n rows hw (BinaryPackedEarlyData.fourth q b n Z hb hbq a))=
    asControl s q b n rows hq hw x (controlIndex s q b n rows hw a) at h
  simp only [fourth,fromControl,cast_control_index]
  exact h.trans (congrArg x (control_index s q b n rows hq hw a))

 def run (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : Fin (rows*s.recordWidth) → Bool) :=
  fourth s q b n rows hq hw Z hb hbq (third s q b n rows hq hw Z hb hbq
    (second s q b n rows hq hw hb hbq (first s q b n rows hq hw Z hb hbq x)))

 theorem run_entry (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : Fin (rows*s.recordWidth) → Bool) (a : Address s q b n rows) :
    run s q b n rows hq hw Z hb hbq x (index s q b n rows hq hw (BinaryPackedEarlyData.run q b n Z hb hbq a))=
      x (index s q b n rows hq hw a) := by
  rw [run,BinaryPackedEarlyData.run,fourth_entry,third_entry s q b n rows hq hw Z hb hbq hZ,second_entry,first_entry]

end
end IntegerMultBounds.Machine.BinaryPackedEarlyArray
