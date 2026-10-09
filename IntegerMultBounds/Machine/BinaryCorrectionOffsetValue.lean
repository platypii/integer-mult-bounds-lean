import IntegerMultBounds.Machine.BinaryCorrectionOffsetData

/-! Every correction row is the integer residue of the packed original
controls minus the selected mask-shift offset, modulo its own n*q-bit width. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetValue
open BinaryCorrectionOffsetData

def rowWord (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryCorrectionOffsetRow.diff (controlRow q Z) (BinarySelectedOffsetValue.rowWord q b n i Z hb hbq)

theorem rowWord_length (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    (rowWord q b n i Z hb hbq).length=n*q := by
  simp only [rowWord,BinaryCorrectionOffsetRow.diff,ColumnTransducer.digits_length,List.length_zip,
    controlRow_length q Z (by omega),hZ,BinarySelectedOffsetValue.rowWord_length,Nat.min_self]

theorem field_eq (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) (hi : i<2^(n*b)) :
    Gather.field (word q b n Z hb hbq) (i*(n*q)) (n*q)=rowWord q b n i Z hb hbq := by
  let blocks := (rows q b n Z hb hbq).map (fun x => BinaryCorrectionOffsetRow.diff x.1 x.2)
  have hu := BinaryCorrectionOffsetLoop.result_uniform (n*q) (rows q b n Z hb hbq) (rows_uniform q b n Z hb hbq hZ)
  apply List.ext_getElem
  · simp [rowWord_length q b n i Z hb hbq hZ]
  · intro j hj hj'
    have hjW : j<n*q := by simpa only [Gather.field_length] using hj
    have hh := BlockRotationData.flatten_index (n*q) blocks hu i j (by simpa [blocks,rows] using hi) hjW
    simp only [blocks,rows,List.getElem_map,List.getElem_range] at hh
    simp only [Gather.field,List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD]
    change (blocks.flatten[i*(n*q)+j]?).getD false=_
    change blocks.flatten[i*(n*q)+j]?=(rowWord q b n i Z hb hbq)[j]? at hh
    rw [hh,List.getElem?_eq_getElem hj']
    rfl

theorem controlRow_value (q b : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    (Counter.value (controlRow q Z) : ℤ)=Compact.Radix.pack ((2 : ℤ)^q) (Z.map Compact.PowerTwo.ctrl) := by
  rw [←controls_gather q b Z (List.replicate Z.length false) hb hbq]
  exact Compact.PowerTwo.controls_value q b hb hbq Z _ (by simp)

theorem field_value (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) (hi : i<2^(n*b)) :
    (Counter.value (Gather.field (word q b n Z hb hbq) (i*(n*q)) (n*q)) : ℤ)=
      (Compact.Radix.pack ((2 : ℤ)^q) (Z.map Compact.PowerTwo.ctrl)-
        Compact.Radix.pack ((2 : ℤ)^q) (List.zipWith (fun z w => 2*z*w) (Z.map Compact.PowerTwo.ctrl)
          (Compact.Radix.digits ((2 : ℤ)^b) n i))) % (2 : ℤ)^(n*q) := by
  rw [field_eq q b n i Z hb hbq hZ hi,rowWord,BinaryCorrectionOffsetRow.diff]
  have hl : (controlRow q Z).length=(BinarySelectedOffsetValue.rowWord q b n i Z hb hbq).length := by
    rw [controlRow_length q Z (by omega),hZ,BinarySelectedOffsetValue.rowWord_length]
  rw [ColumnTransducer.subRule_value _ _ hl,controlRow_value q b Z hb hbq,controlRow_length q Z (by omega),hZ,
    ←BinarySelectedOffsetValue.field_eq q b n i Z hb hbq hZ hi,
    BinarySelectedOffsetValue.field_value q b n i Z hb hbq hZ hi]

end IntegerMultBounds.Machine.BinaryCorrectionOffsetValue
