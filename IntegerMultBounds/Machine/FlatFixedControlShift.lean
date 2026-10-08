import IntegerMultBounds.Machine.FixedControlTranslationStream
import IntegerMultBounds.Machine.FlatControlledShift

/-! Concrete flat-array translation across an arbitrary middle spectator range.
A physical H word is held fixed while all C D-fibers are translated. The count
C is an arbitrary binary input; this routine performs no radix-power padding
or spectator reorder. It is a recurring prepared boundary, not a bootstrap or
the complete outer H/prefix scheduler. -/
namespace IntegerMultBounds.Machine.FlatFixedControlShift
variable {radix : ℕ} [Fact radix.Prime]

abbrev offset (r : ℚ) (xs : List (Fin radix)) := Counter.value (RationalOffsetPrepare.result r xs)

def state (r : ℚ) {B C : ℕ} (xs : List (Fin radix)) (a : Fin (C*(radix^xs.length*B)) → Fin 4) (bs qs cs old : List Bool) (i : ℕ) :=
  CountedLoopReuseAlphabet.bank
    (FixedControlTranslationStream.state r B C (fun _ => blank) (fun _ => blank) 0 0 bs qs old xs
      (FlatControlledShift.payload a) i)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary cs) 1 1

/-- Literal input array: no address tags or duplicated payload family. -/
theorem source_tape (r : ℚ) {B C : ℕ} (xs : List (Fin radix))
    (a : Fin (C*(radix^xs.length*B)) → Fin 4) (bs qs cs old : List Bool) (i : ℕ) :
    (state r xs a bs qs cs old i).tape 10 = fun z =>
      (RadixToBinary.binaryEncoding (q := radix)).encode (putWord (fun _ => blank) 0 (List.ofFn a) z) := by
  change (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
    (putWord (fun _ => blank) 0 (TranslationStream.fibers (radix^xs.length) C (FlatControlledShift.payload a)).flatten z)) = _
  rw [FlatControlledShift.source_eq]

theorem destination_tape (r : ℚ) {B C : ℕ} (xs : List (Fin radix))
    (a : Fin (C*(radix^xs.length*B)) → Fin 4) (bs qs cs old : List Bool) :
    (state r xs a bs qs cs old C).tape 11 = fun z =>
      (RadixToBinary.binaryEncoding (q := radix)).encode
        (putWord (fun _ => blank) 0 (FiberLayoutData.translated a (fun _ => offset r xs)) z) := by
  change (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
    (putWord (fun _ => blank) 0 (FixedControlTranslationStream.outputPrefix r xs C (FlatControlledShift.payload a)) z)) = _
  unfold FixedControlTranslationStream.outputPrefix
  rw [FlatControlledShift.output_eq]
  rfl

/-- The control is literally unchanged, even when the spectator count is not a radix power. -/
theorem control_tape (r : ℚ) {B C : ℕ} (xs : List (Fin radix))
    (a : Fin (C*(radix^xs.length*B)) → Fin 4) (bs qs cs old : List Bool) (i : ℕ) :
    (state r xs a bs qs cs old i).head 15 = 1 ∧
    (state r xs a bs qs cs old i).tape 15 = RadixRationalBinary.source xs := ⟨rfl,rfl⟩

theorem realizes_hoare (r : ℚ) {B C : ℕ} (hB : 0 < B) (xs : List (Fin radix))
    (a : Fin (C*(radix^xs.length*B)) → Fin 4) (bs qs cs old : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length) (hc : Counter.value cs = C)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cold : GrowingCounterData.Canonical old)
    (hold : Counter.value old < radix^xs.length) :
    HoareTime (FixedControlTranslationStream.program r)
      (fun v => v = state r xs a bs qs cs old 0) (fun v => v = state r xs a bs qs cs old C)
      (529*(C*(radix^xs.length*B))+23) := by
  have hh := FixedControlTranslationStream.translate_hoare_linear r hB
    (fun _ => blank) (fun _ => blank) 0 0 bs qs cs old xs hb hq hc cb cq cc cold hold
    (FlatControlledShift.payload a) (FlatControlledShift.payload_length a)
  rw [TranslationStream.source_length _ B C _ (FlatControlledShift.payload_length a)] at hh
  exact hh

/-- Destination addresses shift only the D coordinate; every middle-spectator
index and suffix symbol is retained. -/
theorem destination_entry (r : ℚ) {B C : ℕ} (xs : List (Fin radix))
    (a : Fin (C*(radix^xs.length*B)) → Fin 4) (bs qs cs old : List Bool)
    (c : Fin C) (y : Fin (radix^xs.length)) (j : Fin B) :
    (state r xs a bs qs cs old C).tape 11
      ((c.val*(radix^xs.length*B)+((y.val+offset r xs)%radix^xs.length)*B+j.val : ℕ) : ℤ) =
        (RadixToBinary.binaryEncoding (q := radix)).encode (a (FiberLayoutData.index c y j)) := by
  rw [destination_tape]
  have hh := FiberLayoutData.translated_entry a (fun _ => offset r xs) c y j
  have hidx := List.getElem?_eq_some_iff.mp hh
  obtain ⟨hidx,hval⟩ := hidx
  rw [show (((c.val*(radix^xs.length*B)+((y.val+offset r xs)%radix^xs.length)*B+j.val : ℕ) : ℤ)) =
      0+((c.val*(radix^xs.length*B)+((y.val+offset r xs)%radix^xs.length)*B+j.val : ℕ) : ℤ) by omega]
  dsimp only
  rw [WordSegments.get _ _ _ _ hidx,hval]

end IntegerMultBounds.Machine.FlatFixedControlShift
