import IntegerMultBounds.Machine.FlatControlledShiftReady

/-! Canonical finite-array output for the complete physical controlled shift.
This representation can be refactored into another prefix/target/suffix split
without copying the tape or attaching explicit address keys. -/
namespace IntegerMultBounds.Machine.FlatControlledShiftArray
variable {radix c B : ℕ} [Fact radix.Prime]

private theorem overwrite {k : ℕ} (f : ℤ → Fin (k+4)) (p : ℤ)
    (xs ys : List (Fin (k+4))) (hlen : xs.length = ys.length) :
    putWord (putWord f p xs) p ys = putWord f p ys := by
  funext z
  by_cases hi : p ≤ z ∧ z < p+ys.length
  · let i := (z-p).toNat
    have he : p+(i : ℤ) = z := by dsimp [i]; omega
    have hb : i < ys.length := by dsimp [i]; omega
    rw [← he,WordSegments.get _ _ _ i hb,WordSegments.get _ _ _ i hb]
  · rw [putWord_outside _ p z ys (by omega),putWord_outside _ p z ys (by omega)]
    exact putWord_outside f p z xs (by omega)

def array (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4) :
    Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4 :=
  fun i => (FlatControlledShiftNormalize.word r low high width a)[i.val]'(by
    rw [FlatControlledShiftNormalize.word_length]; exact i.isLt)

omit [Fact radix.Prime] in
theorem array_word (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4) :
    List.ofFn (array r low high width a) = FlatControlledShiftNormalize.word r low high width a := by
  apply List.ext_getElem
  · simp [FlatControlledShiftNormalize.word_length]
  · intro i hi hj
    simp [array]

omit [Fact radix.Prime] in
/-- Every original symbol occurs at its prescribed shifted coordinate in the
new canonical array, including every suffix position. -/
theorem array_entry (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (i : Fin (radix^PrefixAddressData.widthSum (low++0::high) width))
    (y : Fin (radix^(width 0))) (j : Fin B) :
    array r low high width a (FiberLayoutData.index i
      ⟨(y.val+FlatControlledShift.physicalOffset (radix := radix) r low width i.val)%radix^(width 0),
        Nat.mod_lt _ (Nat.zero_lt_of_lt y.isLt)⟩ j) = a (FiberLayoutData.index i y j) := by
  have hh := FiberLayoutData.translated_entry a
    (fun i => FlatControlledShift.physicalOffset (radix := radix) r low width i.val) i y j
  obtain ⟨hi,hv⟩ := List.getElem?_eq_some_iff.mp hh
  simpa only [array,FlatControlledShiftNormalize.word,FiberLayoutData.index_val] using hv

/-- The physically returned source is exactly a new canonical array over the
original background, independent of the previous contents overwritten there. -/
theorem output_source (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    (FlatControlledShiftReady.output r low high width ws a source dest p q bs qs ns).tape
      (PrefixCounterInitPlacement.handoff (RationalPrefixTranslationInit.streamPlacement c)
        (Fin.castAdd (PrefixCounterInitPlacement.extras (c+1)) (10 : Fin ((16+c)+2)))) =
      fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
        (putWord source p (List.ofFn (array r low high width a)) z) := by
  change (Placement.active (PrefixCounterInitPlacement.handoff (RationalPrefixTranslationInit.streamPlacement c))
    (FlatControlledShiftReady.output r low high width ws a source dest p q bs qs ns)).tape 10 = _
  rw [FlatControlledShiftReady.output_active,
    (FlatControlledShiftNormalize.output_payload r low high width a source dest p q bs qs ns).1,
    array_word,overwrite]
  simp [FlatControlledShiftNormalize.word_length]

end IntegerMultBounds.Machine.FlatControlledShiftArray
