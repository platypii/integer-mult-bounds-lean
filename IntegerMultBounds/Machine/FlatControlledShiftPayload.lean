import IntegerMultBounds.Machine.FlatControlledShiftArray
import IntegerMultBounds.Machine.SharedPayload

/-! Permanent-payload interface of an initialized, normalized controlled shift.
The selected slots are the existing source/output in its metadata suffix. -/
namespace IntegerMultBounds.Machine.FlatControlledShiftPayload
open PrefixCounterInitPlacement
variable {radix c B : ℕ} [Fact radix.Prime]

abbrev TapeCount (c : ℕ) := PrefixCounterInit.tapeCount (c+1)+17

def sourceSlot (c : ℕ) : Fin (TapeCount c) := Fin.natAdd (PrefixCounterInit.tapeCount (c+1)) (10 : Fin 17)
def destSlot (c : ℕ) : Fin (TapeCount c) := Fin.natAdd (PrefixCounterInit.tapeCount (c+1)) (11 : Fin 17)

theorem slots_ne (c : ℕ) : sourceSlot c ≠ destSlot c := by
  intro h
  have hv := congrArg Fin.val h
  simp [sourceSlot,destSlot] at hv

private theorem stream_metadata (i : Fin 15) :
    RationalPrefixTranslationInit.streamPlacement c (Fin.natAdd (c+1) (Fin.castAdd 2 i)) =
      Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd 1 i)) := by
  change appendEquiv (RationalPrefixTranslationExecution.prefixPlacement c) 2 _ = _
  have he : (Fin.natAdd (c+1) (Fin.castAdd 2 i) : Fin (((c+1)+15)+2)) =
      Fin.castAdd 2 (Fin.natAdd (c+1) i) := Fin.ext rfl
  rw [he,appendEquiv_left]
  apply congrArg (Fin.castAdd 2)
  apply Fin.ext
  simp [RationalPrefixTranslationExecution.prefixPlacement,finAddFlip_apply_natAdd]

private theorem handoff_metadata (i : Fin 17) :
    handoff (RationalPrefixTranslationInit.streamPlacement c)
      (Fin.castAdd (extras (c+1)) (RationalPrefixTranslationInit.streamPlacement c (Fin.natAdd (c+1) i))) =
      Fin.natAdd (PrefixCounterInit.tapeCount (c+1)) i := by
  simp only [handoff,Equiv.trans_apply,appendEquiv_left,Equiv.symm_apply_apply,
    FamilyPlacement.withFrame,Equiv.coe_fn_mk,Fin.addCases_left,Fin.addCases_right]

theorem sourceSlot_eq (c : ℕ) : sourceSlot c =
    handoff (RationalPrefixTranslationInit.streamPlacement c)
      (Fin.castAdd (extras (c+1)) (10 : Fin ((16+c)+2))) := by
  have hh := handoff_metadata (c := c) (10 : Fin 17)
  rw [show (10 : Fin 17) = Fin.castAdd 2 (10 : Fin 15) by rfl,stream_metadata] at hh
  have hi : Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd 1 (10 : Fin 15))) = (10 : Fin ((16+c)+2)) := by
    apply Fin.ext
    change 10 = 10 % ((16+c)+2)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simpa only [hi,sourceSlot,show Fin.castAdd 2 (10 : Fin 15) = (10 : Fin 17) from rfl] using hh.symm

theorem destSlot_eq (c : ℕ) : destSlot c =
    handoff (RationalPrefixTranslationInit.streamPlacement c)
      (Fin.castAdd (extras (c+1)) (11 : Fin ((16+c)+2))) := by
  have hh := handoff_metadata (c := c) (11 : Fin 17)
  rw [show (11 : Fin 17) = Fin.castAdd 2 (11 : Fin 15) by rfl,stream_metadata] at hh
  have hi : Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd 1 (11 : Fin 15))) = (11 : Fin ((16+c)+2)) := by
    apply Fin.ext
    change 11 = 11 % ((16+c)+2)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simpa only [hi,destSlot,show Fin.castAdd 2 (11 : Fin 15) = (11 : Fin 17) from rfl] using hh.symm

/-- Source/output values and heads of the raw-workspace stage input. -/
theorem input_payload {P : ℕ} (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool) (a : Fin (P*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    SharedPayload.payload (RationalPrefixTranslationBootstrap.input r order width ws a source dest p q bs qs ns)
      (sourceSlot c) (destSlot c) =
      FlatArrayNormalize.pair
        (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (putWord source p (List.ofFn a) z))
        (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (dest z)) p q := by
  unfold SharedPayload.payload RationalPrefixTranslationBootstrap.input sourceSlot destSlot
  simp only [Tapes.append,Fin.addCases_right,RationalPrefixTranslationBootstrap.raw,
    RationalPrefixTranslationBootstrap.workspace,ne_eq,Fin.isValue]
  simp only [not_true_eq_false]
  have h10 := stream_metadata (c := c) (10 : Fin 15)
  have h11 := stream_metadata (c := c) (11 : Fin 15)
  change RationalPrefixTranslationInit.streamPlacement c (Fin.natAdd (c+1) (10 : Fin 17)) = _ at h10
  change RationalPrefixTranslationInit.streamPlacement c (Fin.natAdd (c+1) (11 : Fin 17)) = _ at h11
  simp only [Placement.extra,h10,h11,FlatControlledShift.bank,CountedLoopReuseAlphabet.bank,
    RationalPrefixTranslationStream.state,RationalPrefixTranslationExecution.bank,Tapes.append,Fin.addCases_left]
  simp only [FlatControlledShift.initial_length,FlatControlledShift.source_eq]
  simp [RationalTranslationExecution.bank,TranslationExecutionReuse.bank,
    TranslationPreparedExecution.bank,TranslationDescriptors.bank,Tapes.append,Alphabet.mapTapes,
    RationalPrefixTranslationStream.outputPrefix,TranslationPreparedFamily.outputPrefix,
    FlatArrayNormalize.pair]
  exact ⟨⟨rfl,rfl⟩,rfl,rfl⟩

/-- The normalized stage returns its canonical transformed array on those same slots. -/
theorem output_payload (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    SharedPayload.payload (FlatControlledShiftReady.output r low high width ws a source dest p q bs qs ns)
      (sourceSlot c) (destSlot c) =
      FlatArrayNormalize.pair
        (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
          (putWord source p (List.ofFn (FlatControlledShiftArray.array r low high width a)) z))
        (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (dest z)) p q := by
  have hs := FlatControlledShiftArray.output_source r low high width ws a source dest p q bs qs ns
  have hh := FlatControlledShiftNormalize.output_payload r low high width a source dest p q bs qs ns
  rw [← FlatControlledShiftReady.output_active r low high width ws a source dest p q bs qs ns] at hh
  change _ ∧ _ ∧ _ ∧ _ at hh
  unfold SharedPayload.payload
  rw [sourceSlot_eq,destSlot_eq]
  change (⟨![_,_],![_,_]⟩ : Tapes 2 radix) = _
  simp only [Placement.active] at hh
  rw [hs,hh.2.1,hh.2.2.1,hh.2.2.2]
  rfl

end IntegerMultBounds.Machine.FlatControlledShiftPayload
