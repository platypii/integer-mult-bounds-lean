import IntegerMultBounds.Machine.FlatControlledShiftPayload

/-! Literal blank-workspace layout of the controlled-shift input, exposing every
supplied descriptor location for physical initialization from a dimension bank. -/
namespace IntegerMultBounds.Machine.FlatControlledShiftLayout
open PrefixCounterInitPlacement
variable {radix c B P : ℕ} [Fact radix.Prime]

def descriptorHead : Option (List Bool) → ℤ
  | none => 0
  | some _ => 1

def descriptorTape (radix : ℕ) : Option (List Bool) → ℤ → Fin (radix+4)
  | none => fun _ => blank
  | some xs => RadixZeroFill.encodedBinary xs

/-- The metadata suffix has only three dimension words and the two payload
slots; all other physical tapes are blank at head zero. -/
def suffix (radix : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns : Option (List Bool)) : Tapes 17 radix :=
  ⟨![0,0,0,0,0,descriptorHead bs,0,descriptorHead qs,0,0,p,q,0,0,0,0,descriptorHead ns],
    ![fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
      descriptorTape radix bs,fun _ => blank,descriptorTape radix qs,fun _ => blank,fun _ => blank,
      fun z => RadixToBinary.binaryEncoding.encode (source z),
      fun z => RadixToBinary.binaryEncoding.encode (dest z),
      fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,descriptorTape radix ns]⟩

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

private theorem stream_outer (i : Fin 2) :
    RationalPrefixTranslationInit.streamPlacement c (Fin.natAdd (c+1) (Fin.natAdd 15 i)) =
      Fin.natAdd (16+c) i := by
  change appendEquiv (RationalPrefixTranslationExecution.prefixPlacement c) 2 _ = _
  have he : (Fin.natAdd (c+1) (Fin.natAdd 15 i) : Fin (((c+1)+15)+2)) =
      Fin.natAdd ((c+1)+15) i := Fin.ext (by simp; omega)
  rw [he,appendEquiv_right]

/-- Exact entire input. Width descriptors, B/Q/P and payloads are the only
nonblank supplied tapes; no initialized marker or computed result is hidden. -/
theorem input_layout (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool) (a : Fin (P*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    RationalPrefixTranslationBootstrap.input r order width ws a source dest p q bs qs ns =
      (PrefixCounterInit.input (q := radix) (c+1) ws).append
        (suffix radix (putWord source p (List.ofFn a)) dest p q (some bs) (some qs) (some ns)) := by
  unfold RationalPrefixTranslationBootstrap.input
  apply congrArg (Tapes.append (PrefixCounterInit.input (q := radix) (c+1) ws))
  unfold RationalPrefixTranslationBootstrap.raw
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [RationalPrefixTranslationBootstrap.workspace,Fin.isValue] <;> norm_num
  all_goals
    simp only [Placement.extra]
    first
    | rw [show (5 : Fin 17) = Fin.castAdd 2 (5 : Fin 15) by rfl,stream_metadata]
    | rw [show (7 : Fin 17) = Fin.castAdd 2 (7 : Fin 15) by rfl,stream_metadata]
    | rw [show (10 : Fin 17) = Fin.castAdd 2 (10 : Fin 15) by rfl,stream_metadata]
    | rw [show (11 : Fin 17) = Fin.castAdd 2 (11 : Fin 15) by rfl,stream_metadata]
    | rw [show (16 : Fin 17) = Fin.natAdd 15 (1 : Fin 2) by rfl,stream_outer]
    simp only [FlatControlledShift.bank,CountedLoopReuseAlphabet.bank,Tapes.append,
      Fin.addCases_left,Fin.addCases_right,RationalPrefixTranslationStream.state,
      RationalPrefixTranslationExecution.bank]
    try rfl
  all_goals
    try simp only [FlatControlledShift.initial_length,FlatControlledShift.source_eq,
      Nat.zero_mul,Nat.cast_zero,add_zero,RationalPrefixTranslationStream.outputPrefix,
      TranslationPreparedFamily.outputPrefix]
    first
    | rfl
    | exact (CountedLoopReuseAlphabet.encoding_binary ns).symm

end IntegerMultBounds.Machine.FlatControlledShiftLayout
