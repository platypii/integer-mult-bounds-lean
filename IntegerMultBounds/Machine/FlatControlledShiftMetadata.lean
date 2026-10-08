import IntegerMultBounds.Machine.FlatControlledShiftPayload

/-! The private input bank of a controlled-shift stage contains only dimensional
metadata. Replacing the permanent payload pair leaves this bank identical. -/
namespace IntegerMultBounds.Machine.FlatControlledShiftMetadata
open SharedPlacementAlphabet (setTape)
open PrefixCounterInitPlacement
variable {radix c B P : ℕ} [Fact radix.Prime]

private theorem setTape_append_right {l r a : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p = v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals rename_i k; intro h; have hk := k.isLt; omega

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

/-- Stripping the two physical payload slots removes all dependence on the
array supplied to the ready input; no stage output is needed to prepare metadata. -/
theorem strip_input_eq (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool) (a a' : Fin (P*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    SharedPayload.strip (RationalPrefixTranslationBootstrap.input r order width ws a source dest p q bs qs ns)
      (FlatControlledShiftPayload.sourceSlot c) (FlatControlledShiftPayload.destSlot c) =
    SharedPayload.strip (RationalPrefixTranslationBootstrap.input r order width ws a' source dest p q bs qs ns)
      (FlatControlledShiftPayload.sourceSlot c) (FlatControlledShiftPayload.destSlot c) := by
  unfold SharedPayload.strip RationalPrefixTranslationBootstrap.input
    FlatControlledShiftPayload.sourceSlot FlatControlledShiftPayload.destSlot
  rw [setTape_append_right,setTape_append_right,setTape_append_right,setTape_append_right]
  apply congrArg (Tapes.append (PrefixCounterInit.input (q := radix) (c+1) ws))
  unfold setTape RationalPrefixTranslationBootstrap.raw
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Function.update_apply,RationalPrefixTranslationBootstrap.workspace,Fin.isValue] <;>
    norm_num
  all_goals
    simp only [Placement.extra]
    first
    | rw [show (5 : Fin 17) = Fin.castAdd 2 (5 : Fin 15) by rfl,stream_metadata]
    | rw [show (7 : Fin 17) = Fin.castAdd 2 (7 : Fin 15) by rfl,stream_metadata]
    | rw [show (16 : Fin 17) = Fin.natAdd 15 (1 : Fin 2) by rfl,stream_outer]
    simp only [FlatControlledShift.bank,CountedLoopReuseAlphabet.bank,Tapes.append,
      Fin.addCases_left,Fin.addCases_right,RationalPrefixTranslationStream.state,
      RationalPrefixTranslationExecution.bank]
    try rfl

end IntegerMultBounds.Machine.FlatControlledShiftMetadata
