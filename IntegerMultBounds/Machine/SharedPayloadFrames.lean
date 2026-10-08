import IntegerMultBounds.Machine.SharedPayloadPair

/-! The common-payload representation has no hidden private copies. The two
old payload slots in each metadata bank are literal blank stationary tapes. -/
namespace IntegerMultBounds.Machine.SharedPayloadFrames
open SharedPlacementAlphabet (setTape)
variable {t u a : ℕ}

theorem strip_payload (v : Tapes t a) (source dest : Fin t) :
    SharedPayload.payload (SharedPayload.strip v source dest) source dest =
      (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes 2 a) := by
  unfold SharedPayload.payload SharedPayload.strip setTape
  by_cases h : source = dest
  · subst dest
    simp only [Function.update_apply,ite_true]
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  · simp only [Function.update_apply,h,ite_false,ite_true]
    congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- Both metadata banks retain blank private payload slots, even though the
second stage's logical input is supplied through the common physical pair. -/
theorem input_private (v : Tapes t a) (x : Tapes u a)
    (source dest : Fin t) (source' dest' : Fin u) :
    SharedPayload.payload (SharedPayloadPair.input v x source dest source' dest')
      (Fin.castAdd u (Fin.natAdd 2 source)) (Fin.castAdd u (Fin.natAdd 2 dest)) =
        (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes 2 a) ∧
    SharedPayload.payload (SharedPayloadPair.input v x source dest source' dest')
      (Fin.natAdd (2+t) source') (Fin.natAdd (2+t) dest') =
        (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes 2 a) := by
  constructor
  · simpa only [SharedPayloadPair.input,SharedPayloadPair.output,SharedPayload.bank,SharedPayload.payload,
      Tapes.append,Fin.addCases_left,Fin.addCases_right] using strip_payload v source dest
  · simpa only [SharedPayloadPair.input,SharedPayloadPair.output,SharedPayload.bank,SharedPayload.payload,
      Tapes.append,Fin.addCases_left,Fin.addCases_right] using strip_payload x source' dest'

/-- Execution also leaves these unused private payload slots blank. -/
theorem output_private (v : Tapes t a) (x : Tapes u a)
    (source dest : Fin t) (source' dest' : Fin u) :
    SharedPayload.payload (SharedPayloadPair.output v x source dest source' dest')
      (Fin.castAdd u (Fin.natAdd 2 source)) (Fin.castAdd u (Fin.natAdd 2 dest)) =
        (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes 2 a) ∧
    SharedPayload.payload (SharedPayloadPair.output v x source dest source' dest')
      (Fin.natAdd (2+t) source') (Fin.natAdd (2+t) dest') =
        (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes 2 a) := by
  constructor
  · simpa only [SharedPayloadPair.input,SharedPayloadPair.output,SharedPayload.bank,SharedPayload.payload,
      Tapes.append,Fin.addCases_left,Fin.addCases_right] using strip_payload v source dest
  · simpa only [SharedPayloadPair.input,SharedPayloadPair.output,SharedPayload.bank,SharedPayload.payload,
      Tapes.append,Fin.addCases_left,Fin.addCases_right] using strip_payload x source' dest'

end IntegerMultBounds.Machine.SharedPayloadFrames
