import IntegerMultBounds.Machine.SharedPayloadFrames

/-! A stage interface recording a concrete program, its exact input/output,
canonical common payload pair, input-independent private metadata, and charged
runtime. Actual affine stage constructors discharge all these fields. -/
namespace IntegerMultBounds.Machine.SharedPayloadStage
universe u

structure Stage (X : Type u) (alphabet : ℕ) (common : X → Tapes 2 alphabet) where
  tapes : ℕ
  states : ℕ
  program : Program tapes states alphabet
  transform : X → X
  input : X → Tapes tapes alphabet
  output : X → Tapes tapes alphabet
  source : Fin tapes
  dest : Fin tapes
  distinct : source ≠ dest
  metadata : Tapes tapes alphabet
  cost : ℕ
  input_payload : ∀ x, SharedPayload.payload (input x) source dest = common x
  output_payload : ∀ x, SharedPayload.payload (output x) source dest = common (transform x)
  strip_input : ∀ x, SharedPayload.strip (input x) source dest = metadata
  realizes : ∀ x, HoareTime program (fun v => v = input x) (fun v => v = output x) cost

end IntegerMultBounds.Machine.SharedPayloadStage
