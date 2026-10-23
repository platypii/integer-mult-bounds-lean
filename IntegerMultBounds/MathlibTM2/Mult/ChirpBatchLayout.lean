module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchState

/-! # Layout preconditions of shared chirp correlation execution -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.Spec.SignedRingProduct

/-- Static layout facts, independent of all operand values and execution states. -/
structure ChirpBatchLayout {T : ℕ} (j : SetupReg → Fin T) (rg : RpReg → Fin T)
    (ι : Fin 91 → Fin T) (e : CorrelationReg → Fin T)
    (records recordSaved srcX srcY saved acc buf savedBlock tmp : Fin T) : Prop where
  setup_inj : Function.Injective j
  width : j .w = rg .wn
  header : j .header = rg .d0
  counters : ∀ s ∈ setupCounters, ∀ r, j s ≠ rg r
  privateBank : ∀ s ∈ setupCounters, ∀ k, j s ≠ ι k
  packX : [records, recordSaved, j .countX, j .padX, srcX, saved, acc, buf, savedBlock, tmp, rg .xs].Nodup
  packY : [records, recordSaved, j .countY, j .padY, srcY, saved, acc, buf, savedBlock, tmp, rg .ys].Nodup
  offY : ∀ k ∈ [records, recordSaved, j .countY, j .padY, srcY, saved, acc, buf, savedBlock, tmp], k ≠ rg .xs
  data : ∀ k ∈ [records, recordSaved, srcX, srcY, saved, acc, buf, savedBlock, tmp],
    ∀ s ∈ setupWritten, k ≠ j s
  extraction_inj : Function.Injective e
  ringSize : e .l = j .l
  word : e .w = j .w
  batch : e .batch = records
  source : e .src = rg .out

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
