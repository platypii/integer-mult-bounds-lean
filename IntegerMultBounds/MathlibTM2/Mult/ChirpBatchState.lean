module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGeneratedBatch

/-! # Data preconditions of the shared chirp batch caller

Separate the tape contents from layout proofs. Updating a distinct raw operand tape
preserves these preconditions, so operand producers can feed S1 without assuming an
execution contract for their continuation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.MathlibTM2.Fast

/-- The supplied unary dimensions and empty workspace of the shared batch caller. -/
structure ChirpBatchState {T A : ℕ} (j : SetupReg → Fin T) (rg : RpReg → Fin T)
    (ι : Fin 91 → Fin T) (e : CorrelationReg → Fin T)
    (records recordSaved saved acc buf savedBlock tmp : Fin T)
    (q l w M m : ℕ) (S : Stacks T A) : Prop where
  clean : RpClean ι S
  precision : (S.R (j .p)).length = q + 1
  ringSize : (S.R (j .l)).length = l
  width : (S.R (j .w)).length = w
  inputLength : (S.R (j .a)).length = 3 * m + 1
  kernelLength : (S.R (j .b)).length = 4 * m
  setup : ∀ s ∈ setupWritten ++ setupScratch, S.R (j s) = []
  batch : (S.R records).length = M
  scratch : ∀ k ∈ [recordSaved, saved, acc, buf, savedBlock, tmp], S.R k = []
  product : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3], S.R (rg r) = []
  outputLength : (S.R (e .m)).length = m
  output : S.R (rg .out) = []
  owned : ∀ r ∈ [CorrelationReg.triples, .skip, .recordSymbols], S.R (e r) = []
  extraction : ∀ r ∈ [CorrelationReg.batchSaved, .acc, .savedSource, .savedSkip, .recordSaved,
    .current, .saved, .buf, .tmp], S.R (e r) = []

/-- Writing an operand disjoint from the caller's controls and scratch preserves readiness. -/
theorem ChirpBatchState.update_operand {T A : ℕ}
    {j : SetupReg → Fin T} {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}
    {e : CorrelationReg → Fin T} {records recordSaved saved acc buf savedBlock tmp : Fin T}
    {q l w M m : ℕ} {S : Stacks T A}
    (h : ChirpBatchState j rg ι e records recordSaved saved acc buf savedBlock tmp q l w M m S)
    (src : Fin T) (words : List (Fin (A + 4)))
    (hj : ∀ r, j r ≠ src) (hrg : ∀ r, rg r ≠ src) (hι : ∀ r, ι r ≠ src)
    (he : ∀ r, e r ≠ src)
    (hdata : ∀ k ∈ [records, recordSaved, saved, acc, buf, savedBlock, tmp], k ≠ src) :
    ChirpBatchState j rg ι e records recordSaved saved acc buf savedBlock tmp q l w M m
      { S with R := Function.update S.R src words } := by
  constructor
  · exact ⟨h.clean.1, fun r hr => (Function.update_of_ne (hι r) _ _).trans (h.clean.2 r hr)⟩
  · simpa only [Function.update_of_ne (hj .p)] using h.precision
  · simpa only [Function.update_of_ne (hj .l)] using h.ringSize
  · simpa only [Function.update_of_ne (hj .w)] using h.width
  · simpa only [Function.update_of_ne (hj .a)] using h.inputLength
  · simpa only [Function.update_of_ne (hj .b)] using h.kernelLength
  · intro r hr
    simpa only [Function.update_of_ne (hj r)] using h.setup r hr
  · simpa only [Function.update_of_ne (hdata records (by simp))] using h.batch
  · intro k hk
    have hne := hdata k (List.mem_cons_of_mem records hk)
    simpa only [Function.update_of_ne hne] using h.scratch k hk
  · intro r hr
    simpa only [Function.update_of_ne (hrg r)] using h.product r hr
  · simpa only [Function.update_of_ne (he .m)] using h.outputLength
  · simpa only [Function.update_of_ne (hrg .out)] using h.output
  · intro r hr
    simpa only [Function.update_of_ne (he r)] using h.owned r hr
  · intro r hr
    simpa only [Function.update_of_ne (he r)] using h.extraction r hr

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
