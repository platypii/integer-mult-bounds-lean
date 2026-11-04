module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerPair

/-! Change a batch's replica-count index using an ordinary length equality.
Records, format and inverse data stay definitionally unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
variable {A s t B L : ℕ} [NeZero s] [NeZero t]

noncomputable def withReplicaCount (batch : PackedExactBatch A s t B L)
    (B' : ℕ) (hB : B = B') : PackedExactBatch A s t B' L :=
  { batch with hreplicas := fun r hr => (batch.hreplicas r hr).trans hB }

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
