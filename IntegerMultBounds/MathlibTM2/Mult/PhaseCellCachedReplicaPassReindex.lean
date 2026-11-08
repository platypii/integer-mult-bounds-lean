module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassPost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaPlacement

/-! Bank views commute with injective placement. Recovery transports the retained
168-tape bank directly, without lifting a consumed residual archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T T' A : ℕ} [NeZero s]

theorem CachedReplicaPassPlacement.reindex_bank_view (job : CachedReplicaPassPlacement T)
    (e : Fin T → Fin T') (he : Function.Injective e) (S : Stacks T' A) :
    embStk (job.reindex e he).coupling.bank S = embStk job.coupling.bank (embStk e S) := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    change S.L ((job.coupling.reindex e he).bank i) = S.L (e (job.coupling.bank i))
    rw [ReplicaCouplingPlacement.reindex_bank]
  · funext i
    change S.R ((job.coupling.reindex e he).bank i) = S.R (e (job.coupling.bank i))
    rw [ReplicaCouplingPlacement.reindex_bank]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
