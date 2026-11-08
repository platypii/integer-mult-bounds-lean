module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJointSourceRecoveryCoupling
public import IntegerMultBounds.MathlibTM2.Host.ExchangePairStock

/-! Recovery replaces two consumed prefixes by two equal-length archives.
Its endpoint stock is unchanged, so iteration can share one scratch reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} {U : Type}

theorem jointSourceRecoveryCouplingState_stock (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (source : Fin T) (hbank : ∀ i, placement.bank i ≠ source)
    (hgather : ∀ i, plan.gather i ≠ source)
    (C B : ZMod s → GaussianInt) (tail rhsTail output : List (Fin (A+4)))
    (houtput : output.length = H.span*H.wordWidth)
    (v w : HS T Q A U) (S : Stacks T A)
    (hsource : S.R source = cstream A H.wordWidth (packedInterval H.origin H.span C)++tail)
    (hrhs : S.R (placement.bank 93) = cstream A H.wordWidth (packedInterval H.origin H.span B)++rhsTail) :
    mnSize (mk w (jointSourceRecoveryCouplingState H placement source C tail rhsTail output S)) = mnSize (mk v S) := by
  have hreg : [source,placement.bank 93,placement.bank 110,plan.gather 125].Nodup := by
    simp [List.nodup_cons,(hbank 93).symm,(hbank 110).symm,(hgather 125).symm,
      placement.bank_injective.eq_iff,placement.bank_gather_disjoint]
  rw [jointSourceRecoveryCouplingState_eq H placement source hbank hgather]
  apply mn_exchange_pair_size source (placement.bank 93) (placement.bank 110) (plan.gather 125)
    hreg v w S _ _ output (cstream A H.wordWidth (packedInterval H.origin H.span C)) tail rhsTail hsource hrhs
  · simpa [length_cstream,packedInterval_length C H.span_fit] using houtput
  · simp [length_cstream,packedInterval_length C H.span_fit,packedInterval_length B H.span_fit]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
