module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicFactorTimeLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFittingCyclicInputLedger
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedOriginCyclicCaller

/-! A time allowance fixed before the origin callback runs. Every term is a
scalar dimension or a mathematical replica problem, never a tape-state witness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement CyclicComplexCallerLayout

noncomputable def generatedOriginTimeCost {Q A s : ℕ} {U : Type} [NeZero s]
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (B : ℕ) (H K : ReplicaHaloProblem s)
    (p u l t a n target q W radius core replicas N V : ℕ) : ℕ :=
  readSupplierEndpointsCost V a n+
    (CyclicSeedLayout.timeCost B p u l target s t a n+
      retiredTimeCost (A := A) (U := U) hR hQ
        ((fittingCyclicInputSharedTime H K W+N*fittingCyclicInputRowTime H K W)+
          (cyclicFactorTime p l s t u (boundaryRecoveryTarget p (target+1)) a n+
            ((4*(W+radius+core)+13)+
              cyclicComplexCoreTimeCost H K p u l t a n target q W radius core replicas N))) (N*n*W)+
      (2*(List.ofFn (inverseMasterValues p u l target s t a (a+n))).sum+21))+
    (2*(a+(a+n))+5)

end IntegerMultBounds.MathlibTM2.Cost
