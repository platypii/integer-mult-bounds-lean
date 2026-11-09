module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicComplexCaller

/-! The executed factor setup bill depends only on scalar dimensions, so a
class scan can choose its per-job time allowance before execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def cyclicBoundaryPageTime (s t band a n : ℕ) [NeZero s] : ℕ :=
  let V := publicationGeometryWidth t band
  let N := (cyclicPrincipalBoundary s t band a n).card
  generatePublicationWidthCost t band+
    ((4*a+4)+(((s+a+n)*(4*V+10)+3*(8*V+12)+1+
      7*(4*V+4)+3*(8*V+8)+2+5*TableVM.tblC V 0)+
      (6*(a+n)+22*V+13)+(2*(7*V)+15))+(2*(a+n)+5)+
    ((residentCyclicBoundaryOrderCost V s t band a n+N*(6*V+6)+4)+closedCyclicPageFoldCost N V))

theorem prepareCyclicBoundaryPageCost_eq {s A : ℕ} [NeZero s]
    (R : Regs 154 A) (t band a n : ℕ)
    (hs : (R 121).length = s) (ha : (R 141).length = a) (hn : (R 142).length = n) :
    prepareCyclicBoundaryPageCost R s t band a n = cyclicBoundaryPageTime s t band a n := by
  simp only [prepareCyclicBoundaryPageCost,retainedCyclicEndpointsCost,cyclicSplitRulersCost,
    binaryHeaderQueueCost,hs,ha,hn,cyclicBoundaryPageTime]
  ring

noncomputable def cyclicFactorTime (p l s t u target a n : ℕ) [NeZero s] : ℕ :=
  (List.ofFn (fun i => 4*cyclicFactorMasterValues p l s t u target a n i+4)).sum+1+
    cyclicBoundaryPageTime s t (PhaseCellBand.width p u) a n

theorem fittingCyclicFactorTime_eq {T A s : ℕ} [NeZero s]
    (ports : CyclicComplexCallerLayout T) (C F : Stacks T A) (p l t u target a n : ℕ)
    (hvalues : ∀ j, (C.R (cachedFactorSeedSource
      (ports.small ∘ CyclicReplicaPlacement.left.plan.gather) ports.span j)).length =
        cyclicFactorMasterValues p l s t u target a n j)
    (hseed : CyclicFactorSeedInput p l s t u target a n []
      (embStk (ports.small ∘ CyclicReplicaPlacement.factorReg) F)) :
    ports.factorTimeCost s t p u a n C F = cyclicFactorTime p l s t u target a n := by
  unfold CyclicComplexCallerLayout.factorTimeCost
  rw [prepareCyclicBoundaryPageCost_eq _ t _ a n hseed.sourceLength hseed.origin hseed.span]
  simp only [Function.comp_def] at hvalues
  simp only [copyUnaryHeadersCost,masterHeaderCopies,List.map_ofFn,Function.comp_def,hvalues,
    cyclicFactorTime]

end IntegerMultBounds.MathlibTM2.Cost
