module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedDyadicPublicationHeaders
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCountedPublicationDimensionBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDyadicPublicationHeaderBudget

/-! Charge the single dimension/binary-header lifecycle once. All generated
words restore after the consumer; both time and peak stock are source-linear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose

theorem generatedPublicationHeadersCosts_le (N b s L W V p cV : ℕ)
    (hrows : N*L ≤ s) (hL : 1 ≤ L) (hspan : L ≤ s) (hW : 1 ≤ W)
    (hp : 1 ≤ p) (hps : p ≤ s) (hV : V ≤ cV*p) :
    generatedPublicationHeadersCost b N L W V+2*(countedPublicationDimensionsVolume b N L W+3*V)+21 ≤
      (1000+100*cV)*(2^b*(s*W)) ∧
    2*generatedPublicationHeadersCost b N L W V ≤ (1000+100*cV)*(2^b*(s*W)) := by
  obtain ⟨htDim,hsDim⟩ := countedPublicationDimensionsCosts_le N b s L W hrows hL hspan (hp.trans hps) hW
  obtain ⟨htBinary,hsBinary⟩ := dyadicPublicationHeaderCosts_le N b s L W V p cV hrows hL hspan hW hp hps hV
  unfold generatedPublicationHeadersCost
  constructor <;> nlinarith only [htDim,hsDim,htBinary,hsBinary]

end IntegerMultBounds.MathlibTM2.Cost
