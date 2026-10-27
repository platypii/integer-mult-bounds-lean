module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFactorBatchReleaseFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageReleaseVolume

/-! Bound batch release with the original retained-page stock and the whole result length. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def placedFactorBatchReleaseCostBound (s replicas N W w V D H : ℕ) : ℕ :=
  s*(4*replicas+9)+4+
    (retirePackedBandTableCost N W w+12*(replicas*s)*w+9*(replicas*s)+12+
      2*sharedPageOwnedVolumeBound s w V N D H+2*sharedPageOwnedRegs.length+1)+
    (2*(replicas*s)+2)

theorem placedFactorBatchReleaseCost_le {A s replicas N W w V D H : ℕ} (S : Stacks 256 A)
    (hvolume : (sharedPageOwnedRegs.map fun i => ((embStk couplingBoundaryReg S).R i).length).sum ≤
      sharedPageOwnedVolumeBound s w V N D H) :
    s*(4*replicas+9)+4+
      sharedPageReleaseCost (replicas*s) N W w
        (embStk placedFactorBatchReleaseReg (placedFactorBatchReleaseInput S (replicas*s)))+
      (2*(replicas*s)+2) ≤ placedFactorBatchReleaseCostBound s replicas N W w V D H := by
  rw [placedFactorBatchReleaseCost_eq]
  dsimp only [sharedPageReleaseCost,placedFactorBatchReleaseCostBound]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
