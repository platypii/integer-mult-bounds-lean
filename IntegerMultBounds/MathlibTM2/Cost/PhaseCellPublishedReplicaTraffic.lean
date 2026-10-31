module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedGatheredPublication

/-! Exact shared/repeated decomposition of the executed publication caller.
Only native packed-line traffic repeats; all page generation is shared. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem preparedGatheredPublicationCost_replicas (N V span L w B : ℕ) :
    preparedGatheredPublicationCost N V span L w B =
      preparedGatheredPublicationCost 0 V span L w B+N*(47*(span*w)+26) := by
  unfold preparedGatheredPublicationCost routedEncodedPublicationCost symbolEncodedPublicationCost
  ring

theorem preparedGatheredPublicationWorkspace_replicas (Q A : ℕ) (U : Type) (N V span L w B : ℕ) :
    preparedGatheredPublicationWorkspace Q A U N V span L w B =
      preparedGatheredPublicationWorkspace Q A U 0 V span L w B+2*N*(47*(span*w)+26) := by
  unfold preparedGatheredPublicationWorkspace routedEncodedPublicationCost symbolEncodedPublicationCost
  ring

/-- This bound also covers empty halos without a positivity side condition. -/
theorem preparedGatheredPublicationCost_le_shared (N V span L w B : ℕ) :
    preparedGatheredPublicationCost N V span L w B ≤
      preparedGatheredPublicationCost 0 V span L w B+73*N*(span*w+1) := by
  rw [preparedGatheredPublicationCost_replicas]
  nlinarith only [Nat.zero_le (N*(span*w))]

theorem preparedGatheredPublicationWorkspace_le_shared (Q A : ℕ) (U : Type) (N V span L w B : ℕ) :
    preparedGatheredPublicationWorkspace Q A U N V span L w B ≤
      preparedGatheredPublicationWorkspace Q A U 0 V span L w B+146*N*(span*w+1) := by
  rw [preparedGatheredPublicationWorkspace_replicas]
  nlinarith only [Nat.zero_le (N*(span*w))]

end IntegerMultBounds.MathlibTM2.Cost
