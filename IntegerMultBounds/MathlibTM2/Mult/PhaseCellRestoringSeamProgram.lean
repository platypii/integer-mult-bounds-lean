module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonDimensionRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication

/-! Fixed restoring seam instructions, independent of core geometry and witnesses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {src dst : Fin T}

def restoringSeamPublication (plan : PreparedPublicationPlan T src dst)
    (clock lineRows wide width count work saved tmp extra coreBits wordWidth skip setupTmp setupSaved retireTmp : Fin T) :
    Pr P T Q A U :=
  (.seq (.seq (singletonPublicationSetup plan coreBits wordWidth skip setupTmp setupSaved)
          (.seq (.seq (widenPackedPrefix wide width count src work saved tmp extra)
          (plan.replicaProgram clock lineRows)) (retireSingletonAdvances skip plan.advances retireTmp))) (clearWords [plan.count,plan.window,plan.wordWidth]))

theorem restoringSeamPublication_native (plan : PreparedPublicationPlan T src dst)
    (clock lineRows wide width count work saved tmp extra coreBits wordWidth skip setupTmp setupSaved retireTmp : Fin T) :
    mnNativePushBound 13 (restoringSeamPublication (P := P) (Q := Q) (A := A) (U := U)
      plan clock lineRows wide width count work saved tmp extra coreBits wordWidth skip setupTmp setupSaved retireTmp) := by
  exact ⟨⟨mnNativePushBound_mono (by decide)
        (singletonPublicationSetup_native plan coreBits wordWidth skip setupTmp setupSaved),
        ⟨⟨widenPackedPrefix_native _ _ _ _ _ _ _ _,
          mnNativePushBound_mono (by decide) (plan.replica_native clock lineRows)⟩,
          mnNativePushBound_mono (by decide) (retireSingletonAdvances_native skip plan.advances retireTmp)⟩⟩,
      mnNativePushBound_mono (by decide) (clearWords_native _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
