module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrdinaryGeneratedNormalize
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryNormalizeStock

/-! Reuse the normalization stock proof; generating its byte ruler is native
work with a smaller push bound than the existing rounding operation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
namespace RecoveryNormalizePlan
variable {T Q A : ℕ} {P U : Type}

def generatedProgram (plan : RecoveryNormalizePlan T) : Pr P T Q A U :=
  ordinaryGeneratedNormalizePackedBatch plan.scalar plan.ports plan.header plan.precision plan.wide plan.rows
    plan.replicas plan.inputWidth plan.count plan.src plan.work plan.saved plan.tmp plan.sp plan.sg plan.cy

theorem generated_native (plan : RecoveryNormalizePlan T) :
    mnNativePushBound 13 (plan.generatedProgram (P := P) (Q := Q) (A := A) (U := U)) := by
  have h := plan.native (P := P) (Q := Q) (A := A) (U := U)
  change mnNativePushBound 13 (ordinaryNormalizePackedBatch ..) at h
  have hw := mnNativePushBound_mono (by decide : 2 ≤ 13)
    (recoveryInputWidth_native (P := P) (Q := Q) (A := A) (U := U)
      (plan.scalar (.v 20)) plan.rows (plan.ports 0) plan.inputWidth plan.count plan.saved plan.tmp)
  have hc : mnNativePushBound 13 (uclear (P := P) (Q := Q) (A := A) (U := U) plan.inputWidth) := by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]
  exact ⟨h.1,⟨h.2.1.1,hw,h.2.1.2.1,hc,h.2.1.2.2⟩,h.2.2⟩

end RecoveryNormalizePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
