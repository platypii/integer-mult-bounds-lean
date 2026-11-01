module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryNormalizePlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderQueue

/-! Build normalization's ordinary parameter-word packet from retained unary
inputs. The queue plan contains only wiring and separation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

structure RecoveryParameterQueue {T : ℕ} (normalize : RecoveryNormalizePlan T) where
  parameters : Fin 8 → Fin T
  word : Fin T
  saved : Fin T
  tmp : Fin T
  carry : Fin T
  regs : ∀ i, [parameters i,normalize.scalar .wr,word,saved,tmp,normalize.header].Nodup

namespace RecoveryParameterQueue
variable {T Q A : ℕ} {P U : Type} {normalize : RecoveryNormalizePlan T}
def program (queue : RecoveryParameterQueue normalize) : Pr P T Q A U :=
  binaryHeaderQueue (normalize.scalar .wr) queue.word queue.saved queue.tmp normalize.header queue.carry
    (List.ofFn queue.parameters)
end RecoveryParameterQueue
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
