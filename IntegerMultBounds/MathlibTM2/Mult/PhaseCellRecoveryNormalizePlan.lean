module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizeNativeBatch

/-! Pure wiring for the existing generated normalization/publication routine. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure RecoveryNormalizePlan (T : ℕ) where
  scalar : TblR 25 → Fin T
  scalar_injective : Function.Injective scalar
  ports : Fin 4 → Fin T
  ports_injective : Function.Injective ports
  header : Fin T
  precision : Fin T
  wide : Fin T
  rows : Fin T
  replicas : Fin T
  inputWidth : Fin T
  count : Fin T
  src : Fin T
  work : Fin T
  saved : Fin T
  tmp : Fin T
  sp : Fin T
  sg : Fin T
  cy : Fin T
  regs : [header,precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,
    ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup
  separate : ∀ k ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy], ∀ i, scalar i ≠ k
  ports_off : ∀ i j, scalar j ≠ ports i
  header_off : ∀ i, scalar i ≠ header

namespace RecoveryNormalizePlan
variable {T Q A : ℕ} {P U : Type}
def program (plan : RecoveryNormalizePlan T) : Pr P T Q A U :=
  ordinaryNormalizePackedBatch plan.scalar plan.ports plan.header plan.precision plan.wide plan.rows plan.replicas
    plan.inputWidth plan.count plan.src plan.work plan.saved plan.tmp plan.sp plan.sg plan.cy
end RecoveryNormalizePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
