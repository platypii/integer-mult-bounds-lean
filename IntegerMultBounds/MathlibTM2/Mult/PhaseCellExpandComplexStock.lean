module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExpandComplexKeyCounted
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Simultaneous stock for the linear complex-input expansion stage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem expandComplexKeyCounted_pushBound (replicas width count src imag saved tmp hold : Fin T) :
    mnNativePushBound 2 (expandComplexKeyCounted (P := P) (Q := Q) (A := A) (U := U)
      replicas width count src imag saved tmp hold) := by
  simp [expandComplexKeyCounted,expandComplexKey,expandComplexPrefix,splitComponentPrefix,
    unaryProduct,scanP,ucopy,umulSym,transfer,copyR,moveR,uclear,
    keepIn,scanR,transferAct,copyStep,drainR,popDo,whileR,moveStep,peekR,pushN,popPush,mnNativePushBound,mnActPush]

/-- The actual expansion trace uses only linear stream work. Its time bill
therefore gives a local-volume stock allowance, including saved counters and
both component streams, over the entire initial spectator bank. -/
theorem expandComplexKeyCounted_within_stock {body : P → Pr P T Q A U}
    {replicas width count src imag saved tmp hold : Fin T}
    {v v' : HS T Q A U} {S G : Stacks T A} {n N W : ℕ}
    (hex : Exec body (expandComplexKeyCounted replicas width count src imag saved tmp hold)
      (mk v S) n (mk v' G)) (hn : n ≤ N*(26*W+17)+34) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(N*(26*W+17)+34))
      depth (expandComplexKeyCounted replicas width count src imag saved tmp hold)
      (mk v S) n (mk v' G) := by
  exact mn_native_exec_within hex 2 (expandComplexKeyCounted_pushBound _ _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
