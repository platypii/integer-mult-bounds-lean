module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComplexBatchAssembly
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Simultaneous stock for the linear complex-output assembly stage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem packedComplexBatchFinish_pushBound (hold replicas nativeCount width count src buf saved tmp : Fin T) :
    mnNativePushBound 2 (packedComplexBatchFinish (P := P) (Q := Q) (A := A) (U := U)
      hold replicas nativeCount width count src buf saved tmp) := by
  simp [packedComplexBatchFinish,pairComplexKey,pairComplexPrefix,pairComponents,pairComponentStep,
    releaseComplexCounts,usub,dropTop,countedLoopBody,countedLoop,unaryProduct,scanP,ucopy,umulSym,transfer,moveR,uclear,
    keepIn,scanR,transferAct,drainR,popDo,whileR,moveStep,peekR,pushN,popPush,mnNativePushBound,mnActPush]


/-- The actual pairing and counter-release trace uses only linear stream work. Its time bill
therefore gives a local-volume stock allowance, including saved counters and
the component streams and returned complex output, over the entire initial spectator bank. -/
theorem packedComplexBatchFinish_within_stock {body : P → Pr P T Q A U}
    {hold replicas nativeCount width count src buf saved tmp : Fin T}
    {v v' : HS T Q A U} {S G : Stacks T A} {n N W : ℕ}
    (hex : Exec body (packedComplexBatchFinish hold replicas nativeCount width count src buf saved tmp)
      (mk v S) n (mk v' G)) (hn : n ≤ N*(16*W+19)+22) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(N*(16*W+19)+22))
      depth (packedComplexBatchFinish hold replicas nativeCount width count src buf saved tmp)
      (mk v S) n (mk v' G) := by
  exact mn_native_exec_within hex 2 (packedComplexBatchFinish_pushBound _ _ _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
