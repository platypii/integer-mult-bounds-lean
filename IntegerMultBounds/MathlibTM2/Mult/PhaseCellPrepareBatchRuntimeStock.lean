module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareBatchRuntime
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Cached batch routing and header installation have only linear native stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem prepareBatchRuntime_native :
    mnNativePushBound 4 (prepareBatchRuntime (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [prepareBatchRuntime,swapBatchPayload,installBatchHeaders,swapAfterPrefix,
    unaryProduct,umul,uadd,clearWords,transfer,transferAct,ucopy,umulSym,
    scanP,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,
    uclear,mnNativePushBound,mnActPush]

theorem prepareBatchRuntime_exec_within (P N q l B L w : ℕ)
    (pre factors rhs tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hN : (S.R 101).length = N)
    (hq : (S.R 112).length = q) (hl : (S.R 109).length = l)
    (hB : (S.R 96).length = B) (hL : (S.R 103).length = L) (hw : (S.R 94).length = w)
    (hpre : pre.length = (3*(B*L)+1)*w) (hfactors : factors.length = B*L*w) (hrhs : rhs.length = B*L*w)
    (hsrc : S.R 110 = pre ++ (factors ++ (rhs ++ tail)))
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 100, 104, 105, 106, 107, 108], S.R k = []) (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareBatchRuntimeCost P N q l B L w ∧
      ExecWithin body (fun level z => mnSize z + level ≤ mnSize (mk v S) + depth +
        4 * prepareBatchRuntimeCost P N q l B L w)
        depth prepareBatchRuntime (mk v S) m
        (mk v' (batchHeaderBank { S with R := (Function.update S.R 110
          (pre ++ (rhs ++ (factors ++ tail)))) } q l B)) := by
  obtain ⟨v',m,hu,hm,he⟩ := prepareBatchRuntime_exec (body := body) P N q l B L w
    pre factors rhs tail v S hP hN hq hl hB hL hw hpre hfactors hrhs hsrc hfresh
  exact ⟨v',m,hu,hm,mn_native_exec_within he 4 prepareBatchRuntime_native depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hm) _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
