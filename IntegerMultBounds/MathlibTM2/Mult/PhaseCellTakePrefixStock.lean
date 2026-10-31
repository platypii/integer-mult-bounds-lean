module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Move an owned counted prefix in its original order. Unlike copying, this
advances the source without retaining another full archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem takePrefix_native (count src dst saved tmp : Fin T) :
    mnNativePushBound 2 (takePrefix (P := P) (Q := Q) (A := A) (U := U) count src dst saved tmp) := by
  simp [takePrefix,transfer,scanR,drainR,popDo,keepIn,transferAct,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

theorem takePrefix_exec_within (count src dst saved tmp : Fin T)
    (hreg : [count,src,dst,saved,tmp].Nodup) (xs tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = xs++tail)
    (hcount : (S.R count).length = xs.length) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+2*(6*xs.length+6)) depth
        (takePrefix count src dst saved tmp) (Host.mk v S) (6*xs.length+6)
        (Host.mk v' {S with R := (Function.update (Function.update S.R src tail) dst (xs++S.R dst))}) := by
  obtain ⟨v',hu,he⟩ := takePrefix_exec hreg v S xs tail hsrc hcount hsaved htmp
  exact ⟨v',hu,mn_native_exec_within he 2 (takePrefix_native _ _ _ _ _) depth _ (by omega)⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
