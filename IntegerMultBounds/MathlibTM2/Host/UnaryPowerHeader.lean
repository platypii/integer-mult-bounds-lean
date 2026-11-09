module

public import IntegerMultBounds.MathlibTM2.Host.UnaryBitLength

/-! Generate a unary power of two from a borrowed exponent, restoring scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def unaryPowerHeader (exponent dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt dst) (fun _ => tick) .done)) (upow2 exponent dst saved tmp)

theorem unaryPowerHeader_exec_within (body : P → Pr P T Q A U)
    (exponent dst saved tmp : Fin T) (hreg : [exponent,dst,saved,tmp].Nodup)
    (b depth : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hexponent : (S.R exponent).length = b)
    (hblank : S.R dst = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 4*2^b+9*b+5 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(4*2^b+9*b+5)) depth
        (unaryPowerHeader exponent dst saved tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R dst (List.replicate (2^b) tick)}) := by
  have hr := hreg
  regs_ne hr
  let M : Stacks T A := {S with R := Function.update S.R dst [tick]}
  have hp : Exec body (.act (.push (.rt dst) (fun _ => tick) .done)) (mk v S) 1 (mk v M) := by
    simpa [M,Action.run,update_rt,hblank] using
      Exec.act (body := body) (.push (.rt dst) (fun _ => tick) .done) (mk v S)
  obtain ⟨v',n,hu,hn,he⟩ := upow2_exec (body := body)
    (a := exponent) (b := dst) (t₁ := saved) (t₂ := tmp) hreg v M
    (by simpa [M,‹dst ≠ saved›.symm] using hsaved) (by simpa [M,‹dst ≠ tmp›.symm] using htmp)
  have he' : Exec body (unaryPowerHeader exponent dst saved tmp) (mk v S) (1+n)
      (mk v' {S with R := Function.update S.R dst (List.replicate (2^b) tick)}) := by
    simpa [unaryPowerHeader,M,‹exponent ≠ dst›,hexponent] using Exec.seq hp he
  have hn' : 1+n ≤ 4*2^b+9*b+5 := by
    have h : n ≤ 4*2^b+9*b+4 := by simpa [M,‹exponent ≠ dst›,hexponent] using hn
    omega
  have hnative : mnNativePushBound 2 (unaryPowerHeader (P := P) (Q := Q) (A := A) (U := U) exponent dst saved tmp) := by
    simp [unaryPowerHeader,upow2,udbl,scanP,popPush,moveR,moveStep,drainR,popDo,pushN,
      peekR,whileR,mnNativePushBound,mnActPush]
  exact ⟨v',1+n,hu,hn',mn_native_exec_within he' 2 hnative depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Host
