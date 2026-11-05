module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Generate affine unary dimensions from a retained unary header. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type}

def affineHeader (c d : ℕ) (src dst tmp : Fin T) : Pr P T Q A U :=
  .seq (umul c src dst tmp) (.act (pushN dst (fun _ => tick) d .done))

theorem affineHeader_exec (body : P → Pr P T Q A U) (c d : ℕ) (src dst tmp : Fin T)
    (hreg : [src,dst,tmp].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (affineHeader c d src dst tmp) (mk v S) (4*(S.R src).length+5)
        (mk v' {S with R := Function.update S.R dst (List.replicate (c*(S.R src).length+d) tick)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v',hu,he⟩ := umul_exec (body := body) c ‹src ≠ dst› ‹src ≠ tmp› ‹dst ≠ tmp› v S htmp
  simp only [hdst,List.append_nil] at he
  let M : Stacks T A := {S with R := Function.update S.R dst (List.replicate (c*(S.R src).length) tick)}
  have hp := Exec.act (body := body) (pushN dst (fun _ => tick) d .done) (mk v' M)
  rw [pushN_run] at hp
  refine ⟨v',hu,(Exec.seq he hp).cast (by omega) ?_⟩
  simp only [M,Action.run,Function.update_self,Function.update_idem,List.replicate_append_replicate]
  rw [Nat.add_comm d]

theorem affineHeader_native (c d : ℕ) (src dst tmp : Fin T) :
    mnNativePushBound (max (c+1) d)
      (affineHeader (P := P) (Q := Q) (A := A) (U := U) c d src dst tmp) := by
  have hpush (n : ℕ) (a : Act T Q A U) :
      mnActPush (pushN dst (fun _ => tick) n a) = mnActPush a+n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pushN,mnActPush,ih,Nat.add_assoc]
  simp [affineHeader,umul,umulSym,scanR,keepIn,drainR,popDo,pushN,popPush,
    moveR,moveStep,whileR,peekR,mnNativePushBound,hpush,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
