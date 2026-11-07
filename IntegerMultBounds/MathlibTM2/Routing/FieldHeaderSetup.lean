module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Reuse retired dimension tapes for the next movement stage. Sources are
retained exactly; destinations are replaced, and scratch is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FieldHeaderSetup
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def resetProduct (a b dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (uclear dst) (unaryProduct a b dst saved tmp)

theorem resetProduct_exec (a b dst saved tmp : Fin T) (hreg : [a,b,dst,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ (2*(S.R dst).length+2)+((S.R a).length*(4*(S.R b).length+9)+4) ∧
      Exec body (resetProduct a b dst saved tmp) (mk v S) n
        (mk vf {S with R := (Function.update S.R dst
          (List.replicate ((S.R a).length*(S.R b).length) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec (body := body) dst v S
  let M : Stacks T A := {S with R := Function.update S.R dst []}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := a) (b := b) (dst := dst) (t₁ := saved) (t₂ := tmp) hreg v₁ M
    (by simp [M,‹dst ≠ saved›.symm,hsaved]) (by simp [M,‹dst ≠ tmp›.symm,htmp])
  refine ⟨v₂,(2*(S.R dst).length+2)+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · simpa only [M,Function.update_of_ne ‹a ≠ dst›,Function.update_of_ne ‹b ≠ dst›] using
      Nat.add_le_add_left hn₂ (2*(S.R dst).length+2)
  · simp [M,‹a ≠ dst›,‹b ≠ dst›]

def resetDyadicWidth (exponent width dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (uclear dst) (.seq (ucopy width dst saved) (upow2 exponent dst saved tmp))

theorem resetDyadicWidth_exec (exponent width dst saved tmp : Fin T)
    (hreg : [exponent,width,dst,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ 2*(S.R dst).length+4*(S.R width).length+
        4*(2^(S.R exponent).length*(S.R width).length)+9*(S.R exponent).length+10 ∧
      Exec body (resetDyadicWidth exponent width dst saved tmp) (mk v S) n
        (mk vf {S with R := (Function.update S.R dst
          (List.replicate (2^(S.R exponent).length*(S.R width).length) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec (body := body) dst v S
  let M : Stacks T A := {S with R := Function.update S.R dst []}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) ‹width ≠ dst› ‹width ≠ saved› ‹dst ≠ saved› v₁ M
    (by simp [M,‹dst ≠ saved›.symm,hsaved])
  let F : Stacks T A := {M with R := Function.update M.R dst (List.replicate (S.R width).length tick)}
  have he₂' : Exec body (ucopy width dst saved) (mk v₁ M) (4*(S.R width).length+4) (mk v₂ F) := by
    simpa only [M,Function.update_of_ne ‹width ≠ dst›,Function.update_self,List.append_nil] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := upow2_exec (body := body)
    (a := exponent) (b := dst) (t₁ := saved) (t₂ := tmp) (by regs_nodup) v₂ F
    (by simp [F,M,‹dst ≠ saved›.symm,hsaved]) (by simp [F,M,‹dst ≠ tmp›.symm,htmp])
  refine ⟨v₃,(2*(S.R dst).length+2)+((4*(S.R width).length+4)+n₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast rfl ?_⟩
  · simp only [F,M,Function.update_of_ne ‹exponent ≠ dst›,Function.update_self,List.length_replicate] at hn₃
    omega
  · simp [F,M,‹exponent ≠ dst›,List.flatMap_replicate, Nat.mul_comm]

theorem resetProduct_pushBound (a b dst saved tmp : Fin T) :
    mnNativePushBound 2 (resetProduct (P := P) (Q := Q) (A := A) (U := U) a b dst saved tmp) := by
  simp [resetProduct,unaryProduct,uclear,scanP,popPush,ucopy,umulSym,scanR,keepIn,pushN,
    drainR,popDo,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem resetDyadicWidth_pushBound (exponent width dst saved tmp : Fin T) :
    mnNativePushBound 2 (resetDyadicWidth (P := P) (Q := Q) (A := A) (U := U) exponent width dst saved tmp) := by
  simp [resetDyadicWidth,uclear,ucopy,umulSym,upow2,scanP,popPush,udbl,scanR,keepIn,pushN,
    drainR,popDo,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Routing.FieldHeaderSetup
