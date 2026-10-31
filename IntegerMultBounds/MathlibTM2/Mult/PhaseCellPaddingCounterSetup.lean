module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Generate a padding-symbol counter from retained row and block dimensions.
The subtraction workspace is retired before returning to the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def paddingCounterSetup (rows capacity width padding missing saved tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy capacity missing saved)
    (.seq (usub rows missing tmp)
      (.seq (unaryProduct missing width padding saved tmp) (uclear missing)))

/-- Setup is linear in the generated word and the retained row dimensions. -/
def paddingCounterSetupCost (rows capacity width : ℕ) : ℕ :=
  4*capacity+4 + (4*rows+4) + ((capacity-rows)*(4*width+9)+4) +
    (2*(capacity-rows)+2)

/-- For a fitting class, setup has a linear bill in the padded row width. -/
theorem paddingCounterSetupCost_le {rows capacity width : ℕ} (hfit : rows ≤ capacity) :
    paddingCounterSetupCost rows capacity width ≤ capacity*(4*width+17)+18 := by
  have hsplit : capacity-rows+rows = capacity := Nat.sub_add_cancel hfit
  unfold paddingCounterSetupCost
  nlinarith only [hsplit,Nat.zero_le ((capacity-rows)*width),Nat.zero_le (rows*width),
    Nat.mul_le_mul_right (4*width) hfit]

theorem paddingCounterSetup_native (rows capacity width padding missing saved tmp : Fin T) :
    mnNativePushBound 2 (paddingCounterSetup (P := P) (Q := Q) (A := A) (U := U)
      rows capacity width padding missing saved tmp) := by
  simp [paddingCounterSetup,unaryProduct,ucopy,usub,uclear,umulSym,scanP,scanR,
    drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,dropTop,popPush,
    mnNativePushBound,mnActPush]

theorem paddingCounterSetup_exec (rows capacity width padding missing saved tmp : Fin T)
    (hreg : [rows,capacity,width,padding,missing,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hpadding : S.R padding = []) (hmissing : S.R missing = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 4*(S.R capacity).length+4 + (4*(S.R rows).length+4) +
        (((S.R capacity).length-(S.R rows).length)*(4*(S.R width).length+9)+4) +
        (2*((S.R capacity).length-(S.R rows).length)+2) ∧
      Exec body (paddingCounterSetup rows capacity width padding missing saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R padding
          (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body ‹capacity ≠ missing› ‹capacity ≠ saved› ‹missing ≠ saved› v S hsaved
  let S₁ : Stacks T A := {S with R := (Function.update S.R missing
    (List.replicate (S.R capacity).length tick))}
  have he₁' : Exec body (ucopy capacity missing saved) (Host.mk v S)
      (4*(S.R capacity).length+4) (Host.mk v₁ S₁) := by
    simpa only [hmissing,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec body ‹rows ≠ missing› ‹rows ≠ tmp› ‹missing ≠ tmp› v₁ S₁
    (by simp [S₁,htmp,‹missing ≠ tmp›.symm])
  let S₂ : Stacks T A := {S with R := (Function.update S.R missing
    (List.replicate ((S.R capacity).length-(S.R rows).length) tick))}
  have he₂' : Exec body (usub rows missing tmp) (Host.mk v₁ S₁)
      (4*(S.R rows).length+4) (Host.mk v₂ S₂) := by
    simpa [S₁,S₂,‹rows ≠ missing›] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := unaryProduct_exec (body := body)
    (a := missing) (b := width) (dst := padding) (t₁ := saved) (t₂ := tmp)
    (by regs_nodup) v₂ S₂
    (by simp [S₂,hsaved,‹missing ≠ saved›.symm])
    (by simp [S₂,htmp,‹missing ≠ tmp›.symm])
  let S₃ : Stacks T A := {S₂ with R := (Function.update S₂.R padding
    (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))}
  have he₃' : Exec body (unaryProduct missing width padding saved tmp)
      (Host.mk v₂ S₂) n₃ (Host.mk v₃ S₃) := by
    simpa [S₂,S₃,‹width ≠ missing›,‹padding ≠ missing›,hpadding] using he₃
  have hn₃' : n₃ ≤ ((S.R capacity).length-(S.R rows).length)*(4*(S.R width).length+9)+4 := by
    simpa [S₂,‹width ≠ missing›] using hn₃
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) missing v₃ S₃
  have he₄' : Exec body (uclear missing) (Host.mk v₃ S₃)
      (2*((S.R capacity).length-(S.R rows).length)+2)
      (Host.mk v₄ {S with R := (Function.update S.R padding
        (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))}) := by
    have hend : {S₃ with R := Function.update S₃.R missing []} =
        {S with R := (Function.update S.R padding
          (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))} := by
      congr 1
      funext k
      by_cases hk : k = missing
      · subst k
        simp [S₃,S₂,‹padding ≠ missing›.symm,hmissing]
      · by_cases hp : k = padding <;> simp [S₃,S₂,hk,hp,‹padding ≠ missing›]
    rw [hend] at he₄
    simpa [S₃,S₂,‹padding ≠ missing›.symm] using he₄
  refine ⟨v₄,_,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄'))⟩
  · omega
/-- The actual setup trace fits one reserve, including subtraction cleanup. -/
theorem paddingCounterSetup_exec_within (rows capacity width padding missing saved tmp : Fin T)
    (hreg : [rows,capacity,width,padding,missing,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hpadding : S.R padding = []) (hmissing : S.R missing = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ paddingCounterSetupCost (S.R rows).length (S.R capacity).length (S.R width).length ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        2*paddingCounterSetupCost (S.R rows).length (S.R capacity).length (S.R width).length)
        depth (paddingCounterSetup rows capacity width padding missing saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R padding
          (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := paddingCounterSetup_exec rows capacity width padding missing saved tmp
    hreg v S hpadding hmissing hsaved htmp
  change n ≤ paddingCounterSetupCost _ _ _ at hn
  refine ⟨v',n,hu,hn,?_⟩
  exact mn_native_exec_within he 2 (paddingCounterSetup_native _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
