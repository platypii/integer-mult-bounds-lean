module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddingCounterSetup

/-! Both counters for grouped padding are generated from three retained dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def gatherCounterSetup (rows capacity width rowSymbols padSymbols missing saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows width rowSymbols saved tmp)
    (paddingCounterSetup rows capacity width padSymbols missing saved tmp)

def gatherCounterSetupCost (rows capacity width : ℕ) : ℕ :=
  rows*(4*width+9)+4 + paddingCounterSetupCost rows capacity width

theorem gatherCounterSetupCost_le {rows capacity width : ℕ} (hfit : rows ≤ capacity) :
    gatherCounterSetupCost rows capacity width ≤ capacity*(4*width+17)+18 := by
  have hsplit := Nat.sub_add_cancel hfit
  unfold gatherCounterSetupCost paddingCounterSetupCost
  nlinarith only [hsplit,Nat.mul_le_mul_right (4*width) hfit]

theorem gatherCounterSetup_native (rows capacity width rowSymbols padSymbols missing saved tmp : Fin T) :
    mnNativePushBound 2 (gatherCounterSetup (P := P) (Q := Q) (A := A) (U := U)
      rows capacity width rowSymbols padSymbols missing saved tmp) := by
  refine ⟨?_,paddingCounterSetup_native _ _ _ _ _ _ _⟩
  simp [unaryProduct,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,popPush,mnNativePushBound,mnActPush]

theorem gatherCounterSetup_exec (rows capacity width rowSymbols padSymbols missing saved tmp : Fin T)
    (hreg : [rows,capacity,width,rowSymbols,padSymbols,missing,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hrow : S.R rowSymbols = []) (hpad : S.R padSymbols = []) (hmissing : S.R missing = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ gatherCounterSetupCost (S.R rows).length (S.R capacity).length (S.R width).length ∧
      Exec body (gatherCounterSetup rows capacity width rowSymbols padSymbols missing saved tmp)
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update
          (Function.update S.R rowSymbols (List.replicate ((S.R rows).length*(S.R width).length) tick))
          padSymbols (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := rows) (b := width) (dst := rowSymbols) (t₁ := saved) (t₂ := tmp)
    (by regs_nodup) v S hsaved htmp
  let M : Stacks T A := {S with R := (Function.update S.R rowSymbols
    (List.replicate ((S.R rows).length*(S.R width).length) tick))}
  have he₁' : Exec body (unaryProduct rows width rowSymbols saved tmp) (Host.mk v S) n₁
      (Host.mk v₁ M) := by simpa only [hrow,List.append_nil] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := paddingCounterSetup_exec rows capacity width padSymbols missing saved tmp
    (by regs_nodup) v₁ M
    (by simp [M,hpad,‹rowSymbols ≠ padSymbols›.symm])
    (by simp [M,hmissing,‹rowSymbols ≠ missing›.symm])
    (by simp [M,hsaved,‹rowSymbols ≠ saved›.symm])
    (by simp [M,htmp,‹rowSymbols ≠ tmp›.symm])
  have hcost : n₂ ≤ paddingCounterSetupCost (S.R rows).length (S.R capacity).length (S.R width).length := by
    simpa [paddingCounterSetupCost,M,‹rows ≠ rowSymbols›,‹capacity ≠ rowSymbols›,‹width ≠ rowSymbols›] using hn₂
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,?_⟩
  · unfold gatherCounterSetupCost
    exact Nat.add_le_add hn₁ hcost
  · simpa [gatherCounterSetup,M,‹rows ≠ rowSymbols›,‹capacity ≠ rowSymbols›,‹width ≠ rowSymbols›]
      using Exec.seq he₁' he₂

theorem gatherCounterSetup_exec_within (rows capacity width rowSymbols padSymbols missing saved tmp : Fin T)
    (hreg : [rows,capacity,width,rowSymbols,padSymbols,missing,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hrow : S.R rowSymbols = []) (hpad : S.R padSymbols = []) (hmissing : S.R missing = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ gatherCounterSetupCost (S.R rows).length (S.R capacity).length (S.R width).length ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        2*gatherCounterSetupCost (S.R rows).length (S.R capacity).length (S.R width).length)
        depth (gatherCounterSetup rows capacity width rowSymbols padSymbols missing saved tmp)
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update
          (Function.update S.R rowSymbols (List.replicate ((S.R rows).length*(S.R width).length) tick))
          padSymbols (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := gatherCounterSetup_exec rows capacity width rowSymbols padSymbols missing saved tmp
    hreg v S hrow hpad hmissing hsaved htmp
  exact ⟨v',n,hu,hn,mn_native_exec_within he 2 (gatherCounterSetup_native _ _ _ _ _ _ _ _) depth _ (by omega)⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
