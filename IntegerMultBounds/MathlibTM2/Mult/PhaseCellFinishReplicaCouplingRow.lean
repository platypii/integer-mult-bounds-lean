module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Retire the staged input field and archive the computed residual in word
order. Both borrowed source suffixes and all scratch tapes are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def finishReplicaCouplingRow (volume field residual dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (discardPrefix volume field saved tmp) (takePrefix volume residual dst saved tmp)

def finishReplicaCouplingRowCost (V : ℕ) := 12*V+12

theorem finishReplicaCouplingRow_exec_within (volume field residual dst saved tmp : Fin T)
    (hreg : [volume,field,residual,dst,saved,tmp].Nodup) (V : ℕ)
    (fieldWords residualWords fieldTail residualTail : List (Fin (A+4)))
    (hfieldLen : fieldWords.length = V) (hresidualLen : residualWords.length = V)
    (v : HS T Q A U) (S : Stacks T A) (hV : (S.R volume).length = V)
    (hfield : S.R field = fieldWords++fieldTail) (hresidual : S.R residual = residualWords++residualTail)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*finishReplicaCouplingRowCost V) depth
        (finishReplicaCouplingRow volume field residual dst saved tmp) (mk v S) (finishReplicaCouplingRowCost V)
        (mk v' {S with R := Function.update (Function.update (Function.update S.R field fieldTail)
          residual residualTail) dst (residualWords++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := discardPrefix_exec (body := body) (count := volume) (src := field)
    (trash := saved) (tmp := tmp) (by regs_nodup) fieldWords fieldTail v S hfield
    (by rw [hV,hfieldLen]) hsaved htmp
  let J : Stacks T A := {S with R := Function.update S.R field fieldTail}
  obtain ⟨v₂,hu₂,he₂⟩ := takePrefix_exec (body := body) (count := volume) (src := residual) (dst := dst)
    (buf := saved) (tmp := tmp) (by regs_nodup) v₁ J residualWords residualTail
    (by simpa [J,‹field ≠ residual›.symm] using hresidual)
    (by simpa [J,‹volume ≠ field›,hresidualLen] using hV)
    (by simpa [J,‹field ≠ saved›.symm] using hsaved)
    (by simpa [J,‹field ≠ tmp›.symm] using htmp)
  have he : Exec body (finishReplicaCouplingRow volume field residual dst saved tmp) (mk v S)
      (finishReplicaCouplingRowCost V) (mk v₂ {S with R := Function.update (Function.update (Function.update S.R field fieldTail) residual residualTail) dst (residualWords++S.R dst)}) := by
    apply (Exec.seq he₁ he₂).cast
    · unfold finishReplicaCouplingRowCost
      rw [hfieldLen,hresidualLen]
      omega
    · apply congrArg (mk v₂)
      simp only [J,Function.update_of_ne ‹field ≠ dst›.symm]
  exact ⟨v₂,hu₂.trans hu₁,mn_native_exec_within he 2 (by
    simp [finishReplicaCouplingRow,discardPrefix,takePrefix,transfer,transferAct,
      scanR,drainR,popDo,keepIn,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]) depth _ (le_refl _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
