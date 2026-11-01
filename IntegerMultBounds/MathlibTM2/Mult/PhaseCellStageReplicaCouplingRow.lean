module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Stage matching owned output/RHS row prefixes into the coupling bank. The
retained symbol-volume header serves both transfers; scratch is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def stageReplicaCouplingRow (volume output rhs fieldDst rhsDst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takePrefix volume output fieldDst saved tmp) (takePrefix volume rhs rhsDst saved tmp)

def stageReplicaCouplingRowCost (V : ℕ) := 12*V+12

theorem stageReplicaCouplingRow_exec_within (volume output rhs fieldDst rhsDst saved tmp : Fin T)
    (hreg : [volume,output,rhs,fieldDst,rhsDst,saved,tmp].Nodup)
    (V : ℕ) (fieldWords rhsWords fieldTail rhsTail : List (Fin (A+4)))
    (hfieldLen : fieldWords.length = V) (hrhsLen : rhsWords.length = V)
    (v : HS T Q A U) (S : Stacks T A)
    (hV : (S.R volume).length = V) (hfield : S.R output = fieldWords++fieldTail)
    (hrhs : S.R rhs = rhsWords++rhsTail) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*stageReplicaCouplingRowCost V) depth
        (stageReplicaCouplingRow volume output rhs fieldDst rhsDst saved tmp) (mk v S) (stageReplicaCouplingRowCost V)
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R output fieldTail)
          fieldDst (fieldWords++S.R fieldDst)) rhs rhsTail) rhsDst (rhsWords++S.R rhsDst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body) (count := volume) (src := output) (dst := fieldDst)
    (buf := saved) (tmp := tmp) (by regs_nodup) v S fieldWords fieldTail hfield
    (by rw [hV,hfieldLen]) hsaved htmp
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R output fieldTail)
    fieldDst (fieldWords++S.R fieldDst))}
  obtain ⟨v₂,hu₂,he₂⟩ := takePrefix_exec (body := body) (count := volume) (src := rhs) (dst := rhsDst)
    (buf := saved) (tmp := tmp) (by regs_nodup) v₁ M rhsWords rhsTail
    (by simpa [M,‹rhs ≠ fieldDst›,‹output ≠ rhs›.symm] using hrhs)
    (by simpa [M,‹volume ≠ fieldDst›,‹volume ≠ output›,hrhsLen] using hV)
    (by simpa [M,‹fieldDst ≠ saved›.symm,‹output ≠ saved›.symm] using hsaved)
    (by simpa [M,‹fieldDst ≠ tmp›.symm,‹output ≠ tmp›.symm] using htmp)
  have he : Exec body (stageReplicaCouplingRow volume output rhs fieldDst rhsDst saved tmp)
      (mk v S) (stageReplicaCouplingRowCost V)
      (mk v₂ {S with R := (Function.update (Function.update (Function.update (Function.update S.R output fieldTail)
        fieldDst (fieldWords++S.R fieldDst)) rhs rhsTail) rhsDst (rhsWords++S.R rhsDst))}) := by
    apply (Exec.seq he₁ he₂).cast
    · unfold stageReplicaCouplingRowCost; rw [hfieldLen,hrhsLen]; omega
    · apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      simp [M,‹fieldDst ≠ rhsDst›.symm,‹output ≠ rhsDst›.symm]
  refine ⟨v₂,hu₂.trans hu₁,mn_native_exec_within he 2 ?_ depth _ (le_refl _)⟩
  simp [stageReplicaCouplingRow,takePrefix,transfer,transferAct,scanR,drainR,popDo,keepIn,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
