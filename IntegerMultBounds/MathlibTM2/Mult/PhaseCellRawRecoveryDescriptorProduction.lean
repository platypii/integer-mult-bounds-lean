module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexRecoveryDescriptor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJob

/-! Connect physical complex-input production to the raw job's exact descriptor
ABI. Replica cardinality follows from the job's normalization relation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem RawRecoveryJob.produceDescriptor_exec (r : RawRecoveryJob s) (hA : 4 ≤ A)
    (Fs : List (ZMod s → GaussianInt)) (hfields : r.inputFields = complexComponentFields Fs)
    (work : Fin 392 → Fin T) (hwork : Function.Injective work)
    (dst tmp saved clock : Fin T) (hreg : [dst,tmp,saved,clock].Nodup)
    (hsep : ∀ i, work i ∉ [dst,tmp,saved,clock])
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : embStk work S = complexRecoveryInput r.problem r.W Fs S.inp S.out)
    (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    let tape := descriptorBankTape (placedDescriptorFields work (r.words (A := A)))
    let budget := prepareComplexRecoveryInputCost r.problem.span r.W Fs.length+13*tape.length+3
    ∃ v' steps, v'.user = v.user ∧ steps ≤ budget ∧
      Exec body (complexRecoveryDescriptor work dst tmp saved clock) (Host.mk v S) steps
        (Host.mk v' (serializedOwnedDescriptorState work dst clock tape S)) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*budget) depth
        (complexRecoveryDescriptor work dst tmp saved clock) (Host.mk v S) steps
        (Host.mk v' (serializedOwnedDescriptorState work dst clock tape S)) := by
  have hN : r.problem.Fs.length = 2*Fs.length := by
    rw [r.fields,recoveryInputFields_length,hfields,complexComponentFields_length]
  simpa only [RawRecoveryJob.words,hfields] using complexRecoveryDescriptor_exec (body := body)
    hA r.problem r.W Fs hN work hwork dst tmp saved clock hreg hsep v S hinput htmp hsaved

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
