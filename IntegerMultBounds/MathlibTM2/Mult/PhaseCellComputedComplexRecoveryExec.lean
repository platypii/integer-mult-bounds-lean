module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedRecoveryExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryMasterValues

/-! The computed recovery call specialized to actual complex halo jobs.
All scalar sizing and master identities follow from ordinary geometric bounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace ComputedRecoveryPlan
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

/-- Actual halo bounds supply the computed call's scalar input and numerical
master identity. The executed program is still independent of the job. -/
theorem exec_ofComplexBounds (plan : ComputedRecoveryPlan T) (boundsProgram : RawRecoveryProgramBounds Q A U)
    {p u l target t a b V : ℕ} {α gap : ℝ} {C : ZMod s → GaussianInt}
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := target+1) (rhsExp := 2) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1)
    (W : ℕ) (hW : 2*packedHaloPrecision p l s t u (target+1) 2 a b+8 ≤ W) :
    let d := InverseMasterInput.ofCuts p u l target t a b bounds.hst bounds.has bounds.hbs bounds.hband
    let r := RawRecoveryJob.ofComplexBounds bounds Fs hF W hW
    ∀
    (wl : List (Fin (A+4))) (_ : wl.length = d.B) (v : HS T Q A U) (S : Stacks T A)
    (_ : (S.R plan.precision).length = r.problem.p) (_ : (S.R plan.packet).length = r.W)
    (_ : (S.R plan.replicas).length = Fs.length)
    (_ : ∀ i, (S.R (plan.master.parameters i)).length = d.values i)
    (_ : S.R (plan.master.scalar .wr) = wl)
    (_ : ∀ k : TblR 25, k ≠ .wr → S.R (plan.master.scalar k) = [])
    (_ : ∀ i, S.R (plan.master.masters i) = [])
    (_ : ∀ k ∈ [plan.master.word,plan.master.saved,plan.master.tmp,plan.master.queue], S.R k = [])
    (_ : ∀ i, i ≠ 124 → S.R (plan.work i) = []) (_ : ∀ i, S.L (plan.work i) = [])
    (_ : S.R (plan.work 124) = cstream A r.W (Fs.map (packedInterval r.problem.origin r.problem.span)).flatten)
    (_ : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = [])
    (_ : S.R plan.clock = []) (_ : S.R plan.saved = []) (_ : S.R plan.savedClock = []),
    ∃ v' steps outputs, v'.user = v.user ∧
      steps ≤ d.timeCost+recoveryLifecycleTime boundsProgram plan.work r Fs.length+retireRecoveryMastersCost r.problem ∧
      List.Forall₂ RawRecoveryJob.output [r] outputs ∧
      Exec body (plan.program boundsProgram) (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update
          (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) plan.result (outputs.reverse.flatten++S.R plan.result))}) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result boundsProgram.hR boundsProgram.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
          (d.stock+recoveryLifecycleStock boundsProgram plan.work r Fs.length Cprog)) depth
          (plan.program boundsProgram) (Host.mk v S) steps
          (Host.mk v' {S with R := (Function.update
            (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) plan.result (outputs.reverse.flatten++S.R plan.result))}) := by
  dsimp only
  intro wl hwl v S hp hWseed hN hvalues hwidth hscalar hmasters hmasterScratch hblank hleft hpayload
    hscratch hclock hsaved hsavedClock
  exact plan.exec boundsProgram
    (InverseMasterInput.ofCuts p u l target t a b bounds.hst bounds.has bounds.hbs bounds.hband)
    (RawRecoveryJob.ofComplexBounds bounds Fs hF W hW)
    (RawRecoveryJob.ofComplexBounds_masterValues bounds Fs hF W hW) Fs rfl
    wl hwl v S hp hWseed hN hvalues hwidth hscalar hmasters hmasterScratch hblank hleft hpayload
    hscratch hclock hsaved hsavedClock

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
