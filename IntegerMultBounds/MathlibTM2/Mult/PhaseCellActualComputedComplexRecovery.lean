module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedPairedRecoveryExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryPairPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySolutionOrder
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryMasterValues

/-! Actual complex halo recovery: computed setup, recovery, pairing and
restoration, with the extra scalar target bit paying complex assembly. -/
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

theorem paired_exec_ofComplexBounds (plan : ComputedRecoveryPlan T) (boundsProgram : RawRecoveryProgramBounds Q A U)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    {p u l target t a b V : ℕ} {α gap : ℝ} {C : ZMod s → GaussianInt}
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := target+1) (rhsExp := 2) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1)
    (W : ℕ) (hW : 2*packedHaloPrecision p l s t u (target+1) 2 a b+8 ≤ W) :
    let d := InverseMasterInput.ofCuts p u l target t a b bounds.hst bounds.has bounds.hbs bounds.hband
    let r := RawRecoveryJob.ofComplexBounds bounds Fs hF W hW
    let q := packedHaloPrecision p l s t u (target+1) 2 a b
    let y := fun F : ZMod s → GaussianInt =>
      GeneratedRecoveryJob.solutionMap bounds (fun i => (2 : GaussianInt)^(q-p-1)*F i)
    let Zs := Fs.map (componentSolution y)
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
    ∃ Gs : List (ZMod s → GaussianInt), Gs.length = Fs.length ∧
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ d.timeCost+recoveryLifecycleTime boundsProgram plan.work r Fs.length+
        preparedPairRecoveryOutputCost r Fs.length+retireRecoveryMastersCost r.problem ∧
      Exec body (plan.complexProgram boundsProgram plan.pairPlacement) (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update
          (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) plan.result
          ((Gs.map (fun D => cstream A r.problem.wordWidth
            (packedInterval r.problem.origin r.problem.span D))).flatten++S.R plan.result))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
        (PhaseCellDiscreteGeometry.haloVertices s r.problem.origin (r.problem.origin+r.problem.span))
        (packedIntervalRead r.problem.precision r.problem.wordWidth r.problem.origin
          (cstream A r.problem.wordWidth (packedInterval r.problem.origin r.problem.span D)++S.R plan.result))
        z (1/(2 : ℝ)^target)) Zs Gs ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result boundsProgram.hR boundsProgram.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
          (d.stock+recoveryLifecycleStock boundsProgram plan.work r Fs.length Cprog+
            8*preparedPairRecoveryOutputCost r Fs.length)) depth
          (plan.complexProgram boundsProgram plan.pairPlacement) (Host.mk v S) steps
          (Host.mk v' {S with R := (Function.update
            (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) plan.result
            ((Gs.map (fun D => cstream A r.problem.wordWidth
              (packedInterval r.problem.origin r.problem.span D))).flatten++S.R plan.result))}) := by
  dsimp only
  intro wl hwl v S hp hWseed hN hvalues hwidth hscalar hmasters hmasterScratch hblank hleft hpayload
    hscratch hclock hsaved hsavedClock
  let d := InverseMasterInput.ofCuts p u l target t a b bounds.hst bounds.has bounds.hbs bounds.hband
  let r := RawRecoveryJob.ofComplexBounds bounds Fs hF W hW
  let q := packedHaloPrecision p l s t u (target+1) 2 a b
  let y := fun F : ZMod s → GaussianInt =>
    GeneratedRecoveryJob.solutionMap bounds (fun i => (2 : GaussianInt)^(q-p-1)*F i)
  obtain ⟨Gs,hGs,v',steps,hu,hn,he,hgood,htrace⟩ := plan.complex_exec boundsProgram plan.pairPlacement
    plan.pairPlacement_injective (plan.pairPlacement_regs hreplicaCount hreplicaSpare)
    plan.pairPlacement_masters plan.pairPlacement_work d r
    (RawRecoveryJob.ofComplexBounds_masterValues bounds Fs hF W hW) Fs rfl
    (Fs.map (componentSolution y)) (List.length_map _)
    (RawRecoveryJob.ofComplexBounds_solutionOrder bounds Fs hF W hW)
    wl hwl v S hp hWseed hN hvalues hwidth hscalar hmasters hmasterScratch hblank hleft hpayload
    hscratch hclock hsaved hsavedClock
  refine ⟨Gs,hGs,v',steps,hu,hn,he,?_,htrace⟩
  have ht : r.target = target+1 := rfl
  simpa only [ht,component_error_bit] using hgood

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
