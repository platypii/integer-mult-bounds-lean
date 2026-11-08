module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedCroppedRecoveryExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedRecoveryPayload
public import IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership

/-! Feed the actually selected target-window RHS to the existing principal
recovery kernel and crop the manuscript's explicit floor-owned J_k rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellRationalArgs IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace ComputedRecoveryPlan
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem selected_target_owned_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (crop : RecoveryCropPlacement plan)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (d : InverseMasterInput s) (r : RawRecoveryJob s)
    (hmastersEq : recoveryMasterValues r.problem = d.masters)
    (L k radius targetOrigin targetSpan : ℕ)
    (hcore : r.problem.origin+radius = cut s r.problem.t L k)
    (hspan : r.problem.span = rows s r.problem.t L k+2*radius)
    (Fs : List (ZMod r.problem.t → GaussianInt))
    (hfields : r.inputFields = complexComponentFields (selectedRhsFields s Fs))
    (hwindow : ∀ j < r.problem.span,
      targetOrigin ≤ nearestNatural s r.problem.t (r.problem.origin+j) ∧
        nearestNatural s r.problem.t (r.problem.origin+j) < targetOrigin+targetSpan)
    (Zs : List (ZMod s → ℂ)) (hlen : Zs.length = Fs.length)
    (htargets : (List.finRange r.problem.Fs.length).reverse.map (fun j => r.solution j.val) = complexComponentTargets Zs)
    (wl : List (Fin (A+4))) (hwl : wl.length = d.B) (v : HS T Q A U) (S : Stacks T A)
    (hp : (S.R plan.precision).length = r.problem.p) (hW : (S.R plan.packet).length = r.W)
    (hN : (S.R plan.replicas).length = Fs.length)
    (hvalues : ∀ i, (S.R (plan.master.parameters i)).length = d.values i)
    (hwidth : S.R (plan.master.scalar .wr) = wl)
    (hscalar : ∀ k : TblR 25, k ≠ .wr → S.R (plan.master.scalar k) = [])
    (hmasters : ∀ i, S.R (plan.master.masters i) = [])
    (hmasterScratch : ∀ k ∈ [plan.master.word,plan.master.saved,plan.master.tmp,plan.master.queue], S.R k = [])
    (hblank : ∀ i, i ≠ 124 → S.R (plan.work i) = []) (hleft : ∀ i, S.L (plan.work i) = [])
    (hpayload : S.R (plan.work 124) = selectedWindowPayload (s := s) A r.W r.problem.origin r.problem.span targetOrigin targetSpan Fs)
    (hscratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = [])
    (hclock : S.R plan.clock = []) (hsaved : S.R plan.saved = []) (hsavedClock : S.R plan.savedClock = [])
    (hoffset : (S.R (crop.reg 3)).length = radius) (hrows : (S.R (crop.reg 4)).length = rows s r.problem.t L k) :
    ∃ Gs : List (ZMod s → GaussianInt), Gs.length = Fs.length ∧
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ d.timeCost+recoveryLifecycleTime b plan.work r Fs.length+preparedPairRecoveryOutputCost r Fs.length+
        generatedRecoveryCropCost r.problem.precision r.problem.origin (r.problem.origin+r.problem.span) radius (rows s r.problem.t L k) Fs.length+
        retireRecoveryMastersCost r.problem ∧
      Exec body (plan.croppedProgram b crop) (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update
          (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) (crop.reg 12)
          ((Gs.reverse.map (fun D => cstream A r.problem.wordWidth
            (packedInterval (cut s r.problem.t L k) (rows s r.problem.t L k) D))).flatten++S.R (crop.reg 12)))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
        (haloVertices s (cut s r.problem.t L k) (cut s r.problem.t L (k+1)))
        (packedIntervalRead r.problem.precision r.problem.wordWidth (cut s r.problem.t L k)
          (cstream A r.problem.wordWidth (packedInterval (cut s r.problem.t L k) (rows s r.problem.t L k) D)++S.R (crop.reg 12)))
        z (1/(2 : ℝ)^r.target+1/(2 : ℝ)^r.target)) Zs.reverse Gs.reverse ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
          (d.stock+recoveryLifecycleStock b plan.work r Fs.length Cprog+8*preparedPairRecoveryOutputCost r Fs.length+
            8*generatedRecoveryCropCost r.problem.precision r.problem.origin (r.problem.origin+r.problem.span) radius (rows s r.problem.t L k) Fs.length))
          depth (plan.croppedProgram b crop) (Host.mk v S) steps
          (Host.mk v' {S with R := (Function.update
            (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) (crop.reg 12)
            ((Gs.reverse.map (fun D => cstream A r.problem.wordWidth
              (packedInterval (cut s r.problem.t L k) (rows s r.problem.t L k) D))).flatten++S.R (crop.reg 12)))}) := by
  have hpart : radius+rows s r.problem.t L k ≤ r.problem.span := by rw [hspan]; omega
  have hend : cut s r.problem.t L k+rows s r.problem.t L k = cut s r.problem.t L (k+1) := by
    have hm := cut_mono s r.problem.t L (show k ≤ k+1 by omega)
    dsimp only [rows]
    omega
  have hinput : S.R (plan.work 124) =
      cstream A r.W ((selectedRhsFields s Fs).map (packedInterval r.problem.origin r.problem.span)).flatten := by
    rw [hpayload,selectedWindowPayload_eq A r.W r.problem.origin r.problem.span targetOrigin targetSpan Fs
      r.problem.span_fit hwindow]
  have hh := plan.cropped_exec (body := body) b crop hreplicaCount hreplicaSpare d r hmastersEq
    (selectedRhsFields s Fs) hfields Zs (by simpa only [selectedRhsFields,List.length_map] using hlen)
    htargets radius (rows s r.problem.t L k) hpart wl hwl v S hp hW
    (by simpa only [selectedRhsFields,List.length_map] using hN) hvalues hwidth hscalar hmasters
    hmasterScratch hblank hleft hinput hscratch hclock hsaved hsavedClock hoffset hrows
  simpa only [hcore,hend,selectedRhsFields,List.length_map] using hh

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
