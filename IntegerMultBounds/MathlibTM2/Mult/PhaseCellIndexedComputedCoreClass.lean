module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedCoreClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreJobQueues

/-! Core-gather geometry supplies the actual origin/payload queues and counts
for the complete computed movement-class execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
namespace ComputedRecoveryPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem indexedClassRun_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (hreg : link.reg = crop.reg)
    (hsupportMaster : ∀ k, normalize.support queue k → ∀ i, plan.master.masters i ≠ k)
    (hsupportPayload : ∀ k, normalize.support queue k → k ≠ plan.work 124)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (coreWidth radius H W : ℕ) (Fs : List (ZMod s → GaussianInt))
    (jobs : Fin (coreGatherIndices s coreWidth radius H).length → PackedNormalizedJob A s)
    (hjobWidth : ∀ i, (jobs i).coreWidth = coreWidth) (hjobRadius : ∀ i, (jobs i).radius = radius)
    (hjobIndex : ∀ i, (jobs i).k = (coreGatherIndices s coreWidth radius H)[i.val])
    (hjobWord : ∀ i, (jobs i).W = W) (hjobFields : ∀ i, (jobs i).Fs = Fs)
    (wl : List (Fin (A+4)))
    (hwl : ∀ r ∈ List.ofFn jobs, wl.length = r.Bcore)
    (width halo origins binary endpointWork endpointSaved endpointTmp count source saved tmp loopCount loopSaved : Fin T)
    (hreader : [width,halo,origins,binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp].Nodup)
    (hports : [count,source,plan.work 124,saved,tmp].Nodup)
    (hframe : [origins,plan.master.parameters 6,plan.master.parameters 7,source,plan.result].Nodup)
    (hloop : [loopCount,loopSaved,origins,source,plan.result].Nodup)
    (hoff : ∀ k, plan.scanSupport normalize queue crop width halo binary endpointWork endpointSaved endpointTmp count saved tmp k →
      k ≠ loopCount ∧ k ≠ loopSaved ∧ k ≠ origins ∧ k ≠ source ∧ k ≠ plan.result)
    (hsourceWork : ∀ i, source ≠ plan.work i) (horiginsWork : ∀ i, origins ≠ plan.work i)
    (htakeOff : ∀ k ∈ [count,saved,tmp], k ≠ origins ∧ k ≠ plan.master.parameters 6 ∧ k ≠ plan.master.parameters 7)
    (hpacketRows : plan.packet ≠ crop.reg 4) (hpacketReplicas : plan.packet ≠ plan.replicas)
    (hpacketDestination : plan.packet ≠ crop.reg 12)
    (V Cprog cost reserve depth : ℕ)
    (htime : ∀ r ∈ List.ofFn jobs, plan.coreTimeCost b V r ≤ cost)
    (hstock : ∀ r ∈ List.ofFn jobs, plan.coreStock b V r Cprog ≤ reserve)
    (hpush : mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
        plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (e : Fin 117 → Fin T) (he : Function.Injective e) (heOrigin : origins = e 109) (heLoop : loopCount = e 116)
    (symbols prepSaved prepTmp : Fin T)
    (hprepReg : [plan.replicas,halo,plan.packet,symbols,count,prepSaved,prepTmp].Nodup)
    (hprepOff : ∀ k ∈ [plan.replicas,halo,plan.packet,symbols,count,prepSaved,prepTmp], k ≠ e 109 ∧ k ≠ e 116)
    (hmain : [e 109,e 116,count,source,plan.result].Nodup)
    (hcountLocal : ¬ plan.localSupport normalize queue crop count)
    (hinitialOff : ∀ k ∈ [width,halo,binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp,saved,tmp,loopSaved], k ≠ e 109 ∧ k ≠ e 116 ∧ k ≠ count)
    (hcoreWidth : 0 < coreWidth) (hwide : s+coreWidth+2*radius < 2^V)
    (hHfit : H < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V coreWidth)
    (hr : S.R (e 34) = binSyms V radius) (hH : S.R (e 35) = binSyms V H) (hz : S.R (e 36) = [])
    (htable : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hN : (S.R plan.replicas).length = Fs.length) (hhalo : (S.R halo).length = H) (hW : (S.R plan.packet).length = W)
    (hprepBlank : ∀ k ∈ [symbols,count,prepSaved,prepTmp], S.R k = [])
    (hwidth : (S.R width).length = V)
    (hreaderBlank : ∀ k ∈ [binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp], S.R k = [])
    (hready : ∀ r ∈ List.ofFn jobs, plan.LocalReady normalize queue crop r wl
      (plan.routedState r source [] (plan.coreEndpointState r origins [] S)))
    (hblank : ∀ i, S.R (plan.work i) = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hsource : S.R source = coreSupplierStream A coreWidth radius H W Fs++tail) (hloopSaved : S.R loopSaved = []) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (preparedCoreOriginsCost V s coreWidth radius H+recoveryPayloadCountCost Fs.length H W)+
        ((List.ofFn jobs).length*(cost+5)+4)+(2*((List.ofFn jobs).length+Fs.length*(H*W))+5) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((3*preparedCoreOriginsCost V s coreWidth radius H+2*recoveryPayloadCountCost Fs.length H W)+reserve)) depth
        (plan.classRun b normalize queue crop link e symbols prepSaved prepTmp width halo binary endpointWork
          endpointSaved endpointTmp count source saved tmp loopSaved) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) plan.result
          (outputs.reverse.flatten++S.R plan.result))}) := by
  have hlength (i : Fin (coreGatherIndices s coreWidth radius H).length) : (jobs i).b-(jobs i).a = H := by
    have hg := (coreGatherIndices_spec s coreWidth radius H (jobs i).k (by
      rw [hjobIndex i]; exact List.getElem_mem i.isLt)).2.2
    have hh := (jobs i).haloLength
    rw [hjobWidth i,hjobRadius i] at hh
    exact hh.trans hg
  have horigin := coreJobs_origins coreWidth radius H V jobs hjobWidth hjobRadius hjobIndex
  have hpayload := coreJobs_payloads coreWidth radius H W Fs jobs hjobWidth hjobRadius hjobIndex hjobWord hjobFields
  have hvolume := coreJobs_payload_length coreWidth radius H W Fs jobs hjobWidth hjobRadius hjobIndex hjobWord hjobFields
  have hpay : (routedPayload (A := A) (s := s)) = PackedNormalizedJob.inputPayload := rfl
  have hsource' : S.R source = (List.ofFn jobs).flatMap routedPayload++tail := by
    simpa only [hpay] using hsource.trans (congrArg (fun xs => xs++tail) hpayload.symm)
  apply plan.classRun_exec b normalize queue crop link hreg hsupportMaster hsupportPayload
    hreplicaCount hreplicaSpare (List.ofFn jobs) wl hwl width halo origins binary endpointWork endpointSaved endpointTmp
    count source saved tmp loopCount loopSaved hreader hports hframe hloop hoff hsourceWork horiginsWork
    htakeOff hpacketRows hpacketReplicas hpacketDestination V Cprog cost reserve depth
    (by intro r hr; have := r.bounds.hab; have := r.bounds.hbs; omega)
    htime hstock hpush hbody e he heOrigin heLoop symbols prepSaved prepTmp hprepReg hprepOff hmain hcountLocal hinitialOff
    coreWidth radius H Fs.length W hcoreWidth hwide hHfit hA hV (List.length_ofFn) horigin
    (by
      intro r hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      simpa only [routedPayload,PackedNormalizedJob.inputPayload,Nat.mul_assoc] using hvolume i)
    v S tail h37 hs hw hr hH hz htable h104 h106 h116 hN hhalo hW hprepBlank hwidth
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact (hlength i).symm)
    hreaderBlank hready hblank hsaved htmp hsource' hloopSaved

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
