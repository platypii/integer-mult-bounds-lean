module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedCoreStep
public import IntegerMultBounds.MathlibTM2.Host.ConsumeScan

/-! One fixed counted scan executes computed recovery on ordered core jobs. -/
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

noncomputable def coreTimeCost (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (V : ℕ) (r : PackedNormalizedJob A s) : ℕ :=
  readSupplierEndpointsCost V r.a (r.b-r.a)+((6*(routedPayload r).length+6)+
    (plan.normalizedTimeCost b r+restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W))+
    (2*(r.a+r.b)+5)

noncomputable def coreStock (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (V : ℕ) (r : PackedNormalizedJob A s) (Cprog : ℕ) : ℕ :=
  3*readSupplierEndpointsCost V r.a (r.b-r.a)+(2*(6*(routedPayload r).length+6)+
    (plan.normalizedStock b r Cprog+2*restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W))

def scanSupport (plan : ComputedRecoveryPlan T) (normalize : RecoveryNormalizePlan T)
    (queue : RecoveryParameterQueue normalize) (crop : RecoveryCropPlacement plan)
    (width halo binary endpointWork endpointSaved endpointTmp count saved tmp : Fin T) (k : Fin T) : Prop :=
  plan.localSupport normalize queue crop k ∨
    k ∈ [width,halo,binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp,count,saved,tmp]

theorem coreScan_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (hreg : link.reg = crop.reg)
    (hsupportMaster : ∀ k, normalize.support queue k → ∀ i, plan.master.masters i ≠ k)
    (hsupportPayload : ∀ k, normalize.support queue k → k ≠ plan.work 124)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (jobs : List (PackedNormalizedJob A s)) (wl : List (Fin (A+4)))
    (hwl : ∀ r ∈ jobs, wl.length = r.Bcore)
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
    (hfit : ∀ r ∈ jobs, r.a < 2^V)
    (htime : ∀ r ∈ jobs, plan.coreTimeCost b V r ≤ cost)
    (hstock : ∀ r ∈ jobs, plan.coreStock b V r Cprog ≤ reserve)
    (hpush : mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
        plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (v : HS T Q A U) (S : Stacks T A) (originTail tail : List (Fin (A+4)))
    (hwidth : (S.R width).length = V) (hhalo : ∀ r ∈ jobs, (S.R halo).length = r.b-r.a)
    (hreaderBlank : ∀ k ∈ [binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp], S.R k = [])
    (hready : ∀ r ∈ jobs, plan.LocalReady normalize queue crop r wl
      (plan.routedState r source [] (plan.coreEndpointState r origins [] S)))
    (hblank : ∀ i, S.R (plan.work i) = [])
    (hcount : ∀ r ∈ jobs, (S.R count).length = (routedPayload r).length)
    (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (horigins : S.R origins = jobs.flatMap (fun r => binSyms V r.a)++originTail)
    (hsource : S.R source = jobs.flatMap routedPayload++tail)
    (hloopCount : (S.R loopCount).length = jobs.length) (hloopSaved : S.R loopSaved = []) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ jobs.length*(cost+5)+4 ∧
      List.Forall₂ PackedNormalizedJob.output jobs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+reserve) depth
        (scanP loopCount loopSaved (plan.coreProgram b normalize queue crop link width halo origins binary
          endpointWork endpointSaved endpointTmp count source saved tmp)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
          source tail) plan.result (outputs.reverse.flatten++S.R plan.result))}) := by
  let protectedRegs := plan.scanSupport normalize queue crop width halo binary endpointWork endpointSaved endpointTmp count saved tmp
  let Inv : Stacks T A → Prop := fun F => F.L = S.L ∧ ∀ k, protectedRegs k → F.R k = S.R k
  have hlocal (k : Fin T) (hk : plan.localSupport normalize queue crop k) : protectedRegs k := Or.inl hk
  have hc (k : Fin T) (hk : k ∈ [width,halo,binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp,count,saved,tmp]) : protectedRegs k := Or.inr hk
  have hw (i : Fin 392) : protectedRegs (plan.work i) :=
    hlocal (plan.work i) (Or.inr (Or.inr (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))))))
  have hcounter : ∀ F R, (∀ k, k ≠ loopCount → k ≠ loopSaved → R k = F.R k) → Inv F → Inv {F with R := R} := by
    intro F R hR hF
    exact ⟨hF.1,fun k hk => (hR k (hoff k hk).1 (hoff k hk).2.1).trans (hF.2 k hk)⟩
  have hstep : ∀ F otail rest xs, Inv F → Inv {F with R := (Function.update
      (Function.update (Function.update F.R origins otail) source rest) plan.result (xs++F.R plan.result))} := by
    intro F otail rest xs hF
    refine ⟨hF.1,?_⟩
    intro k hk
    simp only [Function.update_of_ne (hoff k hk).2.2.2.2,Function.update_of_ne (hoff k hk).2.2.2.1,
      Function.update_of_ne (hoff k hk).2.2.1,hF.2 k hk]
  apply consumeScan_exec _ loopCount loopSaved origins source plan.result hloop
    (fun r => binSyms V r.a) routedPayload jobs originTail tail cost reserve depth PackedNormalizedJob.output
    Inv hcounter hstep ?_ v S ⟨rfl,fun _ _ => rfl⟩ horigins hsource hloopCount hloopSaved
  intro r hr w F otail rest hF ho hpayload
  have hreadyF : plan.LocalReady normalize queue crop r wl
      (plan.routedState r source rest (plan.coreEndpointState r origins otail F)) := by
    apply (hready r hr).of_frame
    · intro k hk
      have hs := hoff k (hlocal k hk)
      by_cases hpay : k = plan.work 124
      · subst k; simp only [routedState,Function.update_self]
      · by_cases hb : k = plan.master.parameters 7
        · subst k; simp [routedState,coreEndpointState,hpay,hs.2.2.2.1]
        · by_cases ha : k = plan.master.parameters 6
          · subst k; simp [routedState,coreEndpointState,hpay,hb,hs.2.2.2.1]
          · simp only [routedState,coreEndpointState,Function.update_of_ne hpay,Function.update_of_ne hb,
              Function.update_of_ne ha,Function.update_of_ne hs.2.2.2.1,Function.update_of_ne hs.2.2.1,
              hF.2 k (hlocal k hk)]
    · intro i; exact congrFun hF.1 (plan.work i)
  obtain ⟨word,w',n,houtput,hu,hn,hex,htrace⟩ := plan.core_exec b normalize queue crop link hreg
    hsupportMaster hsupportPayload hreplicaCount hreplicaSpare r wl (hwl r hr) w F
    width halo origins binary endpointWork endpointSaved endpointTmp count source saved tmp
    hreader hports hframe hsourceWork horiginsWork V (hfit r hr) otail rest
    (by rw [hF.2 width (hc width (by simp))]; exact hwidth)
    (by rw [hF.2 halo (hc halo (by simp))]; exact hhalo r hr) ho
    (by intro k hk; rw [hF.2 k (hc k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))]; exact hreaderBlank k hk)
    hreadyF (by intro i; rw [hF.2 _ (hw i)]; exact hblank i) hpayload
    (by rw [hF.2 count (hc count (by simp))]; exact hcount r hr) htakeOff
    (by rw [hF.2 saved (hc saved (by simp))]; exact hsaved)
    (by rw [hF.2 tmp (hc tmp (by simp))]; exact htmp)
    hpacketRows hpacketReplicas hpacketDestination
  have hvolume : word.length ≤ (routedPayload r).length := by
    rw [r.output_length houtput]
    have hfit : r.a+(r.b-r.a) ≤ s := by have := r.bounds.hbs; have := r.bounds.hab; omega
    have hlen : (routedPayload r).length = r.Fs.length*(r.b-r.a)*r.W := by
      simp [routedPayload,length_cstream,List.length_flatten,List.map_map,Function.comp_def,
        packedInterval_length _ hfit,List.sum_replicate,Nat.mul_assoc]
    rw [hlen,PackedNormalizedJob.outputVolume]
    have hcore : coreLength s r.coreWidth r.k ≤ r.b-r.a := by have := r.haloLength; omega
    exact Nat.mul_le_mul_right r.W (Nat.mul_le_mul_left r.Fs.length hcore)
  refine ⟨w',n,word,hu,hn.trans (htime r hr),hvolume,houtput,?_⟩
  exact (htrace Cprog hpush hbody depth).mono (by intro d z hz; have hs := hstock r hr; unfold coreStock at hs; omega)

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
