module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedCoreScan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareComputedCoreClass

/-! Generate class controls, run computed recovery, and retire restored counts. -/
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

def classPreparedState (e : Fin 117 → Fin T) (count : Fin T)
    (V s width radius H N W : ℕ) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update S.R (e 109)
    ((coreGatherIndices s width radius H).flatMap (fun k => binSyms V (coreStart width k-radius))++S.R (e 109)))
    (e 116) (List.replicate (coreGatherIndices s width radius H).length tick)) count (List.replicate (N*(H*W)) tick))}

noncomputable def classRun (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (e : Fin 117 → Fin T) (symbols prepSaved prepTmp width halo binary endpointWork endpointSaved endpointTmp
      count source saved tmp loopSaved : Fin T) : Pr P T Q A U :=
  .seq (prepareComputedCoreClass e plan.replicas halo plan.packet symbols count prepSaved prepTmp)
    (.seq (scanP (e 116) loopSaved (plan.coreProgram b normalize queue crop link width halo (e 109) binary
      endpointWork endpointSaved endpointTmp count source saved tmp)) (clearWords [e 116,count]))

private theorem classControls_frame (origins clock count source result : Fin T)
    (hreg : [origins,clock,count,source,result].Nodup) (S : Stacks T A)
    (originWords xs tail : List (Fin (A+4))) (m n : ℕ)
    (hclock : S.R clock = []) (hcount : S.R count = []) :
    let F : Stacks T A := {S with R := (Function.update (Function.update (Function.update S.R origins originWords)
      clock (List.replicate m tick)) count (List.replicate n tick))}
    let G : Stacks T A := {F with R := (Function.update (Function.update (Function.update F.R origins (S.R origins))
      source tail) result (xs++F.R result))}
    ((G.R clock).length = m ∧ (G.R count).length = n) ∧
      {G with R := (fun k => if k ∈ [clock,count] then [] else G.R k)} =
        {S with R := (Function.update (Function.update S.R source tail) result (xs++S.R result))} := by
  regs_ne hreg
  dsimp only
  refine ⟨⟨?_,?_⟩,?_⟩
  · simp_all [ne_comm]
  · simp_all [ne_comm]
  · refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hl : k = clock
    · subst k; simp_all
    · by_cases hc : k = count
      · subst k; simp_all [ne_comm]
      · by_cases hr : k = result
        · subst k; simp_all [ne_comm]
        · by_cases hs : k = source
          · subst k; simp_all [ne_comm]
          · by_cases ho : k = origins
            · subst k; simp_all [ne_comm]
            · simp_all [ne_comm]

theorem classRun_sum_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
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
    (V Cprog reserve depth : ℕ)
    (hfit : ∀ r ∈ jobs, r.a < 2^V)
    (hstock : ∀ r ∈ jobs, plan.coreStock b V r Cprog ≤ reserve)
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
    (coreWidth radius H N W : ℕ) (hcoreWidth : 0 < coreWidth) (hwide : s+coreWidth+2*radius < 2^V)
    (hHfit : H < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (hlen : jobs.length = (coreGatherIndices s coreWidth radius H).length)
    (horiginJobs : jobs.flatMap (fun r => binSyms (A := A) V r.a) =
      (coreGatherIndices s coreWidth radius H).flatMap (fun k => binSyms V (coreStart coreWidth k-radius)))
    (hvolume : ∀ r ∈ jobs, (routedPayload r).length = N*(H*W))
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V coreWidth)
    (hr : S.R (e 34) = binSyms V radius) (hH : S.R (e 35) = binSyms V H) (hz : S.R (e 36) = [])
    (htable : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hN : (S.R plan.replicas).length = N) (hhalo : (S.R halo).length = H) (hW : (S.R plan.packet).length = W)
    (hprepBlank : ∀ k ∈ [symbols,count,prepSaved,prepTmp], S.R k = [])
    (hwidth : (S.R width).length = V) (hjobHalo : ∀ r ∈ jobs, H = r.b-r.a)
    (hreaderBlank : ∀ k ∈ [binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp], S.R k = [])
    (hready : ∀ r ∈ jobs, plan.LocalReady normalize queue crop r wl
      (plan.routedState r source [] (plan.coreEndpointState r origins [] S)))
    (hblank : ∀ i, S.R (plan.work i) = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hsource : S.R source = jobs.flatMap routedPayload++tail) (hloopSaved : S.R loopSaved = []) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (preparedCoreOriginsCost V s coreWidth radius H+recoveryPayloadCountCost N H W)+
        ((jobs.map (plan.coreTimeCost b V)).sum+5*jobs.length+4)+(2*(jobs.length+N*(H*W))+5) ∧
      List.Forall₂ PackedNormalizedJob.output jobs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((3*preparedCoreOriginsCost V s coreWidth radius H+2*recoveryPayloadCountCost N H W)+reserve)) depth
        (plan.classRun b normalize queue crop link e symbols prepSaved prepTmp width halo binary endpointWork
          endpointSaved endpointTmp count source saved tmp loopSaved) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) plan.result
          (outputs.reverse.flatten++S.R plan.result))}) := by
  subst origins; subst loopCount
  have hmain' := hmain
  regs_ne hmain'
  let F := classPreparedState e count V s coreWidth radius H N W S
  have hF (k : Fin T) (ho : k ≠ e 109) (hl : k ≠ e 116) (hc : k ≠ count) : F.R k = S.R k := by
    simp only [F,classPreparedState,Function.update_of_ne hc,Function.update_of_ne hl,Function.update_of_ne ho]
  have hlocalFrame (k : Fin T) (hk : plan.localSupport normalize queue crop k) : F.R k = S.R k := by
    have ho := hoff k (Or.inl hk)
    exact hF k ho.2.2.1 ho.1 (by intro hi; subst k; exact hcountLocal hk)
  have hcontrolFrame (k : Fin T) (hk : k ∈ [width,halo,binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp,saved,tmp,loopSaved]) : F.R k = S.R k :=
    hF k (hinitialOff k hk).1 (hinitialOff k hk).2.1 (hinitialOff k hk).2.2
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareComputedCoreClass_exec (body := body) e he
    plan.replicas halo plan.packet symbols count prepSaved prepTmp hprepReg hprepOff
    V s coreWidth radius H N W hcoreWidth hwide hHfit hA hV v S h37 hs hw hr hH hz htable h104 h106 h116
    hN hhalo hW hprepBlank depth
  have hreadyF (r : PackedNormalizedJob A s) (hr : r ∈ jobs) : plan.LocalReady normalize queue crop r wl
      (plan.routedState r source [] (plan.coreEndpointState r (e 109) [] F)) := by
    apply (hready r hr).of_frame
    · intro k hk
      have hs := hoff k (Or.inl hk)
      by_cases hpay : k = plan.work 124
      · subst k; simp only [routedState,Function.update_self]
      · by_cases hb : k = plan.master.parameters 7
        · subst k; simp [routedState,coreEndpointState,hpay,hs.2.2.2.1]
        · by_cases ha : k = plan.master.parameters 6
          · subst k; simp [routedState,coreEndpointState,hpay,hb,hs.2.2.2.1]
          · simp only [routedState,coreEndpointState,Function.update_of_ne hpay,Function.update_of_ne hb,
              Function.update_of_ne ha,Function.update_of_ne hs.2.2.2.1,Function.update_of_ne hs.2.2.1,
              hlocalFrame k hk]
    · intro i; rfl
  have hworkFrame (i : Fin 392) : F.R (plan.work i) = S.R (plan.work i) := by
    apply hlocalFrame
    exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))))
  obtain ⟨v₂,n₂,outputs,hu₂,hn₂,hcert,he₂⟩ := plan.coreScan_sum_exec b normalize queue crop link hreg
    hsupportMaster hsupportPayload hreplicaCount hreplicaSpare jobs wl hwl
    width halo (e 109) binary endpointWork endpointSaved endpointTmp count source saved tmp (e 116) loopSaved
    hreader hports hframe hloop hoff hsourceWork horiginsWork htakeOff hpacketRows hpacketReplicas hpacketDestination
    V Cprog reserve depth hfit hstock hpush hbody v₁ F (S.R (e 109)) tail
    (by rw [hcontrolFrame width (by simp)]; exact hwidth)
    (by intro r hr; rw [hcontrolFrame halo (by simp),hhalo]; exact hjobHalo r hr)
    (by intro k hk
        have hm : k ∈ [width,halo,binary,plan.master.parameters 6,plan.master.parameters 7,
          endpointWork,endpointSaved,endpointTmp,saved,tmp,loopSaved] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
        rw [hcontrolFrame k hm]; exact hreaderBlank k hk)
    hreadyF (by intro i; rw [hworkFrame i]; exact hblank i)
    (by intro r hr; simp only [F,classPreparedState,Function.update_self,List.length_replicate,hvolume r hr])
    (by rw [hcontrolFrame saved (by simp)]; exact hsaved)
    (by rw [hcontrolFrame tmp (by simp)]; exact htmp)
    (by simp only [F,classPreparedState,Function.update_of_ne ‹e 109 ≠ count›,
      Function.update_of_ne ‹e 109 ≠ e 116›,Function.update_self,horiginJobs])
    (by rw [hF source ‹e 109 ≠ source›.symm ‹e 116 ≠ source›.symm ‹count ≠ source›.symm]; exact hsource)
    (by simp only [F,classPreparedState,Function.update_of_ne ‹e 116 ≠ count›,
      Function.update_self,List.length_replicate,hlen])
    (by rw [hcontrolFrame loopSaved (by simp)]; exact hloopSaved)
  let G : Stacks T A := {F with R := (Function.update (Function.update (Function.update F.R (e 109) (S.R (e 109)))
    source tail) plan.result (outputs.reverse.flatten++F.R plan.result))}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [e 116,count]
    (by simp [‹e 116 ≠ count›]) v₂ G
  have hframes := classControls_frame (e 109) (e 116) count source plan.result hmain S
    ((coreGatherIndices s coreWidth radius H).flatMap (fun k => binSyms V (coreStart coreWidth k-radius))++S.R (e 109))
    outputs.reverse.flatten tail (coreGatherIndices s coreWidth radius H).length (N*(H*W))
    h116 (hprepBlank count (by simp))
  change ((G.R (e 116)).length = (coreGatherIndices s coreWidth radius H).length ∧
      (G.R count).length = N*(H*W)) ∧ _ at hframes
  have hlength : 2*(([e 116,count].map (fun k => (G.R k).length)).sum)+2*[e 116,count].length+1 =
      2*(jobs.length+N*(H*W))+5 := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
      hframes.1.1,hframes.1.2,hlen,Nat.add_zero]
  have hfinal := hframes.2
  change {G with R := (fun k => if k ∈ [e 116,count] then [] else G.R k)} =
    {S with R := (Function.update (Function.update S.R source tail) plan.result
      (outputs.reverse.flatten++S.R plan.result))} at hfinal
  rw [hlength,hfinal] at he₃
  have ht₁₂ := mn_seq_within_add he₁ he₂
  have ht₃ := mn_native_exec_within he₃ 0 (clearWords_native _) depth _ (by
    simpa only [Nat.zero_mul,Nat.add_zero] using ht₁₂.final)
  have ht := (ExecWithin.seq ht₁₂ ht₃).seq_assoc
  refine ⟨v₃,n₁+(n₂+(2*(jobs.length+N*(H*W))+5)),outputs,hu₃.trans (hu₂.trans hu₁),?_,hcert,?_⟩
  · omega
  · simpa only [classRun,Nat.add_assoc] using ht


theorem classRun_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
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
    (e : Fin 117 → Fin T) (he : Function.Injective e) (heOrigin : origins = e 109) (heLoop : loopCount = e 116)
    (symbols prepSaved prepTmp : Fin T)
    (hprepReg : [plan.replicas,halo,plan.packet,symbols,count,prepSaved,prepTmp].Nodup)
    (hprepOff : ∀ k ∈ [plan.replicas,halo,plan.packet,symbols,count,prepSaved,prepTmp], k ≠ e 109 ∧ k ≠ e 116)
    (hmain : [e 109,e 116,count,source,plan.result].Nodup)
    (hcountLocal : ¬ plan.localSupport normalize queue crop count)
    (hinitialOff : ∀ k ∈ [width,halo,binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp,saved,tmp,loopSaved], k ≠ e 109 ∧ k ≠ e 116 ∧ k ≠ count)
    (coreWidth radius H N W : ℕ) (hcoreWidth : 0 < coreWidth) (hwide : s+coreWidth+2*radius < 2^V)
    (hHfit : H < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (hlen : jobs.length = (coreGatherIndices s coreWidth radius H).length)
    (horiginJobs : jobs.flatMap (fun r => binSyms (A := A) V r.a) =
      (coreGatherIndices s coreWidth radius H).flatMap (fun k => binSyms V (coreStart coreWidth k-radius)))
    (hvolume : ∀ r ∈ jobs, (routedPayload r).length = N*(H*W))
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V coreWidth)
    (hr : S.R (e 34) = binSyms V radius) (hH : S.R (e 35) = binSyms V H) (hz : S.R (e 36) = [])
    (htable : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hN : (S.R plan.replicas).length = N) (hhalo : (S.R halo).length = H) (hW : (S.R plan.packet).length = W)
    (hprepBlank : ∀ k ∈ [symbols,count,prepSaved,prepTmp], S.R k = [])
    (hwidth : (S.R width).length = V) (hjobHalo : ∀ r ∈ jobs, H = r.b-r.a)
    (hreaderBlank : ∀ k ∈ [binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp], S.R k = [])
    (hready : ∀ r ∈ jobs, plan.LocalReady normalize queue crop r wl
      (plan.routedState r source [] (plan.coreEndpointState r origins [] S)))
    (hblank : ∀ i, S.R (plan.work i) = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hsource : S.R source = jobs.flatMap routedPayload++tail) (hloopSaved : S.R loopSaved = []) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (preparedCoreOriginsCost V s coreWidth radius H+recoveryPayloadCountCost N H W)+
        (jobs.length*(cost+5)+4)+(2*(jobs.length+N*(H*W))+5) ∧
      List.Forall₂ PackedNormalizedJob.output jobs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((3*preparedCoreOriginsCost V s coreWidth radius H+2*recoveryPayloadCountCost N H W)+reserve)) depth
        (plan.classRun b normalize queue crop link e symbols prepSaved prepTmp width halo binary endpointWork
          endpointSaved endpointTmp count source saved tmp loopSaved) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) plan.result
          (outputs.reverse.flatten++S.R plan.result))}) := by
  obtain ⟨v',n,outputs,hu,hn,hcert,hex⟩ := plan.classRun_sum_exec b normalize queue crop link hreg
    hsupportMaster hsupportPayload hreplicaCount hreplicaSpare jobs wl hwl width halo origins binary
    endpointWork endpointSaved endpointTmp count source saved tmp loopCount loopSaved
    hreader hports hframe hloop hoff hsourceWork horiginsWork htakeOff hpacketRows hpacketReplicas hpacketDestination
    V Cprog reserve depth hfit hstock hpush hbody e he heOrigin heLoop symbols prepSaved prepTmp hprepReg hprepOff
    hmain hcountLocal hinitialOff coreWidth radius H N W hcoreWidth hwide hHfit hA hV hlen horiginJobs hvolume
    v S tail h37 hs hw hr hH hz htable h104 h106 h116 hN hhalo hW hprepBlank hwidth hjobHalo
    hreaderBlank hready hblank hsaved htmp hsource hloopSaved
  have hs := plan.coreTimeCost_sum_le_uniform b V cost jobs htime
  refine ⟨v',n,outputs,hu,?_,hcert,hex⟩
  nlinarith only [hn,hs]

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
