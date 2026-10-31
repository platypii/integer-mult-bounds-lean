module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposeRealGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreClassRun

/-! Actual ambient exposure feeds the fixed generated class lifecycle. The
ambient source, routed archive, class controls and scratch restore; only
certified supplier outputs remain. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace SupplierSetupPlan
variable {t₀ T Q c d W K s : ℕ} [NeZero s] {input : SupplierInputPlan T}
  {P U : Type} {body : P → Pr P T Q (prime+K) U}

theorem exposedCoreClassRun_exec (route : ArchiveTilePlan t₀ T Q c d W) (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
    (hsourceReg : ∀ i, [input.work i,producer.src,producer.tmp,producer.saved].Nodup)
    (hworkOff : ∀ i j, producer.work i ≠ input.work j) (hresultInput : producer.result ∉ input.support)
    (hcontrolOff : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock],
      ∀ i, k ≠ input.work i)
    (hkernelOff : ∀ k ∈ producer.support, (∀ i, input.masters i ≠ k) ∧ k ≠ input.publication.retained 1)
    (hA : 96 ≤ (prime+K)) (t B L V : ℕ) [NeZero t]
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (jobs : List (PackedNormalizedJob (prime+K) s))
    (hjobs : ∀ r ∈ jobs, r.t = t ∧ 4 ≤ r.p ∧ r.p+2 ≤ r.targetOut ∧ r.localityTarget = r.targetOut ∧
      J ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1 ∧
      r.Fs.length = B ∧ coreLength s r.coreWidth r.k = L ∧ r.a < 2^V)
    (e : Fin 117 → Fin T) (he : Function.Injective e)
    (count prepSaved prepTmp width halo binary work endpointSaved endpointTmp source saved tmp loopSaved : Fin T)
    (hprepReg : [e 109,e 116,count,prepSaved,prepTmp].Nodup)
    (hcountReg : [input.publication.headers 0,input.publication.headers 3,count,prepSaved,prepTmp].Nodup)
    (hclassOff : ∀ i, input.classDest i ≠ e 109 ∧ input.classDest i ≠ e 116)
    (hmainReg : [e 109,e 116,count,source,producer.result].Nodup)
    (hreader : [width,halo,e 109,binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp].Nodup)
    (hports : [e 109,input.parameters 6,input.parameters 7,count,source,input.publication.retained 6,
      saved,tmp,producer.result].Nodup)
    (hloop : [e 116,loopSaved,e 109,source,producer.result].Nodup)
    (hprotected : ∀ k ∈ plan.coreProtected producer width halo binary work endpointSaved endpointTmp count saved tmp,
      k ≠ e 116 ∧ k ≠ loopSaved ∧ k ≠ e 109 ∧ k ≠ source ∧ k ≠ producer.result)
    (hendpointOff : ∀ k ∈ producer.support, k ≠ e 109 ∧ k ≠ input.parameters 6 ∧ k ≠ input.parameters 7)
    (hsourceOff : source ∉ producer.support) (hpayloadOff : input.publication.retained 6 ∉ producer.support)
    (hcountSetupOff : count ∉ plan.support) (hcountKernelOff : count ∉ producer.support)
    (hinitialOff : ∀ k ∈ [width,halo,binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp,
      input.publication.retained 6,saved,tmp,loopSaved], k ≠ e 109 ∧ k ≠ e 116 ∧ k ≠ count)
    (C cost reserve depth : ℕ) (htime : ∀ r ∈ jobs, coreTimeCost (U := U) producer V r ≤ cost)
    (hstock : ∀ r ∈ jobs, coreStock (U := U) producer C V r ≤ reserve)
    (hpush : mnProgPush (producer.program (P := P) (U := U) (A := (prime+K))) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C)
    (coreWidth radius H : ℕ) (hcoreWidth : 0 < coreWidth) (hwide : s+coreWidth+2*radius < 2^V)
    (hHfit : H < 2^V) (hV : 0 < V) (r₀ : PackedNormalizedJob (prime+K) s)
    (hlen : jobs.length = (coreGatherIndices s coreWidth radius H).length)
    (horiginJobs : jobs.flatMap (fun r => binSyms (A := (prime+K)) V r.a) =
      (coreGatherIndices s coreWidth radius H).flatMap (fun k => binSyms V (coreStart coreWidth k-radius)))
    (hvolume : ∀ r ∈ jobs, r.inputPayload.length = r₀.inputPayload.length)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hclass : input.ClassReady r₀ S) (hcount : S.R count = [])
    (hprepSaved : S.R prepSaved = []) (hprepTmp : S.R prepTmp = [])
    (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V coreWidth)
    (hr : S.R (e 34) = binSyms V radius) (hH : S.R (e 35) = binSyms V H) (hz : S.R (e 36) = [])
    (htable : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hwidth : (S.R width).length = V) (hhalo : ∀ r ∈ jobs, (S.R halo).length = r.b-r.a)
    (hblank : ∀ k ∈ [binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp,
      input.publication.retained 6,saved,tmp], S.R k = [])
    (hready : ∀ r ∈ jobs, plan.Ready r (coreInputState input r (e 109) source S))
    (hkernel : producer.Ready ([] : List (PackedNormalizedJob (prime+K) s)) (S.R producer.src) S)
    (hloopSaved : S.R loopSaved = [])
    (w : ℕ)
    (hW : 0 < W) (gather : Fin 168 → Fin T) (hGather : Function.Injective gather) (gatherCount gatherSource gatherArchive gatherSaved gatherTmp replicas savedReplicas : Fin T)
    (hGatherReg : [gatherCount,gatherSource,gatherArchive,gatherSaved,gatherTmp,replicas,savedReplicas].Nodup)
    (hGatherSep : ∀ k ∈ [gatherCount,gatherSource,gatherArchive,gatherSaved,gatherTmp,replicas,savedReplicas], ∀ i, k ≠ gather i)
    (borrowed : List (Fin (prime+K+4)))
    (hwV : w < 2^V) (hvol : s*w < 2^V)
    (hgroup : 0 < (coreGatherIndices s coreWidth radius H).length)
    (Fs : List (ZMod s → GaussianInt))
    (h163 : (S.R (gather 163)).length = V) (h115 : S.R (gather 115) = []) (h103 : S.R (gather 103) = []) (h105 : S.R (gather 105) = [])
    (hGatherS : S.R (gather 145) = binSyms V s) (hGatherWidth : S.R (gather 150) = binSyms V coreWidth)
    (hGatherRadius : S.R (gather 152) = binSyms V radius) (hGatherH : S.R (gather 165) = binSyms V H) (hGatherZero : S.R (gather 154) = [])
    (hGatherBlank : ∀ k : Fin 168, k.val < 31 → S.R (gather k) = [])
    (hGather104 : S.R (gather 104) = []) (hGather106 : S.R (gather 106) = []) (hGather116 : S.R (gather 116) = [])
    (hAmbientSource : S.R gatherSource = Fs.flatMap (fun C => cstream (prime+K) w (chirpLine s C))++borrowed)
    (hGatherArchive : S.R gatherArchive = [])
    (hReplicas : (S.R replicas).length = Fs.length) (hSavedReplicas : S.R savedReplicas = [])
    (hGatherLocal : S.R (gather 110) = [])
    (hGatherCount : (S.R gatherCount).length = s*w) (hGatherSaved : S.R gatherSaved = []) (hGatherTmp : S.R gatherTmp = [])
    (hGatherWord : (S.R (gather 94)).length = w) (hGatherControl : S.R (gather 91) = []) (hGatherOrigin : S.R (gather 109) = [])
    (hGatherClean : ∀ k ∈ [(92 : Fin 168),93,95,96,97,98,99,100,101,102], S.R (gather k) = [])
    (hGatherFresh : ∀ k ∈ [(88 : Fin 168),89,90], S.R (gather k) = []) 
    (realRows capacityRows blockWidth rowSymbols padSymbols missing acc padSaved padTmp : Fin T)
    (hrouteRegs : [realRows,capacityRows,blockWidth,rowSymbols,padSymbols,missing,route.src,acc,padSaved,padTmp,replicas,savedReplicas].Nodup)
    (hrouteSrc : gather 108 = route.src) (houtput : S.R route.src = [])
    (hRouteReady : route.BankReady S) (hpacket : W = H*w)
    (hcapacity : (coreGatherIndices s coreWidth radius H).length ≤ (2^d)^c)
    (hreplicaPower : Fs.length = 2^d)
    (hrows : (S.R realRows).length = (coreGatherIndices s coreWidth radius H).length)
    (hcapacityRows : (S.R capacityRows).length = (2^d)^c) (hblockWidth : (S.R blockWidth).length = H*w)
    (hrowSymbols : S.R rowSymbols = []) (hpadSymbols : S.R padSymbols = []) (hmissing : S.R missing = [])
    (hacc : S.R acc = []) (hpadSaved : S.R padSaved = []) (hpadTmp : S.R padTmp = [])
    (hArchiveSource : route.src = source) (hLeft : S.L = fun _ => [])
    (hclassSourceOff : ∀ i, input.classDest i ≠ source)
    (hreadSourceOff : ∀ k ∈ [count,prepSaved,prepTmp,e 37,e 32,e 33,e 34,e 35,e 36,e 104,e 106,e 116,
      width,halo,binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp,
      input.publication.retained 6,saved,tmp,loopSaved], k ≠ source)
    (htableSourceOff : ∀ k : Fin 117, k.val < 31 → e k ≠ source)
    (hpayloadJobs : jobs.flatMap PackedNormalizedJob.inputPayload =
      coreSupplierStream (prime+K) coreWidth radius H w Fs.reverse) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ route.realGatherTimeCost V s coreWidth radius H w Fs.length S+
        ((preparedCoreOriginsCost V s coreWidth radius H+supplierBatchCountCost r₀)+
          (jobs.length*(cost+5)+4)+(2*(jobs.length+r₀.inputPayload.length)+5)) ∧
      List.Forall₂ (CoreOutputCert B L J) jobs outputs ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (route.realGatherStockAllowance V s coreWidth radius H w Fs.length+
          ((3*preparedCoreOriginsCost V s coreWidth radius H+2*supplierBatchCountCost r₀)+reserve))) depth
        (.seq (route.realGatherProgram gather gatherCount gatherSource gatherArchive gatherSaved gatherTmp
          replicas savedReplicas realRows capacityRows blockWidth rowSymbols padSymbols missing acc padSaved padTmp)
          (plan.coreClassRun producer e count prepSaved prepTmp width halo binary work endpointSaved endpointTmp
            source saved tmp loopSaved)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R producer.result
          (outputs.reverse.flatten++S.R producer.result))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := route.expose_real_gather_exec_within body hW gather hGather gatherCount
    gatherSource gatherArchive gatherSaved gatherTmp replicas savedReplicas hGatherReg hGatherSep borrowed
    hcoreWidth hwide hHfit hwV hvol (by omega) hV hgroup Fs v S
    h163 h115 h103 h105 hGatherS hGatherWidth hGatherRadius hGatherH hGatherZero hGatherBlank
    hGather104 hGather106 hGather116 hAmbientSource hGatherArchive hReplicas hSavedReplicas
    hGatherLocal hGatherCount hGatherSaved hGatherTmp hGatherWord hGatherControl hGatherOrigin hGatherClean hGatherFresh
    realRows capacityRows blockWidth rowSymbols padSymbols missing acc padSaved padTmp hrouteRegs hrouteSrc houtput
    hRouteReady hpacket hcapacity hreplicaPower hrows hcapacityRows hblockWidth hrowSymbols hpadSymbols hmissing
    hacc hpadSaved hpadTmp depth
  rw [←hLeft,hArchiveSource,←hpayloadJobs] at he₁
  let F : Stacks T (prime+K) := {S with R := Function.update S.R source (jobs.flatMap PackedNormalizedJob.inputPayload)}
  have hF (k : Fin T) (hk : k ≠ source) : F.R k = S.R k := by simp [F,hk]
  have hread (k : Fin T) (hk : k ∈ [count,prepSaved,prepTmp,e 37,e 32,e 33,e 34,e 35,e 36,e 104,e 106,e 116,
      width,halo,binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp,
      input.publication.retained 6,saved,tmp,loopSaved]) : F.R k = S.R k := hF k (hreadSourceOff k hk)
  have hclassF : input.ClassReady r₀ F := hclass.of_frame (by intro i; exact hF _ (hclassSourceOff i))
  have hinput (r : PackedNormalizedJob (prime+K) s) : coreInputState input r (e 109) source F =
      coreInputState input r (e 109) source S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = source
    · subst k; simp [coreInputState,Function.update_apply]
    · simp [coreInputState,endpointState,F,Function.update_apply,hk]
  have hreadyF : ∀ r ∈ jobs, plan.Ready r (coreInputState input r (e 109) source F) := by
    intro r hr; rw [hinput]; exact hready r hr
  have hkframe (k : Fin T) (hk : k ∈ producer.support) : F.R k = S.R k :=
    hF k (by intro heq; exact hsourceOff (heq ▸ hk))
  have hkernelF := hkernel.of_frame (F := F) hkframe (by intros; rfl)
  have hsrcMem : producer.src ∈ producer.support := List.mem_append_right _ (by simp)
  obtain ⟨v₂,n₂,outputs,hu₂,hn₂,hcert,he₂⟩ := plan.coreClassRun_exec (body := body) producer
    hsourceReg hworkOff hresultInput hcontrolOff hkernelOff hA t B L V J jobs hjobs e he
    count prepSaved prepTmp width halo binary work endpointSaved endpointTmp source saved tmp loopSaved
    hprepReg hcountReg hclassOff hmainReg hreader hports hloop hprotected hendpointOff hsourceOff hpayloadOff
    hcountSetupOff hcountKernelOff hinitialOff C cost reserve depth htime hstock hpush hbody
    coreWidth radius H hcoreWidth hwide hHfit hV r₀ hlen horiginJobs hvolume [] v₁ F hclassF
    (by rw [hread (count) (by simp)]; exact hcount)
    (by rw [hread (prepSaved) (by simp)]; exact hprepSaved)
    (by rw [hread (prepTmp) (by simp)]; exact hprepTmp)
    (by rw [hread (e 37) (by simp)]; exact h37)
    (by rw [hread (e 32) (by simp)]; exact hs)
    (by rw [hread (e 33) (by simp)]; exact hw)
    (by rw [hread (e 34) (by simp)]; exact hr)
    (by rw [hread (e 35) (by simp)]; exact hH)
    (by rw [hread (e 36) (by simp)]; exact hz)
    (by intro k hk; rw [hF (e k) (htableSourceOff k hk)]; exact htable k hk)
    (by rw [hread (e 104) (by simp)]; exact h104)
    (by rw [hread (e 106) (by simp)]; exact h106)
    (by rw [hread (e 116) (by simp)]; exact h116)
    (by simp [F]) (by rw [hread width (by simp)]; exact hwidth)
    (by intro r hr; rw [hread halo (by simp)]; exact hhalo r hr)
    (by
      intro k hk
      rw [hF k (hreadSourceOff k (List.mem_append_right
        [count,prepSaved,prepTmp,e 37,e 32,e 33,e 34,e 35,e 36,e 104,e 106,e 116,width,halo]
        (List.mem_append_left [loopSaved] hk)))]
      exact hblank k hk)
    hreadyF (by rw [hkframe producer.src hsrcMem]; exact hkernelF)
    (by rw [hread loopSaved (by simp)]; exact hloopSaved)
  have hregs := hmainReg
  regs_ne hregs
  have hsourceBlank : S.R source = [] := by rw [←hArchiveSource]; exact houtput
  have hend : {F with R := (Function.update (Function.update F.R source []) producer.result
      (outputs.reverse.flatten++F.R producer.result))} =
      {S with R := (Function.update S.R producer.result (outputs.reverse.flatten++S.R producer.result))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hr : k = producer.result
    · subst k; simp [F,Ne.symm ‹source ≠ producer.result›]
    · by_cases hs : k = source
      · subst k; simp [hr,hsourceBlank]
      · simp [F,hr,hs]
  rw [hend] at he₂
  exact ⟨v₂,n₁+n₂,outputs,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hcert,mn_seq_within_add he₁ he₂⟩

end SupplierSetupPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
