module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierCoreLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCoreClass

/-! A fixed movement-class program generates controls, executes the actual
supplier traversal and retires its restored counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {input : SupplierInputPlan T} {P U : Type} {body : P → Pr P T Q A U}

namespace SupplierSetupPlan

private def coreClassPreparedState (e : Fin 117 → Fin T) (count : Fin T)
    (V s width radius H payloadLength : ℕ) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update S.R (e 109)
    ((coreGatherIndices s width radius H).flatMap (fun k => binSyms V (coreStart width k-radius))++S.R (e 109)))
    (e 116) (List.replicate (coreGatherIndices s width radius H).length tick))
    count (List.replicate payloadLength tick))}

noncomputable def coreClassRun (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
    (e : Fin 117 → Fin T) (count prepSaved prepTmp width halo binary work endpointSaved endpointTmp
      source saved tmp loopSaved : Fin T) : Pr P T Q A U :=
  .seq (prepareCoreClass input e count prepSaved prepTmp)
    (.seq (scanP (e 116) loopSaved
      (plan.coreStep producer width halo (e 109) binary work endpointSaved endpointTmp count source saved tmp))
      (clearWords [e 116,count]))

theorem coreClassRun_exec (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
    (hsourceReg : ∀ i, [input.work i,producer.src,producer.tmp,producer.saved].Nodup)
    (hworkOff : ∀ i j, producer.work i ≠ input.work j) (hresultInput : producer.result ∉ input.support)
    (hcontrolOff : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock],
      ∀ i, k ≠ input.work i)
    (hkernelOff : ∀ k ∈ producer.support, (∀ i, input.masters i ≠ k) ∧ k ≠ input.publication.retained 1)
    (hA : 96 ≤ A) (t B L V : ℕ) [NeZero t]
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (jobs : List (PackedNormalizedJob A s))
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
    (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C)
    (coreWidth radius H : ℕ) (hcoreWidth : 0 < coreWidth) (hwide : s+coreWidth+2*radius < 2^V)
    (hHfit : H < 2^V) (hV : 0 < V) (r₀ : PackedNormalizedJob A s)
    (hlen : jobs.length = (coreGatherIndices s coreWidth radius H).length)
    (horiginJobs : jobs.flatMap (fun r => binSyms (A := A) V r.a) =
      (coreGatherIndices s coreWidth radius H).flatMap (fun k => binSyms V (coreStart coreWidth k-radius)))
    (hvolume : ∀ r ∈ jobs, r.inputPayload.length = r₀.inputPayload.length)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hclass : input.ClassReady r₀ S) (hcount : S.R count = [])
    (hprepSaved : S.R prepSaved = []) (hprepTmp : S.R prepTmp = [])
    (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V coreWidth)
    (hr : S.R (e 34) = binSyms V radius) (hH : S.R (e 35) = binSyms V H) (hz : S.R (e 36) = [])
    (htable : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hsource : S.R source = jobs.flatMap PackedNormalizedJob.inputPayload++tail)
    (hwidth : (S.R width).length = V) (hhalo : ∀ r ∈ jobs, (S.R halo).length = r.b-r.a)
    (hblank : ∀ k ∈ [binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp,
      input.publication.retained 6,saved,tmp], S.R k = [])
    (hready : ∀ r ∈ jobs, plan.Ready r (coreInputState input r (e 109) source S))
    (hkernel : producer.Ready ([] : List (PackedNormalizedJob A s)) (S.R producer.src) S)
    (hloopSaved : S.R loopSaved = []) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (preparedCoreOriginsCost V s coreWidth radius H+supplierBatchCountCost r₀)+
        (jobs.length*(cost+5)+4)+(2*(jobs.length+r₀.inputPayload.length)+5) ∧
      List.Forall₂ (CoreOutputCert B L J) jobs outputs ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        ((3*preparedCoreOriginsCost V s coreWidth radius H+2*supplierBatchCountCost r₀)+reserve)) depth
        (plan.coreClassRun producer e count prepSaved prepTmp width halo binary work endpointSaved endpointTmp
          source saved tmp loopSaved) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) producer.result
          (outputs.reverse.flatten++S.R producer.result))}) := by
  let F := coreClassPreparedState e count V s coreWidth radius H r₀.inputPayload.length S
  have hregs := hmainReg
  regs_ne hregs
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareCoreClass_exec_within (body := body) input e he count prepSaved prepTmp
    hprepReg hcountReg hclassOff V coreWidth radius H hcoreWidth hwide hHfit (by omega) hV r₀ v S
    hclass hcount hprepSaved hprepTmp h37 hs hw hr hH hz htable h104 h106 h116 depth
  have hF (k : Fin T) (ho : k ≠ e 109) (hl : k ≠ e 116) (hc : k ≠ count) : F.R k = S.R k := by
    simp [F,coreClassPreparedState,ho,hl,hc]
  have hreadFrame (k : Fin T)
      (hk : k ∈ [width,halo,binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp,
        input.publication.retained 6,saved,tmp,loopSaved]) : F.R k = S.R k :=
    hF k (hinitialOff k hk).1 (hinitialOff k hk).2.1 (hinitialOff k hk).2.2
  have hreadyF : ∀ r ∈ jobs, plan.Ready r (coreInputState input r (e 109) source F) := by
    intro r hr
    apply (hready r hr).of_frame
    · intro k hk
      have hs := hprotected k (List.mem_append_left _ hk)
      have hkc : k ≠ count := by intro heq; exact hcountSetupOff (heq ▸ hk)
      have hFk := hF k hs.2.2.1 hs.1 hkc
      by_cases hpay : k = input.publication.retained 6
      · subst k; simp [coreInputState]
      · by_cases hb : k = input.parameters 7
        · subst k; simp [coreInputState,endpointState,hpay,hs.2.2.2.1]
        · by_cases ha : k = input.parameters 6
          · subst k; simp [coreInputState,endpointState,hpay,hb,hs.2.2.2.1]
          · simp [coreInputState,endpointState,hpay,hb,ha,hs.2.2.1,hs.2.2.2.1,hFk]
    · rfl
  have hkframe (k : Fin T) (hk : k ∈ producer.support) : F.R k = S.R k := by
    have hs := hprotected k (List.mem_append_right _ (List.mem_append_left _ hk))
    exact hF k hs.2.2.1 hs.1 (by intro heq; exact hcountKernelOff (heq ▸ hk))
  have hkernelF := hkernel.of_frame (F := F) hkframe (by intros; rfl)
  have hsrcMem : producer.src ∈ producer.support := List.mem_append_right _ (by simp)
  obtain ⟨v₂,n₂,outputs,hu₂,hn₂,hcert,he₂⟩ := plan.coreLoop_exec (body := body) producer
    hsourceReg hworkOff hresultInput hcontrolOff hkernelOff hA t B L V J jobs hjobs
    width halo (e 109) binary work endpointSaved endpointTmp count source saved tmp (e 116) loopSaved
    hreader hports hloop hprotected hendpointOff hsourceOff hpayloadOff C cost reserve depth htime hstock hpush hbody
    (S.R (e 109)) tail v₁ F (by rw [hreadFrame width (by simp)]; exact hwidth)
    (by intro r hr; rw [hreadFrame halo (by simp)]; exact hhalo r hr)
    (by intro r hr; simp [F,coreClassPreparedState,hvolume r hr])
    (by
      intro k hk
      rw [hreadFrame k (List.mem_append_right [width,halo] (List.mem_append_left [loopSaved] hk))]
      exact hblank k hk)
    hreadyF (by rw [hkframe producer.src hsrcMem]; exact hkernelF)
    (by simp [F,coreClassPreparedState,horiginJobs,‹e 109 ≠ count›,‹e 109 ≠ e 116›])
    (by rw [hF source (Ne.symm ‹e 109 ≠ source›) (Ne.symm ‹e 116 ≠ source›) (Ne.symm ‹count ≠ source›)]; exact hsource)
    (by simp [F,coreClassPreparedState,‹e 116 ≠ count›,hlen])
    (by rw [hreadFrame loopSaved (by simp)]; exact hloopSaved)
  let G : Stacks T A := {F with R := (Function.update
    (Function.update (Function.update F.R (e 109) (S.R (e 109))) source tail) producer.result
      (outputs.reverse.flatten++F.R producer.result))}
  have hsizeLoop : (G.R (e 116)).length = jobs.length := by
    simp [G,F,coreClassPreparedState,‹e 116 ≠ producer.result›,‹e 116 ≠ source›,
      Ne.symm ‹e 109 ≠ e 116›,‹e 116 ≠ count›,hlen]
  have hsizeCount : (G.R count).length = r₀.inputPayload.length := by
    simp [G,F,coreClassPreparedState,‹count ≠ producer.result›,‹count ≠ source›,Ne.symm ‹e 109 ≠ count›]
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [e 116,count]
    (by simp [‹e 116 ≠ count›]) v₂ G
  have hcleanup : 2*([e 116,count].map fun k => (G.R k).length).sum+2*[e 116,count].length+1 =
      2*(jobs.length+r₀.inputPayload.length)+5 := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
      hsizeLoop,hsizeCount]; omega
  rw [hcleanup] at he₃
  have hpref := mn_seq_within_add he₁ he₂
  have hw₃ := mn_native_exec_within he₃ 0 (clearWords_native _) depth _ (by
    simpa only [Nat.zero_mul,Nat.add_zero] using hpref.final)
  have hwhole := (ExecWithin.seq hpref hw₃).seq_assoc
  have hend : {G with R := fun k => if k ∈ [e 116,count] then [] else G.R k} =
      {S with R := (Function.update (Function.update S.R source tail) producer.result
        (outputs.reverse.flatten++S.R producer.result))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hl : k = e 116
    · subst k; simp [h116,‹e 116 ≠ source›,‹e 116 ≠ producer.result›]
    · by_cases hc : k = count
      · subst k; simp [hcount,‹count ≠ source›,‹count ≠ producer.result›]
      · by_cases ho : k = e 109
        · subst k; simp [G,hl,hc,‹e 109 ≠ source›,‹e 109 ≠ producer.result›]
        · by_cases hs : k = source
          · subst k; simp [G,hl,hc,‹source ≠ producer.result›]
          · by_cases hr : k = producer.result
            · subst k
              simp [G,hl,hc,hF producer.result (Ne.symm ‹e 109 ≠ producer.result›)
                (Ne.symm ‹e 116 ≠ producer.result›) (Ne.symm ‹count ≠ producer.result›)]
            · simp [G,hl,hc,ho,hs,hr,hF k ho hl hc]
  rw [hend] at hwhole
  refine ⟨v₃,n₁+(n₂+(2*(jobs.length+r₀.inputPayload.length)+5)),outputs,hu₃.trans (hu₂.trans hu₁),?_,hcert,?_⟩
  · omega
  · simpa only [coreClassRun,F,coreClassPreparedState,G,Nat.add_assoc] using hwhole

end SupplierSetupPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
