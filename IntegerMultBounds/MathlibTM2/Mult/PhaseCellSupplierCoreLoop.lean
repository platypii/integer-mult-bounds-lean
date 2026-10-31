module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierCoreStepStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierSetupFrame

/-! One fixed runtime scan executes the actual core supplier over ordered jobs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {input : SupplierInputPlan T} {P U : Type} {body : P → Pr P T Q A U}

namespace SupplierSetupPlan

noncomputable def coreInputState (input : SupplierInputPlan T) (r : PackedNormalizedJob A s)
    (origins source : Fin T) (S : Stacks T A) : Stacks T A :=
  {(endpointState input r origins [] S) with R := (Function.update
    (Function.update (endpointState input r origins [] S).R source [])
      (input.publication.retained 6) r.inputPayload)}

def coreProtected (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
    (width halo binary work endpointSaved endpointTmp count saved tmp : Fin T) : List (Fin T) :=
  plan.support ++ (producer.support ++ [width,halo,binary,work,endpointSaved,endpointTmp,count,saved,tmp])

def CoreOutputCert (B L : ℕ) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (r : PackedNormalizedJob A s) (xs : List (Fin (A+4))) : Prop :=
  ∃ rows : Fin 1 → Fin B → List GaussianInt,
    (∀ i j, (rows i j).length = L) ∧ (∀ i : Fin 1, r.ExactRowOutput J (List.ofFn (rows i))) ∧
    xs = (List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten

theorem coreLoop_exec (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
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
    (width halo origins binary work endpointSaved endpointTmp count source saved tmp loopCount loopSaved : Fin T)
    (hreader : [width,halo,origins,binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp].Nodup)
    (hports : [origins,input.parameters 6,input.parameters 7,count,source,input.publication.retained 6,
      saved,tmp,producer.result].Nodup)
    (hloop : [loopCount,loopSaved,origins,source,producer.result].Nodup)
    (hprotected : ∀ k ∈ plan.coreProtected producer width halo binary work endpointSaved endpointTmp count saved tmp,
      k ≠ loopCount ∧ k ≠ loopSaved ∧ k ≠ origins ∧ k ≠ source ∧ k ≠ producer.result)
    (hendpointOff : ∀ k ∈ producer.support, k ≠ origins ∧ k ≠ input.parameters 6 ∧ k ≠ input.parameters 7)
    (hsourceOff : source ∉ producer.support) (hpayloadOff : input.publication.retained 6 ∉ producer.support)
    (C cost reserve depth : ℕ) (htime : ∀ r ∈ jobs, coreTimeCost (U := U) producer V r ≤ cost)
    (hstock : ∀ r ∈ jobs, coreStock (U := U) producer C V r ≤ reserve)
    (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C)
    (originTail tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V)
    (hhalo : ∀ r ∈ jobs, (S.R halo).length = r.b-r.a)
    (hcount : ∀ r ∈ jobs, (S.R count).length = r.inputPayload.length)
    (hblank : ∀ k ∈ [binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp,
      input.publication.retained 6,saved,tmp], S.R k = [])
    (hready : ∀ r ∈ jobs, plan.Ready r (coreInputState input r origins source S))
    (hkernel : producer.Ready ([] : List (PackedNormalizedJob A s)) (S.R producer.src) S)
    (horigins : S.R origins = jobs.flatMap (fun r => binSyms V r.a)++originTail)
    (hsource : S.R source = jobs.flatMap PackedNormalizedJob.inputPayload++tail)
    (hloopCount : (S.R loopCount).length = jobs.length) (hloopSaved : S.R loopSaved = []) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ jobs.length*(cost+5)+4 ∧
      List.Forall₂ (CoreOutputCert B L J) jobs outputs ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+reserve) depth
        (scanP loopCount loopSaved
          (plan.coreStep producer width halo origins binary work endpointSaved endpointTmp count source saved tmp))
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update
          (Function.update (Function.update S.R origins originTail) source tail) producer.result
          (outputs.reverse.flatten++S.R producer.result))}) := by
  let protectedRegs := plan.coreProtected producer width halo binary work endpointSaved endpointTmp count saved tmp
  let Inv : Stacks T A → Prop := fun F => F.L = S.L ∧ ∀ k ∈ protectedRegs, F.R k = S.R k
  have hplan (k : Fin T) (hk : k ∈ plan.support) : k ∈ protectedRegs := List.mem_append_left _ hk
  have hkernelMem (k : Fin T) (hk : k ∈ producer.support) : k ∈ protectedRegs :=
    List.mem_append_right _ (List.mem_append_left _ hk)
  have hcontrol (k : Fin T) (hk : k ∈ [width,halo,binary,work,endpointSaved,endpointTmp,count,saved,tmp]) :
      k ∈ protectedRegs := List.mem_append_right _ (List.mem_append_right _ hk)
  have hJcounter : ∀ F R, (∀ k, k ≠ loopCount → k ≠ loopSaved → R k = F.R k) → Inv F → Inv {F with R := R} := by
    intro F R hR hF
    refine ⟨hF.1,?_⟩
    intro k hk
    exact (hR k (hprotected k hk).1 (hprotected k hk).2.1).trans (hF.2 k hk)
  have hJstep : ∀ F otail rest xs, Inv F → Inv {F with R := (Function.update
      (Function.update (Function.update F.R origins otail) source rest) producer.result (xs++F.R producer.result))} := by
    intro F otail rest xs hF
    refine ⟨hF.1,?_⟩
    intro k hk
    have hs := hprotected k hk
    simpa only [Function.update_of_ne hs.2.2.2.2,Function.update_of_ne hs.2.2.2.1,
      Function.update_of_ne hs.2.2.1] using hF.2 k hk
  refine consumeScan_exec (body := body) _ loopCount loopSaved origins source producer.result hloop
    (fun r => binSyms V r.a) PackedNormalizedJob.inputPayload jobs originTail tail cost reserve depth
    (CoreOutputCert B L J) Inv hJcounter hJstep ?_ v S ⟨rfl,by intros; rfl⟩
    horigins hsource hloopCount hloopSaved
  · intro r hr w F otail rest hF ho hpayload
    obtain ⟨ht,hp,htarget,hlocal,hJ,hreplicas,hcore,hfit⟩ := hjobs r hr
    have hc (k : Fin T) (hk : k ∈ [width,halo,binary,work,endpointSaved,endpointTmp,count,saved,tmp]) :
        F.R k = S.R k := hF.2 k (hcontrol k hk)
    have hsetup : plan.Ready r {(endpointState input r origins otail F) with R :=
        (Function.update (Function.update (endpointState input r origins otail F).R source rest)
          (input.publication.retained 6) r.inputPayload)} := by
      apply (hready r hr).of_frame
      · intro k hk
        have hs := hprotected k (hplan k hk)
        by_cases hpay : k = input.publication.retained 6
        · subst k; simp [coreInputState]
        · by_cases hb : k = input.parameters 7
          · subst k; simp [coreInputState,endpointState,hpay,hs.2.2.2.1]
          · by_cases ha : k = input.parameters 6
            · subst k; simp [coreInputState,endpointState,hpay,hb,hs.2.2.2.1]
            · simp [coreInputState,endpointState,hpay,hb,ha,hs.2.2.1,hs.2.2.2.1,hF.2 k (hplan k hk)]
      · exact hF.1
    have hk := hkernel.of_frame (F := F) (by intro k hk; exact hF.2 k (hkernelMem k hk))
      (by intro i; rw [hF.1])
    have hsrcMem : producer.src ∈ producer.support := List.mem_append_right _ (by simp)
    have hrblank (k : Fin T) (hk : k ∈ [binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp]) :
        F.R k = [] := by
      by_cases ha : k = input.parameters 6
      · subst k
        have hm : input.parameters 6 ∈ input.baseSupport := List.mem_append_right _
          (List.mem_append_left _ (List.mem_ofFn.mpr ⟨6,rfl⟩))
        rw [hF.2 _ (hplan _ (List.mem_append_left _ hm))]
        exact hblank _ (by simp)
      · by_cases hb : k = input.parameters 7
        · subst k
          have hm : input.parameters 7 ∈ input.baseSupport := List.mem_append_right _
            (List.mem_append_left _ (List.mem_ofFn.mpr ⟨7,rfl⟩))
          rw [hF.2 _ (hplan _ (List.mem_append_left _ hm))]
          exact hblank _ (by simp)
        · have hkc : k ∈ [width,halo,binary,work,endpointSaved,endpointTmp,count,saved,tmp] := by
            simp only [List.mem_cons,List.not_mem_nil,or_false,ha,hb,false_or] at hk
            rcases hk with rfl | rfl | rfl | rfl <;> simp
          rw [hc k hkc]
          exact hblank k (List.mem_append_left [input.publication.retained 6,saved,tmp] hk)
    have hlocalPayload : F.R (input.publication.retained 6) = [] := by
      have hm : input.publication.retained 6 ∈ input.baseSupport := List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _ (by simp)))
      rw [hF.2 _ (hplan _ (List.mem_append_left _ hm))]
      exact hblank _ (by simp)
    obtain ⟨H,w',n,rows,hheaders,hu,hn,hlen,hrows,he⟩ := plan.coreStep_exec (body := body) producer r
      hsourceReg hworkOff hresultInput hcontrolOff hkernelOff hA t B L ht hp htarget hlocal J hJ hreplicas hcore
      width halo origins binary work endpointSaved endpointTmp count source saved tmp hreader hports hendpointOff
      V hfit otail rest w F (by rw [hc width (by simp)]; exact hwidth)
      (by rw [hc halo (by simp)]; exact hhalo r hr) ho hrblank hsetup
      (by rw [hc count (by simp)]; exact hcount r hr) hpayload hlocalPayload
      (by rw [hc saved (by simp)]; exact hblank _ (by simp))
      (by rw [hc tmp (by simp)]; exact hblank _ (by simp)) hsourceOff hpayloadOff
      (by rw [hF.2 producer.src (hkernelMem _ hsrcMem)]; exact hk) C depth hpush hbody
    exact ⟨w',n,_,hu,hn.trans (htime r hr),r.coreOutput_length_le_payload rows hreplicas hcore hlen,
      ⟨rows,hlen,hrows,rfl⟩,he.mono (by intro d z hz; have hs := hstock r hr; omega)⟩

end SupplierSetupPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
