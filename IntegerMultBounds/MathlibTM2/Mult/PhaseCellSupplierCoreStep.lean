module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierReadyCosts
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadSupplierJobEndpoints

/-! A fixed core step reads its origin, consumes one routed batch, and restores
all endpoint and numerical setup storage after publishing its result. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {input : SupplierInputPlan T} {P U : Type} {body : P → Pr P T Q A U}

namespace SupplierSetupPlan

def endpointState (input : SupplierInputPlan T) (r : PackedNormalizedJob A s)
    (origins : Fin T) (tail : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update S.R origins tail)
    (input.parameters 6) (List.replicate r.a Node.tick))
    (input.parameters 7) (List.replicate r.b Node.tick))}

noncomputable def coreStep (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
    (width halo origins binary work endpointSaved endpointTmp count source saved tmp : Fin T) : Pr P T Q A U :=
  .seq (readSupplierEndpoints width halo origins binary (input.parameters 6) (input.parameters 7)
    work endpointSaved endpointTmp)
    (.seq (plan.routedRun producer count source saved tmp)
      (clearWords [input.parameters 6,input.parameters 7]))

theorem coreStep_exec (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
    (r : PackedNormalizedJob A s)
    (hsourceReg : ∀ i, [input.work i,producer.src,producer.tmp,producer.saved].Nodup)
    (hworkOff : ∀ i j, producer.work i ≠ input.work j) (hresultInput : producer.result ∉ input.support)
    (hcontrolOff : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock],
      ∀ i, k ≠ input.work i)
    (hkernelOff : ∀ k ∈ producer.support, (∀ i, input.masters i ≠ k) ∧ k ≠ input.publication.retained 1)
    (hA : 96 ≤ A) (t B L : ℕ) [NeZero t] (ht : r.t = t) (hp : 4 ≤ r.p)
    (htarget : r.p+2 ≤ r.targetOut) (hlocal : r.localityTarget = r.targetOut)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1)
    (hreplicas : r.Fs.length = B) (hcore : coreLength s r.coreWidth r.k = L)
    (width halo origins binary work endpointSaved endpointTmp count source saved tmp : Fin T)
    (hreader : [width,halo,origins,binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp].Nodup)
    (hports : [origins,input.parameters 6,input.parameters 7,count,source,input.publication.retained 6,
      saved,tmp,producer.result].Nodup)
    (hendpointOff : ∀ k ∈ producer.support,
      k ≠ origins ∧ k ≠ input.parameters 6 ∧ k ≠ input.parameters 7)
    (V : ℕ) (hfit : r.a < 2^V) (originTail tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hhalo : (S.R halo).length = r.b-r.a)
    (horigins : S.R origins = binSyms V r.a++originTail)
    (hblank : ∀ k ∈ [binary,input.parameters 6,input.parameters 7,work,endpointSaved,endpointTmp], S.R k = [])
    (hready : plan.Ready r {(endpointState input r origins originTail S) with R :=
      (Function.update (Function.update (endpointState input r origins originTail S).R source tail)
        (input.publication.retained 6) r.inputPayload)})
    (hcount : (S.R count).length = r.inputPayload.length) (hsource : S.R source = r.inputPayload++tail)
    (hpayload : S.R (input.publication.retained 6) = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hsourceOff : source ∉ producer.support) (hpayloadOff : input.publication.retained 6 ∉ producer.support)
    (hkernel : producer.Ready ([] : List (PackedNormalizedJob A s)) (S.R producer.src) S)
    (C depth : ℕ) (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    ∃ H v' n, ∃ rows : Fin 1 → Fin B → List GaussianInt,
      input.Ready r H ∧ v'.user = v.user ∧
      n ≤ readSupplierEndpointsCost V r.a (r.b-r.a)+
        ((6*r.inputPayload.length+6)+(timeCost r+(r.inputTimeCost+
          (producer.timeCost (U := U) [r]+20*(descriptorScheduleTape producer.work PackedNormalizedJob.words [r]).length+7)+
          (2*(∑ i, (r.words i).length)+651))+retirementCost r)+(2*r.inputPayload.length+2))+
        (2*(r.a+r.b)+5) ∧
      (∀ i j, (rows i j).length = L) ∧ (∀ i : Fin 1, r.ExactRowOutput J (List.ofFn (rows i))) ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        (3*readSupplierEndpointsCost V r.a (r.b-r.a)+
          (2*(6*r.inputPayload.length+6)+(stock r+(r.inputStock+
            (31*(descriptorScheduleTape producer.work PackedNormalizedJob.words [r]).length+9+
              (C+1)*producer.workspace (U := U) [r])))))) depth
        (plan.coreStep producer width halo origins binary work endpointSaved endpointTmp count source saved tmp)
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update
          (Function.update (Function.update S.R origins originTail) source tail) producer.result
          ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++S.R producer.result))}) := by
  have hr := hports
  regs_ne hr
  let E := endpointState input r origins originTail S
  have hE (k : Fin T) (ho : k ≠ origins) (ha : k ≠ input.parameters 6) (hb : k ≠ input.parameters 7) :
      E.R k = S.R k := by simp [E,endpointState,ho,ha,hb]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readSupplierJobEndpoints_exec (body := body) input
    width halo origins binary work endpointSaved endpointTmp hreader r V hfit originTail v S hwidth hhalo horigins hblank depth
  have hreg : [count,source,input.publication.retained 6,saved,tmp].Nodup := by
    simp_all only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_false_eq_true,not_or,ne_eq,and_true]
  have hframe (k : Fin T) (hk : k ∈ producer.support) : E.R k = S.R k :=
    hE k (hendpointOff k hk).1 (hendpointOff k hk).2.1 (hendpointOff k hk).2.2
  have hsrcMem : producer.src ∈ producer.support := List.mem_append_right _ (by simp)
  have hk := hkernel.of_frame (F := E) hframe (by intros; rfl)
  obtain ⟨H,v₂,n₂,rows,hheaders,hu₂,hn₂,hlen,hrows,he₂⟩ := plan.routedRun_exec (body := body) producer r
    hsourceReg hworkOff hresultInput hcontrolOff hkernelOff hA t B L ht hp htarget hlocal J hJ hreplicas hcore
    count source saved tmp hreg tail v₁ E hready
    (by rw [hE count (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption))]; exact hcount)
    (by rw [hE source (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption))]; exact hsource)
    (by rw [hE (input.publication.retained 6) (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption))]; exact hpayload)
    (by rw [hE saved (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption))]; exact hsaved)
    (by rw [hE tmp (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption))]; exact htmp)
    hsourceOff hpayloadOff (by first | assumption | exact Ne.symm (by assumption)) (by rw [hframe producer.src hsrcMem]; exact hk) C depth hpush hbody
  rw [hheaders.timeCost_eq] at hn₂
  rw [hheaders.stock_eq] at he₂
  let output := (List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten
  let G : Stacks T A := {E with R := (Function.update (Function.update E.R source tail) producer.result
    (output++E.R producer.result))}
  have hlengthA : (G.R (input.parameters 6)).length = r.a := by
    simp [G,E,endpointState,‹input.parameters 6 ≠ producer.result›,‹input.parameters 6 ≠ source›,
      ‹input.parameters 6 ≠ input.parameters 7›]
  have hlengthB : (G.R (input.parameters 7)).length = r.b := by
    simp [G,E,endpointState,‹input.parameters 7 ≠ producer.result›,‹input.parameters 7 ≠ source›]
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [input.parameters 6,input.parameters 7]
    (by simp [‹input.parameters 6 ≠ input.parameters 7›]) v₂ G
  have hcost : 2*([input.parameters 6,input.parameters 7].map fun k => (G.R k).length).sum+
      2*[input.parameters 6,input.parameters 7].length+1 = 2*(r.a+r.b)+5 := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
      hlengthA,hlengthB]; omega
  rw [hcost] at he₃
  have hpref := mn_seq_within_add he₁ he₂
  have hw₃ := mn_native_exec_within he₃ 0 (clearWords_native _) depth _ (by
    simpa only [Nat.zero_mul,Nat.add_zero] using hpref.final)
  have hwhole := (ExecWithin.seq hpref hw₃).seq_assoc
  have hblankA := hblank (input.parameters 6) (by simp)
  have hblankB := hblank (input.parameters 7) (by simp)
  have hend : {G with R := fun k => if k ∈ [input.parameters 6,input.parameters 7] then [] else G.R k} =
      {S with R := (Function.update (Function.update (Function.update S.R origins originTail) source tail)
        producer.result (output++S.R producer.result))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases ha : k = input.parameters 6
    · subst k; simp [hblankA,‹input.parameters 6 ≠ producer.result›,‹input.parameters 6 ≠ source›,
        Ne.symm ‹origins ≠ input.parameters 6›]
    · by_cases hb : k = input.parameters 7
      · subst k; simp [hblankB,‹input.parameters 7 ≠ producer.result›,‹input.parameters 7 ≠ source›,
          Ne.symm ‹origins ≠ input.parameters 7›]
      · by_cases hresult : k = producer.result
        · subst k; simp [G,E,endpointState,Ne.symm ‹input.parameters 6 ≠ producer.result›,
            Ne.symm ‹input.parameters 7 ≠ producer.result›,Ne.symm ‹origins ≠ producer.result›]
        · by_cases hs : k = source
          · subst k; simp [G,E,endpointState,ha,hb,hresult]
          · simp [G,E,endpointState,ha,hb,hresult,hs]
  rw [hend] at hwhole
  refine ⟨H,v₃,n₁+(n₂+(2*(r.a+r.b)+5)),rows,hheaders,hu₃.trans (hu₂.trans hu₁),?_,hlen,hrows,?_⟩
  · omega
  · simpa only [coreStep,endpointState,E,output,Nat.add_assoc] using hwhole
end SupplierSetupPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
