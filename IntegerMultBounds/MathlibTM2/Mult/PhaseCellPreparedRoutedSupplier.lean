module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedSupplierRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefixStock

/-! Consume one routed batch through a fixed supplier body with generated
numerical setup, retiring both numerical headers and the local payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {input : SupplierInputPlan T} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def PackedNormalizedJob.inputPayload (r : PackedNormalizedJob A s) : List (Fin (A+4)) :=
  cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten

namespace SupplierSetupPlan
noncomputable def routedRun (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
    (count source saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takePrefix count source (input.publication.retained 6) saved tmp)
    (.seq (plan.run producer) (uclear (input.publication.retained 6)))

theorem routedRun_exec (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
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
    (count source saved tmp : Fin T) (hreg : [count,source,input.publication.retained 6,saved,tmp].Nodup)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : plan.Ready r {S with R := (Function.update (Function.update S.R source tail)
      (input.publication.retained 6) r.inputPayload)})
    (hcount : (S.R count).length = r.inputPayload.length) (hsource : S.R source = r.inputPayload++tail)
    (hpayload : S.R (input.publication.retained 6) = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hsourceOff : source ∉ producer.support) (hpayloadOff : input.publication.retained 6 ∉ producer.support)
    (hresultSource : producer.result ≠ source)
    (hkernel : producer.Ready ([] : List (PackedNormalizedJob A s)) (S.R producer.src) S)
    (C depth : ℕ) (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    ∃ H v' n, ∃ rows : Fin 1 → Fin B → List GaussianInt,
      input.Ready r H ∧ v'.user = v.user ∧
      n ≤ (6*r.inputPayload.length+6)+(timeCost r+(input.timeCost r H+
        (producer.timeCost (U := U) [r]+20*(descriptorScheduleTape producer.work PackedNormalizedJob.words [r]).length+7)+
        (2*(∑ i, (r.words i).length)+651))+retirementCost r)+(2*r.inputPayload.length+2) ∧
      (∀ i j, (rows i j).length = L) ∧ (∀ i : Fin 1, r.ExactRowOutput J (List.ofFn (rows i))) ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        (2*(6*r.inputPayload.length+6)+(stock r+(input.stock r H+
          (31*(descriptorScheduleTape producer.work PackedNormalizedJob.words [r]).length+9+
            (C+1)*producer.workspace (U := U) [r]))))) depth
        (plan.routedRun producer count source saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) producer.result
          ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++S.R producer.result))}) := by
  have hr := hreg
  regs_ne hr
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R source tail)
    (input.publication.retained 6) r.inputPayload)}
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec_within (body := body) count source (input.publication.retained 6) saved tmp
    hreg r.inputPayload tail v S hsource hcount hsaved htmp depth
  simp only [hpayload,List.append_nil] at he₁
  have hframe (k : Fin T) (hk : k ∈ producer.support) : M.R k = S.R k := by
    have hs : k ≠ source := by intro he; exact hsourceOff (he ▸ hk)
    have hp : k ≠ input.publication.retained 6 := by intro he; exact hpayloadOff (he ▸ hk)
    simp [M,hs,hp]
  have hsrcMem : producer.src ∈ producer.support := List.mem_append_right _ (by simp)
  have hk := hkernel.of_frame (F := M) hframe (by intros; rfl)
  obtain ⟨H,v₂,n₂,rows,hheaders,hu₂,hn₂,hlen,hrows,he₂⟩ := plan.run_exec (body := body) producer r
    hsourceReg hworkOff hresultInput hcontrolOff hkernelOff hA t B L ht hp htarget hlocal J hJ hreplicas hcore
    v₁ M hready (by rw [hframe producer.src hsrcMem]; exact hk) C depth hpush hbody
  let output := (List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten
  let F : Stacks T A := {M with R := Function.update M.R producer.result (output++M.R producer.result)}
  have hresultPayload : producer.result ≠ input.publication.retained 6 := by
    intro he
    exact hresultInput (he ▸ input.retained_mem 6)
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body (input.publication.retained 6) v₂ F
  have hlenPayload : (F.R (input.publication.retained 6)).length = r.inputPayload.length := by
    simp [F,M,hresultPayload.symm]
  rw [hlenPayload] at he₃
  have hpref := mn_seq_within_add he₁ he₂
  have hw₃ := mn_native_exec_within he₃ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (by
      simpa only [Nat.zero_mul,Nat.add_zero] using hpref.final)
  have hwhole := (ExecWithin.seq hpref hw₃).seq_assoc
  have hend : {F with R := Function.update F.R (input.publication.retained 6) []} =
      {S with R := Function.update (Function.update S.R source tail) producer.result (output++S.R producer.result)} := by
    congr 1
    funext k
    by_cases hp : k = input.publication.retained 6
    · subst k; simp [F,M,hresultPayload.symm,hpayload,‹source ≠ input.publication.retained 6›.symm]
    · by_cases hr : k = producer.result
      · subst k; simp [F,M,hresultPayload,hresultSource]
      · simp [F,M,hp,hr]
  rw [hend] at hwhole
  refine ⟨H,v₃,(6*r.inputPayload.length+6)+(n₂+(2*r.inputPayload.length+2)),rows,
    hheaders,hu₃.trans (hu₂.trans hu₁),?_,hlen,hrows,?_⟩
  · omega
  · simpa only [routedRun,output,Nat.add_assoc] using hwhole
end SupplierSetupPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
