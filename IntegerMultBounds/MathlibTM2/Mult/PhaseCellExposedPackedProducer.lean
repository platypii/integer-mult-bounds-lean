module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaPayload
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedProducerLifecycle
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputFrame

/-! Gather the actual ambient payload, execute a generated supplier, and erase
its local exposure. The caller supplies ordinary headers and ambient data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace SupplierInputPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

/-- Readiness here checks ordinary headers in the state after payload installation.
It does not assert that the initial physical payload is present. -/
noncomputable def payloadState (input : SupplierInputPlan T) (r : PackedNormalizedJob A s) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update S.R (input.publication.retained 6)
    (cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten))}

noncomputable def exposedRun (input : SupplierInputPlan T) (producer : PackedProducerPlan T Q)
    (e : Fin 117 → Fin T) : Pr P T Q A U :=
  .seq (placedReplicaPayload e) (.seq (input.run producer) (uclear (input.publication.retained 6)))

theorem exposedRun_exec (input : SupplierInputPlan T) (producer : PackedProducerPlan T Q)
    (r : PackedNormalizedJob A s)
    (hsourceReg : ∀ i, [input.work i,producer.src,producer.tmp,producer.saved].Nodup)
    (hworkOff : ∀ i j, producer.work i ≠ input.work j)
    (hresultInput : producer.result ∉ input.support)
    (hcontrolOff : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock],
      ∀ i, k ≠ input.work i)
    (hA : 96 ≤ A) (t B L : ℕ) [NeZero t] (ht : r.t = t) (hp : 4 ≤ r.p)
    (htarget : r.p+2 ≤ r.targetOut) (hlocal : r.localityTarget = r.targetOut)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1)
    (hreplicas : r.Fs.length = B) (hcore : IntegerMultBounds.NLogN.PhaseCellMatrix.coreLength s r.coreWidth r.k = L)
    (v : HS T Q A U) (S : Stacks T A) (hheaders : input.Ready r (input.payloadState r S))
    (e : Fin 117 → Fin T) (he : Function.Injective e) (hdst : e 93 = input.publication.retained 6)
    (replicas : ℕ) (hcount : r.Fs.length = replicas+1) (hLpos : 0 < r.b-r.a)
    (borrowed : List (Fin (A+4)))
    (hgWidth : (S.R (e 94)).length = r.W) (hgPeriod : (S.R (e 97)).length = s)
    (hgOrigin : (S.R (e 111)).length = r.a) (hgLength : (S.R (e 102)).length = r.b-r.a)
    (hgCount : (S.R (e 116)).length = r.Fs.length)
    (hgSource : S.R (e 110) = cstream A r.W (r.Fs.flatMap (chirpLine s))++borrowed)
    (hgDst : S.R (input.publication.retained 6) = [])
    (hgBlank : ∀ k : Fin 117, k.val < 13 → S.R (e k) = [])
    (hgFresh : ∀ k ∈ [(91 : Fin 117),92], S.R (e k) = [])
    (hpayloadOff : input.publication.retained 6 ∉ producer.support)
    (hblank : ∀ i, S.R (producer.work i) = []) (hleft : ∀ i, S.L (producer.work i) = [])
    (hscratch : ∀ k ∈ [producer.count,producer.tmp,producer.spare], S.R k = [])
    (hclock : S.R producer.clock = []) (hsaved : S.R producer.saved = []) (hsavedClock : S.R producer.savedClock = [])
    (C depth : ℕ) (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    let H := input.payloadState r S
    let tape := descriptorScheduleTape producer.work PackedNormalizedJob.words [r]
    let payload := cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten
    ∃ v' n, ∃ rows : Fin 1 → Fin B → List GaussianInt,
      v'.user = v.user ∧ n ≤ rawReplicaPayloadCost r.W s r.a (r.b-r.a) replicas+
        (input.timeCost r H+(producer.timeCost (U := U) [r]+20*tape.length+7)+
          (2*(∑ i, (r.words i).length)+651))+(2*payload.length+2) ∧
      (∀ i j, (rows i j).length = L) ∧
      (∀ i : Fin 1, r.ExactRowOutput J (List.ofFn (rows i))) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (500*(r.Fs.length*s*r.W)+(input.stock r H+(31*tape.length+9+(C+1)*producer.workspace (U := U) [r])))) depth
        (input.exposedRun producer e) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R producer.result
          ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++S.R producer.result))}) := by
  dsimp only
  let H := input.payloadState r S
  have hfit : r.a+(r.b-r.a) ≤ s := by
    have ha := r.bounds.hab
    have hb := r.bounds.hbs
    omega
  have hWpos : 0 < r.W := by have := r.hW; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedReplicaPayload_exec_within (body := body) e he r.Fs replicas r.W r.a (r.b-r.a)
    hcount hWpos hLpos hfit borrowed v S hgWidth hgPeriod hgOrigin hgLength hgCount hgSource
    (by rw [hdst]; exact hgDst) hgBlank hgFresh depth
  rw [hdst] at he₁
  have hkFrame (i : Fin T) (hi : i ∈ producer.support) : H.R i = S.R i := by
    change Function.update S.R (input.publication.retained 6) _ i = _
    have hn : i ≠ input.publication.retained 6 := by intro heq; exact hpayloadOff (heq ▸ hi)
    exact Function.update_of_ne hn _ _
  have hresultPayload : producer.result ≠ input.publication.retained 6 := by
    intro heq
    apply hresultInput
    rw [heq]
    exact input.retained_mem 6
  have hworkMem (i : Fin 325) : producer.work i ∈ producer.support :=
    List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hcontrolMem (i : Fin T)
      (hi : i ∈ [producer.src,producer.saved,producer.count,producer.tmp,producer.spare,producer.clock,producer.savedClock]) :
      i ∈ producer.support := List.mem_append_right _ hi
  obtain ⟨v₂,n₂,rows,hu₂,hn₂,hlen,hrows,he₂⟩ := input.run_exec (body := body) producer r hsourceReg hworkOff
    (by intro i heq; exact hresultInput (heq ▸ input.work_mem i)) hcontrolOff hA t B L ht hp htarget hlocal J hJ hreplicas hcore
    v₁ H hheaders
    (by intro i; rw [hkFrame _ (hworkMem i)]; exact hblank i)
    (by intro i; exact hleft i)
    (by
      intro i hi
      have hm : i ∈ [producer.src,producer.saved,producer.count,producer.tmp,producer.spare,producer.clock,producer.savedClock] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
        rcases hi with rfl | rfl | rfl <;> simp
      rw [hkFrame i (hcontrolMem i hm)]
      exact hscratch i hi)
    (by rw [hkFrame producer.clock (hcontrolMem _ (by simp))]; exact hclock)
    (by rw [hkFrame producer.saved (hcontrolMem _ (by simp))]; exact hsaved)
    (by rw [hkFrame producer.savedClock (hcontrolMem _ (by simp))]; exact hsavedClock) C depth hpush hbody
  let output := (List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten
  let F : Stacks T A := {H with R := Function.update H.R producer.result (output++H.R producer.result)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body (input.publication.retained 6) v₂ F
  have hpayload : (F.R (input.publication.retained 6)).length =
      (cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten).length := by
    simp [F,H,payloadState,hresultPayload.symm]
  rw [hpayload] at he₃
  have hprefix := mn_seq_within_add he₁ he₂
  have hw₃ := mn_native_exec_within he₃ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (by
      simpa only [Nat.zero_mul,Nat.add_zero] using hprefix.final)
  have hwhole := (ExecWithin.seq hprefix hw₃).seq_assoc
  have hout : Host.mk v₃ {F with R := Function.update F.R (input.publication.retained 6) []} =
      Host.mk v₃ {S with R := Function.update S.R producer.result (output++S.R producer.result)} := by
    apply congrArg (Host.mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hp : i = input.publication.retained 6
    · subst i; simp [F,H,payloadState,hresultPayload.symm,hgDst]
    by_cases hr : i = producer.result
    · subst i; simp [F,H,payloadState,hresultPayload]
    · simp [F,H,payloadState,hp,hr]
  rw [hout] at hwhole
  refine ⟨v₃,n₁+(n₂+(2*(cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten).length+2)),rows,
    hu₃.trans (hu₂.trans hu₁),?_,hlen,hrows,?_⟩
  · have hb := Nat.add_le_add hn₁ hn₂
    simpa only [Nat.add_assoc] using Nat.add_le_add_right hb
      (2*(cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten).length+2)
  · simpa only [exposedRun,Nat.add_assoc] using hwhole

end SupplierInputPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
