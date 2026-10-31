module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposedPackedProducer
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefixStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedProducerLifecycle
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputFrame

/-! Consume one routed supplier batch, run the existing supplier lifecycle,
and erase the local payload without revisiting ambient replica lines. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace SupplierInputPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def routedRun (input : SupplierInputPlan T) (producer : PackedProducerPlan T Q)
    (count source saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takePrefix count source (input.publication.retained 6) saved tmp) (.seq (input.run producer) (uclear (input.publication.retained 6)))

theorem routedRun_exec (input : SupplierInputPlan T) (producer : PackedProducerPlan T Q)
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
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (count source saved tmp : Fin T)
    (hreg : [count,source,input.publication.retained 6,saved,tmp].Nodup)
    (hheaders : input.Ready r (input.payloadState r {S with R := Function.update S.R source tail}))
    (hcount : (S.R count).length = (cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten).length)
    (hsource : S.R source = cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten++tail)
    (hgDst : S.R (input.publication.retained 6) = []) (htakeSaved : S.R saved = []) (htakeTmp : S.R tmp = [])
    (hsourceOff : source ∉ producer.support) (hresultSource : producer.result ≠ source)
    (hpayloadOff : input.publication.retained 6 ∉ producer.support)
    (hblank : ∀ i, S.R (producer.work i) = []) (hleft : ∀ i, S.L (producer.work i) = [])
    (hscratch : ∀ k ∈ [producer.count,producer.tmp,producer.spare], S.R k = [])
    (hclock : S.R producer.clock = []) (hsaved : S.R producer.saved = []) (hsavedClock : S.R producer.savedClock = [])
    (C depth : ℕ) (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    let H := input.payloadState r {S with R := Function.update S.R source tail}
    let tape := descriptorScheduleTape producer.work PackedNormalizedJob.words [r]
    let payload := cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten
    ∃ v' n, ∃ rows : Fin 1 → Fin B → List GaussianInt,
      v'.user = v.user ∧ n ≤ (6*payload.length+6)+
        (input.timeCost r H+(producer.timeCost (U := U) [r]+20*tape.length+7)+
          (2*(∑ i, (r.words i).length)+651))+(2*payload.length+2) ∧
      (∀ i j, (rows i j).length = L) ∧
      (∀ i : Fin 1, r.ExactRowOutput J (List.ofFn (rows i))) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (2*(6*payload.length+6)+(input.stock r H+(31*tape.length+9+(C+1)*producer.workspace (U := U) [r])))) depth
        (input.routedRun producer count source saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) producer.result
          ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++S.R producer.result))}) := by
  dsimp only
  let H := input.payloadState r {S with R := Function.update S.R source tail}
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec_within (body := body) count source (input.publication.retained 6) saved tmp
    hreg (cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten) tail v S hsource hcount htakeSaved htakeTmp depth
  simp only [hgDst,List.append_nil] at he₁
  let n₁ := 6*(cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten).length+6
  have hn₁ : n₁ ≤ n₁ := le_rfl
  have hkFrame (i : Fin T) (hi : i ∈ producer.support) : H.R i = S.R i := by
    have hp : i ≠ input.publication.retained 6 := by intro heq; exact hpayloadOff (heq ▸ hi)
    have hs : i ≠ source := by intro heq; exact hsourceOff (heq ▸ hi)
    simp [H,payloadState,hp,hs]
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
      Host.mk v₃ {S with R := Function.update (Function.update S.R source tail) producer.result (output++S.R producer.result)} := by
    apply congrArg (Host.mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hp : i = input.publication.retained 6
    · subst i; simp [F,H,payloadState,hresultPayload.symm,hgDst,‹source ≠ input.publication.retained 6›.symm]
    by_cases hr : i = producer.result
    · subst i; simp [F,H,payloadState,hresultPayload,hresultSource]
    · simp [F,H,payloadState,hp,hr]
  rw [hout] at hwhole
  refine ⟨v₃,n₁+(n₂+(2*(cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten).length+2)),rows,
    hu₃.trans (hu₂.trans hu₁),?_,hlen,hrows,?_⟩
  · have hb := Nat.add_le_add hn₁ hn₂
    simpa only [n₁,H,Nat.add_assoc] using Nat.add_le_add_right hb
      (2*(cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten).length+2)
  · simpa only [routedRun,n₁,H,output,Nat.add_assoc] using hwhole

end SupplierInputPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
