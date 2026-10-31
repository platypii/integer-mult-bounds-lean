module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerLifecycle

/-! Generate a packed job's actual bank, then execute its descriptor lifecycle
and numerical producer. Ordinary retained headers replace all prepared words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
namespace SupplierInputPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def produce (input : SupplierInputPlan T) (producer : PackedProducerPlan T Q) : Pr P T Q A U :=
  .seq input.program (producer.fromLiveBank input.work)

theorem produce_exec (input : SupplierInputPlan T) (producer : PackedProducerPlan T Q)
    (r : PackedNormalizedJob A s)
    (hsourceReg : ∀ i, [input.work i,producer.src,producer.tmp,producer.saved].Nodup)
    (hworkOff : ∀ i j, producer.work i ≠ input.work j)
    (hresultOff : ∀ i, producer.result ≠ input.work i)
    (hcontrolOff : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock],
      ∀ i, k ≠ input.work i)
    (hA : 96 ≤ A) (t B L : ℕ) [NeZero t] (ht : r.t = t) (hp : 4 ≤ r.p)
    (htarget : r.p+2 ≤ r.targetOut) (hlocal : r.localityTarget = r.targetOut)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1)
    (hreplicas : r.Fs.length = B) (hcore : IntegerMultBounds.NLogN.PhaseCellMatrix.coreLength s r.coreWidth r.k = L)
    (v : HS T Q A U) (S : Stacks T A) (hready : input.Ready r S)
    (hblank : ∀ i, S.R (producer.work i) = []) (hleft : ∀ i, S.L (producer.work i) = [])
    (hscratch : ∀ k ∈ [producer.count,producer.tmp,producer.spare], S.R k = [])
    (hclock : S.R producer.clock = []) (hsaved : S.R producer.saved = []) (hsavedClock : S.R producer.savedClock = [])
    (C depth : ℕ) (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    let tape := descriptorScheduleTape producer.work PackedNormalizedJob.words [r]
    ∃ v' n F, ∃ rows : Fin 1 → Fin B → List GaussianInt,
      v'.user = v.user ∧ n ≤ input.timeCost r S+(producer.timeCost (U := U) [r]+20*tape.length+7) ∧
      (∀ i j, (rows i j).length = L) ∧
      (∀ i : Fin 1, r.ExactRowOutput J (List.ofFn (rows i))) ∧
      (∀ i, F.R (input.work i) = r.words i) ∧
      (∀ i, i ≠ producer.result → (∀ j, i ≠ input.work j) → F.R i = S.R i) ∧ F.L = S.L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (input.stock r S+(31*tape.length+9+(C+1)*producer.workspace (U := U) [r]))) depth
        (input.produce producer) (Host.mk v S) n (Host.mk v' F) ∧
      F.R producer.result =
        (List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++
          S.R producer.result := by
  dsimp only
  obtain ⟨v₁,n₁,H,hu₁,hn₁,hwords,hframe,hL,he₁⟩ := input.exec (body := body) r v S hready depth
  have hcontrol (k : Fin T)
      (hk : k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock]) :
      H.R k = S.R k := hframe k (hcontrolOff k hk)
  obtain ⟨v₂,n₂,rows,hu₂,hn₂,hlen,hrows,he₂⟩ := producer.fromLiveBank_exec (body := body)
    r input.work hsourceReg hA t B L ht hp htarget hlocal J hJ hreplicas hcore v₁ H hwords
    (by intro i; rw [hframe _ (hworkOff i)]; exact hblank i)
    (by intro i; rw [hL]; exact hleft i)
    (by
      intro k hk
      have hk' : k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hcontrol k hk']
      exact hscratch k hk)
    (by rw [hcontrol producer.clock (by simp)]; exact hclock)
    (by rw [hcontrol producer.saved (by simp)]; exact hsaved)
    (by rw [hcontrol producer.savedClock (by simp)]; exact hsavedClock) C depth hpush hbody
  have he₂' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v₁ H)+depth+
      (31*(descriptorScheduleTape producer.work PackedNormalizedJob.words [r]).length+9+
        (C+1)*producer.workspace (U := U) [r])) depth (producer.fromLiveBank input.work) (Host.mk v₁ H) n₂
      (Host.mk v₂ {H with R := (Function.update H.R producer.result
        ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++H.R producer.result))}) := by
    simpa only [Nat.add_assoc] using he₂
  have hwhole := mn_seq_within_add he₁ he₂'
  let F : Stacks T A := {H with R := (Function.update H.R producer.result
    ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++H.R producer.result))}
  refine ⟨v₂,n₁+n₂,F,rows,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hlen,hrows,?_,?_,hL,hwhole,?_⟩
  · intro i
    change Function.update H.R producer.result _ (input.work i) = _
    rw [Function.update_of_ne (hresultOff i).symm,hwords]
  · intro i hi hoff
    change Function.update H.R producer.result _ i = _
    rw [Function.update_of_ne hi,hframe i hoff]
  · change Function.update H.R producer.result _ producer.result = _
    rw [Function.update_self,hframe producer.result hresultOff]

end SupplierInputPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
