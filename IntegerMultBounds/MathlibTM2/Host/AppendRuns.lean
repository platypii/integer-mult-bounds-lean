module

public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! Sequential restored calls retain their outputs but share one scratch reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U C : Type} {body : P → Pr P T Q A U}

def appendRuns (run : C → Pr P T Q A U) : List C → Pr P T Q A U
  | [] => .act .done
  | c::cs => .seq (run c) (appendRuns run cs)

def maxRunStock (stock : C → ℕ) : List C → ℕ
  | [] => 0
  | c::cs => max (stock c) (maxRunStock stock cs)

theorem mn_appendR_size (v w : HS T Q A U) (S : Stacks T A) (result : Fin T)
    (xs : List (Fin (A+4))) :
    mnSize (mk w {S with R := Function.update S.R result (xs++S.R result)}) = mnSize (mk v S)+xs.length := by
  have h := mn_size_update (mk v S) w (.rt result) (xs++S.R result)
  have h' : mnSize (mk w {S with R := Function.update S.R result (xs++S.R result)})+(S.R result).length =
      mnSize (mk v S)+(xs++S.R result).length := by
    simpa only [mk,update_rt,get_rt] using h
  simp only [List.length_append] at h'
  omega

theorem appendRuns_exec (run : C → Pr P T Q A U) (result : Fin T) (cs : List C)
    (time stock volume : C → ℕ) (Cert : C → List (Fin (A+4)) → Prop) (I : Stacks T A → Prop)
    (hstable : ∀ S xs, I S → I {S with R := Function.update S.R result (xs++S.R result)})
    (depth : ℕ)
    (hrun : ∀ c ∈ cs, ∀ (v : HS T Q A U) (S : Stacks T A), I S →
      ∃ v' n xs, v'.user = v.user ∧ n ≤ time c ∧ xs.length ≤ volume c ∧ Cert c xs ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+stock c) depth
          (run c) (mk v S) n (mk v' {S with R := Function.update S.R result (xs++S.R result)}))
    (v : HS T Q A U) (S : Stacks T A) (hI : I S) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (cs.map time).sum+1 ∧ List.Forall₂ Cert cs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        ((cs.map volume).sum+maxRunStock stock cs)) depth (appendRuns run cs) (mk v S) n
        (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  induction cs generalizing v S with
  | nil =>
    refine ⟨v,1,[],rfl,by simp,.nil,?_⟩
    have he := ExecWithin.act (body := body) (Inv := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      ((([] : List C).map volume).sum+maxRunStock stock [])) (d := depth) .done (mk v S)
      (by simp [maxRunStock]) (by simp [maxRunStock,Action.run])
    simpa [appendRuns,Function.update_eq_self_iff] using he
  | cons c cs ih =>
    obtain ⟨v₁,n₁,xs,hu₁,hn₁,hxs,hcert,he₁⟩ := hrun c (by simp) v S hI
    let H : Stacks T A := {S with R := Function.update S.R result (xs++S.R result)}
    obtain ⟨v₂,n₂,outputs,hu₂,hn₂,hcerts,he₂⟩ := ih
      (by intro c hc; exact hrun c (by simp [hc])) v₁ H (hstable S xs hI)
    have hsize : mnSize (mk v₁ H) = mnSize (mk v S)+xs.length := mn_appendR_size v v₁ S result xs
    let bound := mnSize (mk v S)+depth+
      (((c::cs).map volume).sum+maxRunStock stock (c::cs))
    have hhead : ExecWithin body (fun d z => mnSize z+d ≤ bound) depth (run c) (mk v S) n₁ (mk v₁ H) :=
      he₁.mono (by
        intro d z hz
        have hm : stock c ≤ max (stock c) (maxRunStock stock cs) := le_max_left _ _
        dsimp only [bound]
        simp only [List.map_cons,List.sum_cons,maxRunStock]
        omega)
    have htail := he₂.mono (J := fun d z => mnSize z+d ≤ bound) (by
      intro d z hz
      rw [hsize] at hz
      have hm : maxRunStock stock cs ≤ max (stock c) (maxRunStock stock cs) := le_max_right _ _
      dsimp only [bound]
      simp only [List.map_cons,List.sum_cons,maxRunStock]
      omega)
    have hwhole := ExecWithin.seq hhead htail
    have hout : mk v₂ {H with R := Function.update H.R result (outputs.reverse.flatten++H.R result)} =
        mk v₂ {S with R := Function.update S.R result ((xs::outputs).reverse.flatten++S.R result)} := by
      apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = result
      · subst i; simp [H,List.reverse_cons,List.flatten_append,List.append_assoc]
      · simp [H,hi]
    rw [hout] at hwhole
    refine ⟨v₂,n₁+n₂,xs::outputs,hu₂.trans hu₁,?_,.cons hcert hcerts,hwhole⟩
    simp only [List.map_cons,List.sum_cons]
    omega

end IntegerMultBounds.MathlibTM2.Host
