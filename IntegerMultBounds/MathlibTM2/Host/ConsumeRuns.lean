module

public import IntegerMultBounds.MathlibTM2.Host.AppendRuns
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! Sequential calls consume an owned input stream and retain outputs while
sharing a maximum scratch reserve. Input retirement cannot increase stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U C : Type} {body : P → Pr P T Q A U}

theorem mn_consume_appendR_size_le (v w : HS T Q A U) (S : Stacks T A) (source result : Fin T)
    (hne : source ≠ result) (payload tail xs : List (Fin (A+4))) (hsrc : S.R source = payload++tail) :
    mnSize (mk w {S with R := Function.update (Function.update S.R source tail) result (xs++S.R result)}) ≤
      mnSize (mk v S)+xs.length := by
  let M : Stacks T A := {S with R := Function.update S.R source tail}
  have hm := mn_size_update (mk v S) w (.rt source) tail
  have hm' : mnSize (mk w M)+(S.R source).length = mnSize (mk v S)+tail.length := by
    simpa only [M,mk,update_rt,get_rt] using hm
  rw [hsrc,List.length_append] at hm'
  have hr := mn_appendR_size w w M result xs
  have hresult : M.R result = S.R result := by simp [M,hne.symm]
  rw [hresult] at hr
  change mnSize (mk w {M with R := Function.update M.R result (xs++S.R result)}) ≤ _
  rw [hr]
  omega

theorem consumeRuns_exec (run : C → Pr P T Q A U) (source result : Fin T) (hne : source ≠ result)
    (payload : C → List (Fin (A+4))) (cs : List C) (tail : List (Fin (A+4)))
    (time stock volume : C → ℕ) (Cert : C → List (Fin (A+4)) → Prop) (I : Stacks T A → Prop)
    (hstable : ∀ S rest xs, I S → I {S with R := (Function.update (Function.update S.R source rest) result (xs++S.R result))})
    (depth : ℕ)
    (hrun : ∀ c ∈ cs, ∀ (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4))), I S → S.R source = payload c++rest →
      ∃ v' n xs, v'.user = v.user ∧ n ≤ time c ∧ xs.length ≤ volume c ∧ Cert c xs ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+stock c) depth
          (run c) (mk v S) n (mk v' {S with R := Function.update (Function.update S.R source rest) result (xs++S.R result)}))
    (v : HS T Q A U) (S : Stacks T A) (hI : I S) (hsrc : S.R source = cs.flatMap payload++tail) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (cs.map time).sum+1 ∧ List.Forall₂ Cert cs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        ((cs.map volume).sum+maxRunStock stock cs)) depth (appendRuns run cs) (mk v S) n
        (mk v' {S with R := Function.update (Function.update S.R source tail) result (outputs.reverse.flatten++S.R result)}) := by
  induction cs generalizing v S with
  | nil =>
    refine ⟨v,1,[],rfl,by simp,.nil,?_⟩
    have he := ExecWithin.act (body := body) (Inv := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      ((([] : List C).map volume).sum+maxRunStock stock [])) (d := depth) .done (mk v S)
      (by simp [maxRunStock]) (by simp [maxRunStock,Action.run])
    have htail : S.R source = tail := by simpa using hsrc
    simpa [appendRuns,←htail,Function.update_eq_self_iff] using he
  | cons c cs ih =>
    obtain ⟨v₁,n₁,xs,hu₁,hn₁,hxs,hcert,he₁⟩ := hrun c (by simp) v S (cs.flatMap payload++tail) hI (by simpa only [List.flatMap_cons,List.append_assoc] using hsrc)
    let H : Stacks T A := {S with R := Function.update (Function.update S.R source (cs.flatMap payload++tail)) result (xs++S.R result)}
    obtain ⟨v₂,n₂,outputs,hu₂,hn₂,hcerts,he₂⟩ := ih
      (by intro c hc; exact hrun c (by simp [hc])) v₁ H (hstable S _ xs hI)
      (by simp [H,hne])
    have hsize : mnSize (mk v₁ H) ≤ mnSize (mk v S)+xs.length :=
      mn_consume_appendR_size_le v v₁ S source result hne (payload c) (cs.flatMap payload++tail) xs
        (by simpa only [List.flatMap_cons,List.append_assoc] using hsrc)
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
      have hbound := hsize
      have hm : maxRunStock stock cs ≤ max (stock c) (maxRunStock stock cs) := le_max_right _ _
      dsimp only [bound]
      simp only [List.map_cons,List.sum_cons,maxRunStock]
      omega)
    have hwhole := ExecWithin.seq hhead htail
    have hout : mk v₂ {H with R := Function.update (Function.update H.R source tail) result (outputs.reverse.flatten++H.R result)} =
        mk v₂ {S with R := Function.update (Function.update S.R source tail) result ((xs::outputs).reverse.flatten++S.R result)} := by
      apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = result
      · subst i; simp [H,List.reverse_cons,List.flatten_append,List.append_assoc]
      · by_cases hs : i = source
        · subst i; simp [H,hne]
        · simp [H,hi,hs]
    rw [hout] at hwhole
    refine ⟨v₂,n₁+n₂,xs::outputs,hu₂.trans hu₁,?_,.cons hcert hcerts,hwhole⟩
    simp only [List.map_cons,List.sum_cons]
    omega

end IntegerMultBounds.MathlibTM2.Host
