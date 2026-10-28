module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorFinish

/-! A structural list proof for counted dispatch over physical descriptor packets. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

def descriptorScheduleTape (work : Fin 303 → Fin T) (words : β → Fin 303 → List (Fin (A+4)))
    (records : List β) : List (Fin (A+4)) :=
  records.flatMap (fun r => descriptorBankTape (placedDescriptorFields work (words r)))

def descriptorLoopFinal (work : Fin 303 → Fin T) (words : β → Fin 303 → List (Fin (A+4)))
    (records : List β) (src saved result clock : Fin T)
    (rest : List (Fin (A+4))) (outputs : List (List (Fin (A+4)))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R src rest)
    saved ((descriptorScheduleTape work words records).reverse++S.R saved))
    result (outputs.reverse.flatten++S.R result)) clock [])}

theorem descriptorListLoop_exec (work : Fin 303 → Fin T)
    (words : β → Fin 303 → List (Fin (A+4)))
    (src saved result clock : Fin T) (hreg : [src,saved,result,clock].Nodup)
    (fresh : List (Fin T)) (hsep : ∀ k ∈ fresh, k ∉ [src,saved,result,clock])
    (L : Fin T → List (Fin (A+4))) (step : Pr P T Q A U) (cost : β → ℕ)
    (good : β → List (Fin (A+4)) → Prop) (records : List β)
    (hstep : ∀ r ∈ records, ∀ (v : HS T Q A U) S rest,
      (∀ k ∈ fresh, S.R k = []) → S.L = L →
      S.R src = descriptorBankTape (placedDescriptorFields work (words r))++rest →
      ∃ v' n output, v'.user = v.user ∧ n ≤ cost r ∧
        Exec body step (mk v S) n (mk v' (dispatchedDescriptorState work (words r) src saved result rest output S)) ∧
        good r output)
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hfresh : ∀ k ∈ fresh, S.R k = []) (hL : S.L = L)
    (hsource : S.R src = descriptorScheduleTape work words records++rest)
    (hclock : (S.R clock).length = records.length) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => cost r+3)).sum+2 ∧
      Exec body (countedLoop clock step) (mk v S) n
        (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) ∧
      List.Forall₂ good records outputs := by
  have hr := hreg
  regs_ne hr
  have hloop : ∀ records : List β,
      (∀ r ∈ records, ∀ (v : HS T Q A U) S rest,
        (∀ k ∈ fresh, S.R k = []) → S.L = L →
        S.R src = descriptorBankTape (placedDescriptorFields work (words r))++rest →
        ∃ v' n output, v'.user = v.user ∧ n ≤ cost r ∧
          Exec body step (mk v S) n (mk v' (dispatchedDescriptorState work (words r) src saved result rest output S)) ∧
          good r output) →
      ∀ (v : HS T Q A U) S rest, (∀ k ∈ fresh, S.R k = []) → S.L = L →
      S.R src = descriptorScheduleTape work words records++rest →
      (S.R clock).length = records.length → v.flag = (S.R clock).head?.isSome →
      ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => cost r+3)).sum+1 ∧
        Exec body (.loop (·.flag) (countedLoopBody clock step)) (mk v S) n
          (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) ∧
        List.Forall₂ good records outputs := by
    intro records
    induction records with
    | nil =>
      intro hs vi Si tail hfresh hL hsource hc hflag
      have hc0 : Si.R clock = [] := List.eq_nil_of_length_eq_zero hc
      have hfinal : descriptorLoopFinal work words [] src saved result clock tail [] Si = Si := by
        simp only [descriptorScheduleTape,List.flatMap_nil,List.nil_append] at hsource
        simp only [descriptorLoopFinal,descriptorScheduleTape,List.flatMap_nil,List.reverse_nil,
          List.flatten_nil,List.nil_append]
        rw [← hsource,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self,
          ← hc0,Function.update_eq_self]
      refine ⟨vi,1,[],rfl,by simp,?_,.nil⟩
      rw [hfinal]
      exact .loop_false (by simpa only [mk_var,hc0,List.head?_nil,Option.isSome_none] using hflag)
    | cons r records ih =>
      intro hs vi Si tail hfresh hL hsource hc hflag
      cases hxs : Si.R clock with
      | nil => simp [hxs] at hc
      | cons tick xs =>
        let S₀ : Stacks T A := {Si with R := Function.update Si.R clock xs}
        have hpop : Exec body (.act (.pop (.rt clock) (fun v _ => v) .done))
            (mk vi Si) 1 (mk vi S₀) := by
          simpa [S₀,Action.run,hxs,update_rt] using
            (Exec.act (body := body) (.pop (.rt clock) (fun v _ => v) .done) (mk vi Si))
        have hne (k : Fin T) (hk : k ∈ fresh) : k ≠ src ∧ k ≠ saved ∧ k ≠ result ∧ k ≠ clock := by
          simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep k hk
        obtain ⟨v₁,n₁,output,hu₁,hn₁,he₁,hgood⟩ := hs r (by simp) vi S₀
          (descriptorScheduleTape work words records++tail)
          (by intro k hk; simpa [S₀,(hne k hk).2.2.2] using hfresh k hk) hL
          (by simpa only [S₀,Function.update_of_ne ‹src ≠ clock›,descriptorScheduleTape,
            List.flatMap_cons,List.append_assoc] using hsource)
        let S₁ := dispatchedDescriptorState work (words r) src saved result
          (descriptorScheduleTape work words records++tail) output S₀
        have hc₁ : S₁.R clock = xs := by
          simp [S₁,dispatchedDescriptorState,S₀,‹src ≠ clock›.symm,
            ‹saved ≠ clock›.symm,‹result ≠ clock›.symm]
        have hpeek := Exec.act (body := body) (peekR clock) (mk v₁ S₁)
        rw [peekR_run] at hpeek
        obtain ⟨v₂,n₂,outputs,hu₂,hn₂,he₂,hgoods⟩ := ih
          (fun r hr => hs r (by simp [hr])) {v₁ with flag := (S₁.R clock).head?.isSome} S₁ tail
          (by intro k hk; simpa [S₁,dispatchedDescriptorState,S₀,(hne k hk).1,
            (hne k hk).2.1,(hne k hk).2.2.1,(hne k hk).2.2.2] using hfresh k hk) hL
          (by simp [S₁,dispatchedDescriptorState,‹src ≠ saved›,‹src ≠ result›])
          (by rw [hc₁]; simp only [hxs,List.length_cons] at hc; omega) rfl
        have hfinal : descriptorLoopFinal work words records src saved result clock tail outputs S₁ =
            descriptorLoopFinal work words (r::records) src saved result clock tail (output::outputs) Si := by
          refine Stacks.ext rfl rfl rfl ?_
          funext k
          simp only [descriptorLoopFinal,descriptorScheduleTape,List.flatMap_cons,List.reverse_append,
            List.reverse_cons,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
            S₁,dispatchedDescriptorState,S₀,Function.update_apply]
          split_ifs <;> subst_vars <;> simp_all only [List.append_assoc,Ne.symm]
        refine ⟨v₂,1+(n₁+1)+n₂+1,output::outputs,hu₂.trans hu₁,?_,?_,.cons hgood hgoods⟩
        · simp only [List.map_cons,List.sum_cons]
          omega
        · exact (Exec.loop_true (by simpa only [mk_var,hxs,List.head?_cons,Option.isSome_some] using hflag)
            (Exec.seq hpop (Exec.seq he₁ hpeek)) he₂).cast rfl (congrArg (mk v₂) hfinal)
  have hpeek := Exec.act (body := body) (peekR clock) (mk v S)
  rw [peekR_run] at hpeek
  obtain ⟨v',n,outputs,hu,hn,he,hgood⟩ := hloop records hstep
    {v with flag := (S.R clock).head?.isSome} S rest hfresh hL hsource hclock rfl
  exact ⟨v',1+n,outputs,hu,by omega,Exec.seq hpeek he,hgood⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
