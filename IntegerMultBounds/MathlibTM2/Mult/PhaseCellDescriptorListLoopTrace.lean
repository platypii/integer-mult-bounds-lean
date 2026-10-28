module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSchedule
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorFinish

/-! Counted descriptor loops compose proved stock allowances instead of numerical running times. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main

variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

theorem descriptorListLoop_exec_trace (work : Fin 303 → Fin T)
    (words : β → Fin 303 → List (Fin (A+4)))
    (src saved result clock : Fin T) (hreg : [src,saved,result,clock].Nodup)
    (fresh : List (Fin T)) (hsep : ∀ k ∈ fresh, k ∉ [src,saved,result,clock])
    (L : Fin T → List (Fin (A+4))) (step : Pr P T Q A U) (cost stock : β → ℕ)
    (good : β → List (Fin (A+4)) → Prop) (records : List β)
    (hstep : ∀ r ∈ records, ∀ (v : HS T Q A U) S rest,
      (∀ k ∈ fresh, S.R k = []) → S.L = L →
      S.R src = descriptorBankTape (placedDescriptorFields work (words r))++rest →
      ∃ v' n output, v'.user = v.user ∧ n ≤ cost r ∧
        Exec body step (mk v S) n (mk v' (dispatchedDescriptorState work (words r) src saved result rest output S)) ∧
        good r output ∧
        ∀ C, mnProgPush step ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
          ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*stock r)
            depth step (mk v S) n (mk v' (dispatchedDescriptorState work (words r) src saved result rest output S)))
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hfresh : ∀ k ∈ fresh, S.R k = []) (hL : S.L = L)
    (hsource : S.R src = descriptorScheduleTape work words records++rest)
    (hclock : (S.R clock).length = records.length) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => cost r+3)).sum+2 ∧
      Exec body (countedLoop clock step) (mk v S) n
        (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) ∧
      List.Forall₂ good records outputs ∧
      ∀ C, mnProgPush (countedLoop clock step) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*(records.map stock).sum)
          depth (countedLoop clock step) (mk v S) n
          (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) := by
  have hr := hreg
  regs_ne hr
  have hloop : ∀ records : List β,
      (∀ r ∈ records, ∀ (v : HS T Q A U) S rest,
        (∀ k ∈ fresh, S.R k = []) → S.L = L →
        S.R src = descriptorBankTape (placedDescriptorFields work (words r))++rest →
        ∃ v' n output, v'.user = v.user ∧ n ≤ cost r ∧
          Exec body step (mk v S) n (mk v' (dispatchedDescriptorState work (words r) src saved result rest output S)) ∧
          good r output ∧
        ∀ C, mnProgPush step ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
          ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*stock r)
            depth step (mk v S) n (mk v' (dispatchedDescriptorState work (words r) src saved result rest output S))) →
      ∀ (v : HS T Q A U) S rest, (∀ k ∈ fresh, S.R k = []) → S.L = L →
      S.R src = descriptorScheduleTape work words records++rest →
      (S.R clock).length = records.length → v.flag = (S.R clock).head?.isSome →
      ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => cost r+3)).sum+1 ∧
        Exec body (.loop (·.flag) (countedLoopBody clock step)) (mk v S) n
          (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) ∧
        List.Forall₂ good records outputs ∧
        ∀ C, mnProgPush step ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
          ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*(records.map stock).sum)
            depth (.loop (·.flag) (countedLoopBody clock step)) (mk v S) n
            (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) := by
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
      refine ⟨vi,1,[],rfl,by simp,?_,.nil,?_⟩
      · rw [hfinal]
        exact .loop_false (by simpa only [mk_var,hc0,List.head?_nil,Option.isSome_none] using hflag)
      · intro C hp hb depth
        rw [hfinal]
        exact .loop_false (by simpa only [mk_var,hc0,List.head?_nil,Option.isSome_none] using hflag)
          (by simp)
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
        obtain ⟨v₁,n₁,output,hu₁,hn₁,he₁,hgood,ht₁⟩ := hs r (by simp) vi S₀
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
        obtain ⟨v₂,n₂,outputs,hu₂,hn₂,he₂,hgoods,ht₂⟩ := ih
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
        refine ⟨v₂,1+(n₁+1)+n₂+1,output::outputs,hu₂.trans hu₁,?_,?_,.cons hgood hgoods,?_⟩
        · simp only [List.map_cons,List.sum_cons]
          omega
        · exact (Exec.loop_true (by simpa only [mk_var,hxs,List.head?_cons,Option.isSome_some] using hflag)
            (Exec.seq hpop (Exec.seq he₁ hpeek)) he₂).cast rfl (congrArg (mk v₂) hfinal)
        · intro C hp hb depth
          have htPop₀ := mn_native_exec_within hpop 0 (by simp [mnNativePushBound,mnActPush]) 0
            (mnSize (mk vi Si)) (by simp)
          have hsize₀ : mnSize (mk vi S₀) ≤ mnSize (mk vi Si) := by simpa using htPop₀.final
          have hsize₁ : mnSize (mk v₁ S₁) ≤ mnSize (mk vi Si)+(C+1)*stock r := by
            have hh := (ht₁ C hp hb 0).final
            simp only [Nat.add_zero] at hh
            change mnSize (mk v₁ S₁) ≤ mnSize (mk vi S₀)+(C+1)*stock r at hh
            omega
          let B := mnSize (mk vi Si)+depth+(C+1)*((r::records).map stock).sum
          have hpopBound := mn_native_exec_within hpop 0
            (by simp [mnNativePushBound,mnActPush]) depth B (by dsimp only [B]; omega)
          have hbodyBound : ExecWithin body (fun d z => mnSize z+d ≤ B) depth step
              (mk vi S₀) n₁ (mk v₁ S₁) := by
            apply (ht₁ C hp hb depth).mono
            intro d z hz
            change mnSize z+d ≤ mnSize (mk vi Si)+depth+(C+1)*(stock r+(records.map stock).sum)
            nlinarith only [hz,hsize₀,Nat.zero_le ((C+1)*(records.map stock).sum)]
          have hpeekBound := mn_native_exec_within hpeek 0
            (by simp [peekR,mnNativePushBound,mnActPush]) depth B (by
              change mnSize (mk v₁ S₁)+depth ≤ mnSize (mk vi Si)+depth+(C+1)*(stock r+(records.map stock).sum)
              nlinarith only [hsize₁,Nat.zero_le ((C+1)*(records.map stock).sum)])
          have htailBound : ExecWithin body (fun d z => mnSize z+d ≤ B) depth
              (.loop (·.flag) (countedLoopBody clock step))
              (mk {v₁ with flag := (S₁.R clock).head?.isSome} S₁) n₂
              (mk v₂ (descriptorLoopFinal work words records src saved result clock tail outputs S₁)) := by
            apply (ht₂ C hp hb depth).mono
            intro d z hz
            change mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+(C+1)*(records.map stock).sum at hz
            change mnSize z+d ≤ mnSize (mk vi Si)+depth+(C+1)*(stock r+(records.map stock).sum)
            nlinarith only [hz,hsize₁]
          have htOut := ExecWithin.loop_true
            (by simpa only [mk_var,hxs,List.head?_cons,Option.isSome_some] using hflag)
            (.seq hpopBound (.seq hbodyBound hpeekBound)) htailBound
          rw [hfinal] at htOut
          exact htOut
  have hpeek := Exec.act (body := body) (peekR clock) (mk v S)
  rw [peekR_run] at hpeek
  obtain ⟨v',n,outputs,hu,hn,he,hgood,ht⟩ := hloop records hstep
    {v with flag := (S.R clock).head?.isSome} S rest hfresh hL hsource hclock rfl
  refine ⟨v',1+n,outputs,hu,by omega,Exec.seq hpeek he,hgood,?_⟩
  intro C hp hb depth
  have hpStep : mnProgPush step ≤ C := by
    simpa only [countedLoop,countedLoopBody,mnProgPush,peekR,mnActPush,Nat.zero_max,Nat.max_zero] using hp
  have htPeek := mn_native_exec_within hpeek 0
    (by simp [peekR,mnNativePushBound,mnActPush]) depth
    (mnSize (mk v S)+depth+(C+1)*(records.map stock).sum) (by omega)
  exact .seq htPeek (ht C hpStep hb depth)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
