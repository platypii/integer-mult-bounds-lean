module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSolverStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseCallerWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoopTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoop

/-! The executed numerical descriptor loop carries every per-step stock certificate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {N L T Q A : ℕ} {P U ρ : Type} {body : P → Pr P T Q A U}

theorem descriptorSolverLoop_exec_trace_with_peak_on (work : Fin N → Fin T) (_hwork : Function.Injective work) (left : Fin L → Fin N)
    (src saved count tmp spare result clock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock])
    (words : ρ → Fin N → List (Fin (A+4))) (step : Pr P T Q A U)
    (time stock : ρ → ℕ) (post : ρ → List (Fin (A+4)) → Prop)
    (records : List ρ) (v : HS T Q A U) (S : Stacks T A)
    (hstep : ∀ r ∈ records, ∀ (vi : HS T Q A U) (Si : Stacks T A) (tail : List (Fin (A+4))),
      (∀ i, Si.R (work i) = []) → (∀ i, Si.L (work (left i)) = []) →
      Si.R src = descriptorBankTape (placedDescriptorFields work (words r))++tail →
      Si.R count = [] → Si.R tmp = [] → Si.R spare = [] →
      ∃ vf n output, vf.user = vi.user ∧ n ≤ time r ∧
        Exec body step (mk vi Si) n
          (mk vf (dispatchedDescriptorState work (words r) src saved result tail output Si)) ∧ post r output ∧
        ∀ C, mnProgPush step ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
          ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi Si)+depth+(C+1)*stock r)
            depth step (mk vi Si) n
            (mk vf (dispatchedDescriptorState work (words r) src saved result tail output Si)))
    (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (left i)) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work words records++rest)
    (hclock : (S.R clock).length = records.length) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => time r+3)).sum+2 ∧
      Exec body (countedLoop clock step) (mk v S) n
        (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) ∧
      List.Forall₂ post records outputs ∧
      ∀ C, mnProgPush (countedLoop clock step) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*(records.map stock).sum)
          depth (countedLoop clock step) (mk v S) n
          (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          outputs.flatten.length+(C+1)*(records.map stock).foldr max 0)
          depth (countedLoop clock step) (mk v S) n
          (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) := by
  have houter : [src,saved,result,clock].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg ⊢
    tauto
  have hr := hreg
  regs_ne hr
  have hn (i : Fin N) : work i ≠ src ∧ work i ≠ saved ∧ work i ≠ count ∧
      work i ≠ tmp ∧ work i ≠ spare ∧ work i ≠ result ∧ work i ≠ clock := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep i
  let fresh := List.ofFn work ++ [count,tmp,spare]
  have hcontrol : ∀ k ∈ [count,tmp,spare], k ∉ [src,saved,result,clock] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with hk | hk | hk
    · subst k
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨‹src ≠ count›.symm,‹saved ≠ count›.symm,‹count ≠ result›,‹count ≠ clock›⟩
    · subst k
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨‹src ≠ tmp›.symm,‹saved ≠ tmp›.symm,‹tmp ≠ result›,‹tmp ≠ clock›⟩
    · subst k
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨‹src ≠ spare›.symm,‹saved ≠ spare›.symm,‹spare ≠ result›,‹spare ≠ clock›⟩
  have hfresh : ∀ k ∈ fresh, k ∉ [src,saved,result,clock] := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨(hn i).1,(hn i).2.1,(hn i).2.2.2.2.2.1,(hn i).2.2.2.2.2.2⟩
    · exact hcontrol k hk
  have hcountFresh : count ∈ fresh := List.mem_append_right _ (by simp)
  have htmpFresh : tmp ∈ fresh := List.mem_append_right _ (by simp)
  have hspareFresh : spare ∈ fresh := List.mem_append_right _ (by simp)
  apply descriptorListLoop_exec_trace_with_peak work words src saved result clock houter fresh hfresh S.L
    step time stock post records ?_ v S rest ?_ rfl hsource hclock
  · intro r hm vi Si tail hf hL hs
    exact hstep r hm vi Si tail
      (fun i => hf (work i) (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))
      (by intro i; rw [hL]; exact hleft i) hs
      (hf count hcountFresh) (hf tmp htmpFresh) (hf spare hspareFresh)
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
      exact hblank i
    · exact hscratch k hk


theorem descriptorSolverLoop_exec_trace_on (work : Fin N → Fin T) (_hwork : Function.Injective work) (left : Fin L → Fin N)
    (src saved count tmp spare result clock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock])
    (words : ρ → Fin N → List (Fin (A+4))) (step : Pr P T Q A U)
    (time stock : ρ → ℕ) (post : ρ → List (Fin (A+4)) → Prop)
    (records : List ρ) (v : HS T Q A U) (S : Stacks T A)
    (hstep : ∀ r ∈ records, ∀ (vi : HS T Q A U) (Si : Stacks T A) (tail : List (Fin (A+4))),
      (∀ i, Si.R (work i) = []) → (∀ i, Si.L (work (left i)) = []) →
      Si.R src = descriptorBankTape (placedDescriptorFields work (words r))++tail →
      Si.R count = [] → Si.R tmp = [] → Si.R spare = [] →
      ∃ vf n output, vf.user = vi.user ∧ n ≤ time r ∧
        Exec body step (mk vi Si) n
          (mk vf (dispatchedDescriptorState work (words r) src saved result tail output Si)) ∧ post r output ∧
        ∀ C, mnProgPush step ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
          ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi Si)+depth+(C+1)*stock r)
            depth step (mk vi Si) n
            (mk vf (dispatchedDescriptorState work (words r) src saved result tail output Si)))
    (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (left i)) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work words records++rest)
    (hclock : (S.R clock).length = records.length) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => time r+3)).sum+2 ∧
      Exec body (countedLoop clock step) (mk v S) n
        (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) ∧
      List.Forall₂ post records outputs ∧
      ∀ C, mnProgPush (countedLoop clock step) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*(records.map stock).sum)
          depth (countedLoop clock step) (mk v S) n
          (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) := by
  obtain ⟨v',n,outputs,hu,hn,he,hgood,ht⟩ := descriptorSolverLoop_exec_trace_with_peak_on
    work _hwork left src saved count tmp spare result clock hreg hsep words step time stock post
    records v S hstep rest hblank hleft hscratch hsource hclock
  exact ⟨v',n,outputs,hu,hn,he,hgood,fun C hp hb depth => (ht C hp hb depth).1⟩

theorem descriptorSolverLoop_exec_trace (work : Fin 303 → Fin T) (_hwork : Function.Injective work)
    (src saved count tmp spare result clock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock])
    (words : ρ → Fin 303 → List (Fin (A+4))) (step : Pr P T Q A U)
    (time stock : ρ → ℕ) (post : ρ → List (Fin (A+4)) → Prop)
    (records : List ρ) (v : HS T Q A U) (S : Stacks T A)
    (hstep : ∀ r ∈ records, ∀ (vi : HS T Q A U) (Si : Stacks T A) (tail : List (Fin (A+4))),
      (∀ i, Si.R (work i) = []) → (∀ i, Si.L (work (familyInverseCoreReg i)) = []) →
      Si.R src = descriptorBankTape (placedDescriptorFields work (words r))++tail →
      Si.R count = [] → Si.R tmp = [] → Si.R spare = [] →
      ∃ vf n output, vf.user = vi.user ∧ n ≤ time r ∧
        Exec body step (mk vi Si) n
          (mk vf (dispatchedDescriptorState work (words r) src saved result tail output Si)) ∧ post r output ∧
        ∀ C, mnProgPush step ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
          ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi Si)+depth+(C+1)*stock r)
            depth step (mk vi Si) n
            (mk vf (dispatchedDescriptorState work (words r) src saved result tail output Si)))
    (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work words records++rest)
    (hclock : (S.R clock).length = records.length) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => time r+3)).sum+2 ∧
      Exec body (countedLoop clock step) (mk v S) n
        (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) ∧
      List.Forall₂ post records outputs ∧
      ∀ C, mnProgPush (countedLoop clock step) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*(records.map stock).sum)
          depth (countedLoop clock step) (mk v S) n
          (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) := by
  exact descriptorSolverLoop_exec_trace_on work _hwork familyInverseCoreReg
    src saved count tmp spare result clock hreg hsep words step time stock post records v S
    hstep rest hblank hleft hscratch hsource hclock

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
