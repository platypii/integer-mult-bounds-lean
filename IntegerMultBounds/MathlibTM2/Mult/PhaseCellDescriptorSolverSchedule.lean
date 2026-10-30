module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSolverLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorTapeCost
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

def descriptorSolverSchedule (src saved tmp clock savedClock : Fin T) (step : Pr P T Q A U) : Pr P T Q A U :=
  .seq (copyR clock savedClock tmp id)
    (.seq (countedLoop clock step) (.seq (moveR saved src id) (moveR savedClock clock id)))

theorem descriptorSolverSchedule_exec_trace_with_peak_on (work : Fin N → Fin T) (hwork : Function.Injective work) (left : Fin L → Fin N)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
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
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => time r+3)).sum+6*records.length+
        2*(descriptorScheduleTape work words records).length+10 ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
        (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ post records outputs ∧
      ∀ C, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*((records.map stock).sum+6*records.length+2*(descriptorScheduleTape work words records).length+8))
          depth (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(outputs.flatten.length+(records.map stock).foldr max 0+
            6*records.length+2*(descriptorScheduleTape work words records).length+8))
          depth (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  have hsub : [src,saved,count,tmp,spare,result,clock].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg ⊢
    tauto
  have hr := hreg
  regs_ne hr
  have hn (i : Fin N) : work i ≠ src ∧ work i ≠ saved ∧ work i ≠ count ∧ work i ≠ tmp ∧
      work i ≠ spare ∧ work i ≠ result ∧ work i ≠ clock ∧ work i ≠ savedClock := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep i
  have htmp : S.R tmp = [] := hscratch tmp (by simp)
  obtain ⟨v₀,hu₀,he₀⟩ := copyR_exec (body := body) clock savedClock tmp
    ‹clock ≠ savedClock› ‹tmp ≠ clock›.symm ‹tmp ≠ savedClock›.symm id v S htmp
  simp only [List.map_id] at he₀
  let S₀ : Stacks T A := {S with R := Function.update S.R savedClock ((S.R clock).reverse++S.R savedClock)}
  obtain ⟨v₁,n₁,outputs,hu₁,hn₁,he₁,hgood,ht₁⟩ := descriptorSolverLoop_exec_trace_with_peak_on (body := body)
    work hwork left src saved count tmp spare result clock hsub
    (by intro i; simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
        exact ⟨(hn i).1,(hn i).2.1,(hn i).2.2.1,(hn i).2.2.2.1,
          (hn i).2.2.2.2.1,(hn i).2.2.2.2.2.1,(hn i).2.2.2.2.2.2.1⟩)
    words step time stock post records v₀ S₀ hstep rest
    (by intro i; simpa only [S₀,Function.update_of_ne (hn i).2.2.2.2.2.2.2] using hblank i)
    hleft
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with hk | hk | hk
        · subst k; simpa only [S₀,Function.update_of_ne ‹count ≠ savedClock›] using hscratch count (by simp)
        · subst k; simpa only [S₀,Function.update_of_ne ‹tmp ≠ savedClock›] using htmp
        · subst k; simpa only [S₀,Function.update_of_ne ‹spare ≠ savedClock›] using hscratch spare (by simp))
    (by simpa only [S₀,Function.update_of_ne ‹src ≠ savedClock›] using hsource)
    (by simpa only [S₀,Function.update_of_ne ‹clock ≠ savedClock›] using hclock)
  let tape := descriptorScheduleTape work words records
  let S₁ := descriptorLoopFinal work words records src saved result clock rest outputs S₀
  have hs₁ : S₁.R saved = tape.reverse := by
    simp only [S₁,descriptorLoopFinal,Function.update_of_ne ‹saved ≠ clock›,
      Function.update_of_ne ‹saved ≠ result›,Function.update_self,S₀,
      Function.update_of_ne ‹saved ≠ savedClock›,hsaved,List.append_nil,tape]
  obtain ⟨v₂,hu₂,he₂⟩ := restoreDescriptorTape_exec (body := body) src saved ‹src ≠ saved›.symm v₁ S₁ tape hs₁
  let S₂ : Stacks T A := {S₁ with R := Function.update (Function.update S₁.R saved []) src (tape++S₁.R src)}
  have hsc₂ : S₂.R savedClock = (S.R clock).reverse := by
    simp only [S₂,Function.update_of_ne ‹src ≠ savedClock›.symm,Function.update_of_ne ‹saved ≠ savedClock›.symm,
      S₁,descriptorLoopFinal,Function.update_of_ne ‹clock ≠ savedClock›.symm,
      Function.update_of_ne ‹result ≠ savedClock›.symm,S₀,Function.update_self,hsavedClock,List.append_nil]
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body savedClock clock ‹clock ≠ savedClock›.symm id v₂ S₂
  have hfinal : ({S₂ with R := movedR S₂.R savedClock clock id (S₂.R savedClock)} : Stacks T A) =
      {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [movedR,hsc₂,List.map_id,List.reverse_reverse,S₂,S₁,descriptorLoopFinal,S₀,
      Function.update_apply,hsaved,hsavedClock,List.append_nil]
    split_ifs <;> subst_vars <;> simp_all only [List.append_assoc,Ne.symm,ne_self_iff_false,List.reverse_reverse,List.append_nil,tape]
  refine ⟨v₃,(4*(S.R clock).length+4)+(n₁+((2*tape.length+2)+(2*(S₂.R savedClock).length+2))),
    outputs,hu₃.trans (hu₂.trans (hu₁.trans hu₀)),?_,
    (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ he₃))).cast rfl (congrArg (mk v₃) hfinal),hgood,?_⟩
  · rw [hclock,hsc₂,List.length_reverse]
    dsimp only [tape]
    omega
  · have hp : 4*(S.R clock).length+4 ≤ 4*records.length+4 := by rw [hclock]
    have hs : 2*(S₂.R savedClock).length+2 ≤ 2*records.length+2 := by
      rw [hsc₂,List.length_reverse,hclock]
    have htAll := mn_seq_exec_within (mn_bounded_exec_certify he₀ hp)
      (mn_seq_exec_within (fun C hp hb depth => (ht₁ C hp hb depth).1) (mn_seq_exec_within (mn_bounded_exec_certify he₂ le_rfl)
        (mn_bounded_exec_certify he₃ hs)))
    rw [hfinal] at htAll
    have hc : (4*records.length+4)+((records.map stock).sum+
        ((2*tape.length+2)+(2*records.length+2))) =
        (records.map stock).sum+6*records.length+2*tape.length+8 := by ring
    rw [hc] at htAll
    have htPeak : ∀ C, mnProgPush (countedLoop clock step) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+
          (C+1)*(outputs.flatten.length+(records.map stock).foldr max 0))
          depth (countedLoop clock step) (mk v₀ S₀) n₁ (mk v₁ S₁) := by
      intro C hp hb depth
      apply (ht₁ C hp hb depth).2.mono
      intro d z hz
      simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul] at hz ⊢
      omega
    have htPeakAll := mn_seq_exec_within (mn_bounded_exec_certify he₀ hp)
      (mn_seq_exec_within htPeak (mn_seq_exec_within (mn_bounded_exec_certify he₂ le_rfl)
        (mn_bounded_exec_certify he₃ hs)))
    rw [hfinal] at htPeakAll
    have hcPeak : (4*records.length+4)+((outputs.flatten.length+(records.map stock).foldr max 0)+
        ((2*tape.length+2)+(2*records.length+2))) =
        outputs.flatten.length+(records.map stock).foldr max 0+6*records.length+2*tape.length+8 := by omega
    rw [hcPeak] at htPeakAll
    exact fun C hp hb depth => ⟨htAll C hp hb depth, htPeakAll C hp hb depth⟩


theorem descriptorSolverSchedule_exec_trace_on (work : Fin N → Fin T) (hwork : Function.Injective work) (left : Fin L → Fin N)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
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
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => time r+3)).sum+6*records.length+
        2*(descriptorScheduleTape work words records).length+10 ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
        (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ post records outputs ∧
      ∀ C, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*((records.map stock).sum+6*records.length+2*(descriptorScheduleTape work words records).length+8))
          depth (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  obtain ⟨v',n,outputs,hu,hn,he,hgood,ht⟩ := descriptorSolverSchedule_exec_trace_with_peak_on
    work hwork left src saved count tmp spare result clock savedClock hreg hsep words step time stock post
    records v S hstep rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  exact ⟨v',n,outputs,hu,hn,he,hgood,fun C hp hb depth => (ht C hp hb depth).1⟩

theorem descriptorSolverSchedule_exec_trace (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
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
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => time r+3)).sum+6*records.length+
        2*(descriptorScheduleTape work words records).length+10 ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
        (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ post records outputs ∧
      ∀ C, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*((records.map stock).sum+6*records.length+2*(descriptorScheduleTape work words records).length+8))
          depth (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  exact descriptorSolverSchedule_exec_trace_on work hwork familyInverseCoreReg
    src saved count tmp spare result clock savedClock hreg hsep words step time stock post records v S
    hstep rest hblank hleft hscratch hsource hclock hsaved hsavedClock

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
