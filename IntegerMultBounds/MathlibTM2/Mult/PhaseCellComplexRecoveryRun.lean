module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryDescriptorProduction
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryScheduleBudgets
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseDescriptorBank
public import IntegerMultBounds.MathlibTM2.StackInvariantShift

/-! Produce, solve and retire a raw recovery descriptor from ordinary complex
input. All three physical stages contribute to time and simultaneous stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def complexRecoveryRun (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (src saved count tmp spare result clock savedClock : Fin T) : Pr P T Q A U :=
  .seq (complexRecoveryDescriptor work src tmp saved clock)
    (.seq (descriptorSolverSchedule src saved tmp clock savedClock
      (normalizedRecoveryDescriptorStep work src saved count tmp spare result b.hR b.hQ))
      (releaseDescriptorBank src count tmp clock 392))

theorem complexRecoveryRun_exec (b : RawRecoveryProgramBounds Q A U) (r : RawRecoveryJob s)
    (Fs : List (ZMod s → GaussianInt)) (hfields : r.inputFields = complexComponentFields Fs)
    (work : Fin 392 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : embStk work S = complexRecoveryInput r.problem r.W Fs S.inp S.out)
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hclock : S.R clock = []) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    let tape := descriptorBankTape (placedDescriptorFields work (r.words (A := A)))
    let production := prepareComplexRecoveryInputCost r.problem.span r.W Fs.length+13*tape.length+3
    ∃ v' steps outputs, v'.user = v.user ∧
      steps ≤ production+rawRecoveryScheduleTimeBudget b work [r]+(9*tape.length+5) ∧
      List.Forall₂ RawRecoveryJob.output [r] outputs ∧
      Exec body (complexRecoveryRun b work src saved count tmp spare result clock savedClock)
        (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update
          (fun k => if k ∈ List.ofFn work then [] else S.R k) result (outputs.reverse.flatten++S.R result))}) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            work src saved count tmp spare result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          (2*production+(Cprog+1)*rawRecoveryScheduleWorkspaceBudget b work [r]+(9*tape.length+5))) depth
          (complexRecoveryRun b work src saved count tmp spare result clock savedClock)
          (Host.mk v S) steps
          (Host.mk v' {S with R := (Function.update
            (fun k => if k ∈ List.ofFn work then [] else S.R k) result (outputs.reverse.flatten++S.R result))}) := by
  dsimp only
  let tape := descriptorBankTape (placedDescriptorFields work (r.words (A := A)))
  let production := prepareComplexRecoveryInputCost r.problem.span r.W Fs.length+13*tape.length+3
  have hr := hreg
  regs_ne hr
  have hports (i : Fin 392) : work i ≠ src ∧ work i ≠ saved ∧ work i ≠ count ∧ work i ≠ tmp ∧
      work i ≠ spare ∧ work i ≠ result ∧ work i ≠ clock ∧ work i ≠ savedClock := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep i
  have hsmall : [src,tmp,saved,clock].Nodup := by regs_nodup
  have hsepSmall (i : Fin 392) : work i ∉ [src,tmp,saved,clock] := by
    have hi := hports i
    simp_all
  have hoff (k : Fin T) (hk : k ∉ List.ofFn work) :
      (serializedOwnedDescriptorState work src clock tape S).R k =
        Function.update (Function.update S.R src (tape++S.R src)) clock (tick::S.R clock) k := by
    simp only [serializedOwnedDescriptorState,Function.update_apply,hk,ite_false]
  have hnot (k : Fin T) (hk : ∀ i, work i ≠ k) : k ∉ List.ofFn work := by
    intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    exact hk i hi
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,htrace₁⟩ := r.produceDescriptor_exec (body := body) (by have := b.hA; omega)
    Fs hfields work hwork src tmp saved clock hsmall hsepSmall v S hinput
    (hscratch tmp (by simp)) hsaved
  let M := serializedOwnedDescriptorState work src clock tape S
  have hM (k : Fin T) (hk : ∀ i, work i ≠ k) (hs : k ≠ src) (hc : k ≠ clock) : M.R k = S.R k := by
    rw [hoff k (hnot k hk)]
    simp only [Function.update_of_ne hc,Function.update_of_ne hs]
  have hblank (i : Fin 392) : M.R (work i) = [] := by
    simp only [M,serializedOwnedDescriptorState,Function.update_of_ne (hports i).2.2.2.2.2.2.1,
      Function.update_of_ne (hports i).1,List.mem_ofFn.mpr ⟨i,rfl⟩,ite_true]
  have hleft (i : Fin 392) : M.L (work i) = [] :=
    congrArg (fun B : Stacks 392 A => B.L i) hinput
  have hsource : M.R src = descriptorScheduleTape work (RawRecoveryJob.words (A := A)) [r]++S.R src := by
    simp only [M,serializedOwnedDescriptorState,Function.update_of_ne ‹src ≠ clock›,
      Function.update_self,descriptorScheduleTape,List.flatMap_cons,List.flatMap_nil,List.append_nil,tape]
  have hMclock : (M.R clock).length = [r].length := by
    simp only [M,serializedOwnedDescriptorState,Function.update_self,hclock,List.length_cons,List.length_nil]
  obtain ⟨v₂,n₂,outputs,hu₂,hn₂,he₂,hcert,htrace₂⟩ := rawRecoverySchedule_exec (body := body) b
    work hwork src saved count tmp spare result clock savedClock hreg hsep [r] v₁ M (S.R src)
    hblank hleft (by
      intro k hk
      have hne : k ≠ src ∧ k ≠ clock := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl
        all_goals constructor <;> first | assumption | exact Ne.symm (by assumption)
      rw [hM k (by
        intro i
        have hi := hports i
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> tauto) hne.1 hne.2]
      exact hscratch k hk) hsource hMclock
    (by rw [hM saved (fun i => (hports i).2.1) ‹src ≠ saved›.symm ‹saved ≠ clock›]; exact hsaved)
    (by rw [hM savedClock (fun i => (hports i).2.2.2.2.2.2.2) ‹src ≠ savedClock›.symm ‹clock ≠ savedClock›.symm]; exact hsavedClock)
  let N : Stacks T A := {M with R := Function.update M.R result (outputs.reverse.flatten++M.R result)}
  have hN (k : Fin T) (hk : k ≠ result) : N.R k = M.R k := Function.update_of_ne hk _ _
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseDescriptorBank_exec (body := body) work (r.words (A := A))
    src count tmp clock (by regs_nodup) (S.R src) v₂ N
    (by rw [hN src ‹src ≠ result›]; simpa only [descriptorScheduleTape,List.flatMap_cons,List.flatMap_nil,List.append_nil] using hsource)
    (by rw [hN count ‹count ≠ result›,hM count (fun i => (hports i).2.2.1) ‹src ≠ count›.symm ‹count ≠ clock›]; exact hscratch count (by simp))
    (by rw [hN tmp ‹tmp ≠ result›,hM tmp (fun i => (hports i).2.2.2.1) ‹src ≠ tmp›.symm ‹tmp ≠ clock›]; exact hscratch tmp (by simp))
    (by rw [hN clock ‹result ≠ clock›.symm]; simpa using hMclock) 0
  have hresult : M.R result = S.R result := hM result (fun i => (hports i).2.2.2.2.2.1)
    ‹src ≠ result›.symm ‹result ≠ clock›
  have hfinal : {N with R := Function.update (Function.update N.R src (S.R src)) clock []} =
      {S with R := (Function.update (fun k => if k ∈ List.ofFn work then [] else S.R k)
        result (outputs.reverse.flatten++S.R result))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hc : k = clock
    · subst k; simp only [Function.update_self,Function.update_of_ne ‹result ≠ clock›.symm,hnot clock (fun i => (hports i).2.2.2.2.2.2.1),ite_false,hclock]
    by_cases hs : k = src
    · subst k; simp only [Function.update_of_ne hc,Function.update_self,Function.update_of_ne ‹src ≠ result›,
        hnot src (fun i => (hports i).1),ite_false]
    simp only [Function.update_of_ne hc,Function.update_of_ne hs,N,M,serializedOwnedDescriptorState]
    by_cases ho : k = result
    · subst k
      simp only [Function.update_self,Function.update_of_ne hc,Function.update_of_ne hs,
        hnot result (fun i => (hports i).2.2.2.2.2.1),ite_false]
    · simp only [Function.update_of_ne ho,Function.update_of_ne hc,Function.update_of_ne hs]
  rw [hfinal] at he₃
  have he := Exec.seq he₁ (Exec.seq he₂ he₃.toExec)
  refine ⟨v₃,n₁+(n₂+n₃),outputs,hu₃.trans (hu₂.trans hu₁),?_,hcert,he,?_⟩
  · omega
  · intro Cprog hpush hbody depth
    have ht₁ := htrace₁ depth
    have ht₂ := htrace₂ Cprog hpush hbody depth
    have hsize₁ := (htrace₁ 0).final
    have hsize₂ := (htrace₂ Cprog hpush hbody 0).final
    have ht₃ := he₃.shift depth (J := fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
      (2*production+(Cprog+1)*rawRecoveryScheduleWorkspaceBudget b work [r]+(9*tape.length+5))) (by
        intro d z hz
        dsimp only [M,N,production,tape] at hz hsize₁ hsize₂ ⊢
        omega)
    simp only [Nat.zero_add,production,tape,N] at ht₃
    refine .seq (ht₁.mono ?_) (.seq (ht₂.mono ?_) ht₃)
    all_goals
      intro d z hz
      dsimp only [M,N,production,tape] at hz hsize₁ hsize₂ ⊢
      omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
