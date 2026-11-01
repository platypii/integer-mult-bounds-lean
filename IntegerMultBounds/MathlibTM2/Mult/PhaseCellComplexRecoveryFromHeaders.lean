module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallComplexRecoveryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexRecoveryRun

/-! Retained ordinary headers and an exposed complex payload execute the full
recovery lifecycle. No prepared-bank or serialized-tape premise remains. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def complexRecoveryFromHeaders (b : RawRecoveryProgramBounds Q A U)
    (source work : Fin 392 → Fin T) (src saved count tmp spare result clock savedClock : Fin T) : Pr P T Q A U :=
  .seq (installComplexRecoveryHeaders source work tmp)
    (complexRecoveryRun b work src saved count tmp spare result clock savedClock)

theorem complexRecoveryFromHeaders_exec (b : RawRecoveryProgramBounds Q A U) (r : RawRecoveryJob s)
    (Fs : List (ZMod s → GaussianInt)) (hfields : r.inputFields = complexComponentFields Fs)
    (work : Fin 392 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (source : Fin 392 → Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i ∈ complexRecoveryHeaderPorts,
      (S.R (source i)).length = complexRecoveryHeader r.problem r.W Fs.length i)
    (hblank : ∀ i, i ≠ 124 → S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hpayload : S.R (work 124) = cstream A r.W (Fs.map (packedInterval r.problem.origin r.problem.span)).flatten)
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hclock : S.R clock = []) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    let headerCost := copyUnaryHeadersCost (fun k => (S.R k).length) (complexRecoveryHeaderCopies source work)
    let tape := descriptorBankTape (placedDescriptorFields work (r.words (A := A)))
    let production := prepareComplexRecoveryInputCost r.problem.span r.W Fs.length+13*tape.length+3
    ∃ v' steps outputs, v'.user = v.user ∧
      steps ≤ headerCost+production+rawRecoveryScheduleTimeBudget b work [r]+(9*tape.length+5) ∧
      List.Forall₂ RawRecoveryJob.output [r] outputs ∧
      Exec body (complexRecoveryFromHeaders b source work src saved count tmp spare result clock savedClock)
        (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update
          (fun k => if k ∈ List.ofFn work then [] else S.R k) result (outputs.reverse.flatten++S.R result))}) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            work src saved count tmp spare result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          (2*headerCost+2*production+(Cprog+1)*rawRecoveryScheduleWorkspaceBudget b work [r]+(9*tape.length+5))) depth
          (complexRecoveryFromHeaders b source work src saved count tmp spare result clock savedClock)
          (Host.mk v S) steps
          (Host.mk v' {S with R := (Function.update
            (fun k => if k ∈ List.ofFn work then [] else S.R k) result (outputs.reverse.flatten++S.R result))}) := by
  dsimp only
  let rs := complexRecoveryHeaderCopies source work
  let headerCost := copyUnaryHeadersCost (fun k => (S.R k).length) rs
  let F : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R rs}
  have hworkTmp (i : Fin 392) : work i ≠ tmp := by
    intro heq
    apply hsep i
    rw [heq]
    simp only [List.mem_cons,eq_self,or_true,true_or]
  obtain ⟨v₁,hu₁,hbank,hframe,he₁,htrace₁⟩ := installComplexRecoveryHeaders_exec (body := body)
    r.problem r.W Fs source work hwork tmp hsourceOff hsourceTmp hworkTmp v S hvalues hblank hleft hpayload
      (hscratch tmp (by simp))
  have hcontrol (k : Fin T) (hk : k ∈ [src,saved,count,tmp,spare,result,clock,savedClock]) : F.R k = S.R k := by
    apply hframe
    intro i heq
    exact hsep i (heq ▸ hk)
  obtain ⟨v₂,steps,outputs,hu₂,hn₂,hcert,he₂,htrace₂⟩ := complexRecoveryRun_exec (body := body) b r Fs hfields
    work hwork src saved count tmp spare result clock savedClock hreg hsep v₁ F hbank
    (by
      intro k hk
      rw [hcontrol k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp only [List.mem_cons,eq_self,or_true,true_or])]
      exact hscratch k hk)
    (by rw [hcontrol clock (by simp)]; exact hclock)
    (by rw [hcontrol saved (by simp)]; exact hsaved)
    (by rw [hcontrol savedClock (by simp)]; exact hsavedClock)
  have hcleared : (fun k => if k ∈ List.ofFn work then [] else F.R k) =
      (fun k => if k ∈ List.ofFn work then [] else S.R k) := by
    funext k
    split_ifs with hk
    · rfl
    · exact hframe k (by intro i heq; exact hk (List.mem_ofFn.mpr ⟨i,heq.symm⟩))
  have hresult : F.R result = S.R result := hcontrol result (by simp)
  have hfinal : {F with R := (Function.update (fun k => if k ∈ List.ofFn work then [] else F.R k)
      result (outputs.reverse.flatten++F.R result))} =
      {S with R := (Function.update (fun k => if k ∈ List.ofFn work then [] else S.R k)
        result (outputs.reverse.flatten++S.R result))} := by
    refine Stacks.ext rfl rfl rfl ?_
    change (Function.update (fun k => if k ∈ List.ofFn work then [] else F.R k)
      result (outputs.reverse.flatten++F.R result) : Regs T A) = _
    rw [hcleared,hresult]
  rw [hfinal] at he₂ htrace₂
  have he := Exec.seq he₁ he₂
  refine ⟨v₂,headerCost+steps,outputs,hu₂.trans hu₁,?_,hcert,he,?_⟩
  · simpa only [Nat.add_assoc] using Nat.add_le_add_left hn₂ headerCost
  · intro Cprog hpush hbody depth
    have ht₁ := htrace₁ depth
    have ht₂ := htrace₂ Cprog hpush hbody depth
    have hsize := (htrace₁ 0).final
    refine .seq (ht₁.mono ?_) (ht₂.mono ?_)
    all_goals
      intro d z hz
      dsimp -failIfUnchanged only [F,headerCost,rs] at hz hsize ⊢
      omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
