module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRecoveryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexRecoveryRun

/-! Computed master headers, ordinary seed dimensions and an exposed complex payload execute the full
recovery lifecycle. No prepared-bank or serialized-tape premise remains. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def complexRecoveryFromSeeds (b : RawRecoveryProgramBounds Q A U)
    (source work : Fin 392 → Fin T) (src saved count tmp spare result clock savedClock : Fin T) : Pr P T Q A U :=
  .seq (prepareRecoveryHeaders source work tmp)
    (complexRecoveryRun b work src saved count tmp spare result clock savedClock)

theorem complexRecoveryFromSeeds_exec (b : RawRecoveryProgramBounds Q A U) (r : RawRecoveryJob s)
    (Fs : List (ZMod s → GaussianInt)) (hfields : r.inputFields = complexComponentFields Fs)
    (work : Fin 392 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (source : Fin 392 → Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (source i)).length = recoverySeedHeader r.problem r.W Fs.length i)
    (hblank : ∀ i, i ≠ 124 → S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hpayload : S.R (work 124) = cstream A r.W (Fs.map (packedInterval r.problem.origin r.problem.span)).flatten)
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hclock : S.R clock = []) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    let headerCost := copyUnaryHeadersCost (fun k => (S.R k).length) (recoverySeedHeaderCopies source work)
    let tape := descriptorBankTape (placedDescriptorFields work (r.words (A := A)))
    let production := prepareComplexRecoveryInputCost r.problem.span r.W Fs.length+13*tape.length+3
    ∃ v' steps outputs, v'.user = v.user ∧
      steps ≤ headerCost+completeComplexRecoveryHeadersCost r.problem Fs.length+production+rawRecoveryScheduleTimeBudget b work [r]+(9*tape.length+5) ∧
      List.Forall₂ RawRecoveryJob.output [r] outputs ∧
      Exec body (complexRecoveryFromSeeds b source work src saved count tmp spare result clock savedClock)
        (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update
          (fun k => if k ∈ List.ofFn work then [] else S.R k) result (outputs.reverse.flatten++S.R result))}) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            work src saved count tmp spare result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          (2*headerCost+18*completeComplexRecoveryHeadersCost r.problem Fs.length+2*production+(Cprog+1)*rawRecoveryScheduleWorkspaceBudget b work [r]+(9*tape.length+5))) depth
          (complexRecoveryFromSeeds b source work src saved count tmp spare result clock savedClock)
          (Host.mk v S) steps
          (Host.mk v' {S with R := (Function.update
            (fun k => if k ∈ List.ofFn work then [] else S.R k) result (outputs.reverse.flatten++S.R result))}) := by
  dsimp only
  have hN : r.problem.Fs.length = 2*Fs.length := by
    rw [r.fields,recoveryInputFields_length,hfields,complexComponentFields_length]
  have hworkTmp (i : Fin 392) : work i ≠ tmp := by
    intro heq
    apply hsep i
    rw [heq]
    simp only [List.mem_cons,eq_self,or_true,true_or]
  obtain ⟨v₁,G,n₁,hu₁,hn₁,hbank,hI,hO,hL,hframe,he₁,htrace₁⟩ := prepareRecoveryHeaders_exec (body := body)
    r.problem r.W Fs hN source work hwork tmp hsourceOff hsourceTmp hworkTmp v S
    hvalues hblank hleft hpayload (hscratch tmp (by simp))
  have hcontrol (k : Fin T) (hk : k ∈ [src,saved,count,tmp,spare,result,clock,savedClock]) : G.R k = S.R k := by
    apply hframe
    intro i heq
    exact hsep i (heq ▸ hk)
  obtain ⟨v₂,steps,outputs,hu₂,hn₂,hcert,he₂,htrace₂⟩ := complexRecoveryRun_exec (body := body) b r Fs hfields
    work hwork src saved count tmp spare result clock savedClock hreg hsep v₁ G
    (by simpa only [hI,hO] using hbank)
    (by
      intro k hk
      rw [hcontrol k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp only [List.mem_cons,eq_self,or_true,true_or])]
      exact hscratch k hk)
    (by rw [hcontrol clock (by simp)]; exact hclock)
    (by rw [hcontrol saved (by simp)]; exact hsaved)
    (by rw [hcontrol savedClock (by simp)]; exact hsavedClock)
  have hcleared : (fun k => if k ∈ List.ofFn work then [] else G.R k) =
      (fun k => if k ∈ List.ofFn work then [] else S.R k) := by
    funext k
    split_ifs with hk
    · rfl
    · exact hframe k (by intro i heq; exact hk (List.mem_ofFn.mpr ⟨i,heq.symm⟩))
  have hresult : G.R result = S.R result := hcontrol result (by simp)
  have hfinal : {G with R := (Function.update (fun k => if k ∈ List.ofFn work then [] else G.R k)
      result (outputs.reverse.flatten++G.R result))} =
      {S with R := (Function.update (fun k => if k ∈ List.ofFn work then [] else S.R k)
        result (outputs.reverse.flatten++S.R result))} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hI
    · exact hO
    · exact hL
    · change (Function.update (fun k => if k ∈ List.ofFn work then [] else G.R k)
        result (outputs.reverse.flatten++G.R result) : Regs T A) = _
      rw [hcleared,hresult]
  rw [hfinal] at he₂ htrace₂
  have he := Exec.seq he₁ he₂
  refine ⟨v₂,n₁+steps,outputs,hu₂.trans hu₁,?_,hcert,he,?_⟩
  · simpa only [Nat.add_assoc] using Nat.add_le_add hn₁ hn₂
  · intro Cprog hpush hbody depth
    have ht := mn_seq_within_add (htrace₁ depth) (htrace₂ Cprog hpush hbody depth)
    refine ht.mono ?_
    intro d z hz
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
