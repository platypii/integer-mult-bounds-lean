module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSolverCall
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorFinish
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Load a descriptor bank and transport any solver execution and stock certificate to its placement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def descriptorSolverStep (work : Fin 303 → Fin T) (src saved count tmp spare result : Fin T)
    (solve : Pr Empty 303 Q A U) : Pr P T Q A U :=
  .seq (descriptorSolverCall work src saved count tmp spare solve)
    (finishDescriptorBank (List.ofFn work) (work 132) result tmp)

theorem descriptorSolverStep_exec
    (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hresult : result ∉ [src,saved,count,tmp,spare]) (hresultWork : ∀ i, work i ≠ result)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (words : Fin 303 → List (Fin (A+4))) (rest : List (Fin (A+4)))
    (solve : Pr Empty 303 Q A U) (time stock outputSize : ℕ) (post : List (Fin (A+4)) → Prop)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, S.R (work i) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work words)++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = [])
    (hsolve : ∀ vi : HS 303 Q A U, ∃ vf n output, vf.user = vi.user ∧ n ≤ time ∧
      Exec (fun f : Empty => nomatch f) solve (mk vi (descriptorReadyBank work words S)) n
        (mk vf {descriptorReadyBank work words S with R :=
          (Function.update (descriptorReadyBank work words S).R 132 output)}) ∧ post output ∧
      ∀ C, mnProgPush solve ≤ C → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f)
          (fun d z => mnSize z+d ≤ mnSize (mk vi (descriptorReadyBank work words S))+depth+(C+1)*stock)
          depth solve (mk vi (descriptorReadyBank work words S)) n
          (mk vf {descriptorReadyBank work words S with R :=
            (Function.update (descriptorReadyBank work words S).R 132 output)}))
    (hsize : ∀ output, post output → output.length ≤ outputSize) :
    ∃ v' n output, v'.user = v.user ∧
      n ≤ takeDescriptorBankCost (placedDescriptorFields work words)+time+
        (6*outputSize+2*(∑ i, (words i).length)+611) ∧
      Exec body (descriptorSolverStep work src saved count tmp spare result solve) (mk v S) n
        (mk v' (dispatchedDescriptorState work words src saved result rest output S)) ∧ post output ∧
      ∀ C, mnProgPush (descriptorSolverStep (P := P) work src saved count tmp spare result solve) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+stock+
            (6*outputSize+2*(∑ i, (words i).length)+611))) depth
          (descriptorSolverStep work src saved count tmp spare result solve) (mk v S) n
          (mk v' (dispatchedDescriptorState work words src saved result rest output S)) := by
  obtain ⟨v₁,n₁,output,hu₁,hn₁,he₁,hpost,htrace⟩ := descriptorSolverCall_exec (body := body)
    work hwork src saved count tmp spare hreg hsep words rest solve time stock post v S
      hblank hsource hcount htmp hspare hsolve
  have hr := hreg
  regs_ne hr
  have hresultNe : result ≠ src ∧ result ≠ saved ∧ result ≠ count ∧ result ≠ tmp ∧ result ≠ spare := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hresult
  have hfinish : [src,saved,result,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨‹src ≠ saved›,hresultNe.1.symm,‹src ≠ tmp›⟩,
      ⟨hresultNe.2.1.symm,‹saved ≠ tmp›⟩,hresultNe.2.2.2.1,by simp⟩
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := finishPlacedDescriptorBank_exec (body := body) work hwork words
    src saved result tmp hfinish
    (by intro i; have hi := hsep i; simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi ⊢
        exact ⟨hi.1,hi.2.1,hresultWork i,hi.2.2.2.1⟩)
    132 rest output v₁ S hblank htmp
  have hn₂' : n₂ ≤ 6*outputSize+2*(∑ i, (words i).length)+611 := by
    have hlen := hsize output hpost
    omega
  exact ⟨v₂,n₁+n₂,output,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂',Exec.seq he₁ he₂,hpost,
    mn_seq_exec_within htrace (mn_bounded_exec_certify he₂ hn₂')⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
