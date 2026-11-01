module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorCleanupStock

/-! A certified closed solver's private-stock bound pays collection and complete
cleanup. Loading and restoration reuse the generic descriptor machinery. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast
variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem descriptorBankStep_exec_stock
    (work : Fin N → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result : Fin T) (hreg : [src,saved,count,tmp,spare,result].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result])
    (words : Fin N → List (Fin (A+4))) (rest : List (Fin (A+4))) (output : Fin N)
    (solve : Pr Empty N Q A U) (time stock : ℕ) (post : List (Fin (A+4)) → Prop)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work words)++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = [])
    (hsolve : ∀ vi : HS N Q A U, ∃ vf F n, vf.user = vi.user ∧ n ≤ time ∧
      Exec (fun f : Empty => nomatch f) solve (mk vi (descriptorReadyBank work words S)) n (mk vf F) ∧
      (F.inp = S.inp ∧ F.out = S.out ∧ post (F.R output) ∧ registerBankStock F ≤ stock) ∧
      ∀ C, mnProgPush solve ≤ C → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f)
          (fun d z => mnSize z+d ≤ mnSize (mk vi (descriptorReadyBank work words S))+depth+(C+1)*stock)
          depth solve (mk vi (descriptorReadyBank work words S)) n (mk vf F)) :
    ∃ v' n word, v'.user = v.user ∧
      n ≤ takeDescriptorBankCost (placedDescriptorFields work words)+time+(6*stock+6*N+6) ∧
      Exec body (descriptorBankStep work src saved count tmp spare result output solve) (mk v S) n
        (mk v' (dispatchedDescriptorState work words src saved result rest word S)) ∧ post word ∧
      ∀ C, mnProgPush (descriptorBankStep (P := P) work src saved count tmp spare result output solve) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+stock+(6*stock+6*N+6))) depth
          (descriptorBankStep work src saved count tmp spare result output solve) (mk v S) n
          (mk v' (dispatchedDescriptorState work words src saved result rest word S)) := by
  have hr := hreg
  regs_ne hr
  have hreg' : [src,saved,count,tmp,spare].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg ⊢
    tauto
  have hsep' (i : Fin N) : work i ∉ [src,saved,count,tmp,spare] := by
    have hh := hsep i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hh ⊢
    tauto
  have hresult (i : Fin N) : work i ≠ result := by
    have hh := hsep i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hh
    exact hh.2.2.2.2.2
  have houter : [src,saved,result].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg ⊢
    tauto
  obtain ⟨v',F,n,hu,hn,hex,hp,htrace⟩ := descriptorBankStep_exec_restored (body := body)
    work hwork src saved count tmp spare result hreg' hsep' hresult ‹tmp ≠ result›.symm houter
    words rest output solve time stock (6*stock+6*N+6)
    (fun F => F.inp = S.inp ∧ F.out = S.out ∧ post (F.R output) ∧ registerBankStock F ≤ stock)
    v S hblank hleft hsource hcount htmp hspare hsolve
    (by intro F hf
        have hh := descriptorBankCleanupCost_le_stock output F
        have hb := hf.2.2.2
        omega)
    (by intro F hf; exact ⟨hf.1,hf.2.1⟩)
  exact ⟨v',n,F.R output,hu,hn,hex,hp.2.2.1,htrace⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
