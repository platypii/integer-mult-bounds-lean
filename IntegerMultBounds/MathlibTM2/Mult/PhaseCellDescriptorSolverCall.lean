module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorBank
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Load a descriptor bank and transport any solver execution and stock certificate to its placement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast
variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def descriptorSolverCall (work : Fin N → Fin T) (src saved count tmp spare : Fin T)
    (solve : Pr Empty N Q A U) : Pr P T Q A U :=
  .seq (takePlacedDescriptorBank work src saved count tmp spare)
    (embProg work (Empty.elim : Empty → P) solve)

/-- Load and execute a solver whose private bank may change arbitrarily.
Its complete postcondition and intermediate-stock certificate are transported
through the placement; complementary register stacks remain in the background. -/
theorem descriptorSolverCall_exec_bank
    (work : Fin N → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (words : Fin N → List (Fin (A+4))) (rest : List (Fin (A+4)))
    (solve : Pr Empty N Q A U) (time stock : ℕ) (post : Stacks N A → Prop)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, S.R (work i) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work words)++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = [])
    (hsolve : ∀ vi : HS N Q A U, ∃ vf F n, vf.user = vi.user ∧ n ≤ time ∧
      Exec (fun f : Empty => nomatch f) solve (mk vi (descriptorReadyBank work words S)) n (mk vf F) ∧ post F ∧
      ∀ C, mnProgPush solve ≤ C → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f)
          (fun d z => mnSize z+d ≤ mnSize (mk vi (descriptorReadyBank work words S))+depth+(C+1)*stock)
          depth solve (mk vi (descriptorReadyBank work words S)) n (mk vf F)) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ takeDescriptorBankCost (placedDescriptorFields work words)+time ∧
      Exec body (descriptorSolverCall work src saved count tmp spare solve) (mk v S) n
        (mk v' (embOvr work F.get (placedDescriptorState work words src saved rest S))) ∧ post F ∧
      ∀ C, mnProgPush (descriptorSolverCall (P := P) work src saved count tmp spare solve) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+stock)) depth
          (descriptorSolverCall work src saved count tmp spare solve) (mk v S) n
          (mk v' (embOvr work F.get (placedDescriptorState work words src saved rest S))) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hload⟩ := takePlacedDescriptorBank_exec (body := body)
    work hwork src saved count tmp spare hreg hsep words v S rest hsource hblank hcount htmp hspare
  let S₁ := placedDescriptorState work words src saved rest S
  have hload' : embStk work S₁ = descriptorReadyBank work words S := hload
  obtain ⟨vi,F,n₂,hui,hn₂,hei,hpost,htrace⟩ := hsolve (embDn work v₁)
  rw [←hload'] at hei htrace
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body) hwork
    (fun f => nomatch f) hei v₁ rfl S₁ rfl
  refine ⟨v₂,F,n₁+n₂,(hu₂.trans hui).trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hpost,?_⟩
  have htBig : ∀ C, mnProgPush (embProg work (Empty.elim : Empty → P) solve) ≤ C →
      (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+(C+1)*stock)
        depth (embProg work (Empty.elim : Empty → P) solve) (mk v₁ S₁) n₂
        (mk v₂ (embOvr work F.get S₁)) := by
    intro C hpC _ depth
    have hpSmall : mnProgPush solve ≤ C := by simpa only [embProg_push] using hpC
    obtain ⟨vf,hvf,huf,ht⟩ := exec_emb_ovr_within_stock work hwork
      (ι := Empty.elim) (body' := body) (fun f => nomatch f)
      (htrace C hpSmall depth) v₁ rfl S₁ rfl
    rw [(ht.toExec.unique he₂).2] at ht
    exact ht
  exact mn_seq_exec_within (mn_bounded_exec_certify he₁ hn₁) htBig

theorem descriptorSolverCall_exec_on
    (work : Fin N → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (words : Fin N → List (Fin (A+4))) (rest : List (Fin (A+4)))
    (solve : Pr Empty N Q A U) (outputReg : Fin N) (time stock : ℕ) (post : List (Fin (A+4)) → Prop)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, S.R (work i) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work words)++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = [])
    (hsolve : ∀ vi : HS N Q A U, ∃ vf n output, vf.user = vi.user ∧ n ≤ time ∧
      Exec (fun f : Empty => nomatch f) solve (mk vi (descriptorReadyBank work words S)) n
        (mk vf {descriptorReadyBank work words S with R :=
          (Function.update (descriptorReadyBank work words S).R outputReg output)}) ∧ post output ∧
      ∀ C, mnProgPush solve ≤ C → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f)
          (fun d z => mnSize z+d ≤ mnSize (mk vi (descriptorReadyBank work words S))+depth+(C+1)*stock)
          depth solve (mk vi (descriptorReadyBank work words S)) n
          (mk vf {descriptorReadyBank work words S with R :=
            (Function.update (descriptorReadyBank work words S).R outputReg output)})) :
    ∃ v' n output, v'.user = v.user ∧ n ≤ takeDescriptorBankCost (placedDescriptorFields work words)+time ∧
      Exec body (descriptorSolverCall work src saved count tmp spare solve) (mk v S) n
        (mk v' {placedDescriptorState work words src saved rest S with R :=
          (Function.update (placedDescriptorState work words src saved rest S).R (work outputReg) output)}) ∧ post output ∧
      ∀ C, mnProgPush (descriptorSolverCall (P := P) work src saved count tmp spare solve) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+stock)) depth
          (descriptorSolverCall work src saved count tmp spare solve) (mk v S) n
          (mk v' {placedDescriptorState work words src saved rest S with R :=
            (Function.update (placedDescriptorState work words src saved rest S).R (work outputReg) output)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hload⟩ := takePlacedDescriptorBank_exec (body := body)
    work hwork src saved count tmp spare hreg hsep words v S rest hsource hblank hcount htmp hspare
  let S₁ := placedDescriptorState work words src saved rest S
  have hload' : embStk work S₁ = descriptorReadyBank work words S := hload
  obtain ⟨vi,n₂,output,hui,hn₂,hei,hpost,htrace⟩ := hsolve (embDn work v₁)
  rw [←hload'] at hei htrace
  obtain ⟨v₂,_,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body) hwork
    (fun f => nomatch f) hei v₁ rfl S₁ rfl
  have hfinal : embOvr work ({embStk work S₁ with R := Function.update (embStk work S₁).R outputReg output}).get S₁ =
      {S₁ with R := Function.update S₁.R (work outputReg) output} := by
    rw [embOvr_updR hwork,embOvr_stk]
  have heOut := he₂.cast rfl (congrArg (mk v₂) hfinal)
  refine ⟨v₂,n₁+n₂,output,(hu₂.trans hui).trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ heOut,hpost,?_⟩
  have htBig : ∀ C, mnProgPush (embProg work (Empty.elim : Empty → P) solve) ≤ C →
      (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+(C+1)*stock)
        depth (embProg work (Empty.elim : Empty → P) solve) (mk v₁ S₁) n₂
        (mk v₂ {S₁ with R := Function.update S₁.R (work outputReg) output}) := by
    intro C hpC _ depth
    have hpSmall : mnProgPush solve ≤ C := by simpa only [embProg_push] using hpC
    obtain ⟨vf,_,_,ht⟩ := exec_emb_ovr_within_stock work hwork
      (ι := Empty.elim) (body' := body) (fun f => nomatch f)
      (htrace C hpSmall depth) v₁ rfl S₁ rfl
    rw [(ht.toExec.unique heOut).2] at ht
    exact ht
  exact mn_seq_exec_within (mn_bounded_exec_certify he₁ hn₁) htBig


/-- Compatibility specialization for the existing inverse-family bank. -/
theorem descriptorSolverCall_exec
    (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (words : Fin 303 → List (Fin (A+4))) (rest : List (Fin (A+4)))
    (solve : Pr Empty 303 Q A U) (time stock : ℕ) (post : List (Fin (A+4)) → Prop)
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
            (Function.update (descriptorReadyBank work words S).R 132 output)})) :
    ∃ v' n output, v'.user = v.user ∧ n ≤ takeDescriptorBankCost (placedDescriptorFields work words)+time ∧
      Exec body (descriptorSolverCall work src saved count tmp spare solve) (mk v S) n
        (mk v' {placedDescriptorState work words src saved rest S with R :=
          (Function.update (placedDescriptorState work words src saved rest S).R (work 132) output)}) ∧ post output ∧
      ∀ C, mnProgPush (descriptorSolverCall (P := P) work src saved count tmp spare solve) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+stock)) depth
          (descriptorSolverCall work src saved count tmp spare solve) (mk v S) n
          (mk v' {placedDescriptorState work words src saved rest S with R :=
            (Function.update (placedDescriptorState work words src saved rest S).R (work 132) output)}) := by
  exact descriptorSolverCall_exec_on work hwork src saved count tmp spare hreg hsep words rest solve 132
    time stock post v S hblank hsource hcount htmp hspare hsolve

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
