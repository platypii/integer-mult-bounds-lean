module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Count selected symbols while restoring the selector stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def countSelectorStep (dst : Fin T) (f : Fin (A+4) → Bool) : Pr P T Q A U :=
  .cond (fun v => f (v.sym.getD blank)) (.act (pushN dst (fun _ => tick) 1 .done)) (.act .done)

theorem countSelectorStep_exec (dst : Fin T) (f : Fin (A+4) → Bool) (x : Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A) (hsym : v.sym = some x) :
    Exec body (countSelectorStep dst f) (mk v S) 2
      (mk v {S with R := Function.update S.R dst (List.replicate (if f x then 1 else 0) tick++S.R dst)}) := by
  cases hx : f x
  · apply Exec.cond_false (by simp [hsym,hx])
    simpa [hx] using Exec.act (body := body) (.done : Act T Q A U) (mk v S)
  · apply Exec.cond_true (by simp [hsym,hx])
    have he := Exec.act (body := body) (pushN dst (fun _ => tick) 1 .done) (mk v S)
    rw [pushN_run] at he
    simpa [hx,Action.run] using he

def countSelectors (src saved dst : Fin T) (f : Fin (A+4) → Bool) : Pr P T Q A U :=
  .seq (eachSym src saved (countSelectorStep dst f)) (moveR saved src id)

theorem countSelectors_exec {src saved dst : Fin T} (hreg : [src,saved,dst].Nodup)
    (f : Fin (A+4) → Bool) (v : HS T Q A U) (S : Stacks T A) (hsaved : S.R saved = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 7*(S.R src).length+4 ∧
      Exec body (countSelectors src saved dst f) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (List.replicate ((S.R src).filter f).length tick++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  let xs := S.R src
  let Ψ := fun j => Function.update S.R dst (List.replicate ((xs.take j).filter f).length tick++S.R dst)
  have hspec : SymSpec body (countSelectorStep dst f) src saved xs Ψ 2 := by
    intro j hj vi Si hsym hSi
    have he := countSelectorStep_exec (body := body) dst f xs[j] vi Si hsym
    refine ⟨vi,_,2,rfl,le_rfl,he,?_,?_,?_⟩
    · simp [‹src ≠ dst›]
    · simp [‹saved ≠ dst›]
    · intro k hks hkt
      by_cases hk : k = dst
      · subst k
        rw [Function.update_self,hSi dst ‹src ≠ dst›.symm ‹saved ≠ dst›.symm]
        simp only [Ψ,Function.update_self]
        rw [List.take_succ_eq_append_getElem hj,List.filter_append,List.length_append]
        cases hf : f xs[j] <;> simp [hf,List.replicate_succ]
      · rw [Function.update_of_ne hk,hSi k hks hkt]
        simp [Ψ,hk]
  obtain ⟨v₁,R₁,m₁,hu₁,hm₁,he₁,hsrc,hsave,hΨ⟩ := eachSym_exec (body := body)
    ‹src ≠ saved› v S hspec (by intro k hks hkt; simp [Ψ])
  let S₁ : Stacks T A := {S with R := R₁}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body saved src ‹src ≠ saved›.symm id v₁ S₁
  have hsave' : R₁ saved = xs.reverse := by simpa [xs,hsaved] using hsave
  refine ⟨v₂,m₁+(2*xs.length+2),hu₂.trans hu₁,by dsimp only [xs] at *; omega,
    (Exec.seq he₁ he₂).cast (by simp only [S₁,hsave',List.length_reverse]) ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k = src
  · subst k; simp [movedR,S₁,hsrc,hsave',xs,‹src ≠ dst›]
  by_cases ht : k = saved
  · subst k; simp [movedR,S₁,hk,hsaved,‹saved ≠ dst›]
  · simp [movedR,S₁,hk,ht,hΨ k hk ht,Ψ,xs]

end IntegerMultBounds.MathlibTM2.Host
