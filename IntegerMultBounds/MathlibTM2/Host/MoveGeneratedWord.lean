module

public import IntegerMultBounds.MathlibTM2.Node.Params

/-! Move a generated word to a fresh retained port and restore its temporary
source to the original blank. Arbitrary word values are supported. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {P U : Type}

theorem moveGeneratedWord_exec (body : P → Pr P T Q A U) (src dst : Fin T) (hne : src ≠ dst)
    (word : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = []) (hdst : S.R dst = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveR src dst id) (mk v {S with R := Function.update S.R src word})
        (2*word.length+2) (mk v' {S with R := Function.update S.R dst word.reverse}) := by
  let M : Stacks T A := {S with R := Function.update S.R src word}
  obtain ⟨v',hu,he⟩ := moveR_exec body src dst hne id v M
  have hlen : M.R src = word := Function.update_self _ _ _
  rw [hlen] at he
  refine ⟨v',hu,?_⟩
  convert he using 1
  congr 1
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hd : i = dst
  · subst i; simp [movedR,M,hdst,hne.symm]
  by_cases hs : i = src
  · subst i; simp [movedR,M,hd,hsrc]
  · simp [movedR,M,hd,hs]

def moveGeneratedPair (a b x y : Fin T) : Pr P T Q A U :=
  .seq (moveR a x id) (moveR b y id)

theorem moveGeneratedPair_exec (body : P → Pr P T Q A U) (a b x y : Fin T)
    (hreg : [a,b,x,y].Nodup) (xs ys : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hblank : S.R a = [] ∧ S.R b = [] ∧ S.R x = [] ∧ S.R y = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveGeneratedPair a b x y)
        (mk v {S with R := Function.update (Function.update S.R a xs) b ys})
        ((2*xs.length+2)+(2*ys.length+2))
        (mk v' {S with R := Function.update (Function.update S.R x xs.reverse) y ys.reverse}) := by
  obtain ⟨ha,hb,hx,hy⟩ := hblank
  have hn : (a ≠ b ∧ a ≠ x ∧ a ≠ y) ∧ (b ≠ x ∧ b ≠ y) ∧ x ≠ y := by
    simpa only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
      List.nodup_nil,not_false_eq_true,and_true] using hreg
  obtain ⟨⟨hab,hax,hay⟩,⟨hbx,hby⟩,hxy⟩ := hn
  let B : Stacks T A := {S with R := Function.update S.R b ys}
  obtain ⟨u,hu,he⟩ := moveGeneratedWord_exec body a x (by assumption) xs v B
    (by simpa [B,Function.update_of_ne (show a ≠ b by assumption)] using ha)
    (by simpa [B,Function.update_of_ne (show x ≠ b from Ne.symm (by assumption))] using hx)
  let C : Stacks T A := {S with R := Function.update S.R x xs.reverse}
  obtain ⟨v',hv,hf⟩ := moveGeneratedWord_exec body b y (by assumption) ys u C
    (by simpa [C,Function.update_of_ne (show b ≠ x by assumption)] using hb)
    (by simpa [C,Function.update_of_ne (show y ≠ x from Ne.symm (by assumption))] using hy)
  have he' : Exec body (moveR a x id)
      (mk v {S with R := Function.update (Function.update S.R a xs) b ys}) (2*xs.length+2)
      (mk u {C with R := Function.update C.R b ys}) := by
    simpa only [B,C,Function.update_comm (show a ≠ b by assumption),
      Function.update_comm (show b ≠ x by assumption)] using he
  exact ⟨v',hv.trans hu,Exec.seq he' hf⟩

end IntegerMultBounds.MathlibTM2.Host
