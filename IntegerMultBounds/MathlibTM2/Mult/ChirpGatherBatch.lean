module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherLoop

/-! # Restore the complete overlapping-window sweep

One output reversal and one move for each saved prefix restore every working stack.
The cost charges each copied window and the total source advance, rather than a
fresh traversal of the source for each block.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem gatherFits_sum_le (L : ℕ) (E : List (Fin (A + 4))) (ds : List ℕ)
    (hfit : GatherFits L E ds) : ds.sum ≤ E.length := by
  induction ds generalizing E with
  | nil => simp
  | cons d ds ih =>
    have hrest := ih (E.drop d) hfit.2.2
    simp only [List.length_drop] at hrest
    simp only [List.sum_cons]
    have := hfit.2.1
    omega

def gatherBatch (dst control savedControl advance window src acc current savedSource buf tmp : Fin T) :
    Pr P T Q A U :=
  .seq (.act (peekR control)) <|
  .seq (.loop (·.flag) (gatherLoopBody control savedControl advance window src acc current savedSource buf tmp)) <|
  .seq (moveR acc dst id) <|
  .seq (moveR savedControl control id) (moveR savedSource src id)

/-- Execute all overlapping copies; only the destination stack changes. -/
theorem gatherBatch_exec {dst control savedControl advance window src acc current savedSource buf tmp : Fin T}
    (hreg : [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp].Nodup)
    (L : ℕ) (ds : List ℕ) (E : List (Fin (A + 4))) (hfit : GatherFits L E ds)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A ds) (hs : S.R src = E) (hw : (S.R window).length = L)
    (hclean : ∀ k ∈ [savedControl, advance, acc, current, savedSource, buf, tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (gatherBatch dst control savedControl advance window src acc current savedSource buf tmp)
        (mk v S) (ds.length * (14 * L + 25) + 12 * ds.sum + 8)
        (mk v' { S with R := Function.update S.R dst (gatherRows L E ds ++ S.R dst) }) := by
  have hloop := (List.nodup_cons.mp hreg).2
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := gatherLoop_exec (body := body) hloop L ds E hfit
    { v with flag := (gatherControls A ds).head?.isSome } S hc hs hw
    (fun k hk => hclean k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; tauto)) rfl
  let S₁ : Stacks T A := { S with R := (gatherUpdate S.R control savedControl src savedSource acc []
    (gatherControls A ds).reverse (E.drop ds.sum) (E.take ds.sum).reverse (gatherRows L E ds).reverse) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body acc dst ‹dst ≠ acc›.symm id v₁ S₁
  let S₂ : Stacks T A := { S₁ with R := movedR S₁.R acc dst id (S₁.R acc) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body savedControl control ‹control ≠ savedControl›.symm id v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := movedR S₂.R savedControl control id (S₂.R savedControl) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body savedSource src ‹src ≠ savedSource›.symm id v₃ S₃
  have hc0 : S.R savedControl = [] := hclean _ (by simp)
  have ha0 : S.R acc = [] := hclean _ (by simp)
  have hs0 : S.R savedSource = [] := hclean _ (by simp)
  have hsum := gatherFits_sum_le L E ds hfit
  have hrows := length_gatherRows L E ds hfit
  have hp := Exec.act (body := body) (peekR control) (mk v S)
  rw [peekR_run, hc] at hp
  refine ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq hp (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)))).cast ?_ ?_⟩
  · simp (disch := first | assumption | (apply Ne.symm; assumption))
      [S₃, S₂, S₁, gatherUpdate, movedR, hc0, ha0, hs0, hrows]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ he₄ hp hu₁ hu₂ hu₃ hu₄ hclean
    funext k
    by_cases hdst : k = dst
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₃, S₂, S₁, gatherUpdate, movedR, hc0, ha0, hs0]
    by_cases hcontrol : k = control
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₃, S₂, S₁, gatherUpdate, movedR, hc0, ha0, hs0, hc]
    by_cases hsavedControl : k = savedControl
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₃, S₂, S₁, gatherUpdate, movedR, hc0, ha0, hs0]
    by_cases hsrc : k = src
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₃, S₂, S₁, gatherUpdate, movedR, hc0, ha0, hs0, hs]
    by_cases hacc : k = acc
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₃, S₂, S₁, gatherUpdate, movedR, hc0, ha0, hs0]
    by_cases hsavedSource : k = savedSource
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₃, S₂, S₁, gatherUpdate, movedR, hc0, ha0, hs0]
    simp (disch := first | assumption | (apply Ne.symm; assumption))
      [S₃, S₂, S₁, gatherUpdate, movedR]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
