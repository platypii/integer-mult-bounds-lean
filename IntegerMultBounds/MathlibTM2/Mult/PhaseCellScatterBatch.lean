module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterLoop

/-! Restore the forward publication sweep with one prefix reversal. Only the
consumed solution stream and overwritten ambient output change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def scatterBatch (control savedControl gap window src dst acc trash tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR control)) <|
  .seq (.loop (·.flag) (scatterLoopBody control savedControl gap window src dst acc trash tmp)) <|
  .seq (moveR acc dst id) (moveR savedControl control id)

theorem scatterBatch_exec {control savedControl gap window src dst acc trash tmp : Fin T}
    (hreg : [control,savedControl,gap,window,src,dst,acc,trash,tmp].Nodup)
    (L : ℕ) (ds : List ℕ) (E X : List (Fin (A+4)))
    (hf : ScatterFits L E ds) (hx : ds.length*L ≤ X.length)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A ds) (hdst : S.R dst = E) (hsrc : S.R src = X)
    (hw : (S.R window).length = L)
    (hclean : ∀ k ∈ [savedControl,gap,acc,trash,tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (scatterBatch control savedControl gap window src dst acc trash tmp) (mk v S)
        (ds.length*(12*L+23)+12*ds.sum+6)
        (mk v' { S with R := (Function.update (Function.update S.R src (X.drop (ds.length*L)))
          dst (scatterRows L E X ds)) }) := by
  have hr := hreg
  regs_ne hr
  have hsc : S.R savedControl = [] := hclean _ (by simp)
  have ha : S.R acc = [] := hclean _ (by simp)
  obtain ⟨v₁,hu₁,he₁⟩ := scatterLoop_exec (body := body) hreg L ds E X hf hx
    { v with flag := (gatherControls A ds).head?.isSome } S hc hdst hsrc hw
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hclean _ (by simp)) rfl
  let S₁ : Stacks T A := { S with R := (scatterUpdate S.R control savedControl src dst acc []
    (gatherControls A ds).reverse (X.drop (ds.length*L)) (E.drop (scatterVolume L ds))
    (scatterPrefix L E X ds).reverse) }
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body acc dst ‹dst ≠ acc›.symm id v₁ S₁
  let S₂ : Stacks T A := { S₁ with R := movedR S₁.R acc dst id (S₁.R acc) }
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body savedControl control ‹control ≠ savedControl›.symm id v₂ S₂
  have hp := Exec.act (body := body) (peekR control) (mk v S)
  rw [peekR_run,hc] at hp
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),
    (Exec.seq hp (Exec.seq he₁ (Exec.seq he₂ he₃))).cast ?_ ?_⟩
  · simp (disch := first | assumption | (apply Ne.symm; assumption))
      [S₂,S₁,scatterUpdate,movedR,hsc,ha,length_scatterPrefix L E X ds hf hx,
        length_gatherControls,scatterVolume]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ hp hclean
    funext k
    by_cases hkc : k = control
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₂,S₁,scatterUpdate,movedR,hsc,ha,hc]
    by_cases hksc : k = savedControl
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₂,S₁,scatterUpdate,movedR,hsc,ha]
    by_cases hks : k = src
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₂,S₁,scatterUpdate,movedR,hsc,ha]
    by_cases hkd : k = dst
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₂,S₁,scatterUpdate,movedR,hsc,ha,scatterRows]
    by_cases hka : k = acc
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₂,S₁,scatterUpdate,movedR,hsc,ha]
    simp [S₂,S₁,scatterUpdate,movedR,hkc,hksc,hks,hkd,hka]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
