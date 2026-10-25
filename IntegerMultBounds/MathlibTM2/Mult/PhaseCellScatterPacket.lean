module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherControl

/-! One forward publication step. A delimited gap is preserved in reverse,
the old window is discarded, and the new window joins the saved prefix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def scatterPacket (control savedControl gap window src dst acc trash tmp : Fin T) : Pr P T Q A U :=
  .seq (gatherRead control gap savedControl) <|
  .seq (transfer gap dst acc tmp) <|
  .seq (uclear gap) <|
  .seq (discardPrefix window dst trash tmp) (transfer window src acc tmp)

def scatterUpdate (R : Regs T A) (control savedControl src dst acc : Fin T)
    (ct cs xs ys zs : List (Fin (A+4))) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update R
    control ct) savedControl (cs++R savedControl)) src xs) dst ys) acc (zs++R acc)

theorem scatterUpdate_comp {control savedControl src dst acc : Fin T}
    (hreg : [control,savedControl,src,dst,acc].Nodup) (R : Regs T A)
    (ct cs xs ys zs ct' cs' xs' ys' zs' : List (Fin (A+4))) :
    scatterUpdate (scatterUpdate R control savedControl src dst acc ct cs xs ys zs)
      control savedControl src dst acc ct' cs' xs' ys' zs' =
    scatterUpdate R control savedControl src dst acc ct' (cs'++cs) xs' ys' (zs'++zs) := by
  have hr := hreg
  regs_ne hr
  funext k
  simp only [scatterUpdate, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all only [ne_eq, eq_self, not_false_eq_true, List.append_assoc]

theorem scatterPacket_exec {control savedControl gap window src dst acc trash tmp : Fin T}
    (hreg : [control,savedControl,gap,window,src,dst,acc,trash,tmp].Nodup)
    (d : ℕ) (ctail kept old rest xs tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = List.replicate d tick ++ blank :: ctail)
    (hdst : S.R dst = kept++old++rest) (hsrc : S.R src = xs++tail)
    (hd : kept.length = d) (hw : (S.R window).length = xs.length) (hold : old.length = xs.length)
    (hgap : S.R gap = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (scatterPacket control savedControl gap window src dst acc trash tmp) (mk v S)
        (8*d+10*xs.length+19)
        (mk v' { S with R := (scatterUpdate S.R control savedControl src dst acc ctail
          (blank :: (List.replicate d tick)) tail rest (xs.reverse++kept.reverse)) }) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := gatherRead_exec (body := body)
    (show [control,gap,savedControl].Nodup by regs_nodup) d ctail v S hc
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update (Function.update S.R
    control ctail) gap (List.replicate d tick)) savedControl (blank :: (List.replicate d tick++S.R savedControl))) }
  have he₁' : Exec body (gatherRead control gap savedControl) (mk v S) (2*d+3) (mk v₁ S₁) := by
    simpa [S₁,hgap] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body)
    (show [gap,dst,acc,tmp].Nodup by regs_nodup) v₁ S₁ kept (old++rest)
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₁,List.append_assoc] using hdst)
    (by simp [S₁,‹savedControl ≠ gap›.symm,hd])
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₁,htmp])
  let S₂ : Stacks T A := { S₁ with R := (Function.update (Function.update S₁.R dst (old++rest))
    acc (kept.reverse++S₁.R acc)) }
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body gap v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R gap [] }
  have he₃' : Exec body (uclear gap) (mk v₂ S₂) (2*d+2) (mk v₃ S₃) := by
    simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₃,S₂,S₁] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := discardPrefix_exec (body := body)
    (show [window,dst,trash,tmp].Nodup by regs_nodup) old rest v₃ S₃
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₃,S₂])
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₃,S₂,S₁,hold] using hw)
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₃,S₂,S₁,htrash])
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₃,S₂,S₁,htmp])
  let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R dst rest }
  obtain ⟨v₅,hu₅,he₅⟩ := transfer_exec (body := body)
    (show [window,src,acc,tmp].Nodup by regs_nodup) v₄ S₄ xs tail
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₄,S₃,S₂,S₁] using hsrc)
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₄,S₃,S₂,S₁] using hw)
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₄,S₃,S₂,S₁,htmp])
  refine ⟨v₅,hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
  · rw [hd,hold]; ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [S₄,S₃,S₂,S₁,scatterUpdate,Function.update_apply]
    split_ifs <;> subst_vars <;>
      simp_all only [ne_eq,eq_self,not_false_eq_true,List.append_assoc,List.cons_append]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
