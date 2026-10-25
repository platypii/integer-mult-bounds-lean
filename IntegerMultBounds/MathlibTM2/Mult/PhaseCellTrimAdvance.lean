module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherLoop

/-! Turn one inter-origin advance into the gap after the previous window.
The original packet is retained for restoration, and only its gap is emitted. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def trimAdvance (control savedControl counter window acc trash tmp : Fin T) : Pr P T Q A U :=
  .seq (gatherRead control counter savedControl) <|
  .seq (discardPrefix window counter trash tmp) <|
  .seq (moveR counter acc id) (.act (.push (.rt acc) (fun _ => blank) .done))

theorem trimAdvance_exec {control savedControl counter window acc trash tmp : Fin T}
    (hreg : [control,savedControl,counter,window,acc,trash,tmp].Nodup)
    (L d : ℕ) (hLd : L ≤ d) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = List.replicate d tick++blank::tail)
    (hw : (S.R window).length = L)
    (hz : ∀ k ∈ [counter,trash,tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (trimAdvance control savedControl counter window acc trash tmp) (mk v S)
        (4*L+4*d+12)
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R control tail)
          savedControl (blank::(List.replicate d tick++S.R savedControl)))
          acc (blank::(List.replicate (d-L) tick++S.R acc))) }) := by
  have hr := hreg
  regs_ne hr
  have hc0 := hz counter (by simp)
  have ht0 := hz trash (by simp)
  have hm0 := hz tmp (by simp)
  obtain ⟨v₁,hu₁,he₁⟩ := gatherRead_exec (body := body)
    (show [control,counter,savedControl].Nodup by regs_nodup) d tail v S hc
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update (Function.update S.R control tail)
    counter (List.replicate d tick)) savedControl (blank::(List.replicate d tick++S.R savedControl))) }
  have he₁' : Exec body (gatherRead control counter savedControl) (mk v S) (2*d+3) (mk v₁ S₁) := by
    simpa [S₁,hc0] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (show [window,counter,trash,tmp].Nodup by regs_nodup)
    (List.replicate L tick) (List.replicate (d-L) tick) v₁ S₁
    (by simp [S₁,‹savedControl ≠ counter›.symm,Nat.add_sub_of_le hLd])
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [S₁] using hw)
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₁,ht0])
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₁,hm0])
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R counter (List.replicate (d-L) tick) }
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body counter acc ‹counter ≠ acc› id v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := movedR S₂.R counter acc id (S₂.R counter) }
  have hp := Exec.act (body := body) (.push (.rt acc) (fun _ => blank) .done) (mk v₃ S₃)
  let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R acc (blank::S₃.R acc) }
  have hp' : Exec body (.act (.push (.rt acc) (fun _ => blank) .done)) (mk v₃ S₃) 1 (mk v₃ S₄) := by
    simpa [S₄,Action.run,update_rt] using hp
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ hp'))).cast ?_ ?_⟩
  · simp only [S₂,Function.update_self,List.length_replicate]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    clear he₁ he₁' he₂ he₃ hp
    simp only [S₄,S₃,S₂,S₁,movedR,List.map_id,Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all only [ne_eq,eq_self,not_false_eq_true,List.reverse_replicate]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
