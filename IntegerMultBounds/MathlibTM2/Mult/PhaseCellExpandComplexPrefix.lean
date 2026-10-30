module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSplitComponents

/-! Expand a local complex prefix into one real/imaginary RHS batch per key. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def expandComplexPrefix (count src imag saved tmp : Fin T) : Pr P T Q A U :=
  .seq (splitComponentPrefix count src imag saved tmp)
    (.seq (transfer count src saved tmp)
      (.seq (moveR imag tmp id) (.seq (moveR tmp src id) (moveR saved src id))))

/-- Real replicas precede imaginary replicas, each in original order. The later
key suffix is never moved or mapped, and every private stack restores. -/
theorem expandComplexPrefix_exec {count src imag saved tmp : Fin T}
    (hreg : [count,src,imag,saved,tmp].Nodup) (hA : 4 ≤ A)
    (w : ℕ) (zs : List GaussianInt) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w zs++tail) (hcount : (S.R count).length = zs.length*w)
    (himag : S.R imag = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (expandComplexPrefix count src imag saved tmp) (mk v S) (20*(zs.length*w)+20)
        (mk v' {S with R := (Function.update S.R src
          (cstream A w (zs.map realPartWord++zs.map imagPartWord)++tail))}) := by
  have hr := hreg
  regs_ne hr
  let X := cstream A w (zs.map realPartWord)
  let Y := cstream A w (zs.map imagPartWord)
  have hX : X.length = zs.length*w := by simp [X]
  have hY : Y.length = zs.length*w := by simp [Y]
  obtain ⟨v₁,hu₁,he₁⟩ := splitComponentPrefix_exec (body := body) hreg hA w zs tail v S hsrc hcount hsaved htmp
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src (X++tail)) imag Y)}
  have he₁' : Exec body (splitComponentPrefix count src imag saved tmp) (mk v S)
      (10*zs.length*w+10) (mk v₁ S₁) := by simpa [S₁,X,Y,himag] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body)
    (show [count,src,saved,tmp].Nodup by regs_nodup) v₁ S₁ X tail
    (by simp [S₁,‹src ≠ imag›]) (by simpa [S₁,‹count ≠ src›,‹count ≠ imag›,hX] using hcount)
    (by simpa [S₁,‹src ≠ tmp›.symm,‹imag ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := (Function.update (Function.update S₁.R src tail) saved X.reverse)}
  have he₂' : Exec body (transfer count src saved tmp) (mk v₁ S₁) (4*X.length+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,‹src ≠ saved›.symm,‹imag ≠ saved›.symm,hsaved] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) imag tmp ‹imag ≠ tmp› id v₂ S₂
  let S₃ : Stacks T A := {S₂ with R := movedR S₂.R imag tmp id (S₂.R imag)}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec (body := body) tmp src ‹src ≠ tmp›.symm id v₃ S₃
  let S₄ : Stacks T A := {S₃ with R := movedR S₃.R tmp src id (S₃.R tmp)}
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec (body := body) saved src ‹src ≠ saved›.symm id v₄ S₄
  refine ⟨v₅,hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
  · have h₂imag : S₂.R imag = Y := by
      simp [S₂,S₁,‹imag ≠ saved›,‹src ≠ imag›.symm]
    have h₂tmp : S₂.R tmp = [] := by
      simp [S₂,S₁,‹saved ≠ tmp›.symm,‹src ≠ tmp›.symm,‹imag ≠ tmp›.symm,htmp]
    have h₃tmp : S₃.R tmp = Y.reverse := by
      simp [S₃,movedR,h₂imag,h₂tmp]
    have h₄saved : S₄.R saved = X.reverse := by
      simp [S₄,S₃,S₂,movedR,‹src ≠ saved›.symm,‹saved ≠ tmp›,‹imag ≠ saved›.symm]
    rw [h₂imag,h₃tmp,h₄saved]
    simp only [List.length_reverse,hX,hY]
    ring
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    simp only [S₄,S₃,S₂,S₁,movedR,Function.update_apply,List.map_id]
    split_ifs <;> subst_vars <;> simp_all [X,Y,hsaved,himag,htmp,cstream_append,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
