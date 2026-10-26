module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentWorkspace

/-! Preserve the borrowed complex input across the two destructive real passes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 148 Q A U}

def saveOriginalPrefix : Pr P₀ 148 Q A U := copyPrefix 131 110 146 147 134

def restoreOriginalPrefix : Pr P₀ 148 Q A U := movePrefix 131 146 110 147 134

theorem saveOriginalPrefix_exec (xs tail : List (Fin (A+4)))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hsource : S.R 110 = xs++tail) (hcount : (S.R 131).length = xs.length)
    (h134 : S.R 134 = []) (h147 : S.R 147 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body saveOriginalPrefix (mk v S) (10*xs.length+10)
        (mk v' {S with R := Function.update S.R 146 (xs++S.R 146)}) ∧
      embStk componentReg {S with R := Function.update S.R 146 (xs++S.R 146)} =
        embStk componentReg S := by
  obtain ⟨v',hu,he⟩ := copyPrefix_exec (body := body)
    (count := 131) (src := 110) (dst := 146) (saved := 147) (tmp := 134)
    (by decide) v S xs tail hsource hcount h147 h134
  exact ⟨v',hu,he,componentProject_updateR S 146 (xs++S.R 146) (by decide)⟩

theorem restoreOriginalPrefix_exec (xs savedTail : List (Fin (A+4)))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hsaved : S.R 146 = xs++savedTail) (hcount : (S.R 131).length = xs.length)
    (h134 : S.R 134 = []) (h147 : S.R 147 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body restoreOriginalPrefix (mk v S) (6*xs.length+6)
        (mk v' {S with R := (Function.update (Function.update S.R 146 savedTail)
          110 (xs++S.R 110))}) :=
  movePrefix_exec (by decide) xs savedTail v S hsaved hcount h147 h134

/-- Any intervening computation may change the output and private banks, provided
it releases the input suffix and retains the saved original prefix and clock. -/
theorem restoreOriginalPrefix_after {work : Pr P₀ 148 Q A U}
    (xs tail savedTail : List (Fin (A+4))) (v v₁ : HS 148 Q A U)
    (S S₁ : Stacks 148 A) (n : ℕ)
    (he : Exec body work (mk v S) n (mk v₁ S₁)) (hu : v₁.user = v.user)
    (hsource : S₁.R 110 = tail) (hsaved : S₁.R 146 = xs++savedTail)
    (hcount : (S₁.R 131).length = xs.length)
    (h134 : S₁.R 134 = []) (h147 : S₁.R 147 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (.seq work restoreOriginalPrefix) (mk v S) (n+(6*xs.length+6))
        (mk v' {S₁ with R := (Function.update (Function.update S₁.R 146 savedTail)
          110 (xs++tail))}) := by
  obtain ⟨v',hu',he'⟩ := restoreOriginalPrefix_exec (body := body)
    xs savedTail v₁ S₁ hsaved hcount h134 h147
  exact ⟨v',hu'.trans hu,by simpa only [hsource] using Exec.seq he he'⟩

/-- Save the original prefix, run an owned-input computation, then restore both
borrowed input and backup tails while preserving the computation's other results. -/
theorem originalPrefix_roundTrip {work : Pr P₀ 148 Q A U}
    (xs tail : List (Fin (A+4))) (v v₁ : HS 148 Q A U)
    (S S₁ : Stacks 148 A) (n : ℕ)
    (hsource : S.R 110 = xs++tail) (hcount : (S.R 131).length = xs.length)
    (h134 : S.R 134 = []) (h147 : S.R 147 = [])
    (hwork : ∀ v₀, v₀.user = v.user →
      Exec body work (mk v₀ {S with R := Function.update S.R 146 (xs++S.R 146)})
        n (mk v₁ S₁))
    (hu : v₁.user = v.user) (hsource₁ : S₁.R 110 = tail)
    (hsaved₁ : S₁.R 146 = xs++S.R 146)
    (hcount₁ : (S₁.R 131).length = xs.length)
    (h134₁ : S₁.R 134 = []) (h147₁ : S₁.R 147 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (.seq saveOriginalPrefix (.seq work restoreOriginalPrefix))
        (mk v S) ((10*xs.length+10)+(n+(6*xs.length+6)))
        (mk v' {S₁ with R := (Function.update (Function.update S₁.R 146 (S.R 146))
          110 (xs++tail))}) := by
  obtain ⟨v₀,hu₀,he₀,_⟩ := saveOriginalPrefix_exec (body := body)
    xs tail v S hsource hcount h134 h147
  obtain ⟨v',hu',he'⟩ := restoreOriginalPrefix_after (body := body)
    xs tail (S.R 146) v₀ v₁
    {S with R := Function.update S.R 146 (xs++S.R 146)} S₁ n
    (hwork v₀ hu₀) (hu.trans hu₀.symm) hsource₁ hsaved₁ hcount₁ h134₁ h147₁
  exact ⟨v',hu'.trans hu₀,Exec.seq he₀ he'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
