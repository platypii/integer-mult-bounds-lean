module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginalPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedComponentInputs
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate and release the byte clock for preserving the original complex input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def originalInputClock : Pr P₀ 148 Q A U :=
  .seq (embProg componentReg id couplingHeaderWidth) (unaryProduct 121 94 131 134 135)

theorem originalInputClock_exec (q s : ℕ) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (h94 : S.R 94 = []) (h131 : S.R 131 = [])
    (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 8*q+9+(s*(4*(2*q+8)+9)+4) ∧
      Exec (embTab componentReg body) originalInputClock (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 94 (List.replicate (2*q+8) tick))
          131 (List.replicate (s*(2*q+8)) tick))}) := by
  let w := 2*q+8
  obtain ⟨v₁,hu₁,he₁⟩ := couplingHeaderWidth_exec (body := body) q (embDn componentReg v) (embStk componentReg S)
    (by simpa [embStk,componentReg] using hq) (by simpa [embStk,componentReg] using h94)
    (by simpa [embStk,componentReg] using h135)
  have hbody : ∀ p, (embTab componentReg body) (id p) = embProg componentReg id (body p) := fun _ => rfl
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id) (body' := embTab componentReg body)
    componentReg_injective hbody he₁ v rfl S rfl
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  have he₂' : Exec (embTab componentReg body) (embProg componentReg id couplingHeaderWidth)
      (mk v S) (8*q+9) (mk v₂ S₁) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    rw [embOvr_updR componentReg_injective (embStk componentReg S) S 94 (List.replicate w tick),embOvr_stk]
    rfl
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := unaryProduct_exec (body := embTab componentReg body)
    (a := 121) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v₂ S₁
    (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 131 (List.replicate (s*w) tick)}
  have he₃' : Exec (embTab componentReg body) (unaryProduct 121 94 131 134 135)
      (mk v₂ S₁) n₃ (mk v₃ S₂) := by simpa [S₂,S₁,hs,h131] using he₃
  have hn₃' : n₃ ≤ s*(4*w+9)+4 := by simpa [S₁,hs] using hn₃
  refine ⟨v₃,(8*q+9)+n₃,hu₃.trans (hu₂.trans hu₁),Nat.add_le_add_left hn₃' _,
    Exec.seq he₂' he₃'⟩

def saveOriginalInput : Pr P₀ 148 Q A U :=
  .seq originalInputClock (.seq saveOriginalPrefix (clearWords [94,131]))

def saveOriginalInputCost (q s : ℕ) : ℕ := 16*s*(2*q+8)+9*s+12*q+44

theorem saveOriginalInput_exec (q s : ℕ) (xs tail : List (Fin (A+4)))
    (hlen : xs.length = s*(2*q+8)) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsource : S.R 110 = xs++tail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = [])
    (h134 : S.R 134 = []) (h135 : S.R 135 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ saveOriginalInputCost q s ∧
      Exec (embTab componentReg body) saveOriginalInput (mk v S) n
        (mk v' {S with R := (Function.update S.R 146 (xs++S.R 146))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := originalInputClock_exec (body := body)
    q s v S hq hs h94 h131 h134 h135
  let S₂ : Stacks 148 A := {S with R := (Function.update
    (Function.update S.R 94 (List.replicate (2*q+8) tick))
    131 (List.replicate (s*(2*q+8)) tick))}
  obtain ⟨v₂,hu₂,he₂,_⟩ := saveOriginalPrefix_exec (body := embTab componentReg body)
    xs tail v₁ S₂
    (by simpa [S₂] using hsource)
    (by simp [S₂,hlen]) (by simpa [S₂] using h134) (by simpa [S₂] using h147)
  let S₃ : Stacks 148 A := {S₂ with R := (Function.update S₂.R 146 (xs++S₂.R 146))}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := embTab componentReg body)
    [(94 : Fin 148),131] (by decide) v₂ S₃
  have hsum : ([(94 : Fin 148),131].map (fun r => (S₃.R r).length)).sum =
      (2*q+8)+s*(2*q+8) := by simp [S₃,S₂]
  refine ⟨v₃,n₁+((10*xs.length+10)+(2*((2*q+8)+s*(2*q+8))+5)),
    hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp [saveOriginalInputCost]
    rw [hlen]
    nlinarith only [hn₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h94' : k = 94 <;> by_cases h131' : k = 131 <;>
      simp [S₃,S₂,h94',h131',h94,h131,Function.update_apply]

def restoreOriginalInput : Pr P₀ 148 Q A U :=
  .seq originalInputClock (.seq restoreOriginalPrefix (clearWords [94,131]))

def restoreOriginalInputCost (q s : ℕ) : ℕ := 12*s*(2*q+8)+9*s+12*q+40

theorem restoreOriginalInput_exec (q s : ℕ) (xs savedTail : List (Fin (A+4)))
    (hlen : xs.length = s*(2*q+8)) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsaved : S.R 146 = xs++savedTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = [])
    (h134 : S.R 134 = []) (h135 : S.R 135 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ restoreOriginalInputCost q s ∧
      Exec (embTab componentReg body) restoreOriginalInput (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 146 savedTail) 110 (xs++S.R 110))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := originalInputClock_exec (body := body)
    q s v S hq hs h94 h131 h134 h135
  let S₂ : Stacks 148 A := {S with R := (Function.update
    (Function.update S.R 94 (List.replicate (2*q+8) tick))
    131 (List.replicate (s*(2*q+8)) tick))}
  obtain ⟨v₂,hu₂,he₂⟩ := restoreOriginalPrefix_exec (body := embTab componentReg body)
    xs savedTail v₁ S₂
    (by simpa [S₂] using hsaved)
    (by simp [S₂,hlen]) (by simpa [S₂] using h134) (by simpa [S₂] using h147)
  let S₃ : Stacks 148 A := {S₂ with R := (Function.update (Function.update S₂.R 146 savedTail) 110 (xs++S₂.R 110))}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := embTab componentReg body)
    [(94 : Fin 148),131] (by decide) v₂ S₃
  have hsum : ([(94 : Fin 148),131].map (fun r => (S₃.R r).length)).sum =
      (2*q+8)+s*(2*q+8) := by simp [S₃,S₂]
  refine ⟨v₃,n₁+((6*xs.length+6)+(2*((2*q+8)+s*(2*q+8))+5)),
    hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp [restoreOriginalInputCost]
    rw [hlen]
    nlinarith only [hn₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h94' : k = 94 <;> by_cases h131' : k = 131 <;>
      simp [S₃,S₂,h94',h131',h94,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
