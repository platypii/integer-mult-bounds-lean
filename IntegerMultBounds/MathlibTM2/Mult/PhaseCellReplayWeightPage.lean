module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightStep

/-! Replay a generated weight page without evaluating its coefficients again. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

/-- Ports 117/118 retain the page and its symbol count; 119/120 are private scratch. -/
def replayWeightPage : Pr P 121 Q A U :=
  .seq (copyPrefix 118 117 110 119 120)
    (.seq (takePrefix 64 110 95 119 120) (takePrefix 64 110 113 119 120))

theorem replayWeightPage_exec (v : HS 121 Q A U) (S : Stacks 121 A)
    (X Y tail : List (Fin (A+4))) (n : ℕ)
    (hX : X.length = n) (hY : Y.length = n)
    (hpage : S.R 117 = X++Y++tail)
    (hcount : (S.R 118).length = 2*n) (hrow : (S.R 64).length = n)
    (h119 : S.R 119 = []) (h120 : S.R 120 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body replayWeightPage (mk v S) (32*n+22)
        (mk v' {S with R := (Function.update (Function.update S.R 95 (X++S.R 95))
          113 (Y++S.R 113))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := copyPrefix_exec (body := body)
    (show [(118 : Fin 121),117,110,119,120].Nodup by decide)
    v S (X++Y) tail (by simpa only [List.append_assoc] using hpage)
    (by simp only [List.length_append,hX,hY]; omega) h119 h120
  let S₁ : Stacks 121 A := {S with R := Function.update S.R 110 ((X++Y)++S.R 110)}
  obtain ⟨v₂,hu₂,he₂⟩ := takePrefix_exec (body := body)
    (show [(64 : Fin 121),110,95,119,120].Nodup by decide)
    v₁ S₁ X (Y++S.R 110) (by simp [S₁,List.append_assoc])
    (by simpa [S₁,hX] using hrow) (by simp [S₁,h119]) (by simp [S₁,h120])
  let S₂ : Stacks 121 A := {S₁ with R := (Function.update (Function.update S₁.R 110
    (Y++S.R 110)) 95 (X++S₁.R 95))}
  obtain ⟨v₃,hu₃,he₃⟩ := takePrefix_exec (body := body)
    (show [(64 : Fin 121),110,113,119,120].Nodup by decide)
    v₂ S₂ Y (S.R 110) (by simp [S₂])
    (by simpa [S₂,S₁,hY] using hrow) (by simp [S₂,S₁,h119]) (by simp [S₂,S₁,h120])
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp only [List.length_append,hX,hY]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h110 : i = 110 <;> by_cases h95 : i = 95 <;> by_cases h113 : i = 113 <;>
      simp [S₂,S₁,Function.update_apply,h110,h95,h113]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
