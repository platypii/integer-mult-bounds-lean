module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealPrefix

/-! Generate the real-projection byte count from retained boundary dimensions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryRealProjection : Pr P 224 Q A U :=
  .seq (unaryProduct 116 160 223 184 217)
    (.seq (realPrefix 223 204 184 217) (uclear 223))

theorem boundaryRealProjection_exec (hA : 4 ≤ A) (w : ℕ) (xs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hcount : (S.R 116).length = xs.length) (hwidth : (S.R 160).length = w)
    (hsrc : S.R 204 = cstream A w xs++tail)
    (h184 : S.R 184 = []) (h217 : S.R 217 = []) (h223 : S.R 223 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ xs.length*(12*w+9)+12 ∧
      Exec body boundaryRealProjection (mk v S) n
        (mk v' {S with R := Function.update S.R 204 (cstream A w (xs.map realPartWord)++tail)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 116) (b := 160) (dst := 223) (t₁ := 184) (t₂ := 217) (by decide) v S h184 h217
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 223 (List.replicate (xs.length*w) tick)}
  have he₁' : Exec body (unaryProduct 116 160 223 184 217) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hcount,hwidth,h223] using he₁
  have hn₁' : n₁ ≤ xs.length*(4*w+9)+4 := by simpa [hcount,hwidth] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := realPrefix_exec (body := body)
    (count := 223) (src := 204) (saved := 184) (tmp := 217) (by decide) v₁ S₁
    (cstream A w xs) tail (by simpa [S₁] using hsrc)
    (by simp [S₁]) (by simpa [S₁] using h184) (by simpa [S₁] using h217)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 204 (cstream A w (xs.map realPartWord)++tail)}
  have he₂' : Exec body (realPrefix 223 204 184 217) (mk v₁ S₁) (6*(xs.length*w)+6) (mk v₂ S₂) := by
    simpa [S₂,realPartSymbol_cstream hA] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 223 v₂ S₂
  have he₃' : Exec body (uclear 223) (mk v₂ S₂) (2*(xs.length*w)+2)
      (mk v₃ {S₂ with R := Function.update S₂.R 223 []}) := by
    simpa [S₂,S₁] using he₃
  refine ⟨v₃,n₁+((6*(xs.length*w)+6)+(2*(xs.length*w)+2)),hu₃.trans (hu₂.trans hu₁),
    by nlinarith only [hn₁'],(Exec.seq he₁' (Exec.seq he₂' he₃')).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi223 : i = 223 <;> by_cases hi204 : i = 204 <;>
    simp [S₂,S₁,hi223,hi204,h223]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
