module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationWidth

/-! Derive cyclic packet dimensions from the solver's retained endpoint rulers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 280 Q A U}

def cyclicNormalizationControls : Pr P 280 Q A U :=
  .seq (generateWordWidth 119 94 4)
    (.seq (ucopy 145 95 7) (.seq (usub 144 95 7) (umul 1 146 95 7)))

theorem cyclicNormalizationControls_exec (q a left right : ℕ)
    (v : HS 280 Q A U) (S : Stacks 280 A)
    (hq : (S.R 119).length = q) (ha : (S.R 144).length = a)
    (hleft : (S.R 145).length = a+left) (hright : (S.R 146).length = right)
    (hfresh : ∀ k ∈ ([(4 : Fin 280),7,94,95]), S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body cyclicNormalizationControls (mk v S) (8*q+4*(2*a+left+right)+21)
        (mk v' {S with R := (Function.update (Function.update S.R 94
          (List.replicate (2*q+8) tick)) 95 (List.replicate (left+right) tick))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body) (by decide) q v S hq
    (hfresh 94 (by simp)) (hfresh 4 (by simp))
  let S₁ : Stacks 280 A := {S with R := Function.update S.R 94 (List.replicate (2*q+8) tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 145) (b := 95) (t := 7)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 7 (by simp))
  let S₂ : Stacks 280 A := {S₁ with R := Function.update S₁.R 95 (List.replicate (a+left) tick)}
  have he₂' : Exec body (ucopy 145 95 7) (mk v₁ S₁) (4*(a+left)+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hleft,hfresh 95 (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := usub_exec body (a := 144) (b := 95) (t := 7)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂,S₁] using hfresh 7 (by simp))
  let S₃ : Stacks 280 A := {S₁ with R := Function.update S₁.R 95 (List.replicate left tick)}
  have he₃' : Exec body (usub 144 95 7) (mk v₂ S₂) (4*a+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,ha] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := umul_exec body 1 (a := 146) (b := 95) (t := 7)
    (by decide) (by decide) (by decide) v₃ S₃ (by simpa [S₃,S₁] using hfresh 7 (by simp))
  have he₄' : Exec body (umul 1 146 95 7) (mk v₃ S₃) (4*right+4)
      (mk v₄ {S₁ with R := Function.update S₁.R 95 (List.replicate (left+right) tick)}) := by
    simpa [S₃,S₁,hright,Nat.add_comm,←List.replicate_add] using he₄
  exact ⟨v₄,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' he₄'))).cast (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
