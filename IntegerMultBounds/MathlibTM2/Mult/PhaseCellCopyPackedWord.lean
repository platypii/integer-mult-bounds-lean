module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyIndexedWord

/-! Restoring indexed access to the packed table, with generated fixed-point word width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def copyPackedWord : Pr P 154 Q A U :=
  .seq (generateWordWidth 119 94 135) (.seq (copyIndexedWord 0 94 132 143 1 2 3 4 5 6) (uclear 94))

def copyPackedWordCost (q i : ℕ) : ℕ :=
  (8*q+9)+(i*(12*(2*q+8)+9)+10*(2*q+8)+22+(2*(2*q+8)+2))

theorem copyPackedWord_exec (q i : ℕ) (xs : List GaussianInt) (hi : i < xs.length)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hindex : (S.R 0).length = i)
    (hsource : S.R 132 = cstream A (2*q+8) xs++tail)
    (h94 : S.R 94 = []) (h135 : S.R 135 = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ copyPackedWordCost q i ∧
      Exec body copyPackedWord (mk v S) m
        (mk v' {S with R := Function.update S.R 143 (csyms A (2*q+8) xs[i]++S.R 143)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (precision := 119) (width := 94) (tmp := 135) (by decide) q v S hq h94 h135
  let w := 2*q+8
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := copyIndexedWord_exec (body := body)
    (index := 0) (width := 94) (src := 132) (dst := 143) (skip := 1)
    (savedSkip := 2) (saved := 3) (tmp := 4) (work₁ := 5) (work₂ := 6) (by decide)
    w i xs hi tail v₁ S₁ (by simpa [S₁] using hindex) (by simp [S₁])
    (by simpa [S₁] using hsource) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₁] using hblank _ (by decide) (by decide))
  let output := csyms A w xs[i]++S.R 143
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 143 output}
  have he₂' : Exec body (copyIndexedWord 0 94 132 143 1 2 3 4 5 6)
      (mk v₁ S₁) m₂ (mk v₂ S₂) := by simpa [S₂,S₁,output] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 94 v₂ S₂
  have hlen : (S₂.R 94).length = w := by simp [S₂,S₁]
  refine ⟨v₃,(8*q+9)+(m₂+(2*w+2)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hm₂ _) _,
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast (by rw [hlen]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk94 : k = 94 <;> by_cases hk132 : k = 143 <;> simp_all [S₂,S₁,output,w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
