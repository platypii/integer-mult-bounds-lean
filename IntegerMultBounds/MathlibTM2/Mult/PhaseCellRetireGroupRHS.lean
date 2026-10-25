module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Expose the retained ambient line after one solved group. The symbol count
is generated from retained batch/row/word headers, and all counters are released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

def retireGroupRHS : Pr P 144 Q A U :=
  .seq (unaryProduct 128 130 131 134 135) (.seq (unaryProduct 129 131 136 134 135)
    (.seq (discardPrefix 136 110 137 135) (clearWords [131,136])))

theorem retireGroupRHS_exec (B L w : ℕ) (rhs tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A) (hL : (S.R 128).length = L)
    (hB : (S.R 129).length = B) (hw : (S.R 130).length = w)
    (hsrc : S.R 110 = rhs++tail) (hrhs : rhs.length = B*L*w)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135,136,137], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 12*B*L*w+6*L*w+9*L+9*B+19 ∧
      Exec body retireGroupRHS (mk v S) n (mk v' { S with R := Function.update S.R 110 tail }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := unaryProduct_exec (body := body)
    (a := 128) (b := 130) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S
    (hfresh 134 (by simp)) (hfresh 135 (by simp))
  let S₁ : Stacks 144 A := { S with R := Function.update S.R 131 (List.replicate (L*w) tick) }
  have he₁' : Exec body (unaryProduct 128 130 131 134 135) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁, hL, hw, hfresh 131 (by simp)] using he₁
  have hn₁' : n₁ ≤ L*(4*w+9)+4 := by simpa [hL, hw] using hn₁
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := unaryProduct_exec (body := body)
    (a := 129) (b := 131) (dst := 136) (t₁ := 134) (t₂ := 135) (by decide) v₁ S₁
    (by simpa [S₁] using hfresh 134 (by simp)) (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 144 A := { S₁ with R := Function.update S₁.R 136 (List.replicate (B*L*w) tick) }
  have he₂' : Exec body (unaryProduct 129 131 136 134 135) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂, S₁, hB, hfresh 136 (by simp), Nat.mul_assoc] using he₂
  have hn₂' : n₂ ≤ B*(4*(L*w)+9)+4 := by simpa [S₁, hB] using hn₂
  obtain ⟨v₃, hu₃, he₃⟩ := discardPrefix_exec (body := body)
    (count := 136) (src := 110) (trash := 137) (tmp := 135) (by decide) rhs tail v₂ S₂
    (by simpa [S₂, S₁] using hsrc) (by simp [S₂, hrhs])
    (by simpa [S₂, S₁] using hfresh 137 (by simp)) (by simpa [S₂, S₁] using hfresh 135 (by simp))
  let S₃ : Stacks 144 A := { S₂ with R := Function.update S₂.R 110 tail }
  obtain ⟨v₄, hu₄, he₄⟩ := clearWords_exec (body := body) [(131 : Fin 144),136] (by decide) v₃ S₃
  have hsum : (([(131 : Fin 144),136]).map (fun k => (S₃.R k).length)).sum = L*w+B*L*w := by
    simp [S₃, S₂, S₁]
  refine ⟨v₄, n₁+(n₂+((6*rhs.length+6)+(2*(L*w+B*L*w)+5))), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hsum]; rfl) ?_⟩
  · rw [hrhs]
    nlinarith only [hn₁', hn₂']
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h131 : k = 131
      · subst k; simp [hfresh 131 (by simp)]
      by_cases h136 : k = 136
      · subst k; simp [hfresh 136 (by simp)]
      simp [S₃, S₂, S₁, h131, h136, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
