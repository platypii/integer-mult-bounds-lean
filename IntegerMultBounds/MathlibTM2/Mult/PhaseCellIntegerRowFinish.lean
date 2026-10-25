module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRow

/-! # Release integer-row operands and publish the accumulator

Only owned operand copies are erased. Two symbol moves preserve the result's
low-bit-first encoding in front of the arbitrary existing output suffix.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def finishIntegerRow : Pr P 117 Q A U :=
  .seq (clearWords [cr .xs, cr .ys]) (.seq (moveR 96 106 id) (moveR 106 113 id))

theorem finishIntegerRow_exec (L w : ℕ) (xs as : List GaussianInt) (z : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hx : S.R (cr .xs) = cstream A w xs) (ha : S.R (cr .ys) = cstream A w as)
    (hz : S.R 96 = csyms A w z) (hbuf : S.R 106 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body finishIntegerRow (mk v S) (4 * (L * w) + 4 * w + 9)
        (mk v' { S with R := (Function.update (Function.update (Function.update
          (Function.update S.R (cr .xs) []) (cr .ys) []) 96 []) 113
            (csyms A w z ++ S.R 113)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := clearWords_exec (body := body) [cr .xs, cr .ys] (by decide) v S
  let S₁ : Stacks 117 A := { S with R := fun k => if k ∈ [cr .xs, cr .ys] then [] else S.R k }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body 96 106 (by decide) id v₁ S₁
  let S₂ : Stacks 117 A := { S₁ with R := movedR S₁.R 96 106 id (S₁.R 96) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body 106 113 (by decide) id v₂ S₂
  have hz₁ : S₁.R 96 = csyms A w z := by simpa [S₁, cr, OutputPlacement.code] using hz
  have hb₁ : S₁.R 106 = [] := by simpa [S₁, cr, OutputPlacement.code] using hbuf
  have hb₂ : S₂.R 106 = (csyms A w z).reverse := by simp [S₂, movedR, hz₁, hb₁]
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hz₁, hb₂]
    simp [hx, ha, hxlen, halen, csyms]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hb : k = 106
    · subst k
      simp [S₂, S₁, movedR, cr, OutputPlacement.code, hbuf]
    by_cases ho : k = 113
    · subst k
      simp [S₂, S₁, movedR, cr, OutputPlacement.code, hz, hbuf]
    by_cases hz' : k = 96
    · subst k
      simp [S₂, S₁, movedR, cr, OutputPlacement.code]
    simp only [S₂, S₁, movedR, Function.update_apply, hb, ho, hz', ite_false]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    by_cases hx' : k = cr .xs
    · subst k; simp [cr, OutputPlacement.code]
    by_cases ha' : k = cr .ys
    · subst k; simp [cr, OutputPlacement.code]
    simp [hx', ha']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
