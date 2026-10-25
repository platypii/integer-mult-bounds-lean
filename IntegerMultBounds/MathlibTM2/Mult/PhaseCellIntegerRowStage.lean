module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRow
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Stage an integer generator row from borrowed streams

The row-symbol count is generated from ordinary L/W headers and released.
The borrowed column, factor row and RHS word retain arbitrary suffixes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def stageIntegerRow : Pr P 117 Q A U :=
  .seq (unaryProduct 102 94 99 104 105)
    (.seq (copyPrefix 99 110 (cr .xs) 104 105)
      (.seq (copyPrefix 99 111 (cr .ys) 104 105)
        (.seq (copyPrefix 94 112 96 104 105) (uclear 99))))

def stagedIntegerRow {A : ℕ} (S : Stacks 117 A) (w : ℕ)
    (xs as : List GaussianInt) (rhs : GaussianInt) : Stacks 117 A :=
  { S with R := (Function.update (Function.update (Function.update S.R
    (cr .xs) (cstream A w xs)) (cr .ys) (cstream A w as)) 96 (csyms A w rhs)) }

theorem stageIntegerRow_exec (L w : ℕ) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hw : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w xs ++ tailX) (ha : S.R 111 = cstream A w as ++ tailA)
    (hrhs : S.R 112 = csyms A w rhs ++ tailR)
    (hfresh : ∀ k ∈ [cr .xs, cr .ys, 96, 99, 104, 105], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 26 * (L * w) + 9 * L + 10 * w + 36 ∧
      Exec body stageIntegerRow (mk v S) m (mk v' (stagedIntegerRow S w xs as rhs)) := by
  have hxs : (cstream A w xs).length = L * w := by simp [hxlen]
  have has : (cstream A w as).length = L * w := by simp [halen]
  have hx0 : S.R 84 = [] := by simpa [cr, OutputPlacement.code] using hfresh (cr .xs) (by simp)
  have ha0 : S.R 85 = [] := by simpa [cr, OutputPlacement.code] using hfresh (cr .ys) (by simp)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(102 : Fin 117), 94, 99, 104, 105].Nodup by decide) v S
    (hfresh _ (by simp)) (hfresh _ (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 99 (List.replicate (L * w) tick) }
  have he₁' : Exec body (unaryProduct 102 94 99 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hL, hw, hfresh 99 (by simp), List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := copyPrefix_exec (body := body)
    (show [(99 : Fin 117), 110, cr .xs, 104, 105].Nodup by decide) v₁ S₁
    (cstream A w xs) tailX (by simpa [S₁] using hx) (by simp [S₁, hxs])
    (by simpa [S₁] using hfresh 104 (by simp)) (by simpa [S₁] using hfresh 105 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R (cr .xs) (cstream A w xs) }
  have he₂' : Exec body (copyPrefix 99 110 (cr .xs) 104 105) (mk v₁ S₁)
      (10 * (L * w) + 10) (mk v₂ S₂) := by
    simpa [S₂, S₁, cr, OutputPlacement.code, hx0, hxs] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := copyPrefix_exec (body := body)
    (show [(99 : Fin 117), 111, cr .ys, 104, 105].Nodup by decide) v₂ S₂
    (cstream A w as) tailA (by simpa [S₂, S₁, cr, OutputPlacement.code] using ha)
    (by simp [S₂, S₁, cr, OutputPlacement.code, has])
    (by simpa [S₂, S₁, cr, OutputPlacement.code] using hfresh 104 (by simp))
    (by simpa [S₂, S₁, cr, OutputPlacement.code] using hfresh 105 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R (cr .ys) (cstream A w as) }
  have he₃' : Exec body (copyPrefix 99 111 (cr .ys) 104 105) (mk v₂ S₂)
      (10 * (L * w) + 10) (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, cr, OutputPlacement.code, ha0, has] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := copyPrefix_exec (body := body)
    (show [(94 : Fin 117), 112, 96, 104, 105].Nodup by decide) v₃ S₃
    (csyms A w rhs) tailR (by simpa [S₃, S₂, S₁, cr, OutputPlacement.code] using hrhs)
    (by simpa [S₃, S₂, S₁, cr, OutputPlacement.code, csyms] using hw)
    (by simpa [S₃, S₂, S₁, cr, OutputPlacement.code] using hfresh 104 (by simp))
    (by simpa [S₃, S₂, S₁, cr, OutputPlacement.code] using hfresh 105 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 96 (csyms A w rhs) }
  have he₄' : Exec body (copyPrefix 94 112 96 104 105) (mk v₃ S₃) (10 * w + 10) (mk v₄ S₄) := by
    simpa [S₄, S₃, S₂, S₁, cr, OutputPlacement.code, hfresh 96 (by simp), csyms] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body 99 v₄ S₄
  have hcount : (S₄.R 99).length = L * w := by simp [S₄, S₃, S₂, S₁, cr, OutputPlacement.code]
  refine ⟨v₅, m₁ + ((10 * (L * w) + 10) + ((10 * (L * w) + 10) +
    ((10 * w + 10) + (2 * (L * w) + 2)))), hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, ?_⟩
  · rw [hL, hw] at hm₁
    nlinarith only [hm₁]
  · refine (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅)))).cast
      (by rw [hcount]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = 99
    · subst k
      simp [S₄, S₃, S₂, S₁, stagedIntegerRow, cr, OutputPlacement.code, hfresh 99 (by simp)]
    simp [S₄, S₃, S₂, S₁, stagedIntegerRow, Function.update_apply, hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
