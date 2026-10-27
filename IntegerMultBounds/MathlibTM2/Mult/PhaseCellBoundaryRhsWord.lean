module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLoadBoundaryCoordinate

/-! Read one folded boundary RHS word, restoring the coordinate page and ambient RHS. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def boundaryRhsWord : Pr P 148 Q A U :=
  .seq loadBoundaryCoordinate
    (.seq (copyIndexedWord 139 94 110 143 1 2 3 4 5 6) (uclear 139))

def boundaryRhsWordCost (V w j coordinate : ℕ) : ℕ :=
  j*(12*V+9)+27*V+6*coordinate+34+
    (coordinate*(12*w+9)+10*w+22+(2*coordinate+2))

theorem boundaryRhsWord_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (V w j : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (hj : j < B.card) (C : ZMod s → GaussianInt)
    (coordinateTail rhsTail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hindex : (S.R 0).length = j) (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (hcoordinates : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail)
    (hrhs : S.R 110 = cstream A w (chirpLine s C)++rhsTail)
    (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 148, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryRhsWordCost V w j (bFoldAt s B j).val ∧
      Exec body boundaryRhsWord (mk v S) n
        (mk v' {S with R := Function.update S.R 143 (csyms A w (C (bFoldAt s B j))++S.R 143)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,-,-⟩ := loadBoundaryCoordinate_exec (body := body)
    B V j hA hs hj coordinateTail v S hindex hV hcoordinates h106 h139 hblank
  let coordinate := (bFoldAt s B j).val
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 139 (List.replicate coordinate tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := copyIndexedWord_exec (body := body)
    (index := 139) (width := 94) (src := 110) (dst := 143) (skip := 1)
    (savedSkip := 2) (saved := 3) (tmp := 4) (work₁ := 5) (work₂ := 6) (by decide)
    w coordinate (chirpLine s C) (by simpa [coordinate] using (bFoldAt s B j).val_lt) rhsTail v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hw) (by simpa [S₁] using hrhs) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₁] using hblank _ (by decide) (by decide))
  have hword : (chirpLine s C)[coordinate]'(by simpa [coordinate] using (bFoldAt s B j).val_lt) =
      C (bFoldAt s B j) := by simp [chirpLine,coordinate]
  let output := csyms A w (C (bFoldAt s B j))++S.R 143
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 143 output}
  have he₂' : Exec body (copyIndexedWord 139 94 110 143 1 2 3 4 5 6) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂,output,S₁,hword] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 139 v₂ S₂
  have hlen : (S₂.R 139).length = coordinate := by simp [S₂,S₁]
  have he₃' : Exec body (uclear 139) (mk v₂ S₂) (2*coordinate+2)
      (mk v₃ {S₂ with R := Function.update S₂.R 139 []}) := he₃.cast (by rw [hlen]) rfl
  refine ⟨v₃,n₁+(n₂+(2*coordinate+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂' he₃')).cast rfl ?_⟩
  · dsimp only [boundaryRhsWordCost,coordinate] at hn₂ ⊢
    omega
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h : k = 139 <;> by_cases hk : k = 143 <;> simp [S₂,S₁,output,h,hk,h139]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
