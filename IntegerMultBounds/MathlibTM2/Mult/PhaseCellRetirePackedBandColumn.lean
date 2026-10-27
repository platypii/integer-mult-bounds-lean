module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClippedBandControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryTable

/-! Retire one clipped packed column using only retained unary headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def retirePackedBandColumn : Pr P 224 Q A U :=
  .seq (clippedBandControls 151 190 116 137 138 136 135)
    (.seq (unaryProduct 138 160 131 134 135)
      (.seq (discardPrefix 131 132 134 135) (clearWords [137,138,131])))

def retirePackedBandColumnCost (n W N w : ℕ) : ℕ :=
  let c := min N (n+W+1)-(n-W)
  clippedBandControlsCost n W N+(c*(4*w+9)+4)+
    (6*(c*w)+6)+(2*((n-W)+c+c*w)+7)

theorem retirePackedBandColumn_exec (n W N w : ℕ) (xs tail : List (Fin (A+4)))
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hn : (S.R 151).length = n) (hW : (S.R 190).length = W)
    (hN : (S.R 116).length = N) (hw : (S.R 160).length = w)
    (hsource : S.R 132 = xs++tail)
    (hlen : xs.length = (min N (n+W+1)-(n-W))*w)
    (hfresh : ∀ i ∈ ([131,134,135,136,137,138] : List (Fin 224)), S.R i = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retirePackedBandColumnCost n W N w ∧
      Exec body retirePackedBandColumn (mk v S) m
        (mk v' {S with R := Function.update S.R 132 tail}) := by
  let c := min N (n+W+1)-(n-W)
  obtain ⟨v₁,hu₁,he₁⟩ := clippedBandControls_exec (body := body)
    (index := 151) (band := 190) (total := 116) (cursor := 137) (count := 138) (saved := 136) (tmp := 135)
    (by decide) n W N v S hn hW hN (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  let S₁ : Stacks 224 A := {S with R := (Function.update (Function.update S.R
    137 (List.replicate (n-W) tick)) 138 (List.replicate c tick))}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := 138) (b := 160) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v₁ S₁
    (by simpa [S₁] using hfresh 134 (by simp)) (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 131 (List.replicate (c*w) tick)}
  have he₂' : Exec body (unaryProduct 138 160 131 134 135) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,hw,hfresh 131 (by simp)] using he₂
  have hm₂' : m₂ ≤ c*(4*w+9)+4 := by simpa [S₁,hw] using hm₂
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 132) (trash := 134) (tmp := 135) (by decide) xs tail v₂ S₂
    (by simpa [S₂,S₁] using hsource) (by simp [S₂,hlen,c])
    (by simpa [S₂,S₁] using hfresh 134 (by simp)) (by simpa [S₂,S₁] using hfresh 135 (by simp))
  let S₃ : Stacks 224 A := {S₂ with R := Function.update S₂.R 132 tail}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) ([137,138,131] : List (Fin 224)) (by decide) v₃ S₃
  have hsum : (([137,138,131] : List (Fin 224)).map fun i => (S₃.R i).length).sum = (n-W)+c+c*w := by
    simp [S₃,S₂,S₁,Nat.add_assoc]
  refine ⟨v₄,clippedBandControlsCost n W N+(m₂+((6*xs.length+6)+(2*((n-W)+c+c*w)+7))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [retirePackedBandColumnCost]
    rw [hlen]
    dsimp only [c] at hm₂' ⊢
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h137 : i = 137 <;> by_cases h138 : i = 138 <;> by_cases h131 : i = 131 <;> by_cases h132 : i = 132 <;>
      simp [S₃,S₂,S₁,h137,h138,h131,h132,hfresh 137 (by simp),hfresh 138 (by simp),hfresh 131 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
