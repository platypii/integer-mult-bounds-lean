module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetirePackedBandTable
public import IntegerMultBounds.MathlibTM2.Host.Stream

/-! Preserve the recovered line while retiring the table and initial interior beneath it. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def retirePublishedBoundary : Pr P 224 Q A U :=
  .seq (unaryProduct 121 160 184 134 135)
    (.seq (transfer 184 132 217 135)
      (.seq retirePackedBandTable (.seq (discardPrefix 184 132 134 135)
        (.seq (moveR 217 132 id) (uclear 184)))))

def retirePublishedBoundaryCost (s N W w : ℕ) : ℕ :=
  retirePackedBandTableCost N W w+18*s*w+9*s+18

theorem retirePublishedBoundary_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W w : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (xs ys tail : List (Fin (A+4))) (hxs : xs.length = s*w) (hys : ys.length = s*w)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hs : (S.R 121).length = s) (hW : (S.R 190).length = W)
    (hN : (S.R 116).length = B.card) (hw : (S.R 160).length = w)
    (hsource : S.R 132 = xs++(bandTableWords A w B W columns 0++ys++tail))
    (hfresh : ∀ i ∈ ([184,217,152,151,131,134,135,136,137,138] : List (Fin 224)), S.R i = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retirePublishedBoundaryCost s B.card W w ∧
      Exec body retirePublishedBoundary (mk v S) m
        (mk v' {S with R := Function.update S.R 132 (xs++tail)}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 160) (dst := 184) (t₁ := 134) (t₂ := 135) (by decide) v S
    (hfresh 134 (by simp)) (hfresh 135 (by simp))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 184 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 121 160 184 134 135) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hs,hw,hfresh 184 (by simp)] using he₁
  have hm₁' : m₁ ≤ s*(4*w+9)+4 := by simpa [hs,hw] using hm₁
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body)
    (count := 184) (src := 132) (dst := 217) (tmp := 135) (by decide) v₁ S₁ xs
    (bandTableWords A w B W columns 0++ys++tail) (by simpa [S₁] using hsource)
    (by simp [S₁,hxs]) (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 224 A := {S₁ with R := (Function.update (Function.update S₁.R
    132 (bandTableWords A w B W columns 0++ys++tail)) 217 xs.reverse)}
  have he₂' : Exec body (transfer 184 132 217 135) (mk v₁ S₁) (4*xs.length+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hfresh 217 (by simp)] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := retirePackedBandTable_exec (body := body) B W w columns hlen
    (ys++tail) v₂ S₂ (by simpa [S₂,S₁] using hW) (by simpa [S₂,S₁] using hN)
    (by simpa [S₂,S₁] using hw) (by simp [S₂,List.append_assoc]) (by
      intro i hi
      have hi184 : i ≠ 184 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hi217 : i ≠ 217 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hi132 : i ≠ 132 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [S₂,S₁,hi184,hi217,hi132] using hfresh i (List.mem_cons_of_mem 184 (List.mem_cons_of_mem 217 hi)))
  let S₃ : Stacks 224 A := {S₂ with R := Function.update S₂.R 132 (ys++tail)}
  obtain ⟨v₄,hu₄,he₄⟩ := discardPrefix_exec (body := body)
    (count := 184) (src := 132) (trash := 134) (tmp := 135) (by decide) ys tail v₃ S₃
    (by simp [S₃]) (by simp [S₃,S₂,S₁,hys])
    (by simpa [S₃,S₂,S₁] using hfresh 134 (by simp)) (by simpa [S₃,S₂,S₁] using hfresh 135 (by simp))
  let S₄ : Stacks 224 A := {S₃ with R := Function.update S₃.R 132 tail}
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec body 217 132 (by decide) id v₄ S₄
  let S₅ : Stacks 224 A := {S₄ with R := Function.update (Function.update S₄.R 217 []) 132 (xs++tail)}
  have he₅' : Exec body (moveR 217 132 id) (mk v₄ S₄) (2*xs.length+2) (mk v₅ S₅) := by
    simpa [S₅,S₄,S₃,S₂,S₁,movedR] using he₅
  obtain ⟨v₆,hu₆,he₆⟩ := uclear_exec body 184 v₅ S₅
  refine ⟨v₆,m₁+((4*xs.length+4)+(m₃+((6*ys.length+6)+((2*xs.length+2)+(2*(s*w)+2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅' he₆))))).cast
      (by simp [S₅,S₄,S₃,S₂,S₁]) ?_⟩
  · dsimp only [retirePublishedBoundaryCost]
    rw [hxs,hys]
    nlinarith only [hm₁',hm₃]
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h184 : i = 184 <;> by_cases h217 : i = 217 <;> by_cases h132 : i = 132 <;>
      simp [S₅,S₄,S₃,S₂,S₁,h184,h217,h132,hfresh 184 (by simp),hfresh 217 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
