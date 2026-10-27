module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetirePackedBandColumn

/-! Use the loop's remaining count as the reverse column index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def retirePackedBandStep : Pr P 224 Q A U :=
  .seq (ucopy 152 151 135) (.seq retirePackedBandColumn (uclear 151))

def retirePackedBandStepCost (n W N w : ℕ) : ℕ :=
  (4*n+4)+retirePackedBandColumnCost n W N w+(2*n+2)

theorem retirePackedBandStep_exec (n W N w : ℕ) (xs tail : List (Fin (A+4)))
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hn : (S.R 152).length = n) (hW : (S.R 190).length = W)
    (hN : (S.R 116).length = N) (hw : (S.R 160).length = w)
    (hsource : S.R 132 = xs++tail)
    (hlen : xs.length = (min N (n+W+1)-(n-W))*w)
    (hfresh : ∀ i ∈ ([151,131,134,135,136,137,138] : List (Fin 224)), S.R i = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retirePackedBandStepCost n W N w ∧
      Exec body retirePackedBandStep (mk v S) m
        (mk v' {S with R := Function.update S.R 132 tail}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 152) (b := 151) (t := 135)
    (by decide) (by decide) (by decide) v S (hfresh 135 (by simp))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 151 (List.replicate n tick)}
  have he₁' : Exec body (ucopy 152 151 135) (mk v S) (4*n+4) (mk v₁ S₁) := by
    simpa [S₁,hn,hfresh 151 (by simp)] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := retirePackedBandColumn_exec (body := body) n W N w xs tail v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hW) (by simpa [S₁] using hN) (by simpa [S₁] using hw)
    (by simpa [S₁] using hsource) hlen (by
      intro i hi
      have hi151 : i ≠ 151 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [S₁,hi151] using hfresh i (List.mem_cons_of_mem 151 hi))
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 132 tail}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 151 v₂ S₂
  refine ⟨v₃,(4*n+4)+(m₂+(2*n+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by simp [S₂,S₁]) ?_⟩
  · dsimp only [retirePackedBandStepCost]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h151 : i = 151 <;> by_cases h132 : i = 132 <;>
      simp [S₂,S₁,h151,h132,hfresh 151 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
