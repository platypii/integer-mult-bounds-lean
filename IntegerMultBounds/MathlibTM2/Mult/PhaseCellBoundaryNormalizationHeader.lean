module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizePhysical

/-! Generate the normalization scalar exponent from the retained precision counter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryNormalizationHeader : Pr P 224 Q A U :=
  .seq (udiv 2 119 223 184) (.act (dropTop 223 .done))

theorem boundaryNormalizationHeader_exec (q : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hq : (S.R 119).length = q) (h184 : S.R 184 = []) (h223 : S.R 223 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 4*q+5 ∧
      Exec body boundaryNormalizationHeader (mk v S) n
        (mk v' {S with R := Function.update S.R 223 (List.replicate (q/2-1) tick)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := udiv_exec (body := body) (c := 2) (by decide)
    (a := 119) (b := 223) (t := 184) (by decide) (by decide) (by decide) v S h184
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 223 (List.replicate (q/2) tick)}
  have he₁' : Exec body (udiv 2 119 223 184) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hq,h223] using he₁
  have he₂ := Exec.act (body := body) (dropTop 223 .done) (mk v₁ S₁)
  refine ⟨v₁,n₁+1,hu₁,by rw [hq] at hn₁; omega,(Exec.seq he₁' he₂).cast rfl ?_⟩
  simp [S₁,dropTop,Action.run,update_rt,List.tail_replicate]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
