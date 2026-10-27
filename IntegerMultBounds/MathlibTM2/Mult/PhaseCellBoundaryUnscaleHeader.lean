module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizationHeader

/-! Generate the inverse-scale scalar exponent from the retained precision master. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryUnscaleHeader : Pr P 224 Q A U :=
  .seq (udiv 2 119 223 184) (.seq (umul 1 119 223 184) (.act (.push (.rt 223) (fun _ => tick) .done)))

theorem boundaryUnscaleHeader_exec (q : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hq : (S.R 119).length = q) (h184 : S.R 184 = []) (h223 : S.R 223 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 8*q+9 ∧
      Exec body boundaryUnscaleHeader (mk v S) n
        (mk v' {S with R := Function.update S.R 223 (List.replicate (q+q/2+1) tick)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := udiv_exec (body := body) (c := 2) (by decide)
    (a := 119) (b := 223) (t := 184) (by decide) (by decide) (by decide) v S h184
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 223 (List.replicate (q/2) tick)}
  have he₁' : Exec body (udiv 2 119 223 184) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hq,h223] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := umul_exec body 1 (a := 119) (b := 223) (t := 184)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using h184)
  let S₂ : Stacks 224 A := {S with R := Function.update S.R 223 (List.replicate (q+q/2) tick)}
  have he₂' : Exec body (umul 1 119 223 184) (mk v₁ S₁) (4*q+4) (mk v₂ S₂) := by
    simpa only [S₂,S₁,Function.update_of_ne (show (119 : Fin 224) ≠ 223 by decide),
      Function.update_self,hq,Nat.mul_one,one_mul,← List.replicate_add,Function.update_idem] using he₂
  have he₃ := Exec.act (body := body) (.push (.rt 223) (fun _ => tick) .done) (mk v₂ S₂)
  refine ⟨v₂,n₁+((4*q+4)+1),hu₂.trans hu₁,by rw [hq] at hn₁; omega,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast rfl ?_⟩
  simp [S₂,Action.run,update_rt,List.replicate_succ]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
