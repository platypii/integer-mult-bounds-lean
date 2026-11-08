module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryWorkspace

/-! Lift a restoring two-stream arithmetic execution while the boundary page remains resident. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

theorem boundaryArithmeticProject_twoPorts {A : ℕ} (S : Stacks 151 A)
    (input output : List (Fin (A+4))) :
    embStk boundaryArithmeticReg {S with R := Function.update (Function.update S.R 110 input) 132 output} =
      {(embStk boundaryArithmeticReg S) with R := (Function.update
        (Function.update (embStk boundaryArithmeticReg S).R 110 input) 132 output)} := by
  have hc : boundaryArithmeticReg (132 : Fin 148) = (132 : Fin 151) := by decide
  have hh := boundaryArithmeticProject_updateR_inner {S with R := Function.update S.R 110 input} 132 output
  rw [hc] at hh
  rw [hh,boundaryArithmeticProject_source]

theorem boundaryArithmeticExec_twoPorts (p : Pr P 148 Q A U) (v : HS 151 Q A U) (S : Stacks 151 A)
    (vi : HS 148 Q A U) (n : ℕ) (input output : List (Fin (A+4))) (hu : vi.user = v.user)
    (he : Exec body p (mk (embDn boundaryArithmeticReg v) (embStk boundaryArithmeticReg S)) n
      (mk vi {(embStk boundaryArithmeticReg S) with R := (Function.update
        (Function.update (embStk boundaryArithmeticReg S).R 110 input) 132 output)})) :
    ∃ vf, vf.user = v.user ∧ Exec (embTab boundaryArithmeticReg body) (embProg boundaryArithmeticReg id p)
      (mk v S) n (mk vf {S with R := Function.update (Function.update S.R 110 input) 132 output}) := by
  obtain ⟨vf,_,huser,hex⟩ := exec_emb_ovr (ι := id) (body' := embTab boundaryArithmeticReg body)
    boundaryArithmeticReg_injective (fun _ => rfl) he v rfl S rfl
  refine ⟨vf,huser.trans hu,hex.cast rfl ?_⟩
  apply congrArg (mk vf)
  let M := embStk boundaryArithmeticReg S
  let F : Stacks 148 A := {M with R := Function.update M.R 110 input}
  change embOvr boundaryArithmeticReg ({F with R := Function.update F.R 132 output}).get S = _
  rw [embOvr_updR boundaryArithmeticReg_injective]
  dsimp only [F,M]
  rw [embOvr_updR boundaryArithmeticReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
